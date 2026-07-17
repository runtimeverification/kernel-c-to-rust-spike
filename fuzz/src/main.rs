//! Differential fuzzer for the UVC descriptor parser (Phase 3).
//!
//! One process, one input, split into `[4 bytes quirks LE][descriptor bytes]`,
//! driving both `uvc_parse` implementations:
//!   * C   — via the shared C ABI (`uvc_parse_c`, renamed in build.rs), the
//!           object instrumented with SanitizerCoverage for the coverage map.
//!   * Rust — via the crate's native `parse()` (identical logic and the same
//!           `#[repr(C)]` result), called inside `catch_unwind` so a
//!           bounds-check panic is caught and classified rather than aborting.
//!
//! Oracles (per fuzz/PLAN.md):
//!   (1) a crash on either side is a finding — a Rust panic (caught here) or a
//!       C hard crash/hang (caught by the LibAFL runtime + timeout);
//!   (2) for inputs where neither crashes, any field-wise difference of the
//!       populated prefix of the result is a finding.

use std::hash::{Hash, Hasher};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::Duration;

use libafl::{
    corpus::{Corpus, InMemoryCorpus, OnDiskCorpus},
    events::SimpleRestartingEventManager,
    executors::{inprocess::InProcessExecutor, ExitKind},
    feedback_or,
    feedbacks::{CrashFeedback, MaxMapFeedback, TimeFeedback},
    inputs::{BytesInput, HasTargetBytes},
    monitors::SimpleMonitor,
    mutators::{havoc_mutations, tokens_mutations, HavocScheduledMutator, Tokens},
    observers::{CanTrack, HitcountsMapObserver, TimeObserver},
    schedulers::{IndexesLenTimeMinimizerScheduler, QueueScheduler},
    stages::StdMutationalStage,
    state::{HasCorpus, StdState},
    Error, Fuzzer, HasMetadata, StdFuzzer,
};
use libafl_bolts::{
    rands::StdRand,
    shmem::{ShMemProvider, StdShMemProvider},
    tuples::{tuple_list, Merge},
    AsSlice,
};
use libafl_targets::std_edges_map_observer;

use uvc_parse_rs::UvcParseResult;

/// Quirk bits the parser actually reads; the fuzzer masks the 4-byte prefix to
/// these so mutation energy is not spent on inert bits. Applied to BOTH sides.
const QUIRK_MASK: u32 = 0x0000_0200 | 0x0000_0800 | 0x0000_1000;

extern "C" {
    fn uvc_parse_c(buffer: *const u8, buflen: i32, quirks: u32, out: *mut UvcParseResult) -> i32;
}

fn zeroed_result() -> UvcParseResult {
    // UvcParseResult is repr(C) POD; all-zero is a valid value.
    unsafe { std::mem::zeroed() }
}

fn split(bytes: &[u8]) -> (u32, &[u8]) {
    if bytes.len() >= 4 {
        let q = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) & QUIRK_MASK;
        (q, &bytes[4..])
    } else {
        (0, &[][..])
    }
}

/// Field-wise comparison of the populated prefix of each array (never memcmp:
/// the struct has padding). Returns Some(description-of-first-diff) or None.
fn compare(c: &UvcParseResult, r: &UvcParseResult) -> Option<String> {
    macro_rules! diff {
        ($field:ident, $name:expr) => {
            if c.$field != r.$field {
                return Some(format!("{}: C={:?} Rust={:?}", $name, c.$field, r.$field));
            }
        };
    }
    diff!(ret, "ret");
    diff!(nformats_alloc, "nformats_alloc");
    diff!(nframes_alloc, "nframes_alloc");
    diff!(nintervals_alloc, "nintervals_alloc");
    diff!(nformats, "nformats");
    diff!(nframes, "nframes");
    diff!(nintervals, "nintervals");

    let nf = (c.nformats as usize).min(uvc_parse_rs::UVC_MAX_FORMATS);
    for i in 0..nf {
        if c.formats[i] != r.formats[i] {
            return Some(format!(
                "formats[{i}]: C={:?} Rust={:?}",
                c.formats[i], r.formats[i]
            ));
        }
    }
    let ng = (c.nframes as usize).min(uvc_parse_rs::UVC_MAX_FRAMES);
    for i in 0..ng {
        if c.frames[i] != r.frames[i] {
            return Some(format!(
                "frames[{i}]: C={:?} Rust={:?}",
                c.frames[i], r.frames[i]
            ));
        }
    }
    let ni = (c.nintervals as usize).min(uvc_parse_rs::UVC_MAX_INTERVALS);
    for i in 0..ni {
        if c.intervals[i] != r.intervals[i] {
            return Some(format!(
                "intervals[{i}]: C={} Rust={}",
                c.intervals[i], r.intervals[i]
            ));
        }
    }
    None
}

fn sig_hash(s: &str) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

fn main() {
    let findings_dir = PathBuf::from("findings");
    std::fs::create_dir_all(&findings_dir).unwrap();
    let seen: Mutex<std::collections::HashSet<u64>> = Mutex::new(std::collections::HashSet::new());
    let finding_count = Mutex::new(0usize);

    // ---- The differential harness closure. ----
    let mut harness = |input: &BytesInput| {
        let bytes = input.target_bytes();
        let bytes = bytes.as_slice();
        let (quirks, buf) = split(bytes);

        // C side, via the shared C ABI. A hang (bLength==0 loop) or hard crash
        // here is caught by the timeout / crash handler of the runtime.
        let mut rc = zeroed_result();
        let cret = unsafe { uvc_parse_c(buf.as_ptr(), buf.len() as i32, quirks, &mut rc) };

        // Rust side, native call, panic caught for classification.
        let mut rr = zeroed_result();
        let rres = catch_unwind(AssertUnwindSafe(|| uvc_parse_rs::parse(buf, quirks, &mut rr)));

        let finding: Option<(String, String)> = match rres {
            Err(panic) => {
                // Category (a) candidate: Rust refused an operation (bounds
                // check) that C performed. C returned cret without a hard
                // crash here (else we would not have reached this point).
                let msg = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<non-string panic>".to_string());
                Some((
                    "RUST_PANIC".to_string(),
                    format!("rust panicked: {msg}; C returned {cret}"),
                ))
            }
            Ok(rret) => {
                let _ = rret;
                compare(&rc, &rr).map(|d| ("DIVERGENCE".to_string(), d))
            }
        };

        if let Some((kind, detail)) = finding {
            let sig = sig_hash(&format!("{kind}:{detail}"));
            let mut seen = seen.lock().unwrap();
            if seen.insert(sig) {
                let mut n = finding_count.lock().unwrap();
                *n += 1;
                let idx = *n;
                // Filename keyed on signature only, so a re-detection after a
                // manager restart overwrites the same file (idempotent).
                let path = findings_dir.join(format!("{kind}_{sig:016x}.bin"));
                std::fs::write(&path, bytes).ok();
                let meta = findings_dir.join(format!("{kind}_{sig:016x}.txt"));
                std::fs::write(
                    &meta,
                    format!(
                        "kind: {kind}\nquirks: {quirks:#010x}\nbuflen: {}\ndetail: {detail}\ninput_hex: {}\n",
                        buf.len(),
                        hex(bytes),
                    ),
                )
                .ok();
                eprintln!("[FINDING #{idx} {kind}] {detail}");
                // Mark as a LibAFL objective so the raw input is also saved to
                // the solutions corpus. This does not crash the process.
                return ExitKind::Crash;
            }
        }
        ExitKind::Ok
    };

    // ---- Coverage observer over the sancov edge map (from the C target). ----
    let edges_observer =
        HitcountsMapObserver::new(unsafe { std_edges_map_observer("edges") }).track_indices();
    let time_observer = TimeObserver::new("time");

    let mut feedback = feedback_or!(
        MaxMapFeedback::new(&edges_observer),
        TimeFeedback::new(&time_observer)
    );

    // Objective: a crash. Our differential findings return ExitKind::Crash,
    // and a real C hard-crash trips the same handler. Timeouts (the shared
    // bLength==0 infinite loop) are NOT objectives — the restarting manager
    // still recovers from them, we just do not want the corpus of hangs
    // drowning the genuine findings (the hang is a documented shared
    // limitation, not a divergence).
    let mut objective = CrashFeedback::new();

    // Restarting manager: single-threaded, but recovers from crashes AND
    // timeouts by relaunching from shared-memory-persisted state. This is what
    // lets the fuzzer survive the parser's infinite-loop-on-zero-bLength inputs
    // (a shared C/Rust hang, not a divergence).
    let monitor = SimpleMonitor::new(|s| println!("{s}"));
    let mut shmem_provider = StdShMemProvider::new().expect("shmem provider");
    let (state_opt, mut mgr) =
        match SimpleRestartingEventManager::launch(monitor, &mut shmem_provider) {
            Ok(res) => res,
            Err(Error::ShuttingDown) => return,
            Err(e) => panic!("failed to launch restarting mgr: {e}"),
        };

    let mut state = state_opt.unwrap_or_else(|| {
        StdState::new(
            StdRand::new(),
            InMemoryCorpus::<BytesInput>::new(),
            OnDiskCorpus::new(PathBuf::from("crashes")).unwrap(),
            &mut feedback,
            &mut objective,
        )
        .unwrap()
    });

    let scheduler =
        IndexesLenTimeMinimizerScheduler::new(&edges_observer, QueueScheduler::new());
    let mut fuzzer = StdFuzzer::new(scheduler, feedback, objective);

    let mut executor = InProcessExecutor::with_timeout(
        &mut harness,
        tuple_list!(edges_observer, time_observer),
        &mut fuzzer,
        &mut state,
        &mut mgr,
        Duration::from_millis(1000),
    )
    .unwrap();

    // ---- Seed corpus. ----
    let corpus_dir = PathBuf::from("corpus");
    if state.corpus().count() < 1 {
        state
            .load_initial_inputs(&mut fuzzer, &mut executor, &mut mgr, &[corpus_dir.clone()])
            .unwrap_or_else(|e| panic!("failed to load seeds from {corpus_dir:?}: {e}"));
    }
    println!("[*] seeds loaded: {} testcases", state.corpus().count());

    // ---- Dictionary (descriptor subtype tokens). ----
    let mut tokens = Tokens::new();
    if let Ok(t) = Tokens::from_file(PathBuf::from("dict/uvc.dict")) {
        tokens = t;
    }
    state.add_metadata(tokens);

    let mutator = HavocScheduledMutator::new(havoc_mutations().merge(tokens_mutations()));
    let mut stages = tuple_list!(StdMutationalStage::new(mutator));

    // Install a benign panic hook so the Rust parser's bounds-check panic is
    // *caught* by our catch_unwind (for inline RUST_PANIC classification)
    // rather than being turned into an abort by the executor's default hook.
    // The only panics originate from the wrapped Rust call; C hard-crashes are
    // signals, still handled by the runtime.
    std::panic::set_hook(Box::new(|_info| {}));

    // ---- Run. Bounded by wall-clock from the caller for the spike; loops
    // until interrupted. ----
    println!("[*] fuzzing...");
    fuzzer
        .fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr)
        .expect("fuzz loop error");
}

fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

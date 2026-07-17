//! Replay one fuzzer input file against the Rust parser and print the result,
//! reporting a bounds-check panic instead of aborting. Mirrors the harness
//! input model: [4 bytes quirks LE][descriptor bytes].
//!
//!   cargo run --release --example triage -- <input-file>
//!   cargo run --release --features vuln --example triage -- <input-file>
//!
//! (the `vuln` feature reintroduces a CVE-2024-53104-class frame-count
//! under-count as a negative control; off by default.)

use std::panic::{catch_unwind, AssertUnwindSafe};
use uvc_parse_rs::{parse, UvcParseResult};

const QUIRK_MASK: u32 = 0x0000_0200 | 0x0000_0800 | 0x0000_1000;

fn main() {
    let path = std::env::args().nth(1).expect("usage: triage <input-file>");
    let data = std::fs::read(&path).expect("read input");

    let (quirks, buf) = if data.len() >= 4 {
        let q = u32::from_le_bytes([data[0], data[1], data[2], data[3]]) & QUIRK_MASK;
        (q, &data[4..])
    } else {
        (0, &data[..])
    };

    std::panic::set_hook(Box::new(|_| {}));
    let mut r: UvcParseResult = unsafe { std::mem::zeroed() };
    let res = catch_unwind(AssertUnwindSafe(|| parse(buf, quirks, &mut r)));
    let _ = std::panic::take_hook();

    match res {
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "<non-string panic>".into());
            println!("Rust: PANIC (memory-safe refusal): {msg}");
        }
        Ok(ret) => {
            println!(
                "Rust: ret={ret} nformats={} nframes={} nintervals={} alloc(f={} fr={} iv={})",
                r.nformats, r.nframes, r.nintervals,
                r.nformats_alloc, r.nframes_alloc, r.nintervals_alloc
            );
            for i in 0..r.nframes.min(8) as usize {
                println!(
                    "Rust:   frame[{i}] {}x{} maxbuf={} defint={}",
                    r.frames[i].w_width, r.frames[i].w_height,
                    r.frames[i].dw_max_video_frame_buffer_size,
                    r.frames[i].dw_default_frame_interval
                );
            }
        }
    }
}

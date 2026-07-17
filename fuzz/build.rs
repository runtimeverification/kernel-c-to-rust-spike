use std::path::PathBuf;

// Compile the extracted C parser (../c/uvc_parse.c) into the fuzzer with
// clang + SanitizerCoverage (trace-pc-guard). The coverage callbacks and the
// edge map are provided by libafl_targets (sancov_pcguard feature), so we do
// NOT link clang's compiler-rt (which is missing in this environment); clang
// only *compiles* to an object, cargo links.
//
// The C entry point `uvc_parse` is renamed to `uvc_parse_c` so it does not
// clash with the Rust crate's exported `#[no_mangle] uvc_parse`.
fn main() {
    let c_dir = PathBuf::from("../c");
    let src = c_dir.join("uvc_parse.c");

    cc::Build::new()
        .compiler("clang")
        .file(&src)
        .include(&c_dir)
        .std("gnu11")
        .opt_level(1)
        .flag("-g")
        .flag("-fsanitize-coverage=trace-pc-guard")
        // Rename the C entry point to avoid symbol clash with the Rust cdylib.
        .define("uvc_parse", Some("uvc_parse_c"))
        .warnings(false)
        .compile("uvcparse_c_cov");

    println!("cargo:rerun-if-changed={}", src.display());
    println!("cargo:rerun-if-changed={}", c_dir.join("uvc_parse.h").display());
    println!("cargo:rerun-if-changed=build.rs");
}

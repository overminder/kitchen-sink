use build_target::Arch;

const FIBO_INTERP: &str = "src/fibo_interp.c";

fn get_fibo_source() -> &'static str {
    let arch = build_target::target_arch().unwrap();
    match arch {
        Arch::AARCH64 => "src/fibo_aarch64.s",
        Arch::X86_64 => "src/fibo_x64.s",
        _ => panic!("Unsupported arch: {arch}"),
    }
}

fn main() {
    let source = get_fibo_source();
    println!("cargo:rerun-if-changed={source}");
    println!("cargo:rerun-if-changed={FIBO_INTERP}");
    // Use the `cc` crate to build a C file and statically link it.
    cc::Build::new()
        .file(source)
        .compile("fibo-asm");
    cc::Build::new()
        .file(FIBO_INTERP)
        .compile("fibo-interp");
}


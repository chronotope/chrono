fn main() {
    println!("cargo:rustc-link-arg=-sEXPORTED_RUNTIME_METHODS=['cwrap']");
    println!("cargo:rustc-link-arg=-sMODULARIZE");
    println!("cargo:rustc-link-arg=-o{}/js/chrono.js", env!("CARGO_MANIFEST_DIR"));
    println!("cargo:rustc-link-arg=--no-entry");
}

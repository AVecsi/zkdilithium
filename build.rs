fn main() {
    let crate_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    cbindgen::Builder::new()
        .with_crate(crate_dir)
        .with_config(cbindgen::Config::from_file("cbindgen.toml").unwrap())
        .with_parse_deps(false)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("zkDilithiumProof.h");
}
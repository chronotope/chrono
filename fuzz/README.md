# Fuzzing Chrono
To fuzz Chrono we rely on the [Cargo-fuzz](https://rust-fuzz.github.io/) project. 

To install cargo-fuzz:
```
cargo install cargo-fuzz
```

To run the Chrono fuzzer, navigate to the top directory of chrono and issue the following command:
```
cargo-fuzz run fuzz_reader
```

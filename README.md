Our code (for Rust_Capability_verification) is in case_studies/cap.


### How to setup


1. setup up opam and rust, please check README.bak.md

2. enter the main root of the project
```bash
make setup-dune
make all
```

enter ./rr_frontend
```bash
./refinedrust build
./refinedrust install
```

3. To test our code: enter ./case_studies/cap

run `cargo refinedrust` to generate the code, `dune build` to run the Coq code in this folder.

The source rust code is in src.


### refinedrust version

2024.12.17 ab0a69d9516347dc602564db094979c487b08e19


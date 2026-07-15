//! The standalone `prove_validity_stacked`/`verify_validity_stacked` roundtrip
//! test was retired when flock's reduction moved to the tower (`F128T`): that
//! path used the GHASH-only Ligerito opener, which no longer matches the
//! tower-valued reduction claims. The reduction (zerocheck + lincheck) is
//! covered by the per-module unit tests and by the VM end-to-end tests
//! (`lean_vm::blake3_flock`), which exercise the real stacked K-opener.

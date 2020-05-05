// gate-test-lazy_normalization_consts

// FIXME(lazy-normalization) We currently don't have a good way to
// test if `#![feature(lazy_normalization_consts)]` features is missing.
//
// Once lazy normalization is more powerful we should definitely replace this
// with an actually relevant test. (#60471)
fn //~ ERROR expected identifier

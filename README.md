[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/fs-walk/rust.yml?style=for-the-badge)](https://github.com/qjerome/fs-walk/actions/workflows/rust.yml)
[![Crates.io Version](https://img.shields.io/crates/v/fs-walk?style=for-the-badge)](https://crates.io/crates/fs-walk)
[![docs.rs](https://img.shields.io/docsrs/fs-walk?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/fs-walk)

<!-- cargo-rdme start -->

`fs_walk` is a crate providing functionalities to walk a
file-system recursively using `std` Rust APIs.

This crate currently supports:
 - depth configuration
 - results chunking to feed any batch processing routine
 - result selection (only files, only dirs, by extension)

# Example

```rust
use fs_walk;

let o = fs_walk::WalkOptions::new()
    // we want to walk only files
    .files()
    // we want files with .o extension
    .extension("o");

assert!(o.walk("./").count() > 0);
```

<!-- cargo-rdme end -->



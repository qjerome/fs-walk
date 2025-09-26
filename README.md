[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/fs-walk/rust.yml?style=for-the-badge)](https://github.com/qjerome/fs-walk/actions/workflows/rust.yml)
[![Crates.io Version](https://img.shields.io/crates/v/fs-walk?style=for-the-badge)](https://crates.io/crates/fs-walk)
[![docs.rs](https://img.shields.io/docsrs/fs-walk?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/fs-walk)

<!-- cargo-rdme start -->

`fs_walk` is a Rust crate for recursively walking the filesystem with flexible options.

## Features
- Depth configuration
- Result chunking for batch processing
- Filtering by extension, name, or regex
- Optional symlink following with loop protection
- Sorting of directory entries

## Installation
Add to your `Cargo.toml`:
```toml
[dependencies]
fs_walk = "0.1"
```

### Cargo Features
- **`regex`**: Enables regex matching for file and directory names.
  Requires the `regex` crate.
  Enable with:
 
 ```toml
  [dependencies]
  fs_walk = { version = "0.1", features = ["regex"] }
 ```

## Usage
```rust
use fs_walk;

// Walk all files and directories
let walker = fs_walk::WalkOptions::new().walk(".");
for p in walker.flatten() {
    println!("{p:?}");
}
```

### Filtering
```rust
use fs_walk;

// Walk only Rust files
let walker = fs_walk::WalkOptions::new()
    .files()
    .extension("rs")
    .walk(".");
for p in walker.flatten() {
    println!("Found Rust file: {p:?}");
}
```

### Chunking
```rust
use fs_walk;

// Process files in chunks of 10
let walker = fs_walk::WalkOptions::new()
    .files()
    .extension("o")
    .walk(".")
    .chunks(10);
for chunk in walker {
    for p in chunk.iter().flatten() {
        println!("{p:?}");
    }
}
```

### Regex Matching
```rust
use fs_walk;

// Walk files matching a regex pattern
let walker = fs_walk::WalkOptions::new()
    .name_regex(r#"^.*\.rs\$"#)
    .unwrap()
    .walk(".");
for p in walker.flatten() {
    println!("Found matching file: {p:?}");
}
```

### Following Symlinks
```rust
use fs_walk;

// Walk directories, following symlinks
let walker = fs_walk::WalkOptions::new()
    .dirs()
    .follow_symlink()
    .walk(".");
for p in walker.flatten() {
    println!("{p:?}");
}
```

<!-- cargo-rdme end -->



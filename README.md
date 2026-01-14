[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/fs-walk/rust.yml?style=for-the-badge)](https://github.com/qjerome/fs-walk/actions/workflows/rust.yml)
[![Crates.io Version](https://img.shields.io/crates/v/fs-walk?style=for-the-badge)](https://crates.io/crates/fs-walk)
[![docs.rs](https://img.shields.io/docsrs/fs-walk?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/fs-walk)

<!-- cargo-rdme start -->

`fs_walk` is a Rust crate for efficiently and flexibly walking the filesystem.
It provides a simple, ergonomic API for recursively traversing directories with fine-grained control over filtering, sorting, and symlink handling.

## Why Use `fs_walk`?
- **Flexible filtering**: Filter by file extension, name, regex, or custom predicates.
- **Batch processing**: Process files in chunks for memory efficiency.
- **Symlink handling**: Safely follow symlinks with loop protection.
- **Ergonomic API**: Chainable methods for intuitive configuration.

## Features
| Feature               | Description                                                                                     |
|-----------------------|-------------------------------------------------------------------------------------------------|
| **Depth control**     | Limit traversal depth to avoid unnecessary work.                                               |
| **Result chunking**   | Process results in batches for memory efficiency.                                              |
| **Filtering**         | Filter by extension, name, regex, or custom predicates.                                        |
| **Symlink support**   | Optionally follow symlinks with loop protection.                                               |
| **Sorting**           | Sort directory entries for consistent results.                                                 |
| **Regex matching**    | Enable regex-based filtering (requires the `regex` feature).                                   |

## Installation
Add `fs_walk` to your `Cargo.toml`:
```toml
[dependencies]
fs_walk = "0.2"
```

### Cargo Features
- **`regex`**: Enables regex matching for file and directory names, using the `regex` crate
  Enable with:
  ```toml
  [dependencies]
  fs_walk = { version = "0.2", features = ["regex"] }
  ```

## Usage

### Basic Usage
Walk all files and directories in the current directory:
```rust
use fs_walk::WalkOptions;

let walker = WalkOptions::new().walk(".");
for path in walker.flatten() {
    println!("Found: {:?}", path);
}
```

### Filtering Files
Walk only Rust files (`.rs` extension):
```rust
use fs_walk::WalkOptions;

let walker = WalkOptions::new()
    .files()
    .extension("rs")
    .walk(".");
for path in walker.flatten() {
    println!("Found Rust file: {:?}", path);
}
```

### Chunking Results
Process files in chunks of 10 for batch operations:
```rust
use fs_walk::WalkOptions;

let walker = WalkOptions::new()
    .files()
    .extension("o")
    .walk(".")
    .chunks(10);
for chunk in walker {
    for path in chunk.iter().flatten() {
        println!("Processing: {:?}", path);
    }
}
```

### Regex Matching
Walk files matching a regex pattern (requires the `regex` feature):
```rust
use fs_walk::WalkOptions;

let walker = WalkOptions::new()
    .name_regex(r#"^.*\.rs$"#)
    .unwrap()
    .walk(".");
for path in walker.flatten() {
    println!("Found matching file: {:?}", path);
}
```

### Following Symlinks
Walk directories while following symlinks (with loop protection):
```rust
use fs_walk::WalkOptions;

let walker = WalkOptions::new()
    .dirs()
    .follow_symlink()
    .walk(".");
for path in walker.flatten() {
    println!("Found directory: {:?}", path);
}
```

## Contributing
Contributions are welcome! If you’d like to report a bug, suggest a feature, or submit a PR.

## License
This project is licensed under the [GPL-3 License](./LICENSE).

<!-- cargo-rdme end -->



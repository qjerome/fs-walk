#![deny(unused_imports)]

//! `fs_walk` is a crate providing functionalities to walk a
//! file-system recursively using `std` Rust APIs.
//!
//! This crate currently supports:
//!     - depth configuration
//!     - results chunking to feed any batch processing routine
//!     - result selection (only files, only dirs, by extension)
//!
//! # Example
//!
//! ```
//! use fs_walk;
//!
//! let o = fs_walk::WalkOptions::new()
//!     // we want to walk only files
//!     .files()
//!     // we want files with .o extension
//!     .extension("o");
//!
//! assert!(o.walk("./").count() > 0);
//! ```

use std::{
    collections::HashSet,
    fs, io,
    path::{Path, PathBuf},
};

/// Structure encoding the desired walking
/// options
///
/// # Example
///
/// ```
/// use fs_walk;
///
/// let o = fs_walk::WalkOptions::new()
///     // we want to walk only files
///     .files()
///     // we want files with .o extension
///     .extension("o");
///
/// assert!(o.walk("./").count() > 0);
/// ```
#[derive(Debug, Default, Clone)]
pub struct WalkOptions {
    dirs_only: bool,
    files_only: bool,
    max_depth: Option<u64>,
    extensions: HashSet<String>,
}

impl WalkOptions {
    /// Create default walking options. The default
    /// behaviour is to return both files and directories.
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    /// use std::path::PathBuf;
    ///
    /// let o = fs_walk::WalkOptions::new();
    ///
    /// let paths: Vec<PathBuf> = o.walk("./").flatten().collect();
    ///
    /// assert!(paths.iter().any(|p| p.is_dir()));
    /// assert!(paths.iter().any(|p| p.is_file()));
    /// ```
    #[inline(always)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Configure walking option to return only
    /// directories
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    ///
    /// let o = fs_walk::WalkOptions::new()
    ///     .dirs();
    ///
    /// for p in o.walk("./").flatten() {
    ///     assert!(p.is_dir());
    /// }
    /// ```
    #[inline(always)]
    pub fn dirs(mut self) -> Self {
        self.dirs_only = true;
        self
    }

    /// Configure walking option to return only
    /// files
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    ///
    /// let o = fs_walk::WalkOptions::new()
    ///     .files();
    ///
    /// for p in o.walk("./").flatten() {
    ///     assert!(p.is_file());
    /// }
    /// ```
    #[inline(always)]
    pub fn files(mut self) -> Self {
        self.files_only = true;
        self
    }

    /// Configure a maximum depth for the walker. If no depth
    /// is specified the walker will walk through all directories
    /// in a BFS way.
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    /// use std::path::Path;
    ///
    /// let o = fs_walk::WalkOptions::new()
    ///     .max_depth(0);
    ///
    /// for p in o.walk("./").flatten() {
    ///     assert_eq!(p.parent(), Some(Path::new(".")));
    /// }
    ///
    /// ```
    #[inline(always)]
    pub fn max_depth(mut self, depth: u64) -> Self {
        self.max_depth = Some(depth);
        self
    }

    /// Configure walker to return only files matching file extension.
    /// For any file, if [Path::extension] is not [None] it will be
    /// checked against `ext`. This function can be called several
    /// times to return files matching one of the desired extension.
    ///
    /// See [Path::extension] for the correct way to specify `ext`.
    ///
    /// # Example
    /// ```
    /// use fs_walk;
    /// use std::path::PathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let o = fs_walk::WalkOptions::new()
    ///     .files()
    ///     .extension("o")
    ///     .extension("rs");
    ///
    /// let paths: Vec<PathBuf> = o.walk("./").flatten().collect();
    ///
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("o"))));
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("rs"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("toml"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("lock"))));
    /// ```
    #[inline(always)]
    pub fn extension<S: AsRef<str>>(mut self, ext: S) -> Self {
        self.extensions.insert(ext.as_ref().to_string());
        self
    }

    /// Turns [self] into a [Walker]
    #[inline(always)]
    pub fn walk<P: AsRef<Path>>(self, p: P) -> Walker {
        Walker::from_path(p).with_options(self)
    }
}

pub struct Chunks {
    it: Walker,
    capacity: usize,
}

impl Iterator for Chunks {
    type Item = Vec<Result<PathBuf, io::Error>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let out: Self::Item = self.it.by_ref().take(self.capacity).collect();
        if out.is_empty() {
            return None;
        }
        Some(out)
    }
}

#[derive(Debug, Default)]
pub struct Walker {
    init: bool,
    root: PathBuf,
    options: WalkOptions,
    queue: Vec<(u64, Result<PathBuf, io::Error>)>,
    marked: HashSet<PathBuf>,
}

impl Walker {
    /// Creates a [Walker] with default [WalkOptions] configured
    /// to walk path `p`.
    ///
    /// If `p` is a file, only that file will be returned when
    /// iterating over the [Walker]
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk::Walker;
    ///
    /// assert!(Walker::from_path("./").count() > 0)
    /// ```
    #[inline(always)]
    pub fn from_path<P: AsRef<Path>>(p: P) -> Self {
        Self {
            root: p.as_ref().to_path_buf(),
            ..Default::default()
        }
    }

    /// Creates a [Walker] with a [WalkOptions] configured
    /// to walk path `p`.
    ///
    /// If `p` is a file, only that file will be returned when
    /// iterating over the [Walker]
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk::{Walker, WalkOptions};
    ///
    /// let o = WalkOptions::new()
    ///     .files();
    ///
    /// assert!(Walker::from_path("./").with_options(o.clone()).flatten().any(|p| p.is_file()));
    /// assert!(!Walker::from_path("./").with_options(o).flatten().any(|p| p.is_dir()));
    /// ```
    #[inline(always)]
    pub fn with_options(mut self, o: WalkOptions) -> Self {
        self.options = o;
        self
    }

    /// Returns a [Chunks] iterator allowing to process [Walker] data
    /// in chunks of desired `size`.
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk::{Walker, WalkOptions};
    ///
    ///
    /// for chunk in Walker::from_path("./").chunks(1) {
    ///     assert_eq!(chunk.len(), 1);
    ///     for p in chunk.iter().flatten() {
    ///         assert!(p.is_dir() || p.is_file());
    ///     }
    /// }
    /// ```
    #[inline(always)]
    pub fn chunks(self, size: usize) -> Chunks {
        Chunks {
            it: self,
            capacity: size,
        }
    }

    #[inline(always)]
    fn queue<P: AsRef<Path>>(&mut self, p: P, depth: u64) {
        if self.marked.contains(p.as_ref()) {
            return;
        }

        if p.as_ref().is_file() {
            self.queue.push((depth, Ok(p.as_ref().to_path_buf())));
        } else if p.as_ref().is_dir() {
            match fs::read_dir(p.as_ref()) {
                Ok(rd) => self
                    .queue
                    .extend(rd.map(|r| (depth, r.map(|de| de.path())))),
                Err(e) => self.queue.push((depth, Err(e))),
            }
        }

        self.marked.insert(p.as_ref().to_path_buf());
    }

    #[inline(always)]
    fn _next(&mut self) -> Option<Result<PathBuf, io::Error>> {
        if !self.init {
            self.queue(self.root.clone(), 0);
            self.init = true;
        }

        if self.queue.is_empty() {
            return None;
        }

        let (depth, item) = self.queue.pop()?;
        if let Ok(p) = item.as_ref() {
            if p.is_dir()
                && (self.options.max_depth.is_some_and(|md| md > depth)
                    || self.options.max_depth.is_none())
            {
                self.queue(p, depth + 1);
            }
        }

        Some(item)
    }
}

impl Iterator for Walker {
    type Item = Result<PathBuf, io::Error>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self._next() {
            if item.is_err() {
                return Some(item);
            }
            match item {
                Ok(p) => {
                    if !self.options.dirs_only && !self.options.files_only {
                        return Some(Ok(p));
                    }

                    if self.options.dirs_only && p.is_dir() {
                        return Some(Ok(p));
                    }

                    if self.options.files_only && p.is_file() {
                        if self.options.extensions.is_empty() {
                            return Some(Ok(p));
                        } else if let Some(ext) = p.extension() {
                            if self
                                .options
                                .extensions
                                .contains(&ext.to_string_lossy().to_string())
                            {
                                return Some(Ok(p));
                            }
                        }
                    }
                }
                Err(e) => return Some(Err(e)),
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {

    use std::ffi::OsStr;

    use super::*;

    #[test]
    fn test_walker() {
        let w = Walker::from_path("./");
        for e in w.flatten() {
            println!("{e:?}")
        }
    }

    #[test]
    fn test_walker_on_file() {
        // walking on a file doesn't return any error instead
        // it returns only the file
        let w = Walker::from_path("./src/lib.rs");
        let v = w.flatten().collect::<Vec<PathBuf>>();

        assert_eq!(v.len(), 1)
    }

    #[test]
    fn test_walker_only_files() {
        let o = WalkOptions::new().files();
        let w = o.walk("./");

        for p in w.flatten() {
            assert!(p.is_file())
        }
    }

    #[test]
    fn test_files_by_extension() {
        let o = WalkOptions::new().files().extension("o");
        let w = o.walk("./");

        let mut c = 0;
        for p in w.flatten() {
            assert_eq!(p.extension(), Some(OsStr::new("o")));
            c += 1;
        }
        assert!(c > 0);
    }

    #[test]
    fn test_files_by_chunks_and_extension() {
        let o = WalkOptions::new().files().extension("o");
        let w = o.walk("./");

        let mut c = 0;
        for chunk in w.chunks(1) {
            assert_eq!(chunk.len(), 1);
            for p in chunk.iter().flatten() {
                assert_eq!(p.extension(), Some(OsStr::new("o")));
                c += 1;
            }
        }
        assert!(c > 0);
    }

    #[test]
    fn test_walker_only_dirs() {
        let o = WalkOptions::new().dirs();
        let w = o.walk("./");

        for p in w.flatten() {
            assert!(p.is_dir());
        }
    }

    #[test]
    fn test_walker_dirs_and_files() {
        let o = WalkOptions::new().dirs().files();
        let w = o.walk("./");

        for p in w.flatten() {
            assert!(p.is_dir() || p.is_file());
        }
    }

    #[test]
    fn test_max_depth() {
        let d0 = WalkOptions::new().max_depth(0).walk("./").count();
        let d1 = WalkOptions::new().max_depth(1).walk("./").count();

        println!("d0={d0} d1={d1}");
        // we verify that at depth 0 we have less items than at depth 1
        assert!(d1 > d0);
    }
}
#![deny(unused_imports)]
//! `fs_walk` is a crate providing functionalities to walk a
//! file-system recursively using `std` Rust APIs.
//!
//! This crate currently supports:
//!  - depth configuration
//!  - results chunking to feed any batch processing routine
//!  - result selection (only files, only dirs, by extension)
//!  - regex matching
//!
//! # Features
//!  - `regex`: enable regex matching
//!
//! # Example
//!
//! ```
//! use fs_walk;
//!
//! let w = fs_walk::WalkOptions::new()
//!     // we want to walk only files
//!     .files()
//!     // we want files with .o extension
//!     .extension("o")
//!     .walk("./");
//!
//! assert!(w.count() > 0);
//! ```

use std::{
    collections::{HashSet, VecDeque},
    fs, io,
    path::{Path, PathBuf},
};

#[cfg(feature = "regex")]
use regex::Regex;

/// Structure encoding the desired walking
/// options
///
/// # Example
///
/// ```
/// use fs_walk;
///
/// let w = fs_walk::WalkOptions::new()
///     // we want to walk only files
///     .files()
///     // we want files with .o extension
///     .extension("o")
///     .walk("./");
///
/// assert!(w.count() > 0);
/// ```
#[derive(Debug, Default, Clone)]
pub struct WalkOptions {
    sort: bool,
    dirs_only: bool,
    files_only: bool,
    follow_symlink: bool,
    max_depth: Option<u64>,
    extensions: HashSet<String>,
    ends_with: Vec<String>,
    names: HashSet<String>,
    #[cfg(feature = "regex")]
    regex: Vec<Regex>,
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
    /// use fs_walk::WalkOptions;
    ///
    /// for p in WalkOptions::new().dirs().walk("./").flatten() {
    ///     assert!(p.is_dir());
    /// }
    /// ```
    #[inline(always)]
    pub fn dirs(&mut self) -> &mut Self {
        self.dirs_only = true;
        self
    }

    /// Configure walking option to return only
    /// files
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk::WalkOptions;
    ///
    /// for p in WalkOptions::new().files().walk("./").flatten() {
    ///     assert!(p.is_file());
    /// }
    /// ```
    #[inline(always)]
    pub fn files(&mut self) -> &mut Self {
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
    /// use fs_walk::WalkOptions;
    /// use std::path::Path;
    ///
    /// for p in WalkOptions::new().max_depth(0).walk("./").flatten() {
    ///     assert_eq!(p.parent(), Some(Path::new(".")));
    /// }
    ///
    /// ```
    #[inline(always)]
    pub fn max_depth(&mut self, depth: u64) -> &mut Self {
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
    /// let wk = fs_walk::WalkOptions::new()
    ///     .files()
    ///     .extension("o")
    ///     .extension("rs")
    ///     .walk("./");
    ///
    /// let paths: Vec<PathBuf> = wk.flatten().collect();
    ///
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("o"))));
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("rs"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("toml"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("lock"))));
    /// ```
    #[inline(always)]
    pub fn extension<S: AsRef<str>>(&mut self, ext: S) -> &mut Self {
        self.extensions.insert(ext.as_ref().to_string());
        self
    }

    /// Configure walker to return files ending with pattern `pat`
    /// For any file, if [Path::to_string_lossy] **ends with** pattern
    /// `pat` it is going to be returned.
    ///
    /// This method can be used to match path with double extensions (i.e. `.txt.gz`)
    /// without having to do manual pattern matching on walker's output.
    ///
    /// See [str::ends_with] for more detail about matching
    ///
    /// # Example
    /// ```
    /// use fs_walk;
    /// use std::path::PathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let wk = fs_walk::WalkOptions::new()
    ///     .files()
    ///     .extension("o")
    ///     // we can put . here not in extension
    ///     // can be used to match path with double extensions
    ///     .ends_with(".rs")
    ///     .walk("./");
    ///
    /// let paths: Vec<PathBuf> = wk.flatten().collect();
    ///
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("o"))));
    /// assert!(paths.iter().any(|p| p.extension() == Some(OsStr::new("rs"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("toml"))));
    /// assert!(!paths.iter().any(|p| p.extension() == Some(OsStr::new("lock"))));
    /// ```
    #[inline(always)]
    pub fn ends_with<S: AsRef<str>>(&mut self, pat: S) -> &mut Self {
        self.ends_with.push(pat.as_ref().to_string());
        self
    }

    /// Configure walker to return only paths with [Path::file_name] matching `name`
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    /// use std::path::PathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let wk = fs_walk::WalkOptions::new()
    ///     .name("lib.rs")
    ///     .walk("./");
    ///
    /// let paths: Vec<PathBuf> = wk.flatten().collect();
    ///
    /// assert!(paths.iter().all(|p| p.file_name() == Some(OsStr::new("lib.rs"))));
    /// assert!(paths.iter().all(|p| p.is_file()));
    /// ```
    #[inline(always)]
    pub fn name<S: AsRef<str>>(&mut self, name: S) -> &mut Self {
        self.names.insert(name.as_ref().to_string());
        self
    }

    /// Configure walker to return only paths with [Path::file_name] matching `regex`
    ///
    /// # Example
    ///
    /// ```
    /// use fs_walk;
    /// use std::path::PathBuf;
    /// use std::ffi::OsStr;
    ///
    /// let w = fs_walk::WalkOptions::new()
    ///     .name_regex(r#"^(.*\.rs|src|target)$"#)
    ///     .unwrap()
    ///     .walk("./");
    /// let paths: Vec<PathBuf> = w.flatten().collect();
    /// assert!(paths.iter().any(|p| p.is_dir()));
    /// assert!(paths.iter().any(|p| p.is_file()));
    /// ```
    #[inline(always)]
    #[cfg(feature = "regex")]
    pub fn name_regex<S: AsRef<str>>(&mut self, regex: S) -> Result<&mut Self, regex::Error> {
        self.regex.push(Regex::new(regex.as_ref())?);
        Ok(self)
    }

    #[inline(always)]
    fn regex_is_empty(&self) -> bool {
        #[cfg(feature = "regex")]
        return self.regex.is_empty();
        #[cfg(not(feature = "regex"))]
        true
    }

    #[inline(always)]
    fn path_match<P: AsRef<Path>>(&self, p: P) -> bool {
        let p = p.as_ref();

        if self.extensions.is_empty()
            && self.ends_with.is_empty()
            && self.names.is_empty()
            && self.regex_is_empty()
        {
            return true;
        }

        // test filename
        if !self.names.is_empty()
            && p.file_name()
                .and_then(|file_name| file_name.to_str())
                .map(|file_name| self.names.contains(file_name))
                .unwrap_or_default()
        {
            return true;
        }

        // we check for extension
        if !self.extensions.is_empty()
            && p.extension()
                .and_then(|ext| ext.to_str())
                .map(|ext| self.extensions.contains(ext))
                .unwrap_or_default()
        {
            return true;
        }

        // we check for paths ending with pattern
        for trail in self.ends_with.iter() {
            if p.to_string_lossy().ends_with(trail) {
                return true;
            }
        }

        // we check regex
        #[cfg(feature = "regex")]
        if let Some(file_name) = p.file_name().and_then(|n| n.to_str()) {
            for re in self.regex.iter() {
                if re.is_match(file_name) {
                    return true;
                }
            }
        }

        false
    }

    /// Sorts entries at every directory listing
    #[inline(always)]
    pub fn sort(&mut self, value: bool) -> &mut Self {
        self.sort = value;
        self
    }

    /// Turns [self] into a [Walker]
    #[inline(always)]
    pub fn walk<P: AsRef<Path>>(&self, p: P) -> Walker {
        Walker::from_path(p).with_options(self.clone())
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

#[derive(Debug)]
struct PathIterator {
    depth: u64,
    path: Option<PathBuf>,
    items: VecDeque<Result<PathBuf, io::Error>>,
    init: bool,
    sort: bool,
}

impl PathIterator {
    fn new<P: AsRef<Path>>(depth: u64, path: P, sort: bool) -> Self {
        Self {
            depth,
            path: Some(path.as_ref().to_path_buf()),
            items: VecDeque::new(),
            init: false,
            sort,
        }
    }
}

impl Iterator for PathIterator {
    type Item = Result<PathBuf, io::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.init {
            self.init = true;
            // guarantee to exist at init
            let path = self.path.as_ref().unwrap();

            if path.is_file() {
                match self.path.take() {
                    Some(p) => return Some(Ok(p)),
                    None => return None,
                }
            } else {
                match fs::read_dir(path) {
                    Ok(rd) => {
                        let mut tmp: Vec<Result<PathBuf, io::Error>> =
                            rd.map(|r| r.map(|de| de.path())).collect();

                        if self.sort {
                            tmp.sort_by(|res1, res2| {
                                match (res1, res2) {
                                    (Ok(path1), Ok(path2)) => path1.cmp(path2), // Compare paths if both are Ok
                                    (Err(_), Ok(_)) => std::cmp::Ordering::Greater, // Err comes after Ok
                                    (Ok(_), Err(_)) => std::cmp::Ordering::Less, // Ok comes before Err
                                    (Err(e1), Err(e2)) => e1.to_string().cmp(&e2.to_string()), // Compare errors by message
                                }
                            });
                        }

                        self.items.extend(tmp);
                    }
                    Err(e) => self.items.push_back(Err(e)),
                };
            }
        }

        self.items.pop_front()
    }
}

#[derive(Debug, Default)]
pub struct Walker {
    init: bool,
    root: PathBuf,
    options: WalkOptions,
    queue: VecDeque<PathIterator>,
    current: Option<PathIterator>,
    marked: HashSet<[u8; 32]>,
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
    /// let mut o = WalkOptions::new();
    /// o.files();
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
        if let Ok(can) = p.as_ref().canonicalize() {
            let h = blake3::hash(can.as_os_str().as_bytes());

            if !self.marked.contains(h.as_bytes()) {
                self.queue
                    .push_front(PathIterator::new(depth, p, self.options.sort));

                self.marked.insert(h.into());
            }
        }
    }

    #[inline(always)]
    fn _next(&mut self) -> Option<Result<PathBuf, io::Error>> {
        if !self.init {
            self.queue(self.root.clone(), 0);
            self.init = true;
        }

        if let Some(pi) = self.current.as_mut() {
            if let Some(ni) = pi.next() {
                match ni {
                    Ok(p) => {
                        if p.is_file() {
                            Some(Ok(p))
                        } else {
                            let next_depth = pi.depth + 1;
                            if let Some(max_depth) = self.options.max_depth {
                                if next_depth > max_depth {
                                    return Some(Ok(p));
                                }
                            }

                            // we use canonical path for marking directories
                            if let Ok(can) = p.canonicalize() {
                                let mut must_walk = false;

                                if p.is_symlink() && self.options.follow_symlink {
                                    let h = blake3::hash(can.as_os_str().as_bytes());

                                    if !self.marked.contains(h.as_bytes()) {
                                        must_walk |= true;
                                        self.marked.insert(h.into());
                                    }
                                }

                                if must_walk || !p.is_symlink() {
                                    self.queue.push_back(PathIterator::new(
                                        pi.depth + 1,
                                        &can,
                                        self.options.sort,
                                    ));
                                }
                            }

                            Some(Ok(p))
                        }
                    }
                    Err(e) => Some(Err(e)),
                }
            } else {
                self.current = self.queue.pop_front();
                self._next()
            }
        } else {
            if self.queue.is_empty() {
                return None;
            }
            self.current = self.queue.pop_front();
            self._next()
        }
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
                    if p.is_dir()
                        && (!self.options.files_only || self.options.dirs_only)
                        && self.options.path_match(&p)
                    {
                        return Some(Ok(p));
                    }

                    if p.is_file()
                        && (!self.options.dirs_only || self.options.files_only)
                        && self.options.path_match(&p)
                    {
                        return Some(Ok(p));
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
        let w = WalkOptions::new().walk("./src/lib.rs");
        let v = w.flatten().collect::<Vec<PathBuf>>();

        assert_eq!(v.len(), 1)
    }

    #[test]
    fn test_walker_only_files() {
        let mut o = WalkOptions::new();
        o.files();
        let w = o.walk("./");

        for p in w.flatten() {
            assert!(p.is_file())
        }
    }

    #[test]
    fn test_files_by_extension() {
        let mut o = WalkOptions::new();
        o.files().extension("o");

        let w = o.walk("./");

        let mut c = 0;
        for p in w.flatten() {
            assert_eq!(p.extension(), Some(OsStr::new("o")));
            c += 1;
        }
        assert!(c > 0);
    }

    #[test]
    fn test_files_ends_with() {
        let mut o = WalkOptions::new();
        o.ends_with(".o");
        let w = o.walk("./");

        let mut c = 0;
        for p in w.flatten() {
            assert_eq!(p.extension(), Some(OsStr::new("o")));
            c += 1;
        }
        assert!(c > 0);
    }

    #[test]
    fn test_dirs_ends_with() {
        let mut o = WalkOptions::new();
        o.ends_with("src").ends_with(".git");
        let v = o.walk("./").flatten().collect::<Vec<PathBuf>>();

        assert!(v.len() >= 2);
        for p in v.iter() {
            assert!(p.is_dir());
        }
    }

    #[test]
    fn test_files_by_chunks_and_extension() {
        let mut o = WalkOptions::new();
        o.files().extension("o");
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
        let mut o = WalkOptions::new();
        o.dirs();

        let w = o.walk("./");

        for p in w.flatten() {
            assert!(p.is_dir());
        }
    }

    #[test]
    fn test_walker_dirs_and_files() {
        let mut o = WalkOptions::new();
        o.dirs().files();
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

    #[test]
    fn test_sort() {
        let w = WalkOptions::new().max_depth(0).sort(true).walk("./");
        let ns = WalkOptions::new().max_depth(0).sort(false).walk("./");

        let sorted = w.flatten().collect::<Vec<PathBuf>>();
        let mut unsorted = ns.flatten().collect::<Vec<PathBuf>>();

        assert!(sorted.len() > 1);
        assert_ne!(sorted, unsorted);
        unsorted.sort();
        assert_eq!(sorted, unsorted);
    }

    #[test]
    fn test_name() {
        let w = WalkOptions::new().name("lib.rs").name("src").walk("./");

        let v = w.flatten().collect::<Vec<PathBuf>>();
        assert!(v.len() > 1);
        for p in v.iter() {
            if p.file_name().unwrap() == "lib.rs" {
                assert!(p.is_file())
            }
            if p.file_name().unwrap() == "src" {
                assert!(p.is_dir())
            }
        }
    }

    #[test]
    #[cfg(feature = "regex")]
    fn test_name_regex() {
        let mut w = WalkOptions::new();

        w.name_regex(r#"^(.*\.rs|src|target)$"#)
            .unwrap()
            .name_regex(r#".*\.md"#)
            .unwrap();

        assert!(w.clone().dirs().walk("./").count() > 0);
        assert!(w.clone().files().walk("./").count() > 0);
    }
}

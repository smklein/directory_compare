use difference::Changeset;
use itertools::sorted;
use std::cmp::Ordering;
use std::ffi::{OsStr, OsString};
use std::fs::read_to_string;
use std::iter::Peekable;
use std::path::{Path, PathBuf};
use thiserror::Error;
use walkdir::{DirEntry, WalkDir};

#[derive(Error, Debug)]
pub enum DirCompareError {
    #[error("Failed to walk over directory tree: {0}")]
    WalkDir(walkdir::Error),
    #[error("Missing Entry {0:#?}")]
    MissingEntry(OsString),
    #[error("Mismatched Entry Types: [{:#?}]: {:#?} vs [#{:#?}]: {:#?}",
        .lhs.path(),
        .lhs.file_type(),
        .rhs.path(),
        .rhs.file_type()
    )]
    EntryTypeMismatch { lhs: DirEntry, rhs: DirEntry },
    #[error("File contents differ: {0}")]
    ContentsDiffer(String),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

// A wrapper class, containing both the original DirEntry (directly
// returned from Walkdir) and a path relative to the root directory.
#[derive(Clone, Debug)]
struct Entry {
    // Original DirEntry
    dirent: DirEntry,
    // Path relative to provided root directory.
    path: PathBuf,
}

// Move `iter` forward until it returns an entry matching `golden`.
// Returns the DirEntry which contains `golden`.
fn advance_iter<P, I>(
    source: P,
    iter: &mut Peekable<I>,
    golden: &OsStr,
) -> Result<Entry, DirCompareError>
where
    P: AsRef<Path>,
    I: Iterator<Item = walkdir::Result<Entry>>,
{
    loop {
        let result = iter.peek().ok_or_else(|| {
            DirCompareError::MissingEntry(source.as_ref().join(golden.to_owned()).into_os_string())
        })?;

        let item = match result {
            Ok(value) => value,
            Err(_) => {
                // Why this is safe:
                // - We successfully peeked the iterator, so this item exists.
                // - It is an error type.
                //
                // This hackery is a kludge to allow the "non-error" case
                // to continue operating on a non-owned reference, but
                // permitting the error case to take ownership of the error.
                let err = iter.next().unwrap().unwrap_err();
                return Err(DirCompareError::WalkDir(err));
            }
        };

        match item.path.as_path().cmp(Path::new(golden)) {
            Ordering::Less => {
                let _ = iter.next();
            }
            Ordering::Equal => {
                return Ok(item.clone());
            }
            Ordering::Greater => {
                return Err(DirCompareError::MissingEntry(
                    source.as_ref().join(golden.to_owned()).into_os_string(),
                ));
            }
        }
    }
}

fn compare_by_path(a: &DirEntry, b: &DirEntry) -> Ordering {
    a.path().cmp(b.path())
}

fn sorted_walkdir<P>(p: &P) -> impl Iterator<Item = walkdir::Result<Entry>> + '_
where
    P: AsRef<Path>,
{
    WalkDir::new(p)
        // Avoid returning the directory itself.
        .min_depth(1)
        // Return consistent order.
        .sort_by(compare_by_path)
        .into_iter()
        // Strip the provided prefix of the path; we want visibility
        // into the paths of files *relative* to the input path.
        .map(move |item| {
            item.map(|entry| {
                let path = entry.path().strip_prefix(p).unwrap().to_path_buf();
                Entry {
                    dirent: entry,
                    path,
                }
            })
        })
}

/// Compares the selected contents of two directories.
///
/// Checks all requested golden_paths within both directories.
pub fn directory_compare<P, I, P2>(
    golden_paths: &mut I,
    lhs: P2,
    rhs: P2,
) -> Result<(), DirCompareError>
where
    P: AsRef<Path> + Ord,
    P2: AsRef<Path>,
    I: Iterator<Item = P>,
{
    // Stable ordering is necessary for the following comparison
    // algorithm.
    let golden_paths = sorted(golden_paths);
    let mut lhs_iter = sorted_walkdir(&lhs).peekable();
    let mut rhs_iter = sorted_walkdir(&rhs).peekable();

    for golden in golden_paths {
        let golden_os_str = golden.as_ref().as_os_str();

        // Ignore all non-requested paths, advancing the iterators
        // past unrelated content.
        let lhs_entry = advance_iter(&lhs, &mut lhs_iter, golden_os_str)?;
        let rhs_entry = advance_iter(&rhs, &mut rhs_iter, golden_os_str)?;

        if lhs_entry.dirent.file_type() != rhs_entry.dirent.file_type() {
            return Err(DirCompareError::EntryTypeMismatch {
                lhs: lhs_entry.dirent,
                rhs: rhs_entry.dirent,
            });
        }

        if lhs_entry.dirent.file_type().is_file() {
            let lhs_contents = read_to_string(lhs_entry.dirent.path())?;
            let rhs_contents = read_to_string(rhs_entry.dirent.path())?;
            let changes = Changeset::new(&lhs_contents, &rhs_contents, "\n");
            if changes.distance != 0 {
                return Err(DirCompareError::ContentsDiffer(format!(
                    "{:#?} != {:#?}:\n{}",
                    lhs_entry.dirent.path(),
                    rhs_entry.dirent.path(),
                    changes
                )));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn compare_empty() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        let mut iter: std::vec::IntoIter<String> = vec![].into_iter();
        directory_compare(&mut iter, &lhs, &rhs)?;
        Ok(())
    }

    #[test]
    fn compare_file_same_contents() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        directory_compare(&mut vec!["file1.txt"].into_iter(), &lhs, &rhs)?;
        Ok(())
    }

    #[test]
    fn compare_multiple_files_same_contents() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        directory_compare(
            &mut vec!["file1.txt", "file2.txt", "subdirectory/file3.txt"].into_iter(),
            &lhs,
            &rhs,
        )?;
        Ok(())
    }

    #[test]
    fn compare_file_different_contents() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        let result = directory_compare(&mut vec!["differing.txt"].into_iter(), &lhs, &rhs);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            DirCompareError::ContentsDiffer(_)
        ));
        Ok(())
    }

    #[test]
    fn compare_directory_missing() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        let result = directory_compare(&mut vec!["lhs_only"].into_iter(), &lhs, &rhs);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            DirCompareError::MissingEntry(_)
        ));
        Ok(())
    }

    #[test]
    fn compare_file_differing_in_type() -> Result<()> {
        let lhs = "testdata/lhs";
        let rhs = "testdata/rhs";
        let result = directory_compare(&mut vec!["different_type"].into_iter(), &lhs, &rhs);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            DirCompareError::EntryTypeMismatch { lhs: _, rhs: _ }
        ));
        Ok(())
    }
}

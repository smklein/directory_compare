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
pub enum PathCompareError {
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

#[derive(Clone, Debug)]
struct Entry {
    // Original DirEntry
    dirent: DirEntry,
    // Path relative to provided root directory.
    path: PathBuf,
}

// Move `iter` forward until it returns an entry matching `golden`.
// Returns the DirEntry which contains `golden`.
//
// TODO: Return &DirEntry instead of DirEntry clone.
fn advance_iter<I>(iter: &mut Peekable<I>, golden: &OsStr) -> Result<Entry, PathCompareError>
where
    I: Iterator<Item = walkdir::Result<Entry>>,
{
    loop {
        let result = iter
            .peek()
            .ok_or_else(|| PathCompareError::MissingEntry(golden.to_owned()))?;

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
                return Err(PathCompareError::WalkDir(err));
            }
        };

        println!(
            "advance_iter considering: {:#?} vs {:#?}",
            item.path, golden
        );

        match item.path.as_path().cmp(Path::new(golden)) {
            Ordering::Less => {
                println!("  LESS - Not yet!");
                let _ = iter.next();
            }
            Ordering::Equal => {
                println!("  EQ - FOUND IT");
                return Ok(item.clone());
            }
            Ordering::Greater => {
                println!("  GREATER - Too far!");
                return Err(PathCompareError::MissingEntry(golden.to_owned()));
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
    let iter = WalkDir::new(p)
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
        });

    iter
}

/// Compares the selected contents of two directories.
///
/// Checks all requested golden_paths within both directories.
pub fn path_compare<P, I>(golden_paths: &mut I, lhs: &P, rhs: &P) -> Result<(), PathCompareError>
where
    P: AsRef<Path> + Ord,
    I: Iterator<Item = P>,
{
    // Stable ordering is necessary for the following comparison
    // algorithm.
    let mut golden_paths = sorted(golden_paths);
    let mut lhs_iter = sorted_walkdir(&lhs).peekable();
    let mut rhs_iter = sorted_walkdir(&rhs).peekable();

    while let Some(golden) = golden_paths.next() {
        let golden_os_str = golden.as_ref().as_os_str();
        println!(">>> GOLDEN: {:#?}", golden_os_str);
        println!("Checking for LHS file...");
        let lhs_entry = advance_iter(&mut lhs_iter, golden_os_str)?;
        println!("Checking for RHS file...");
        let rhs_entry = advance_iter(&mut rhs_iter, golden_os_str)?;

        if lhs_entry.dirent.file_type() != rhs_entry.dirent.file_type() {
            return Err(PathCompareError::EntryTypeMismatch {
                lhs: lhs_entry.dirent,
                rhs: rhs_entry.dirent,
            });
        }

        if lhs_entry.dirent.file_type().is_file() {
            println!("Comparing contents...");
            // TODO: check these paths
            let lhs_contents = read_to_string(lhs_entry.dirent.path())?;
            let rhs_contents = read_to_string(rhs_entry.dirent.path())?;
            let changes = Changeset::new(&lhs_contents, &rhs_contents, "\n");
            if changes.distance != 0 {
                return Err(PathCompareError::ContentsDiffer(format!(
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
    use std::path::Path;

    #[test]
    fn compare_empty() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        path_compare(&mut vec![].into_iter(), &lhs, &rhs)?;
        Ok(())
    }

    #[test]
    fn compare_file_same_contents() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        path_compare(&mut vec![Path::new("file1.txt")].into_iter(), &lhs, &rhs)?;
        Ok(())
    }

    #[test]
    fn compare_multiple_files_same_contents() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        path_compare(
            &mut vec![
                Path::new("file1.txt"),
                Path::new("file2.txt"),
                Path::new("subdirectory/file3.txt"),
            ]
            .into_iter(),
            &lhs,
            &rhs,
        )?;
        Ok(())
    }

    #[test]
    fn compare_file_different_contents() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        let result = path_compare(
            &mut vec![Path::new("differing.txt")].into_iter(),
            &lhs,
            &rhs,
        );
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathCompareError::ContentsDiffer(_)
        ));
        Ok(())
    }

    #[test]
    fn compare_directory_missing() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        let result = path_compare(&mut vec![Path::new("lhs_only")].into_iter(), &lhs, &rhs);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathCompareError::MissingEntry(_)
        ));
        Ok(())
    }

    #[test]
    fn compare_file_differing_in_type() -> Result<()> {
        let lhs = Path::new("testdata/lhs");
        let rhs = Path::new("testdata/rhs");
        let result = path_compare(
            &mut vec![Path::new("different_type")].into_iter(),
            &lhs,
            &rhs,
        );
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathCompareError::EntryTypeMismatch { lhs: _, rhs: _ }
        ));
        Ok(())
    }
}

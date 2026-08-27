//! File-backed DRAT input with deterministic gzip fallback.
//!
//! Checkers name an ordinary proof path in their manifests.  When that path is
//! absent, [`resolve_drat_or_gzip_path`] admits its `.gz` sibling; the named
//! plain path always wins when both exist.  Limits must be applied to the
//! selected file's stored byte count before calling [`open_drat_reader`].

use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Read};
use std::path::{Path, PathBuf};

use flate2::read::GzDecoder;

enum DratBackingReader {
    /// An ordinary DRAT file.
    Plain(BufReader<File>),
    /// A gzip-compressed DRAT file.
    Gzip(Box<BufReader<GzDecoder<File>>>),
}

/// A buffered plain or gzip-compressed DRAT stream with a decompressed-byte cap.
pub struct DratFileReader {
    reader: DratBackingReader,
    max_decompressed_bytes: u64,
    decompressed_bytes: u64,
}

impl DratFileReader {
    fn remaining(&self) -> usize {
        usize::try_from(
            self.max_decompressed_bytes
                .saturating_sub(self.decompressed_bytes),
        )
        .unwrap_or(usize::MAX)
    }
}

impl Read for DratBackingReader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Plain(reader) => reader.read(buffer),
            Self::Gzip(reader) => reader.read(buffer),
        }
    }
}

impl BufRead for DratBackingReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        match self {
            Self::Plain(reader) => reader.fill_buf(),
            Self::Gzip(reader) => reader.fill_buf(),
        }
    }

    fn consume(&mut self, amount: usize) {
        match self {
            Self::Plain(reader) => reader.consume(amount),
            Self::Gzip(reader) => reader.consume(amount),
        }
    }
}

impl Read for DratFileReader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        let count = {
            let available = self.fill_buf()?;
            let count = available.len().min(buffer.len());
            buffer[..count].copy_from_slice(&available[..count]);
            count
        };
        self.consume(count);
        Ok(count)
    }
}

impl BufRead for DratFileReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let remaining = self.remaining();
        let available = self.reader.fill_buf()?;
        if remaining == 0 && !available.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "proof exceeds decompressed byte limit {}",
                    self.max_decompressed_bytes
                ),
            ));
        }
        Ok(&available[..available.len().min(remaining)])
    }

    fn consume(&mut self, amount: usize) {
        debug_assert!(amount <= self.remaining());
        self.decompressed_bytes += u64::try_from(amount).unwrap_or(u64::MAX);
        self.reader.consume(amount);
    }
}

/// Resolves `path`, or its `.gz` sibling only when `path` is absent.
///
/// # Errors
///
/// Returns an I/O error when neither candidate is readable, or an invalid-input
/// error when the selected candidate is not a regular file.
pub fn resolve_drat_or_gzip_path(path: &Path) -> io::Result<PathBuf> {
    match fs::metadata(path) {
        Ok(metadata) if metadata.is_file() => Ok(path.to_owned()),
        Ok(_) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{} is not a regular proof file", path.display()),
        )),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            let mut compressed = OsString::from(path.as_os_str());
            compressed.push(".gz");
            let compressed = PathBuf::from(compressed);
            let metadata = fs::metadata(&compressed)?;
            if metadata.is_file() {
                Ok(compressed)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("{} is not a regular proof file", compressed.display()),
                ))
            }
        }
        Err(error) => Err(error),
    }
}

/// Opens an exact proof path selected by [`resolve_drat_or_gzip_path`].
///
/// # Errors
///
/// Returns an I/O error when the selected path cannot be opened or its gzip
/// stream cannot be read.
pub fn open_drat_reader(
    path: &Path,
    buffer_capacity: usize,
    max_decompressed_bytes: u64,
) -> io::Result<DratFileReader> {
    let file = File::open(path)?;
    let capacity = buffer_capacity.max(1);
    let reader = if path.extension().is_some_and(|extension| extension == "gz") {
        DratBackingReader::Gzip(Box::new(BufReader::with_capacity(
            capacity,
            GzDecoder::new(file),
        )))
    } else {
        DratBackingReader::Plain(BufReader::with_capacity(capacity, file))
    };
    Ok(DratFileReader {
        reader,
        max_decompressed_bytes,
        decompressed_bytes: 0,
    })
}

#[cfg(test)]
mod tests {
    use std::io::{Read, Write};
    use std::time::{SystemTime, UNIX_EPOCH};

    use flate2::{Compression, write::GzEncoder};

    use super::{open_drat_reader, resolve_drat_or_gzip_path};

    fn directory(label: &str) -> std::path::PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "axeyum-proof-io-{label}-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        path
    }

    #[test]
    fn gzip_is_used_only_when_plain_path_is_absent() {
        let directory = directory("fallback");
        let plain = directory.join("proof.drat");
        let compressed = std::path::PathBuf::from(format!("{}.gz", plain.display()));
        let mut encoder = GzEncoder::new(
            std::fs::File::create(&compressed).unwrap(),
            Compression::default(),
        );
        encoder.write_all(b"0\n").unwrap();
        encoder.finish().unwrap();
        assert_eq!(resolve_drat_or_gzip_path(&plain).unwrap(), compressed);
        std::fs::write(&plain, b"1 0\n").unwrap();
        assert_eq!(resolve_drat_or_gzip_path(&plain).unwrap(), plain);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn gzip_reader_decodes_selected_stream() {
        let directory = directory("reader");
        let path = directory.join("proof.drat.gz");
        let mut encoder = GzEncoder::new(
            std::fs::File::create(&path).unwrap(),
            Compression::default(),
        );
        encoder.write_all(b"0\n").unwrap();
        encoder.finish().unwrap();
        let mut text = String::new();
        open_drat_reader(&path, 1, 1024)
            .unwrap()
            .read_to_string(&mut text)
            .unwrap();
        assert_eq!(text, "0\n");
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn decompressed_limit_fails_closed() {
        let directory = directory("limit");
        let path = directory.join("proof.drat.gz");
        let mut encoder = GzEncoder::new(
            std::fs::File::create(&path).unwrap(),
            Compression::default(),
        );
        encoder.write_all(b"0\n").unwrap();
        encoder.finish().unwrap();
        let mut text = String::new();
        assert!(
            open_drat_reader(&path, 1, 1)
                .unwrap()
                .read_to_string(&mut text)
                .is_err()
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}

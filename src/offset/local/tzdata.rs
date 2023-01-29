//! This module contains functions to locate and parse the tzdata file, which only
//! exists on Android and is a database of all tz files.
//!
//! Logic was mainly ported from https://android.googlesource.com/platform/libcore/+/jb-mr2-release/luni/src/main/java/libcore/util/ZoneInfoDB.java

use core::{cmp::Ordering, convert::TryInto};
use std::{
    fs::File,
    io::{self, ErrorKind, Read, Seek, SeekFrom},
};

use super::tz_info::Error;

// The database uses 32-bit (4 byte) integers.
const TZ_INT_SIZE: usize = 4;
// The first 12 bytes contain a special version string.
const MAGIC_SIZE: usize = 12;
const HEADER_SIZE: usize = MAGIC_SIZE + 3 * TZ_INT_SIZE;
// The database reserves 40 bytes for each id.
const TZ_NAME_SIZE: usize = 40;
const INDEX_ENTRY_SIZE: usize = TZ_NAME_SIZE + 3 * TZ_INT_SIZE;

#[derive(Debug, Clone, Copy)]
struct Header {
    index_offset: usize,
    data_offset: usize,
    _zonetab_offset: usize,
}

#[derive(Debug)]
struct Index(Vec<u8>);

#[derive(Debug, Clone, Copy)]
struct IndexEntry<'a> {
    _name: &'a [u8],
    offset: usize,
    length: usize,
    _raw_utc_offset: usize,
}

pub(super) fn find_tz_data(tz_name: &str) -> Result<Vec<u8>, Error> {
    let mut file = find_file()?;
    find_tz_data_in_file(&mut file, tz_name)
}

fn find_file() -> Result<File, Error> {
    for (env_var, dir) in
        [("ANDROID_DATA", "/misc/zoneinfo/"), ("ANDROID_ROOT", "/usr/share/zoneinfo/")]
    {
        if let Ok(env_value) = std::env::var(env_var) {
            if let Ok(file) = File::open(env_value + dir + "tzdata") {
                return Ok(file);
            }
        }
    }
    Err(Error::Io(io::Error::from(io::ErrorKind::NotFound)))
}

fn find_tz_data_in_file(file: &mut File, tz_name: &str) -> Result<Vec<u8>, Error> {
    let header = Header::new(file)?;
    let index = Index::new(file, header)?;
    if let Some(entry) = index.find_entry(tz_name) {
        file.seek(SeekFrom::Start((entry.offset + header.data_offset) as u64))?;
        let mut tz_data = vec![0u8; entry.length];
        file.read_exact(&mut tz_data)?;
        Ok(tz_data)
    } else {
        Err(Error::Io(io::Error::from(ErrorKind::NotFound)))
    }
}

impl Header {
    fn new(file: &mut File) -> Result<Self, Error> {
        let mut buf = [0; HEADER_SIZE];
        file.read_exact(&mut buf)?;
        if !buf.starts_with(b"tzdata") || buf[MAGIC_SIZE - 1] != 0u8 {
            return Err(Error::InvalidTzdataFile("invalid magic number"));
        }
        Ok(Self {
            index_offset: parse_tz_int(&buf, MAGIC_SIZE) as usize,
            data_offset: parse_tz_int(&buf, MAGIC_SIZE + TZ_INT_SIZE) as usize,
            _zonetab_offset: parse_tz_int(&buf, MAGIC_SIZE + 2 * TZ_INT_SIZE) as usize,
        })
    }
}

impl Index {
    fn new(file: &mut File, header: Header) -> Result<Self, Error> {
        file.seek(SeekFrom::Start(header.index_offset as u64))?;
        let size = (header.data_offset - header.index_offset) as usize;
        let mut bytes = vec![0; size];
        file.read_exact(&mut bytes)?;
        Ok(Self(bytes))
    }

    fn find_entry(&self, name: &str) -> Option<IndexEntry> {
        let name_bytes = name.as_bytes();
        let name_len = name_bytes.len();
        if name_len > TZ_NAME_SIZE {
            return None;
        }

        let zeros = [0u8; TZ_NAME_SIZE];
        let cmp = |chunk: &&[u8]| -> Ordering {
            // tz names always have TZ_NAME_SIZE bytes and are right-padded with 0s
            // so we check that a chunk starts with `name` and the remaining bytes are 0
            chunk[..name_len]
                .cmp(name_bytes)
                .then_with(|| chunk[name_len..TZ_NAME_SIZE].cmp(&zeros[name_len..]))
        };

        let chunks: Vec<_> = self.0.chunks_exact(INDEX_ENTRY_SIZE).collect();
        chunks.binary_search_by(cmp).map(|idx| IndexEntry::new(chunks[idx])).ok()
    }
}

impl<'a> IndexEntry<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            _name: bytes[..TZ_NAME_SIZE].splitn(2, |&b| b == 0u8).next().unwrap(),
            offset: parse_tz_int(bytes, TZ_NAME_SIZE) as usize,
            length: parse_tz_int(bytes, TZ_NAME_SIZE + TZ_INT_SIZE) as usize,
            _raw_utc_offset: parse_tz_int(bytes, TZ_NAME_SIZE + 2 * TZ_INT_SIZE) as usize,
        }
    }
}

/// Panics if slice does not contain [TZ_INT_SIZE] bytes beginning at start.
fn parse_tz_int(slice: &[u8], start: usize) -> u32 {
    u32::from_be_bytes(slice[start..start + TZ_INT_SIZE].try_into().unwrap())
}

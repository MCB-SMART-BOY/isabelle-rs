//! Theory cache — SQLite-backed persistence for compiled theories.
//!
//! ## Schema
//!
//! ```sql
//! CREATE TABLE theory_cache (
//!     path        TEXT NOT NULL,
//!     source_hash TEXT NOT NULL,
//!     compiled_at INTEGER NOT NULL,
//!     theorems    TEXT NOT NULL,  -- JSON array
//!     blob        BLOB NOT NULL,
//!     PRIMARY KEY (path, source_hash)
//! );
//! ```

use rusqlite::{Connection, params};
use sha2::{Sha256, Digest};
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

// =========================================================================
// Cache entry
// =========================================================================

/// A cached compiled theory.
#[derive(Debug, Clone)]
pub struct CacheEntry {
    pub path: String,
    pub source_hash: String,
    pub compiled_at: u64,
    pub theorems: Vec<String>,
    pub blob: Vec<u8>,
}

// =========================================================================
// TheoryCache
// =========================================================================

/// SQLite-backed cache for compiled theory files.
pub struct TheoryCache {
    db: Connection,
}

impl TheoryCache {
    /// Open or create the cache database at the given path.
    pub fn open(path: &Path) -> Result<Self, String> {
        let db = Connection::open(path)
            .map_err(|e| format!("failed to open cache db: {e}"))?;

        db.execute_batch(
            "CREATE TABLE IF NOT EXISTS theory_cache (
                path        TEXT NOT NULL,
                source_hash TEXT NOT NULL,
                compiled_at INTEGER NOT NULL,
                theorems    TEXT NOT NULL,
                blob        BLOB NOT NULL,
                PRIMARY KEY (path, source_hash)
            );
            CREATE INDEX IF NOT EXISTS idx_cache_path ON theory_cache(path);"
        ).map_err(|e| format!("failed to create schema: {e}"))?;

        Ok(TheoryCache { db })
    }

    /// Create an in-memory cache (for testing).
    pub fn in_memory() -> Result<Self, String> {
        let db = Connection::open_in_memory()
            .map_err(|e| format!("failed to create in-memory db: {e}"))?;

        db.execute_batch(
            "CREATE TABLE theory_cache (
                path        TEXT NOT NULL,
                source_hash TEXT NOT NULL,
                compiled_at INTEGER NOT NULL,
                theorems    TEXT NOT NULL,
                blob        BLOB NOT NULL,
                PRIMARY KEY (path, source_hash)
            );"
        ).map_err(|e| format!("failed to create schema: {e}"))?;

        Ok(TheoryCache { db })
    }

    /// Compute SHA256 hash of source text.
    pub fn hash_source(source: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(source.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Look up a cached theory by path + hash.
    pub fn lookup(&self, path: &str, hash: &str) -> Option<CacheEntry> {
        self.db.query_row(
            "SELECT path, source_hash, compiled_at, theorems, blob
             FROM theory_cache WHERE path = ?1 AND source_hash = ?2",
            params![path, hash],
            |row| {
                Ok(CacheEntry {
                    path: row.get(0)?,
                    source_hash: row.get(1)?,
                    compiled_at: row.get(2)?,
                    theorems: serde_json::from_str(&row.get::<_, String>(3)?).unwrap_or_default(),
                    blob: row.get(4)?,
                })
            },
        ).ok()
    }

    /// Store a compiled theory in the cache.
    pub fn store(&self, entry: &CacheEntry) -> Result<(), String> {
        let theorems_json = serde_json::to_string(&entry.theorems)
            .map_err(|e| format!("json error: {e}"))?;

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        self.db.execute(
            "INSERT OR REPLACE INTO theory_cache (path, source_hash, compiled_at, theorems, blob)
             VALUES (?1, ?2, ?3, ?4, ?5)",
            params![entry.path, entry.source_hash, now, theorems_json, entry.blob],
        ).map_err(|e| format!("store failed: {e}"))?;

        Ok(())
    }

    /// List all cached entries.
    pub fn list(&self) -> Result<Vec<CacheEntry>, String> {
        let mut stmt = self.db.prepare(
            "SELECT path, source_hash, compiled_at, theorems, blob FROM theory_cache"
        ).map_err(|e| format!("prepare failed: {e}"))?;

        let entries = stmt.query_map([], |row| {
            Ok(CacheEntry {
                path: row.get(0)?,
                source_hash: row.get(1)?,
                compiled_at: row.get(2)?,
                theorems: serde_json::from_str(&row.get::<_, String>(3)?).unwrap_or_default(),
                blob: row.get(4)?,
            })
        }).map_err(|e| format!("query failed: {e}"))?;

        let mut result = Vec::new();
        for entry in entries {
            result.push(entry.map_err(|e| format!("row error: {e}"))?);
        }
        Ok(result)
    }

    /// Remove a cached entry.
    pub fn remove(&self, path: &str, hash: &str) -> Result<(), String> {
        self.db.execute(
            "DELETE FROM theory_cache WHERE path = ?1 AND source_hash = ?2",
            params![path, hash],
        ).map_err(|e| format!("delete failed: {e}"))?;
        Ok(())
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_source() {
        let h1 = TheoryCache::hash_source("theory Test begin end");
        let h2 = TheoryCache::hash_source("theory Test begin end");
        assert_eq!(h1, h2);
        let h3 = TheoryCache::hash_source("theory Other begin end");
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_store_and_lookup() {
        let cache = TheoryCache::in_memory().unwrap();
        let hash = TheoryCache::hash_source("theory Test begin end");

        let entry = CacheEntry {
            path: "Test.thy".into(),
            source_hash: hash.clone(),
            compiled_at: 0,
            theorems: vec!["True".into(), "refl".into()],
            blob: vec![1, 2, 3],
        };

        cache.store(&entry).unwrap();
        let found = cache.lookup("Test.thy", &hash);
        assert!(found.is_some());
        assert_eq!(found.unwrap().theorems.len(), 2);
    }

    #[test]
    fn test_lookup_miss() {
        let cache = TheoryCache::in_memory().unwrap();
        let found = cache.lookup("nonexistent.thy", "deadbeef");
        assert!(found.is_none());
    }
}

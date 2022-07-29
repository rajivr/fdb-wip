//! Functions and constants documenting the organization of the
//! reserved keyspace in the database beginning with `\xFF`.

// In FoundationDB this information is maintained in
//
// https://github.com/apple/foundationdb/blob/7.1.7/fdbclient/SystemData.cpp
// https://github.com/apple/foundationdb/blob/7.1.7/fdbclient/SystemData.h
//
// and RecordLayer has constants defined in
//
// https://github.com/FoundationDB/fdb-record-layer/blob/3.2.262.0/fdb-extensions/src/main/java/com/apple/foundationdb/system/SystemKeyspace.java

use bytes::Bytes;

// System Keys

/// Metadata Version Key
pub const METADATA_VERSION_KEY: Bytes = Bytes::from_static(b"\xFF/metadataVersion");

/// Primary Datacenter Key
pub const PRIMARY_DATACENTER_KEY: Bytes = Bytes::from_static(b"\xFF/primaryDatacenter");

/// Timekeeper Prefix
///
/// Maintains wall clock to version map
pub const TIMEKEEPER_PREFIX: Bytes = Bytes::from_static(b"\xFF\x02/timeKeeper/map/");

/// Client Latency Info Prefix
pub const CLIENT_LATENCY_INFO_PREFIX: Bytes =
    Bytes::from_static(b"\xFF\x02/fdbClientInfo/client_latency/");

// Special Keys

/// Connection String Key
pub const CONNECTION_STRING_KEY: Bytes = Bytes::from_static(b"\xFF\xFF/connection_string");

/// Cluster File Path
pub const CLUSTER_FILE_PATH_KEY: Bytes = Bytes::from_static(b"\xFF\xFF/cluster_file_path");

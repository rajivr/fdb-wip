//! Provides a set of utilities for serializing and deserializing
//! typed data for use in FDB.
//!
//! When data is packed together into a [`Tuple`] it is suitable for
//! use as an index or organizational structure within FDB. See
//! [general Tuple documentation] for more information about how
//! [`Tuple`] sort and can be uset to efficiently model data.
//!
//! [general Tuple documentation]: https://apple.github.io/foundationdb/data-modeling.html#data-modeling-tuples
mod element;
mod null;
mod versionstamp;

// We do this in order to preserve consistency with Java and Go
// bindings.
#[allow(clippy::module_inception)]
mod tuple;

mod tuple_schema;

pub mod key_util;

pub(crate) use element::TupleValue;

pub use null::Null;
pub use tuple::{Tuple, TupleElementGet, TupleElementPop, TupleElementPush};
pub use tuple_schema::{TupleSchema, TupleSchemaElement};
pub use versionstamp::Versionstamp;

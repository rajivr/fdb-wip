use std::collections::VecDeque;

use crate::tuple::{Tuple, TupleValue};

/// Represents a schema for a [`Tuple`].
///
/// A [`TupleSchema`] consists of [`TupleSchemaElement`]s.
#[derive(Debug, Clone, PartialEq)]
pub struct TupleSchema {
    elements: VecDeque<TupleSchemaElement>,
}

impl TupleSchema {
    /// Create a new [`TupleSchema`]
    pub fn new() -> TupleSchema {
        TupleSchema {
            elements: VecDeque::new(),
        }
    }

    /// Provides a reference to [`TupleSchemaElement`] at the given
    /// index.
    pub fn get(&self, index: usize) -> Option<&TupleSchemaElement> {
        self.elements.get(index)
    }

    /// Removes the last [`TupleSchemaElement`] from the
    /// [`TupleSchema`] and returns it, or `None` if it is empty.
    pub fn pop_back(&mut self) -> Option<TupleSchemaElement> {
        self.elements.pop_back()
    }

    /// Removes the first [`TupleSchemaElement`] from the
    /// [`TupleSchema`] and returns it, or `None` if it is empty.
    pub fn pop_front(&mut self) -> Option<TupleSchemaElement> {
        self.elements.pop_front()
    }

    /// Appends a [`TupleSchemaElement`].
    pub fn push_back(&mut self, value: TupleSchemaElement) {
        self.elements.push_back(value)
    }

    /// Prepends a [`TupleSchemaElement`].
    pub fn push_front<T>(&mut self, value: TupleSchemaElement) {
        self.elements.push_front(value)
    }

    /// Returns `true` if the [`TupleSchema`] is empty.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns the number of [`TupleSchemaElement`]'s in the
    /// [`TupleSchema`].
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if the [`Tuple`] conforms to this [`TupleSchema`].
    pub fn validate(&self, tuple: &Tuple) -> bool {
        let mut tuple_visitor = TupleVisitor::new(tuple);
        walk_tuple_schema(&mut tuple_visitor, self)
    }
}

impl Default for TupleSchema {
    fn default() -> TupleSchema {
        TupleSchema::new()
    }
}

/// Represents the elements that a [`TupleSchema`] may contain.
#[derive(Debug, Clone, PartialEq)]
pub enum TupleSchemaElement {
    /// [`Null`] value
    ///
    /// [`Null`]: crate::tuple::Null
    Null,
    /// [`Bytes`] value
    ///
    /// [`Bytes`]: bytes::Bytes
    Bytes,
    /// [`String`] value
    String,
    /// Nested [`Tuple`] value
    Tuple(TupleSchema),
    /// Integer value
    ///
    /// ## Note
    ///
    /// Integer value can be a [`i8`], [`i16`], [`i32`], [`i64`] or
    /// [`BigInt`].
    ///
    /// [`BigInt`]: num_bigint::BigInt
    Integer,
    /// [`f32`] value
    Float,
    /// [`f64`] value
    Double,
    /// [`bool`] value
    Boolean,
    /// [`Uuid`] value
    ///
    /// [`Uuid`]: uuid::Uuid
    Uuid,
    /// [`Versionstamp`] value
    ///
    /// [`Versionstamp`]: crate::tuple::Versionstamp
    Versionstamp,
    /// Optional [`Bytes`] value
    ///
    /// [`Bytes`]: bytes::Bytes
    MaybeBytes,
    /// Optional [`String`] value
    MaybeString,
    /// Optional nested [`Tuple`] value
    MaybeTuple(TupleSchema),
    /// Optional integer value
    ///
    /// ## Note
    ///
    /// Integer value can be a [`i8`], [`i16`], [`i32`], [`i64`] or
    /// [`BigInt`].
    ///
    /// [`BigInt`]: num_bigint::BigInt
    MaybeInteger,
    /// Optional [`f32`] value
    MaybeFloat,
    /// Optional [`f64`] value
    MaybeDouble,
    /// Optional [`bool`] value
    MaybeBoolean,
    /// Optional [`Uuid`] value
    ///
    /// [`Uuid`]: uuid::Uuid
    MaybeUuid,
    /// Optional [`Versionstamp`] value
    ///
    /// [`Versionstamp`]: crate::tuple::Versionstamp
    MaybeVersionstamp,
}

trait Visitor {
    fn visit_tuple_schema_element(&mut self, tuple_schema_element: &TupleSchemaElement) -> bool;
}

fn walk_tuple_schema(visitor: &mut dyn Visitor, tuple_schema: &TupleSchema) -> bool {
    // TODO: Check for empty schema and visitor.
    for tuple_schema_element in &tuple_schema.elements {
        if !walk_tuple_schema_element(visitor, tuple_schema_element) {
            return false;
        }
    }
    true
}

fn walk_tuple_schema_element(
    visitor: &mut dyn Visitor,
    tuple_schema_element: &TupleSchemaElement,
) -> bool {
    visitor.visit_tuple_schema_element(tuple_schema_element)
}

struct TupleVisitor<'t> {
    tuple: &'t Tuple,
    index: usize,
}

impl<'t> TupleVisitor<'t> {
    fn new(tuple: &'t Tuple) -> TupleVisitor<'t> {
        TupleVisitor { tuple, index: 0 }
    }
}

impl<'t> Visitor for TupleVisitor<'t> {
    fn visit_tuple_schema_element(&mut self, tuple_schema_element: &TupleSchemaElement) -> bool {
        let tuple_value = match self.tuple.get_element(self.index) {
            Some(tv) => tv,
            None => return false,
        };

        self.index += 1;

        let res = match tuple_schema_element {
            TupleSchemaElement::Null => matches!(tuple_value, TupleValue::NullValue),
            TupleSchemaElement::Bytes => matches!(tuple_value, TupleValue::ByteString(_)),
            TupleSchemaElement::String => matches!(tuple_value, TupleValue::UnicodeString(_)),
            TupleSchemaElement::Tuple(ts) => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut tv = TupleVisitor::new(tup);
                    walk_tuple_schema(&mut tv, ts)
                } else {
                    false
                }
            }
            TupleSchemaElement::Integer => {
                matches!(
                    tuple_value,
                    TupleValue::NegativeArbitraryPrecisionInteger(_)
                ) || matches!(tuple_value, TupleValue::NegInt8(_))
                    || matches!(tuple_value, TupleValue::NegInt7(_))
                    || matches!(tuple_value, TupleValue::NegInt6(_))
                    || matches!(tuple_value, TupleValue::NegInt5(_))
                    || matches!(tuple_value, TupleValue::NegInt4(_))
                    || matches!(tuple_value, TupleValue::NegInt3(_))
                    || matches!(tuple_value, TupleValue::NegInt2(_))
                    || matches!(tuple_value, TupleValue::NegInt1(_))
                    || matches!(tuple_value, TupleValue::IntZero)
                    || matches!(tuple_value, TupleValue::PosInt1(_))
                    || matches!(tuple_value, TupleValue::PosInt2(_))
                    || matches!(tuple_value, TupleValue::PosInt3(_))
                    || matches!(tuple_value, TupleValue::PosInt4(_))
                    || matches!(tuple_value, TupleValue::PosInt5(_))
                    || matches!(tuple_value, TupleValue::PosInt6(_))
                    || matches!(tuple_value, TupleValue::PosInt7(_))
                    || matches!(tuple_value, TupleValue::PosInt8(_))
                    || matches!(
                        tuple_value,
                        TupleValue::PositiveArbitraryPrecisionInteger(_)
                    )
            }
            TupleSchemaElement::Float => {
                matches!(tuple_value, TupleValue::IeeeBinaryFloatingPointFloat(_))
            }
            TupleSchemaElement::Double => {
                matches!(tuple_value, TupleValue::IeeeBinaryFloatingPointDouble(_))
            }
            TupleSchemaElement::Boolean => {
                matches!(tuple_value, TupleValue::FalseValue)
                    || matches!(tuple_value, TupleValue::TrueValue)
            }
            TupleSchemaElement::Uuid => matches!(tuple_value, TupleValue::Rfc4122Uuid(_)),
            TupleSchemaElement::Versionstamp => {
                matches!(tuple_value, TupleValue::Versionstamp96Bit(_))
            }
            TupleSchemaElement::MaybeBytes => {
                matches!(tuple_value, TupleValue::ByteString(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeString => {
                matches!(tuple_value, TupleValue::UnicodeString(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeTuple(ts) => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut tv = TupleVisitor::new(tup);
                    walk_tuple_schema(&mut tv, ts)
                } else {
                    matches!(tuple_value, TupleValue::NullValue)
                }
            }
            TupleSchemaElement::MaybeInteger => {
                matches!(
                    tuple_value,
                    TupleValue::NegativeArbitraryPrecisionInteger(_)
                ) || matches!(tuple_value, TupleValue::NegInt8(_))
                    || matches!(tuple_value, TupleValue::NegInt7(_))
                    || matches!(tuple_value, TupleValue::NegInt6(_))
                    || matches!(tuple_value, TupleValue::NegInt5(_))
                    || matches!(tuple_value, TupleValue::NegInt4(_))
                    || matches!(tuple_value, TupleValue::NegInt3(_))
                    || matches!(tuple_value, TupleValue::NegInt2(_))
                    || matches!(tuple_value, TupleValue::NegInt1(_))
                    || matches!(tuple_value, TupleValue::IntZero)
                    || matches!(tuple_value, TupleValue::PosInt1(_))
                    || matches!(tuple_value, TupleValue::PosInt2(_))
                    || matches!(tuple_value, TupleValue::PosInt3(_))
                    || matches!(tuple_value, TupleValue::PosInt4(_))
                    || matches!(tuple_value, TupleValue::PosInt5(_))
                    || matches!(tuple_value, TupleValue::PosInt6(_))
                    || matches!(tuple_value, TupleValue::PosInt7(_))
                    || matches!(tuple_value, TupleValue::PosInt8(_))
                    || matches!(
                        tuple_value,
                        TupleValue::PositiveArbitraryPrecisionInteger(_)
                    )
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeFloat => {
                matches!(tuple_value, TupleValue::IeeeBinaryFloatingPointFloat(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeDouble => {
                matches!(tuple_value, TupleValue::IeeeBinaryFloatingPointDouble(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeBoolean => {
                matches!(tuple_value, TupleValue::FalseValue)
                    || matches!(tuple_value, TupleValue::TrueValue)
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeUuid => {
                matches!(tuple_value, TupleValue::Rfc4122Uuid(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
            TupleSchemaElement::MaybeVersionstamp => {
                matches!(tuple_value, TupleValue::Versionstamp96Bit(_))
                    || matches!(tuple_value, TupleValue::NullValue)
            }
        };

        res
    }
}

#[cfg(test)]
mod tests {
    // TODO: write tests.
}

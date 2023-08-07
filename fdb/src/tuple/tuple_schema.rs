use std::collections::vec_deque::Iter;
use std::collections::VecDeque;

use crate::tuple::{Tuple, TupleValue};

/// Represents a schema for a [`Tuple`].
///
/// A [`TupleSchema`] consists of
/// [`TupleSchemaElement`]s. [`TupleSchema::validate`] method can be
/// used to verify the conformance of a value of [`Tuple`] to its
/// schema.
//
// In the design of `TupleSchema`, when you have a
// `TupleValue::NullValue`, semantically, it could mean
//
//   1. `TupleSchemaElement::Null` or
//
//   2. `TupleSchemaElement::Maybe{Bytes,String,Tuple(_),Integer,
//       Float,Double,Boolean,Uuid,Versionstamp}`.
//
// There is really no way to know just by looking at
// `TupleValue::NullValue`, what schema element it might refer to.
//
// Likewise when you have a `TupleValue::NestedTuple(_)`, semantically
// it could mean
//
//   1. `TupleSchemaElement::Tuple(_)` or
//
//   2. `TupleSchemaElement::ListOf{Bytes,String,Tuple(_), Integer,
//       Float,Double,Boolean,Uuid,Versionstamp}`.
//
// So, when you have a tuple value `((1, 2, 3,), "abcd")`, there is
// really no way to know just by looking at the value if the user
// wanted a schema of `((Integer, Integer, Integer), String)` or if
// the user wanted a schema `(ListOfInteger, String)`. This
// information must be captured elsewhere.
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
    pub fn push_front(&mut self, value: TupleSchemaElement) {
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

    /// Returns an iterator of [`TupleSchemaElement`].
    pub fn iter(&self) -> Iter<'_, TupleSchemaElement> {
        self.elements.iter()
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
    /// List of [`Bytes`] value
    ///
    /// [`Bytes`]: bytes::Bytes
    ListOfBytes,
    /// List of [`String`] value
    ListOfString,
    /// List of [`Tuple`] value
    ListOfTuple(TupleSchema),
    /// List of integer value
    ///
    /// ## Note
    ///
    /// Integer value can be a [`i8`], [`i16`], [`i32`], [`i64`] or
    /// [`BigInt`].
    ///
    /// [`BigInt`]: num_bigint::BigInt
    ListOfInteger,
    /// List of [`f32`] value
    ListOfFloat,
    /// List of [`f64`] value
    ListOfDouble,
    /// List of [`bool`] value
    ListOfBoolean,
    /// List of [`Uuid`] value
    ///
    /// [`Uuid`]: uuid::Uuid
    ListOfUuid,
    /// List of [`Versionstamp`] value
    ///
    /// [`Versionstamp`]: crate::tuple::Versionstamp
    ListOfVersionstamp,
}

trait Visitor {
    fn visit_tuple_schema_element(&mut self, tuple_schema_element: &TupleSchemaElement) -> bool;
    fn len(&self) -> usize;
}

fn walk_tuple_schema(visitor: &mut dyn Visitor, tuple_schema: &TupleSchema) -> bool {
    if visitor.len() == tuple_schema.elements.len() {
        for tuple_schema_element in &tuple_schema.elements {
            if !walk_tuple_schema_element(visitor, tuple_schema_element) {
                return false;
            }
        }
        true
    } else {
        false
    }
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
            TupleSchemaElement::ListOfBytes => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::ByteString(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfString => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::UnicodeString(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfTuple(ts) => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if let TupleValue::NestedTuple(t) = x {
                            let mut tv = TupleVisitor::new(t);

                            if walk_tuple_schema(&mut tv, ts) {
                                continue;
                            } else {
                                res = false;
                                break;
                            }
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfInteger => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::NegativeArbitraryPrecisionInteger(_))
                            || matches!(x, TupleValue::NegInt8(_))
                            || matches!(x, TupleValue::NegInt7(_))
                            || matches!(x, TupleValue::NegInt6(_))
                            || matches!(x, TupleValue::NegInt5(_))
                            || matches!(x, TupleValue::NegInt4(_))
                            || matches!(x, TupleValue::NegInt3(_))
                            || matches!(x, TupleValue::NegInt2(_))
                            || matches!(x, TupleValue::NegInt1(_))
                            || matches!(x, TupleValue::IntZero)
                            || matches!(x, TupleValue::PosInt1(_))
                            || matches!(x, TupleValue::PosInt2(_))
                            || matches!(x, TupleValue::PosInt3(_))
                            || matches!(x, TupleValue::PosInt4(_))
                            || matches!(x, TupleValue::PosInt5(_))
                            || matches!(x, TupleValue::PosInt6(_))
                            || matches!(x, TupleValue::PosInt7(_))
                            || matches!(x, TupleValue::PosInt8(_))
                            || matches!(x, TupleValue::PositiveArbitraryPrecisionInteger(_))
                        {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfFloat => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::IeeeBinaryFloatingPointFloat(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfDouble => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::IeeeBinaryFloatingPointDouble(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfBoolean => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::FalseValue) || matches!(x, TupleValue::TrueValue)
                        {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfUuid => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::Rfc4122Uuid(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
            TupleSchemaElement::ListOfVersionstamp => {
                if let TupleValue::NestedTuple(tup) = tuple_value {
                    let mut res = true;

                    let iter = tup.iter();

                    for x in iter {
                        if matches!(x, TupleValue::Versionstamp96Bit(_)) {
                            continue;
                        } else {
                            res = false;
                            break;
                        }
                    }

                    res
                } else {
                    false
                }
            }
        };

        res
    }

    fn len(&self) -> usize {
        self.tuple.len()
    }
}

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use num_bigint::BigInt;
    use uuid::Uuid;

    use crate::tuple::{Null, Tuple, Versionstamp};

    use super::{TupleSchema, TupleSchemaElement};

    #[test]
    fn pop_back() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_front(TupleSchemaElement::Null);
        tuple_schema.push_front(TupleSchemaElement::Bytes);

        assert_eq!(Some(TupleSchemaElement::Null), tuple_schema.pop_back());
        assert_eq!(Some(TupleSchemaElement::Bytes), tuple_schema.pop_back());
        assert_eq!(None, tuple_schema.pop_back());
    }

    #[test]
    fn pop_front() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_front(TupleSchemaElement::Null);
        tuple_schema.push_front(TupleSchemaElement::Bytes);

        assert_eq!(Some(TupleSchemaElement::Bytes), tuple_schema.pop_front());
        assert_eq!(Some(TupleSchemaElement::Null), tuple_schema.pop_front());
        assert_eq!(None, tuple_schema.pop_back());
    }

    #[test]
    fn push_back() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_back(TupleSchemaElement::Null);
        tuple_schema.push_back(TupleSchemaElement::Bytes);

        assert_eq!(
            tuple_schema.elements,
            vec![TupleSchemaElement::Null, TupleSchemaElement::Bytes],
        )
    }

    #[test]
    fn push_front() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_front(TupleSchemaElement::Null);
        tuple_schema.push_front(TupleSchemaElement::Bytes);

        assert_eq!(
            tuple_schema.elements,
            vec![TupleSchemaElement::Bytes, TupleSchemaElement::Null],
        )
    }

    #[test]
    fn get() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_back(TupleSchemaElement::Null);
        tuple_schema.push_back(TupleSchemaElement::Bytes);

        assert_eq!(tuple_schema.get(0), Some(&TupleSchemaElement::Null));
        assert_eq!(tuple_schema.get(1), Some(&TupleSchemaElement::Bytes));
        assert_eq!(tuple_schema.get(2), None);
    }

    #[test]
    fn is_empty() {
        let mut tuple_schema = TupleSchema::new();

        assert!(tuple_schema.is_empty());

        tuple_schema.push_back(TupleSchemaElement::Null);

        assert!(!tuple_schema.is_empty());
    }

    #[test]
    fn len() {
        let mut tuple_schema = TupleSchema::new();

        assert_eq!(tuple_schema.len(), 0);

        tuple_schema.push_back(TupleSchemaElement::Null);

        assert_eq!(tuple_schema.len(), 1);
    }

    #[test]
    fn validate_empty() {
        {
            let ts = TupleSchema::new();

            let t = Tuple::new();

            assert!(ts.validate(&t));
        }

        {
            let ts = TupleSchema::new();

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);

            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Null);

            let t = Tuple::new();

            assert!(!ts.validate(&t));
        }
    }

    #[test]
    fn validate_single() {
        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Null);

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Bytes);

            let mut t = Tuple::new();
            t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::String);

            let mut t = Tuple::new();
            t.push_back::<String>("hello world".to_string());
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Tuple({
                let mut ts_inner = TupleSchema::new();

                ts_inner.push_back(TupleSchemaElement::Null);

                ts_inner
            }));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut t_inner = Tuple::new();

                t_inner.push_back::<Null>(Null);

                t_inner
            });
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Integer);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(i64::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-72057594037927936);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-72057594037927935);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-281474976710656);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-281474976710655);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-1099511627776);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-1099511627775);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-4294967296);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-4294967295);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-2147483649);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(i32::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-16777216);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-16777215);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-65536);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-65535);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-32769);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(i16::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-256);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-255);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-129);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(i8::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(0);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(i8::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(128);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(255);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(256);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(i16::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(32768);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(65535);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(65536);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(16777215);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(16777216);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(i32::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(2147483648);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(4294967295);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(4294967296);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(1099511627775);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(1099511627776);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(281474976710655);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(281474976710656);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(72057594037927935);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(72057594037927936);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(i64::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());
            ts.validate(&t);
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Float);

            let mut t = Tuple::new();
            t.push_back::<f32>(3.14f32);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Double);

            let mut t = Tuple::new();
            t.push_back::<f64>(-3.14f64);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Boolean);

            let mut t = Tuple::new();
            t.push_back::<bool>(true);
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<bool>(false);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Uuid);

            let mut t = Tuple::new();
            t.push_back::<Uuid>(Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap());
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Versionstamp);

            let mut t = Tuple::new();
            t.push_back::<Versionstamp>(Versionstamp::complete(
                Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                657,
            ));
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeBytes);

            let mut t = Tuple::new();
            t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeString);

            let mut t = Tuple::new();
            t.push_back::<String>("hello world".to_string());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner
            }));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut t_inner = Tuple::new();
                t_inner.push_back::<Null>(Null);
                t_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeInteger);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(i64::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-72057594037927936);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-72057594037927935);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-281474976710656);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-281474976710655);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-1099511627776);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-1099511627775);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-4294967296);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-4294967295);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(-2147483649);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(i32::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-16777216);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-16777215);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-65536);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-65535);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(-32769);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(i16::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-256);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-255);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(-129);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(i8::MIN);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(0);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i8>(i8::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(128);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(255);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(256);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i16>(i16::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(32768);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(65535);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(65536);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(16777215);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(16777216);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i32>(i32::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(2147483648);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(4294967295);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(4294967296);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(1099511627775);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(1099511627776);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(281474976710655);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(281474976710656);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(72057594037927935);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(72057594037927936);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<i64>(i64::MAX);
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());
            ts.validate(&t);

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeFloat);

            let mut t = Tuple::new();
            t.push_back::<f32>(3.14f32);
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeDouble);

            let mut t = Tuple::new();
            t.push_back::<f64>(-3.14f64);
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeBoolean);

            let mut t = Tuple::new();
            t.push_back::<bool>(true);
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<bool>(false);
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeUuid);

            let mut t = Tuple::new();
            t.push_back::<Uuid>(Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeVersionstamp);

            let mut t = Tuple::new();
            t.push_back::<Versionstamp>(Versionstamp::complete(
                Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                657,
            ));
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            assert!(ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfBytes);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Bytes>(Bytes::from_static(b"hello_world1"));
                tup_inner.push_back::<Bytes>(Bytes::from_static(b"hello_world2"));

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Bytes>(Bytes::from_static(b"hello_world1"));
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfString);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<String>("hello_world1".to_string());
                tup_inner.push_back::<String>("hello_world2".to_string());

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Null>(Null);
                tup_inner.push_back::<String>("hello_world1".to_string());

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfTuple({
                let mut ts_inner = TupleSchema::new();

                ts_inner.push_back(TupleSchemaElement::String);
                ts_inner.push_back(TupleSchemaElement::Null);

                ts_inner
            }));

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Tuple>({
                    let mut tup_inner1 = Tuple::new();

                    tup_inner1.push_back::<String>("hello_world1".to_string());
                    tup_inner1.push_back::<Null>(Null);

                    tup_inner1
                });
                tup_inner.push_back::<Tuple>({
                    let mut tup_inner1 = Tuple::new();

                    tup_inner1.push_back::<String>("hello_world2".to_string());
                    tup_inner1.push_back::<Null>(Null);

                    tup_inner1
                });

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Tuple>({
                    let mut tup_inner1 = Tuple::new();

                    tup_inner1.push_back::<String>("hello_world1".to_string());
                    tup_inner1.push_back::<Null>(Null);

                    tup_inner1
                });
                tup_inner.push_back::<Tuple>({
                    let mut tup_inner1 = Tuple::new();

                    tup_inner1.push_back::<Null>(Null);
                    tup_inner1.push_back::<String>("hello_world2".to_string());

                    tup_inner1
                });

                tup_inner
            });
            assert!(!ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Tuple>({
                    let mut tup_inner1 = Tuple::new();

                    tup_inner1.push_back::<String>("hello_world1".to_string());
                    tup_inner1.push_back::<Null>(Null);

                    tup_inner1
                });
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfInteger);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<BigInt>(
                    BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap(),
                );
                tup_inner.push_back::<BigInt>(
                    BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap(),
                );
                tup_inner
                    .push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
                tup_inner.push_back::<i64>(i64::MIN);
                tup_inner.push_back::<i64>(-72057594037927936);
                tup_inner.push_back::<i64>(-72057594037927935);
                tup_inner.push_back::<i64>(-281474976710656);
                tup_inner.push_back::<i64>(-281474976710655);
                tup_inner.push_back::<i64>(-1099511627776);
                tup_inner.push_back::<i64>(-1099511627775);
                tup_inner.push_back::<i64>(-4294967296);
                tup_inner.push_back::<i64>(-4294967295);
                tup_inner.push_back::<i64>(-2147483649);
                tup_inner.push_back::<i32>(i32::MIN);
                tup_inner.push_back::<i32>(-16777216);
                tup_inner.push_back::<i32>(-16777215);
                tup_inner.push_back::<i32>(-65536);
                tup_inner.push_back::<i32>(-65535);
                tup_inner.push_back::<i32>(-32769);
                tup_inner.push_back::<i16>(i16::MIN);
                tup_inner.push_back::<i16>(-256);
                tup_inner.push_back::<i16>(-255);
                tup_inner.push_back::<i16>(-129);
                tup_inner.push_back::<i8>(i8::MIN);
                tup_inner.push_back::<i8>(0);
                tup_inner.push_back::<i8>(i8::MAX);
                tup_inner.push_back::<i16>(128);
                tup_inner.push_back::<i16>(255);
                tup_inner.push_back::<i16>(256);
                tup_inner.push_back::<i16>(i16::MAX);
                tup_inner.push_back::<i32>(32768);
                tup_inner.push_back::<i32>(65535);
                tup_inner.push_back::<i32>(65536);
                tup_inner.push_back::<i32>(16777215);
                tup_inner.push_back::<i32>(16777216);
                tup_inner.push_back::<i32>(i32::MAX);
                tup_inner.push_back::<i64>(2147483648);
                tup_inner.push_back::<i64>(4294967295);
                tup_inner.push_back::<i64>(4294967296);
                tup_inner.push_back::<i64>(1099511627775);
                tup_inner.push_back::<i64>(1099511627776);
                tup_inner.push_back::<i64>(281474976710655);
                tup_inner.push_back::<i64>(281474976710656);
                tup_inner.push_back::<i64>(72057594037927935);
                tup_inner.push_back::<i64>(72057594037927936);
                tup_inner.push_back::<i64>(i64::MAX);
                tup_inner
                    .push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
                tup_inner
                    .push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
                tup_inner
                    .push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<i8>(0);
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfFloat);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<f32>(3.14f32);
                tup_inner.push_back::<f32>(-3.14f32);

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<f32>(3.14f32);
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfDouble);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<f64>(3.14f64);
                tup_inner.push_back::<f64>(-3.14f64);

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Null>(Null);
                tup_inner.push_back::<f64>(3.14f64);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfBoolean);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<bool>(true);
                tup_inner.push_back::<bool>(false);

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<bool>(true);
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfUuid);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Uuid>(
                    Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap(),
                );
                tup_inner.push_back::<Uuid>(
                    Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap(),
                );

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Uuid>(
                    Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap(),
                );
                tup_inner.push_back::<Null>(Null);

                tup_inner
            });
            assert!(!ts.validate(&t));
        }

        {
            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfVersionstamp);

            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Versionstamp>(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                ));
                tup_inner.push_back::<Versionstamp>(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                ));

                tup_inner
            });
            assert!(ts.validate(&t));

            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut tup_inner = Tuple::new();

                tup_inner.push_back::<Null>(Null);
                tup_inner.push_back::<Versionstamp>(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                ));

                tup_inner
            });
            assert!(!ts.validate(&t));
        }
    }

    #[test]
    fn validate_multiple() {
        {
            let mut t = Tuple::new();
            t.push_back::<Null>(Null);
            t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));

            let mut ts1 = TupleSchema::new();
            ts1.push_back(TupleSchemaElement::Null);
            ts1.push_back(TupleSchemaElement::Bytes);
            assert!(ts1.validate(&t));

            let mut ts2 = TupleSchema::new();
            ts2.push_back(TupleSchemaElement::Null);
            ts2.push_back(TupleSchemaElement::MaybeBytes);
            assert!(ts2.validate(&t));
        }

        {
            let mut t = Tuple::new();
            t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));
            t.push_back::<Tuple>({
                let mut t_inner = Tuple::new();
                t_inner.push_back::<Null>(Null);
                t_inner.push_back::<String>("hello_world".to_string());
                t_inner
            });
            t.push_back::<Versionstamp>(Versionstamp::complete(
                Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                657,
            ));

            let mut ts1 = TupleSchema::new();
            ts1.push_back(TupleSchemaElement::Bytes);
            ts1.push_back(TupleSchemaElement::Tuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner.push_back(TupleSchemaElement::String);
                ts_inner
            }));
            ts1.push_back(TupleSchemaElement::Versionstamp);
            assert!(ts1.validate(&t));

            let mut ts2 = TupleSchema::new();
            ts2.push_back(TupleSchemaElement::MaybeBytes);
            ts2.push_back(TupleSchemaElement::MaybeTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner.push_back(TupleSchemaElement::MaybeString);
                ts_inner
            }));
            ts2.push_back(TupleSchemaElement::MaybeVersionstamp);
            assert!(ts2.validate(&t));

            // Invalid schema. Change the order from
            // `(MaybeBytes, (Null, MaybeString), MaybeVersionstamp)` to
            // `((Null, MaybeString), MaybeTuple, MaybeVersionstamp)`
            let mut ts3 = TupleSchema::new();
            ts3.push_back(TupleSchemaElement::MaybeTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner.push_back(TupleSchemaElement::MaybeString);
                ts_inner
            }));
            ts3.push_back(TupleSchemaElement::MaybeBytes);
            ts3.push_back(TupleSchemaElement::MaybeVersionstamp);
            assert!(!ts3.validate(&t));

            // Invalid schema. Change the order from
            // `(MaybeBytes, (Null, MaybeString), MaybeVersionstamp)` to
            // `(MaybeBytes, (MaybeString, Null), MaybeVersionstamp)`
            let mut ts4 = TupleSchema::new();
            ts4.push_back(TupleSchemaElement::MaybeBytes);
            ts4.push_back(TupleSchemaElement::MaybeTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::MaybeString);
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner
            }));
            ts4.push_back(TupleSchemaElement::MaybeVersionstamp);
            assert!(!ts4.validate(&t));
        }
    }

    #[test]
    fn validate_nested() {
        // `((((Null,),),),)`
        let mut ts = TupleSchema::new();
        ts.push_back(TupleSchemaElement::Tuple({
            let mut ts_inner1 = TupleSchema::new();
            ts_inner1.push_back(TupleSchemaElement::Tuple({
                let mut ts_inner2 = TupleSchema::new();
                ts_inner2.push_back(TupleSchemaElement::Tuple({
                    let mut ts_inner3 = TupleSchema::new();
                    ts_inner3.push_back(TupleSchemaElement::Null);
                    ts_inner3
                }));
                ts_inner2
            }));
            ts_inner1
        }));

        let mut t = Tuple::new();
        t.push_back::<Tuple>({
            let mut t_inner1 = Tuple::new();
            t_inner1.push_back::<Tuple>({
                let mut t_inner2 = Tuple::new();
                t_inner2.push_back({
                    let mut t_inner3 = Tuple::new();
                    t_inner3.push_back::<Null>(Null);
                    t_inner3
                });
                t_inner2
            });
            t_inner1
        });

        assert!(ts.validate(&t));
    }

    #[test]
    fn validate_tuple_value_schema_relationship() {
        {
            let mut t = Tuple::new();
            t.push_back::<Null>(Null);

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Null);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeBytes);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeString);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner
            }));
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeInteger);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeFloat);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeDouble);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeBoolean);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeUuid);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::MaybeVersionstamp);
            assert!(ts.validate(&t));
        }

        {
            let mut t = Tuple::new();
            t.push_back::<Tuple>(Tuple::new());

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Tuple(TupleSchema::new()));
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfBytes);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfString);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfTuple({
                let mut ts_inner = TupleSchema::new();
                ts_inner.push_back(TupleSchemaElement::Null);
                ts_inner
            }));
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfInteger);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfFloat);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfDouble);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfBoolean);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfUuid);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfVersionstamp);
            assert!(ts.validate(&t));

            // Tuple of value `((1, 2, 3,), "abcd")` can be a value of
            // two different schemas.
            let mut t = Tuple::new();
            t.push_back::<Tuple>({
                let mut t_inner = Tuple::new();

                t_inner.push_back::<i8>(1);
                t_inner.push_back::<i8>(2);
                t_inner.push_back::<i8>(3);

                t_inner
            });
            t.push_back::<String>("abcd".to_string());

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::Tuple({
                let mut ts_inner = TupleSchema::new();

                ts_inner.push_back(TupleSchemaElement::Integer);
                ts_inner.push_back(TupleSchemaElement::Integer);
                ts_inner.push_back(TupleSchemaElement::Integer);

                ts_inner
            }));
            ts.push_back(TupleSchemaElement::String);
            assert!(ts.validate(&t));

            let mut ts = TupleSchema::new();
            ts.push_back(TupleSchemaElement::ListOfInteger);
            ts.push_back(TupleSchemaElement::String);
            assert!(ts.validate(&t));
        }
    }

    #[test]
    fn iter() {
        let mut tuple_schema = TupleSchema::new();

        tuple_schema.push_back(TupleSchemaElement::Null);
        tuple_schema.push_back(TupleSchemaElement::Bytes);

        for (value, expected) in tuple_schema
            .iter()
            .zip(vec![&TupleSchemaElement::Null, &TupleSchemaElement::Bytes])
        {
            assert_eq!(value, expected);
        }
    }
}

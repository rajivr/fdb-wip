use bytes::{BufMut, Bytes, BytesMut};
use num_bigint::BigInt;
use num_traits::sign::Signed;
use uuid::Uuid;

use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::convert::TryInto;

use crate::error::{
    FdbError, FdbResult, TUPLE_PACK_WITH_VERSIONSTAMP_NOT_FOUND, TUPLE_TRY_FROM_KEY,
    TUPLE_TRY_FROM_VALUE,
};
use crate::range::Range;
use crate::tuple::{
    element::{self, TupleValue},
    Null, Versionstamp,
};
use crate::{Key, Value};

/// Prevent users from implementing private trait.
mod private {
    use bytes::Bytes;
    use num_bigint::BigInt;
    use uuid::Uuid;

    use crate::tuple::{Null, Tuple, Versionstamp};

    pub trait SealedGet {}

    impl SealedGet for &Bytes {}
    impl SealedGet for &String {}
    impl SealedGet for &Uuid {}
    impl SealedGet for BigInt {}
    impl SealedGet for bool {}
    impl SealedGet for f32 {}
    impl SealedGet for f64 {}
    impl SealedGet for i16 {}
    impl SealedGet for i32 {}
    impl SealedGet for i64 {}
    impl SealedGet for i8 {}

    impl SealedGet for &Tuple {}
    impl SealedGet for &Versionstamp {}
    impl SealedGet for Null {}

    pub trait SealedPush {}

    impl SealedPush for BigInt {}
    impl SealedPush for Bytes {}
    impl SealedPush for String {}
    impl SealedPush for Uuid {}
    impl SealedPush for bool {}
    impl SealedPush for f32 {}
    impl SealedPush for f64 {}
    impl SealedPush for i16 {}
    impl SealedPush for i32 {}
    impl SealedPush for i64 {}
    impl SealedPush for i8 {}

    impl SealedPush for Null {}
    impl SealedPush for Versionstamp {}
    impl SealedPush for Tuple {}
}

/// Used by [`Tuple::get`] method.
pub trait TupleElementGet<'a>: private::SealedGet {
    #[doc(hidden)]
    fn get(tuple: &'a Tuple, index: usize) -> Option<Self>
    where
        Self: Sized + 'a;
}

impl<'a> TupleElementGet<'a> for &'a Bytes {
    fn get(tuple: &'a Tuple, index: usize) -> Option<&'a Bytes> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::ByteString(ref b) => Some(b),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for &'a String {
    fn get(tuple: &'a Tuple, index: usize) -> Option<&'a String> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::UnicodeString(ref s) => Some(s),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for &'a Uuid {
    fn get(tuple: &'a Tuple, index: usize) -> Option<&'a Uuid> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::Rfc4122Uuid(ref u) => Some(u),
            _ => None,
        })
    }
}

// A value of `BigInt` type can be returned for any integer
// type. Therefore return an owned type.
impl<'a> TupleElementGet<'a> for BigInt {
    fn get(tuple: &'a Tuple, index: usize) -> Option<BigInt> {
        tuple.get::<i64>(index).map(|x| x.into()).or_else(|| {
            tuple.elements.get(index).and_then(|x| match *x {
                TupleValue::NegativeArbitraryPrecisionInteger(ref i) => Some(i.clone() * -1),
                TupleValue::NegInt8(ref i)
                    if (9223372036854775809..=18446744073709551615).contains(i) =>
                {
                    Some(Into::<BigInt>::into(*i) * -1)
                }
                TupleValue::PosInt8(ref i)
                    if (9223372036854775808..=18446744073709551615).contains(i) =>
                {
                    Some((*i).into())
                }
                TupleValue::PositiveArbitraryPrecisionInteger(ref i) => Some(i.clone()),
                _ => None,
            })
        })
    }
}

impl<'a> TupleElementGet<'a> for bool {
    fn get(tuple: &'a Tuple, index: usize) -> Option<bool> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::FalseValue => Some(false),
            TupleValue::TrueValue => Some(true),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for f32 {
    fn get(tuple: &'a Tuple, index: usize) -> Option<f32> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::IeeeBinaryFloatingPointFloat(f) => Some(f),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for f64 {
    fn get(tuple: &'a Tuple, index: usize) -> Option<f64> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::IeeeBinaryFloatingPointDouble(f) => Some(f),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for i16 {
    fn get(tuple: &Tuple, index: usize) -> Option<i16> {
        tuple.get::<i8>(index).map(|x| x.into()).or_else(|| {
            tuple.elements.get(index).and_then(|x| match *x {
                TupleValue::NegInt2(ref i) if (256..=32768).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i16::try_from(-Into::<i32>::into(*i)).unwrap(),
                ),
                TupleValue::NegInt1(ref i) if (129..=255).contains(i) => {
                    Some(-Into::<i16>::into(*i))
                }
                TupleValue::PosInt1(ref i) if (128..=255).contains(i) => Some((*i).into()),
                TupleValue::PosInt2(ref i) if (256..=32767).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are checking
                    //         for the range.
                    i16::try_from(*i).unwrap(),
                ),
                _ => None,
            })
        })
    }
}

impl<'a> TupleElementGet<'a> for i32 {
    fn get(tuple: &'a Tuple, index: usize) -> Option<i32> {
        tuple.get::<i16>(index).map(|x| x.into()).or_else(|| {
            tuple.elements.get(index).and_then(|x| match *x {
                TupleValue::NegInt4(ref i) if (16777216..=2147483648).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i32::try_from(-Into::<i64>::into(*i)).unwrap(),
                ),
                TupleValue::NegInt3(ref i) if (65536..=16777215).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i32::try_from(-Into::<i64>::into(*i)).unwrap(),
                ),
                TupleValue::NegInt2(ref i) if (32769..=65535).contains(i) => {
                    Some(-Into::<i32>::into(*i))
                }
                TupleValue::PosInt2(ref i) if (32768..=65535).contains(i) => Some((*i).into()),
                TupleValue::PosInt3(ref i) if (65536..=16777215).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i32::try_from(*i).unwrap(),
                ),
                TupleValue::PosInt4(ref i) if (16777216..=2147483647).contains(i) => Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i32::try_from(*i).unwrap(),
                ),
                _ => None,
            })
        })
    }
}

impl<'a> TupleElementGet<'a> for i64 {
    fn get(tuple: &'a Tuple, index: usize) -> Option<i64> {
        tuple.get::<i32>(index).map(|x| x.into()).or_else(|| {
            tuple.elements.get(index).and_then(|x| match *x {
                TupleValue::NegInt8(ref i)
                    if (72057594037927936..=9223372036854775808).contains(i) =>
                {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(-Into::<i128>::into(*i)).unwrap(),
                    )
                }
                TupleValue::NegInt7(ref i) if (281474976710656..=72057594037927935).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(-Into::<i128>::into(*i)).unwrap(),
                    )
                }
                TupleValue::NegInt6(ref i) if (1099511627776..=281474976710655).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(-Into::<i128>::into(*i)).unwrap(),
                    )
                }
                TupleValue::NegInt5(ref i) if (4294967296..=1099511627775).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(-Into::<i128>::into(*i)).unwrap(),
                    )
                }

                TupleValue::NegInt4(ref i) if (2147483649..=4294967295).contains(i) => {
                    Some(-Into::<i64>::into(*i))
                }
                TupleValue::PosInt4(ref i) if (2147483648..=4294967295).contains(i) => {
                    Some((*i).into())
                }
                TupleValue::PosInt5(ref i) if (4294967296..=1099511627775).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(*i).unwrap(),
                    )
                }
                TupleValue::PosInt6(ref i) if (1099511627776..=281474976710655).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(*i).unwrap(),
                    )
                }
                TupleValue::PosInt7(ref i) if (281474976710656..=72057594037927935).contains(i) => {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(*i).unwrap(),
                    )
                }
                TupleValue::PosInt8(ref i)
                    if (72057594037927936..=9223372036854775807).contains(i) =>
                {
                    Some(
                        // Safety: Safe to unwrap here because we
                        //         are checking for the range.
                        i64::try_from(*i).unwrap(),
                    )
                }
                _ => None,
            })
        })
    }
}

impl<'a> TupleElementGet<'a> for i8 {
    fn get(tuple: &'a Tuple, index: usize) -> Option<i8> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::NegInt1(i) if i <= 128 => {
                Some(
                    // Safety: Safe to unwrap here because we are
                    //         checking for the range.
                    i8::try_from(-Into::<i16>::into(i)).unwrap(),
                )
            }
            TupleValue::IntZero => Some(0),
            TupleValue::PosInt1(i) if i <= 127 => Some(
                // Safety: Safe to unwrap here because we are
                //         checking for the range.
                i8::try_from(i).unwrap(),
            ),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for Null {
    fn get(tuple: &'a Tuple, index: usize) -> Option<Null> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::NullValue => Some(Null),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for &'a Versionstamp {
    fn get(tuple: &'a Tuple, index: usize) -> Option<&'a Versionstamp> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::Versionstamp96Bit(ref v) => Some(v),
            _ => None,
        })
    }
}

impl<'a> TupleElementGet<'a> for &'a Tuple {
    fn get(tuple: &'a Tuple, index: usize) -> Option<&'a Tuple> {
        tuple.elements.get(index).and_then(|x| match *x {
            TupleValue::NestedTuple(ref t) => Some(t),
            _ => None,
        })
    }
}

/// Used by [`Tuple::push_back`] and [`Tuple::push_front`] methods.
pub trait TupleElementPush: private::SealedPush {
    #[doc(hidden)]
    fn push_back(tuple: &mut Tuple, value: Self);

    #[doc(hidden)]
    fn push_front(tuple: &mut Tuple, value: Self);
}

impl TupleElementPush for BigInt {
    /// # Panic
    ///
    /// Panics if the [`Bytes`] encoded length of the [`BigInt`] is
    /// greater than 255.
    fn push_back(tuple: &mut Tuple, value: BigInt) {
        let _ = i64::try_from(value.clone())
            .map(|x| tuple.push_back::<i64>(x))
            .map_err(|_| {
                if value.is_negative() {
		    // We are making the negative number positive for
		    // storing it in
		    // `TupleValue::NegativeArbitraryPrecisionInteger`.
                    if ((BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap())
                        ..=(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap()))
                        .contains(&value)
                    {
                        tuple.elements.push_back(TupleValue::NegInt8(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range above.
                            u64::try_from(value * -1).unwrap(),
                        ));
                    } else {
                        let b: BigInt = value * -1;
                        let (_, bigint_vec_u8) = b.to_bytes_be();

                        if Bytes::from(bigint_vec_u8).len() > 255 {
			    panic!("Byte encoded length of BigInt *must* be less than or equal to 255.");
                        }
                        tuple.elements
                            .push_back(TupleValue::NegativeArbitraryPrecisionInteger(b));
                    }
		}
		else if ((BigInt::parse_bytes(b"9223372036854775808", 10).unwrap())
                        ..=(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap()))
                        .contains(&value)
                {
                    tuple.elements.push_back(TupleValue::PosInt8(
                        // Safety: Safe to unwrap here because we are
                        //         checking the range above.
                        u64::try_from(value).unwrap(),
                    ));
                } else {
                    let b: BigInt = value;
                    let (_, bigint_vec_u8) = b.to_bytes_be();

                    if Bytes::from(bigint_vec_u8).len() > 255 {
			panic!("Byte encoded length of BigInt *must* be less than or equal to 255.");
                    }
                    tuple.elements
                        .push_back(TupleValue::PositiveArbitraryPrecisionInteger(b));
                }
            });
    }

    /// # Panic
    ///
    /// Panics if the [`Bytes`] encoded length of the [`BigInt`] is
    /// greater than 255.
    fn push_front(tuple: &mut Tuple, value: BigInt) {
        let _ = i64::try_from(value.clone())
            .map(|x| tuple.push_front::<i64>(x))
            .map_err(|_| {
                if value.is_negative() {
		    // We are making the negative number positive for
		    // storing it in
		    // `TupleValue::NegativeArbitraryPrecisionInteger`.
                    if ((BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap())
                        ..=(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap()))
                        .contains(&value)
                    {
                        tuple.elements.push_front(TupleValue::NegInt8(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range above.
                            u64::try_from(value * -1).unwrap(),
                        ));
                    } else {
                        let b: BigInt = value * -1;
                        let (_, bigint_vec_u8) = b.to_bytes_be();

                        if Bytes::from(bigint_vec_u8).len() > 255 {
			    panic!("Byte encoded length of BigInt *must* be less than or equal to 255.");
                        }
                        tuple.elements
                            .push_front(TupleValue::NegativeArbitraryPrecisionInteger(b));
                    }
		}
		else if ((BigInt::parse_bytes(b"9223372036854775808", 10).unwrap())
                        ..=(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap()))
                        .contains(&value)
                {
                    tuple.elements.push_front(TupleValue::PosInt8(
                        // Safety: Safe to unwrap here because we are
                        //         checking the range above.
                        u64::try_from(value).unwrap(),
                    ));
                } else {
                    let b: BigInt = value;
                    let (_, bigint_vec_u8) = b.to_bytes_be();

                    if Bytes::from(bigint_vec_u8).len() > 255 {
			panic!("Byte encoded length of BigInt *must* be less than or equal to 255.");
                    }
                    tuple.elements
                        .push_front(TupleValue::PositiveArbitraryPrecisionInteger(b));
                }
            });
    }
}

impl TupleElementPush for Bytes {
    fn push_back(tuple: &mut Tuple, value: Bytes) {
        tuple.elements.push_back(TupleValue::ByteString(value));
    }

    fn push_front(tuple: &mut Tuple, value: Bytes) {
        tuple.elements.push_front(TupleValue::ByteString(value));
    }
}

impl TupleElementPush for String {
    fn push_back(tuple: &mut Tuple, value: String) {
        tuple.elements.push_back(TupleValue::UnicodeString(value));
    }

    fn push_front(tuple: &mut Tuple, value: String) {
        tuple.elements.push_front(TupleValue::UnicodeString(value));
    }
}

impl TupleElementPush for Uuid {
    fn push_back(tuple: &mut Tuple, value: Uuid) {
        tuple.elements.push_back(TupleValue::Rfc4122Uuid(value));
    }

    fn push_front(tuple: &mut Tuple, value: Uuid) {
        tuple.elements.push_front(TupleValue::Rfc4122Uuid(value));
    }
}

impl TupleElementPush for bool {
    fn push_back(tuple: &mut Tuple, value: bool) {
        if value {
            tuple.elements.push_back(TupleValue::TrueValue);
        } else {
            tuple.elements.push_back(TupleValue::FalseValue);
        }
    }

    fn push_front(tuple: &mut Tuple, value: bool) {
        if value {
            tuple.elements.push_front(TupleValue::TrueValue);
        } else {
            tuple.elements.push_front(TupleValue::FalseValue);
        }
    }
}

impl TupleElementPush for f32 {
    /// # Note
    ///
    /// The [`f32`] value is encoded using type code [`0x20`], without any conversion.
    ///
    /// [`0x20`]: https://github.com/apple/foundationdb/blob/release-6.3/design/tuple.md#ieee-binary-floating-point
    fn push_back(tuple: &mut Tuple, value: f32) {
        tuple
            .elements
            .push_back(TupleValue::IeeeBinaryFloatingPointFloat(value));
    }

    /// # Note
    ///
    /// The [`f32`] value is encoded using type code [`0x20`], without any conversion.
    ///
    /// [`0x20`]: https://github.com/apple/foundationdb/blob/release-6.3/design/tuple.md#ieee-binary-floating-point
    fn push_front(tuple: &mut Tuple, value: f32) {
        tuple
            .elements
            .push_front(TupleValue::IeeeBinaryFloatingPointFloat(value));
    }
}

impl TupleElementPush for f64 {
    /// # Note
    ///
    /// The [`f64`] value is encoded using type code [`0x21`], without any conversion.
    ///
    /// [`0x21`]: https://github.com/apple/foundationdb/blob/release-6.3/design/tuple.md#ieee-binary-floating-point
    fn push_back(tuple: &mut Tuple, value: f64) {
        tuple
            .elements
            .push_back(TupleValue::IeeeBinaryFloatingPointDouble(value));
    }

    /// # Note
    ///
    /// The [`f64`] value is encoded using type code [`0x21`], without any conversion.
    ///
    /// [`0x21`]: https://github.com/apple/foundationdb/blob/release-6.3/design/tuple.md#ieee-binary-floating-point
    fn push_front(tuple: &mut Tuple, value: f64) {
        tuple
            .elements
            .push_front(TupleValue::IeeeBinaryFloatingPointDouble(value));
    }
}

impl TupleElementPush for i16 {
    fn push_back(tuple: &mut Tuple, value: i16) {
        let _ = i8::try_from(value)
            .map(|x| tuple.push_back::<i8>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i16::MIN..=-256 => tuple
                            .elements
                            .push_back(TupleValue::NegInt2(value.unsigned_abs())),
                        _ => tuple.elements.push_back(TupleValue::NegInt1(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `i16::MIN..=-256`.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        128..=255 => tuple.elements.push_back(TupleValue::PosInt1(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and `>255` using `_`
                            //         below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        _ => tuple
                            .elements
                            .push_back(TupleValue::PosInt2(value.unsigned_abs())),
                    }
                }
            });
    }

    fn push_front(tuple: &mut Tuple, value: i16) {
        let _ = i8::try_from(value)
            .map(|x| tuple.push_front::<i8>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i16::MIN..=-256 => tuple
                            .elements
                            .push_front(TupleValue::NegInt2(value.unsigned_abs())),
                        _ => tuple.elements.push_front(TupleValue::NegInt1(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `i16::MIN..=-256`.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        128..=255 => tuple.elements.push_front(TupleValue::PosInt1(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and `>255` using `_`
                            //         below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        _ => tuple
                            .elements
                            .push_front(TupleValue::PosInt2(value.unsigned_abs())),
                    }
                }
            });
    }
}

impl TupleElementPush for i32 {
    fn push_back(tuple: &mut Tuple, value: i32) {
        let _ = i16::try_from(value)
            .map(|x| tuple.push_back::<i16>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i32::MIN..=-16777216 => tuple
                            .elements
                            .push_back(TupleValue::NegInt4(value.unsigned_abs())),
                        -16777215..=-65536 => tuple
                            .elements
                            .push_back(TupleValue::NegInt3(value.unsigned_abs())),
                        _ => tuple.elements.push_back(TupleValue::NegInt2(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `i32::MIN..=-16777216`,
                            //         `-16777215..=-65536`
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        32768..=65535 => tuple.elements.push_back(TupleValue::PosInt2(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `65536..=16777215`, `>16777215`
                            //         using `_` below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        65536..=16777215 => tuple
                            .elements
                            .push_back(TupleValue::PosInt3(value.unsigned_abs())),
                        _ => tuple
                            .elements
                            .push_back(TupleValue::PosInt4(value.unsigned_abs())),
                    }
                }
            });
    }

    fn push_front(tuple: &mut Tuple, value: i32) {
        let _ = i16::try_from(value)
            .map(|x| tuple.push_front::<i16>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i32::MIN..=-16777216 => tuple
                            .elements
                            .push_front(TupleValue::NegInt4(value.unsigned_abs())),
                        -16777215..=-65536 => tuple
                            .elements
                            .push_front(TupleValue::NegInt3(value.unsigned_abs())),
                        _ => tuple.elements.push_front(TupleValue::NegInt2(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `i32::MIN..=-16777216`,
                            //         `-16777215..=-65536`
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        32768..=65535 => tuple.elements.push_front(TupleValue::PosInt2(
                            // Safety: Safe to unwrap here because we
                            //         are checking the range in
                            //         `try_from` and
                            //         `65536..=16777215`, `>16777215`
                            //         using `_` below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        65536..=16777215 => tuple
                            .elements
                            .push_front(TupleValue::PosInt3(value.unsigned_abs())),
                        _ => tuple
                            .elements
                            .push_front(TupleValue::PosInt4(value.unsigned_abs())),
                    }
                }
            });
    }
}

impl TupleElementPush for i64 {
    fn push_back(tuple: &mut Tuple, value: i64) {
        let _ = i32::try_from(value)
            .map(|x| tuple.push_back::<i32>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i64::MIN..=-72057594037927936 => tuple
                            .elements
                            .push_back(TupleValue::NegInt8(value.unsigned_abs())),
                        -72057594037927935..=-281474976710656 => tuple
                            .elements
                            .push_back(TupleValue::NegInt7(value.unsigned_abs())),
                        -281474976710655..=-1099511627776 => tuple
                            .elements
                            .push_back(TupleValue::NegInt6(value.unsigned_abs())),
                        -1099511627775..=-4294967296 => tuple
                            .elements
                            .push_back(TupleValue::NegInt5(value.unsigned_abs())),
                        _ => tuple.elements.push_back(TupleValue::NegInt4(
                            // Safety: Safe to unwrap here because we are
                            //         checking the range in `try_from`
                            //         and
                            //         `i64::MIN..=-72057594037927936`,
                            //         `-72057594037927935..=-281474976710656`,
                            //         `-281474976710655..=-1099511627776`,
                            //         `-1099511627775..=-4294967296`.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        2147483648..=4294967295 => tuple.elements.push_back(TupleValue::PosInt4(
                            // Safety: Safe to unwrap here because we are
                            //         checking the range in `try_from`
                            //         and `4294967296..=1099511627775`,
                            //         `1099511627776..=281474976710655`,
                            //         `281474976710656..=72057594037927935`,
                            //         `>72057594037927935` using `_`
                            //         below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        4294967296..=1099511627775 => tuple
                            .elements
                            .push_back(TupleValue::PosInt5(value.unsigned_abs())),
                        1099511627776..=281474976710655 => tuple
                            .elements
                            .push_back(TupleValue::PosInt6(value.unsigned_abs())),
                        281474976710656..=72057594037927935 => tuple
                            .elements
                            .push_back(TupleValue::PosInt7(value.unsigned_abs())),
                        _ => tuple
                            .elements
                            .push_back(TupleValue::PosInt8(value.unsigned_abs())),
                    }
                }
            });
    }

    fn push_front(tuple: &mut Tuple, value: i64) {
        let _ = i32::try_from(value)
            .map(|x| tuple.push_front::<i32>(x))
            .map_err(|_| {
                if value.is_negative() {
                    match value {
                        i64::MIN..=-72057594037927936 => tuple
                            .elements
                            .push_front(TupleValue::NegInt8(value.unsigned_abs())),
                        -72057594037927935..=-281474976710656 => tuple
                            .elements
                            .push_front(TupleValue::NegInt7(value.unsigned_abs())),
                        -281474976710655..=-1099511627776 => tuple
                            .elements
                            .push_front(TupleValue::NegInt6(value.unsigned_abs())),
                        -1099511627775..=-4294967296 => tuple
                            .elements
                            .push_front(TupleValue::NegInt5(value.unsigned_abs())),
                        _ => tuple.elements.push_front(TupleValue::NegInt4(
                            // Safety: Safe to unwrap here because we are
                            //         checking the range in `try_from`
                            //         and
                            //         `i64::MIN..=-72057594037927936`,
                            //         `-72057594037927935..=-281474976710656`,
                            //         `-281474976710655..=-1099511627776`,
                            //         `-1099511627775..=-4294967296`.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                    }
                } else {
                    match value {
                        2147483648..=4294967295 => tuple.elements.push_front(TupleValue::PosInt4(
                            // Safety: Safe to unwrap here because we are
                            //         checking the range in `try_from`
                            //         and `4294967296..=1099511627775`,
                            //         `1099511627776..=281474976710655`,
                            //         `281474976710656..=72057594037927935`,
                            //         `>72057594037927935` using `_`
                            //         below.
                            value.unsigned_abs().try_into().unwrap(),
                        )),
                        4294967296..=1099511627775 => tuple
                            .elements
                            .push_front(TupleValue::PosInt5(value.unsigned_abs())),
                        1099511627776..=281474976710655 => tuple
                            .elements
                            .push_front(TupleValue::PosInt6(value.unsigned_abs())),
                        281474976710656..=72057594037927935 => tuple
                            .elements
                            .push_front(TupleValue::PosInt7(value.unsigned_abs())),
                        _ => tuple
                            .elements
                            .push_front(TupleValue::PosInt8(value.unsigned_abs())),
                    }
                }
            });
    }
}

impl TupleElementPush for i8 {
    fn push_back(tuple: &mut Tuple, value: i8) {
        match value {
            i8::MIN..=-1 => tuple
                .elements
                .push_back(TupleValue::NegInt1(value.unsigned_abs())),
            0 => tuple.elements.push_back(TupleValue::IntZero),
            1..=i8::MAX => tuple
                .elements
                .push_back(TupleValue::PosInt1(value.unsigned_abs())),
        }
    }

    fn push_front(tuple: &mut Tuple, value: i8) {
        match value {
            i8::MIN..=-1 => tuple
                .elements
                .push_front(TupleValue::NegInt1(value.unsigned_abs())),
            0 => tuple.elements.push_front(TupleValue::IntZero),
            1..=i8::MAX => tuple
                .elements
                .push_front(TupleValue::PosInt1(value.unsigned_abs())),
        }
    }
}

impl TupleElementPush for Null {
    fn push_back(tuple: &mut Tuple, value: Null) {
        let _ = value;
        tuple.elements.push_back(TupleValue::NullValue);
    }

    fn push_front(tuple: &mut Tuple, value: Null) {
        let _ = value;
        tuple.elements.push_front(TupleValue::NullValue);
    }
}

impl TupleElementPush for Versionstamp {
    fn push_back(tuple: &mut Tuple, value: Versionstamp) {
        tuple.has_incomplete_versionstamp =
            tuple.has_incomplete_versionstamp || (!value.is_complete());
        tuple
            .elements
            .push_back(TupleValue::Versionstamp96Bit(value));
    }

    fn push_front(tuple: &mut Tuple, value: Versionstamp) {
        tuple.has_incomplete_versionstamp =
            tuple.has_incomplete_versionstamp || (!value.is_complete());
        tuple
            .elements
            .push_front(TupleValue::Versionstamp96Bit(value));
    }
}

impl TupleElementPush for Tuple {
    fn push_back(tuple: &mut Tuple, value: Tuple) {
        tuple.has_incomplete_versionstamp =
            tuple.has_incomplete_versionstamp || value.has_incomplete_versionstamp();
        tuple.elements.push_back(TupleValue::NestedTuple(value));
    }

    fn push_front(tuple: &mut Tuple, value: Tuple) {
        tuple.has_incomplete_versionstamp =
            tuple.has_incomplete_versionstamp || value.has_incomplete_versionstamp();
        tuple.elements.push_front(TupleValue::NestedTuple(value));
    }
}

/// Represents a set of elements that make up a sortable, typed key.
///
/// [`Tuple`] is comparable with other [`Tuple`]s and will sort in
/// Rust in the same order in which they would sort in FDB. [`Tuple`]s
/// sort first by the first element, then by the second, etc., This
/// make tuple layer ideal for building a variety of higher-level data
/// models.
///
/// For general guidance on tuple usage, see [this] link.
///
/// [`Tuple`] can contain [`Null`], [`Bytes`], [`String`], another
/// [`Tuple`], [`BigInt`], [`i64`], [`i32`], [`i16`], [`i8`], [`f32`],
/// [`f64`], [`bool`], [`Uuid`], [`Versionstamp`] values.
///
/// [layer]: https://github.com/apple/foundationdb/blob/6.3.0/design/tuple.md
/// [this]: https://apple.github.io/foundationdb/data-modeling.html#tuples
///
// NOTE: Unlike the Java API, we do not implement `Iterator` trait, as
//       that would mean we will have to expose `TupleValue` type to
//       the client. Instead we provide `size()` method and let the
//       client call appropriate `get_<type>(...)` methods.
#[derive(Debug, Clone)]
pub struct Tuple {
    elements: VecDeque<TupleValue>,
    // This is `true` *only* when `Tuple` contains a `Versionstamp`
    // *and* it that `Versionstamp` is incomplete.
    //
    // This is `false` (default) when `Tuple` does not contain a
    // `Versionstamp` or if it contains a `Versionstamp` that is
    // complete.
    //
    // Basically adding complete `Versionstamp` won't change this
    // value to `true`. It is only when incomplete `Versionstamp` is
    // added, that this value changes to `true`.
    has_incomplete_versionstamp: bool,
}

impl Tuple {
    /// Create a new empty [`Tuple`].
    pub fn new() -> Tuple {
        Tuple {
            elements: VecDeque::new(),
            has_incomplete_versionstamp: false,
        }
    }

    /// Provides the [`Tuple`] element at the given index.
    ///
    /// If you want to return a [`FdbResult`], use [`FdbError`] with
    /// [`TUPLE_GET`].
    ///
    /// [`TUPLE_GET`]: crate::error::TUPLE_GET
    //
    // We need to allow for `unconditional_recursion` because `Tuple`
    // can be nested.
    #[allow(unconditional_recursion)]
    pub fn get<'a, T>(&'a self, index: usize) -> Option<T>
    where
        T: TupleElementGet<'a> + 'a,
    {
        TupleElementGet::get(self, index)
    }

    /// Appends a [`Tuple`] element.
    pub fn push_back<T>(&mut self, value: T)
    where
        T: TupleElementPush,
    {
        TupleElementPush::push_back(self, value)
    }

    /// Prepends a [`Tuple`] element.
    pub fn push_front<T>(&mut self, value: T)
    where
        T: TupleElementPush,
    {
        TupleElementPush::push_front(self, value)
    }

    /// Append elements of [`Tuple`] `t` to [`Tuple`] `Self`
    pub fn append(&mut self, mut t: Tuple) {
        self.has_incomplete_versionstamp =
            self.has_incomplete_versionstamp || t.has_incomplete_versionstamp();

        self.elements.append(&mut t.elements);
    }

    /// Determines if there is a [`Versionstamp`] included in this
    /// [`Tuple`] that has not had its transaction version set.
    pub fn has_incomplete_versionstamp(&self) -> bool {
        self.has_incomplete_versionstamp
    }

    /// Determine if this [`Tuple`] contains no elements.
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Gets the number of elements in this [`Tuple`].
    pub fn size(&self) -> usize {
        self.elements.len()
    }

    /// Get an encoded representation of this [`Tuple`].
    pub fn pack(&self) -> Bytes {
        element::to_bytes(self.clone())
    }

    /// Get an encoded representation of this [`Tuple`] for use with
    /// [`SetVersionstampedKey`].
    ///
    /// # Panic
    ///
    /// The index where incomplete versionstamp is located is a 32-bit
    /// little-endian integer. If the generated index overflows
    /// [`u32`], then this function panics.
    ///
    /// [`SetVersionstampedKey`]: crate::transaction::MutationType::SetVersionstampedKey
    pub fn pack_with_versionstamp(&self, prefix: Bytes) -> FdbResult<Bytes> {
        if self.has_incomplete_versionstamp() {
            element::find_incomplete_versionstamp(self.clone()).map(|x| {
                let index = TryInto::<u32>::try_into(x + prefix.len()).unwrap();

                let mut res = BytesMut::new();

                res.put(prefix);
                res.put(self.pack());
                res.put_u32_le(index);

                res.into()
            })
        } else {
            Err(FdbError::new(TUPLE_PACK_WITH_VERSIONSTAMP_NOT_FOUND))
        }
    }

    /// Returns a range representing all keys that encode [`Tuple`]s
    /// strictly starting with this [`Tuple`].
    ///
    /// # Panic
    ///
    /// Panics if the tuple contains an incomplete [`Versionstamp`].
    pub fn range(&self, prefix: Bytes) -> Range {
        if self.has_incomplete_versionstamp() {
            panic!("Cannot create Range value as tuple contains an incomplete versionstamp");
        }

        let begin = {
            let mut x = BytesMut::new();
            x.put(prefix.clone());
            x.put(self.pack());
            x.put_u8(0x00);
            Into::<Bytes>::into(x)
        };

        let end = {
            let mut x = BytesMut::new();
            x.put(prefix);
            x.put(self.pack());
            x.put_u8(0xFF);
            Into::<Bytes>::into(x)
        };

        Range::new(begin, end)
    }

    pub(crate) fn from_elements(elements: Vec<TupleValue>) -> Tuple {
        let has_incomplete_versionstamp = (&elements).iter().fold(false, |acc, x| match *x {
            TupleValue::NestedTuple(ref t) => acc || t.has_incomplete_versionstamp(),
            TupleValue::Versionstamp96Bit(ref vs) => acc || (!vs.is_complete()),
            _ => acc,
        });

        Tuple {
            elements: elements.into(),
            has_incomplete_versionstamp,
        }
    }

    pub(crate) fn into_elements(self) -> Vec<TupleValue> {
        self.elements.into()
    }
}

impl Default for Tuple {
    fn default() -> Tuple {
        Tuple::new()
    }
}

impl PartialEq for Tuple {
    fn eq(&self, other: &Self) -> bool {
        self.pack().eq(&other.pack())
    }
}

impl Eq for Tuple {}

impl PartialOrd for Tuple {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.pack().partial_cmp(&other.pack())
    }
}

impl Ord for Tuple {
    fn cmp(&self, other: &Self) -> Ordering {
        self.pack().cmp(&other.pack())
    }
}

impl TryFrom<Bytes> for Tuple {
    type Error = FdbError;

    /// Construct a new [`Tuple`] with elements decoded from a
    /// supplied [`Bytes`].
    fn try_from(b: Bytes) -> FdbResult<Tuple> {
        element::from_bytes(b)
    }
}

impl TryFrom<Key> for Tuple {
    type Error = FdbError;

    /// Construct a new [`Tuple`] with elements decoded from a
    /// supplied [`Key`].
    fn try_from(k: Key) -> FdbResult<Tuple> {
        Tuple::try_from(Bytes::from(k)).map_err(|_| FdbError::new(TUPLE_TRY_FROM_KEY))
    }
}

impl TryFrom<Value> for Tuple {
    type Error = FdbError;

    /// Construct a new [`Tuple`] with elements decoded from a
    /// supplied [`Value`].
    fn try_from(v: Value) -> FdbResult<Tuple> {
        Tuple::try_from(Bytes::from(v)).map_err(|_| FdbError::new(TUPLE_TRY_FROM_VALUE))
    }
}

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use impls::impls;
    use num_bigint::BigInt;
    use uuid::Uuid;

    use std::convert::TryFrom;

    use crate::error::{
        FdbError, TUPLE_PACK_WITH_VERSIONSTAMP_MULTIPLE_FOUND,
        TUPLE_PACK_WITH_VERSIONSTAMP_NOT_FOUND, TUPLE_TRY_FROM_BYTES, TUPLE_TRY_FROM_KEY,
        TUPLE_TRY_FROM_VALUE,
    };
    use crate::range::Range;
    use crate::tuple::{element::TupleValue, Null, Versionstamp};
    use crate::{Key, Value};

    use super::Tuple;

    #[test]
    fn impls() {
        #[rustfmt::skip]
	assert!(impls!(
	    Tuple:
	        PartialEq<Tuple> &
                Eq &
                PartialOrd<Tuple> &
                Ord
	));
    }

    #[test]
    fn try_from_bytes() {
        // For additonal tests, see the tests for `parsers::tuple`
        // (`test_tuple`) in `element.rs`.
        assert_eq!(
            Tuple::try_from(Bytes::from_static(b"\x00moredata")),
            Err(FdbError::new(TUPLE_TRY_FROM_BYTES)),
        );
        assert_eq!(
            Tuple::try_from(Bytes::from_static(b"no_tuple")),
            Err(FdbError::new(TUPLE_TRY_FROM_BYTES)),
        );
        assert_eq!(
            Tuple::try_from(Bytes::from_static(b"\x02hello\x00")),
            Ok({
                let mut t = Tuple::new();
                t.push_back::<String>("hello".to_string());
                t
            })
        );
    }

    #[test]
    fn try_from_key() {
        assert_eq!(
            Tuple::try_from(Key::from(Bytes::from_static(b"no_tuple"))),
            Err(FdbError::new(TUPLE_TRY_FROM_KEY)),
        );
        assert_eq!(
            Tuple::try_from(Key::from(Bytes::from_static(b"\x02hello\x00"))),
            Ok({
                let mut t = Tuple::new();
                t.push_back::<String>("hello".to_string());
                t
            })
        );
    }

    #[test]
    fn try_from_value() {
        assert_eq!(
            Tuple::try_from(Value::from(Bytes::from_static(b"no_tuple"))),
            Err(FdbError::new(TUPLE_TRY_FROM_VALUE)),
        );
        assert_eq!(
            Tuple::try_from(Key::from(Bytes::from_static(b"\x02hello\x00"))),
            Ok({
                let mut t = Tuple::new();
                t.push_back::<String>("hello".to_string());
                t
            })
        );
    }

    #[test]
    fn push_back_bigint() {
        let mut t = Tuple::new();

        t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap()); // i64::MIN
        t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775807", 10).unwrap()); // i64::MAX
        t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NegativeArbitraryPrecisionInteger(
                    BigInt::parse_bytes(b"18446744073709551616", 10).unwrap()
                ),
                TupleValue::NegInt8(18446744073709551615),
                TupleValue::NegInt8(9223372036854775809),
                TupleValue::NegInt8(9223372036854775808),
                TupleValue::PosInt8(9223372036854775807),
                TupleValue::PosInt8(9223372036854775808),
                TupleValue::PosInt8(18446744073709551615),
                TupleValue::PositiveArbitraryPrecisionInteger(
                    BigInt::parse_bytes(b"18446744073709551616", 10).unwrap()
                )
            ]
        );
    }

    #[test]
    fn push_back_bytes() {
        let mut t = Tuple::new();

        t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));

        assert_eq!(
            t.elements,
            vec![TupleValue::ByteString(Bytes::from_static(b"hello_world"))]
        );
    }

    #[test]
    fn push_back_string() {
        let mut t = Tuple::new();

        t.push_back::<String>("hello world".to_string());

        assert_eq!(
            t.elements,
            vec![TupleValue::UnicodeString("hello world".to_string())]
        );
    }

    #[test]
    fn push_back_uuid() {
        let mut t = Tuple::new();

        t.push_back::<Uuid>(Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap());

        assert_eq!(
            t.elements,
            vec![TupleValue::Rfc4122Uuid(
                Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap()
            )]
        );
    }

    #[test]
    fn push_back_bool() {
        let mut t = Tuple::new();

        t.push_back::<bool>(true);
        assert_eq!(t.elements, vec![TupleValue::TrueValue]);

        t.push_back::<bool>(false);
        assert_eq!(
            t.elements,
            vec![TupleValue::TrueValue, TupleValue::FalseValue]
        );
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn push_back_f32() {
        let mut t = Tuple::new();

        t.push_back::<f32>(3.14f32);

        assert_eq!(
            t.elements,
            vec![TupleValue::IeeeBinaryFloatingPointFloat(3.14f32)]
        );
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn push_back_f64() {
        let mut t = Tuple::new();

        t.push_back::<f64>(-3.14f64);

        assert_eq!(
            t.elements,
            vec![TupleValue::IeeeBinaryFloatingPointDouble(-3.14f64)]
        );
    }

    #[test]
    fn push_back_i16() {
        let mut t = Tuple::new();

        t.push_back::<i16>(i16::MIN);
        t.push_back::<i16>(-256);
        t.push_back::<i16>(-255);
        t.push_back::<i16>(-129);
        t.push_back::<i16>(-128); // i8::MIN
        t.push_back::<i16>(127); // i8::MAX
        t.push_back::<i16>(128);
        t.push_back::<i16>(255);
        t.push_back::<i16>(256);
        t.push_back::<i16>(i16::MAX);

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NegInt2(32768),
                TupleValue::NegInt2(256),
                TupleValue::NegInt1(255),
                TupleValue::NegInt1(129),
                TupleValue::NegInt1(128),
                TupleValue::PosInt1(127),
                TupleValue::PosInt1(128),
                TupleValue::PosInt1(255),
                TupleValue::PosInt2(256),
                TupleValue::PosInt2(32767),
            ]
        );
    }

    #[test]
    fn push_back_i32() {
        let mut t = Tuple::new();

        t.push_back::<i32>(i32::MIN);
        t.push_back::<i32>(-16777216);
        t.push_back::<i32>(-16777215);
        t.push_back::<i32>(-65536);
        t.push_back::<i32>(-65535);
        t.push_back::<i32>(-32769);
        t.push_back::<i32>(-32768); // i16::MIN
        t.push_back::<i32>(32767); // i16::MAX
        t.push_back::<i32>(32768);
        t.push_back::<i32>(65535);
        t.push_back::<i32>(65536);
        t.push_back::<i32>(16777215);
        t.push_back::<i32>(16777216);
        t.push_back::<i32>(i32::MAX);

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NegInt4(2147483648),
                TupleValue::NegInt4(16777216),
                TupleValue::NegInt3(16777215),
                TupleValue::NegInt3(65536),
                TupleValue::NegInt2(65535),
                TupleValue::NegInt2(32769),
                TupleValue::NegInt2(32768),
                TupleValue::PosInt2(32767),
                TupleValue::PosInt2(32768),
                TupleValue::PosInt2(65535),
                TupleValue::PosInt3(65536),
                TupleValue::PosInt3(16777215),
                TupleValue::PosInt4(16777216),
                TupleValue::PosInt4(2147483647),
            ]
        );
    }

    #[test]
    fn push_back_i64() {
        let mut t = Tuple::new();

        t.push_back::<i64>(i64::MIN);
        t.push_back::<i64>(-72057594037927936);
        t.push_back::<i64>(-72057594037927935);
        t.push_back::<i64>(-281474976710656);
        t.push_back::<i64>(-281474976710655);
        t.push_back::<i64>(-1099511627776);
        t.push_back::<i64>(-1099511627775);
        t.push_back::<i64>(-4294967296);
        t.push_back::<i64>(-4294967295);
        t.push_back::<i64>(-2147483649);
        t.push_back::<i64>(-2147483648); // i32::MIN
        t.push_back::<i64>(2147483647); // i32::MAX
        t.push_back::<i64>(2147483648);
        t.push_back::<i64>(4294967295);
        t.push_back::<i64>(4294967296);
        t.push_back::<i64>(1099511627775);
        t.push_back::<i64>(1099511627776);
        t.push_back::<i64>(281474976710655);
        t.push_back::<i64>(281474976710656);
        t.push_back::<i64>(72057594037927935);
        t.push_back::<i64>(72057594037927936);
        t.push_back::<i64>(i64::MAX);

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NegInt8(9223372036854775808),
                TupleValue::NegInt8(72057594037927936),
                TupleValue::NegInt7(72057594037927935),
                TupleValue::NegInt7(281474976710656),
                TupleValue::NegInt6(281474976710655),
                TupleValue::NegInt6(1099511627776),
                TupleValue::NegInt5(1099511627775),
                TupleValue::NegInt5(4294967296),
                TupleValue::NegInt4(4294967295),
                TupleValue::NegInt4(2147483649),
                TupleValue::NegInt4(2147483648),
                TupleValue::PosInt4(2147483647),
                TupleValue::PosInt4(2147483648),
                TupleValue::PosInt4(4294967295),
                TupleValue::PosInt5(4294967296),
                TupleValue::PosInt5(1099511627775),
                TupleValue::PosInt6(1099511627776),
                TupleValue::PosInt6(281474976710655),
                TupleValue::PosInt7(281474976710656),
                TupleValue::PosInt7(72057594037927935),
                TupleValue::PosInt8(72057594037927936),
                TupleValue::PosInt8(9223372036854775807),
            ]
        );
    }

    #[test]
    fn push_back_i8() {
        let mut t = Tuple::new();

        t.push_back::<i8>(i8::MIN);
        t.push_back::<i8>(0);
        t.push_back::<i8>(i8::MAX);

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NegInt1(128),
                TupleValue::IntZero,
                TupleValue::PosInt1(127),
            ]
        );
    }

    #[test]
    fn push_back_null() {
        let mut t = Tuple::new();

        t.push_back::<Null>(Null);

        assert_eq!(t.elements, vec![TupleValue::NullValue]);
    }

    #[test]
    fn push_back_tuple() {
        let mut t = Tuple::new();

        t.push_back::<BigInt>(BigInt::parse_bytes(b"0", 10).unwrap());
        t.push_back::<Tuple>({
            let mut t1 = Tuple::new();
            t1.push_back::<Versionstamp>(Versionstamp::incomplete(0));
            t1
        });

        assert!(t.has_incomplete_versionstamp());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::IntZero,
                TupleValue::NestedTuple(Tuple::from_elements(vec![TupleValue::Versionstamp96Bit(
                    Versionstamp::incomplete(0)
                )])),
            ]
        );
    }

    #[test]
    fn push_back_versionstamp() {
        let mut t = Tuple::new();

        t.push_back::<Versionstamp>(Versionstamp::complete(
            Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
            657,
        ));

        assert!(!t.has_incomplete_versionstamp());

        t.push_back::<Versionstamp>(Versionstamp::incomplete(0));

        assert!(t.has_incomplete_versionstamp());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::Versionstamp96Bit(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                )),
                TupleValue::Versionstamp96Bit(Versionstamp::incomplete(0))
            ]
        );
    }

    #[test]
    fn push_front_bigint() {
        let mut t = Tuple::new();

        t.push_front::<BigInt>(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap());
        t.push_front::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
        t.push_front::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
        t.push_front::<BigInt>(BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap()); // i64::MIN
        t.push_front::<BigInt>(BigInt::parse_bytes(b"9223372036854775807", 10).unwrap()); // i64::MAX
        t.push_front::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
        t.push_front::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
        t.push_front::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());

        assert_eq!(t.elements, {
            let mut v = vec![
                TupleValue::NegativeArbitraryPrecisionInteger(
                    BigInt::parse_bytes(b"18446744073709551616", 10).unwrap(),
                ),
                TupleValue::NegInt8(18446744073709551615),
                TupleValue::NegInt8(9223372036854775809),
                TupleValue::NegInt8(9223372036854775808),
                TupleValue::PosInt8(9223372036854775807),
                TupleValue::PosInt8(9223372036854775808),
                TupleValue::PosInt8(18446744073709551615),
                TupleValue::PositiveArbitraryPrecisionInteger(
                    BigInt::parse_bytes(b"18446744073709551616", 10).unwrap(),
                ),
            ];
            v.reverse();
            v
        });
    }

    #[test]
    fn push_front_bytes() {
        let mut t = Tuple::new();

        t.push_front::<Bytes>(Bytes::from_static(b"hello_world"));

        assert_eq!(
            t.elements,
            vec![TupleValue::ByteString(Bytes::from_static(b"hello_world"))]
        );
    }

    #[test]
    fn push_front_string() {
        let mut t = Tuple::new();

        t.push_front::<String>("hello world".to_string());

        assert_eq!(
            t.elements,
            vec![TupleValue::UnicodeString("hello world".to_string())]
        );
    }

    #[test]
    fn push_front_uuid() {
        let mut t = Tuple::new();

        t.push_front::<Uuid>(Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap());

        assert_eq!(
            t.elements,
            vec![TupleValue::Rfc4122Uuid(
                Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap()
            )]
        );
    }

    #[test]
    fn push_front_bool() {
        let mut t = Tuple::new();

        t.push_front::<bool>(true);
        assert_eq!(t.elements, vec![TupleValue::TrueValue]);

        t.push_front::<bool>(false);
        assert_eq!(
            t.elements,
            vec![TupleValue::FalseValue, TupleValue::TrueValue]
        );
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn push_front_f32() {
        let mut t = Tuple::new();

        t.push_front::<f32>(3.14f32);

        assert_eq!(
            t.elements,
            vec![TupleValue::IeeeBinaryFloatingPointFloat(3.14f32)]
        );
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn push_front_f64() {
        let mut t = Tuple::new();

        t.push_front::<f64>(-3.14f64);

        assert_eq!(
            t.elements,
            vec![TupleValue::IeeeBinaryFloatingPointDouble(-3.14f64)]
        );
    }

    #[test]
    fn push_front_i16() {
        let mut t = Tuple::new();

        t.push_front::<i16>(i16::MIN);
        t.push_front::<i16>(-256);
        t.push_front::<i16>(-255);
        t.push_front::<i16>(-129);
        t.push_front::<i16>(-128); // i8::MIN
        t.push_front::<i16>(127); // i8::MAX
        t.push_front::<i16>(128);
        t.push_front::<i16>(255);
        t.push_front::<i16>(256);
        t.push_front::<i16>(i16::MAX);

        assert_eq!(t.elements, {
            let mut v = vec![
                TupleValue::NegInt2(32768),
                TupleValue::NegInt2(256),
                TupleValue::NegInt1(255),
                TupleValue::NegInt1(129),
                TupleValue::NegInt1(128),
                TupleValue::PosInt1(127),
                TupleValue::PosInt1(128),
                TupleValue::PosInt1(255),
                TupleValue::PosInt2(256),
                TupleValue::PosInt2(32767),
            ];
            v.reverse();
            v
        });
    }

    #[test]
    fn push_front_i32() {
        let mut t = Tuple::new();

        t.push_front::<i32>(i32::MIN);
        t.push_front::<i32>(-16777216);
        t.push_front::<i32>(-16777215);
        t.push_front::<i32>(-65536);
        t.push_front::<i32>(-65535);
        t.push_front::<i32>(-32769);
        t.push_front::<i32>(-32768); // i16::MIN
        t.push_front::<i32>(32767); // i16::MAX
        t.push_front::<i32>(32768);
        t.push_front::<i32>(65535);
        t.push_front::<i32>(65536);
        t.push_front::<i32>(16777215);
        t.push_front::<i32>(16777216);
        t.push_front::<i32>(i32::MAX);

        assert_eq!(t.elements, {
            let mut v = vec![
                TupleValue::NegInt4(2147483648),
                TupleValue::NegInt4(16777216),
                TupleValue::NegInt3(16777215),
                TupleValue::NegInt3(65536),
                TupleValue::NegInt2(65535),
                TupleValue::NegInt2(32769),
                TupleValue::NegInt2(32768),
                TupleValue::PosInt2(32767),
                TupleValue::PosInt2(32768),
                TupleValue::PosInt2(65535),
                TupleValue::PosInt3(65536),
                TupleValue::PosInt3(16777215),
                TupleValue::PosInt4(16777216),
                TupleValue::PosInt4(2147483647),
            ];
            v.reverse();
            v
        });
    }

    #[test]
    fn push_front_i64() {
        let mut t = Tuple::new();

        t.push_front::<i64>(i64::MIN);
        t.push_front::<i64>(-72057594037927936);
        t.push_front::<i64>(-72057594037927935);
        t.push_front::<i64>(-281474976710656);
        t.push_front::<i64>(-281474976710655);
        t.push_front::<i64>(-1099511627776);
        t.push_front::<i64>(-1099511627775);
        t.push_front::<i64>(-4294967296);
        t.push_front::<i64>(-4294967295);
        t.push_front::<i64>(-2147483649);
        t.push_front::<i64>(-2147483648); // i32::MIN
        t.push_front::<i64>(2147483647); // i32::MAX
        t.push_front::<i64>(2147483648);
        t.push_front::<i64>(4294967295);
        t.push_front::<i64>(4294967296);
        t.push_front::<i64>(1099511627775);
        t.push_front::<i64>(1099511627776);
        t.push_front::<i64>(281474976710655);
        t.push_front::<i64>(281474976710656);
        t.push_front::<i64>(72057594037927935);
        t.push_front::<i64>(72057594037927936);
        t.push_front::<i64>(i64::MAX);

        assert_eq!(t.elements, {
            let mut v = vec![
                TupleValue::NegInt8(9223372036854775808),
                TupleValue::NegInt8(72057594037927936),
                TupleValue::NegInt7(72057594037927935),
                TupleValue::NegInt7(281474976710656),
                TupleValue::NegInt6(281474976710655),
                TupleValue::NegInt6(1099511627776),
                TupleValue::NegInt5(1099511627775),
                TupleValue::NegInt5(4294967296),
                TupleValue::NegInt4(4294967295),
                TupleValue::NegInt4(2147483649),
                TupleValue::NegInt4(2147483648),
                TupleValue::PosInt4(2147483647),
                TupleValue::PosInt4(2147483648),
                TupleValue::PosInt4(4294967295),
                TupleValue::PosInt5(4294967296),
                TupleValue::PosInt5(1099511627775),
                TupleValue::PosInt6(1099511627776),
                TupleValue::PosInt6(281474976710655),
                TupleValue::PosInt7(281474976710656),
                TupleValue::PosInt7(72057594037927935),
                TupleValue::PosInt8(72057594037927936),
                TupleValue::PosInt8(9223372036854775807),
            ];
            v.reverse();
            v
        });
    }

    #[test]
    fn push_front_i8() {
        let mut t = Tuple::new();

        t.push_front::<i8>(i8::MIN);
        t.push_front::<i8>(0);
        t.push_front::<i8>(i8::MAX);

        assert_eq!(
            t.elements,
            vec![
                TupleValue::PosInt1(127),
                TupleValue::IntZero,
                TupleValue::NegInt1(128),
            ]
        );
    }

    #[test]
    fn push_front_null() {
        let mut t = Tuple::new();

        t.push_front::<Null>(Null);

        assert_eq!(t.elements, vec![TupleValue::NullValue]);
    }

    #[test]
    fn push_front_tuple() {
        let mut t = Tuple::new();

        t.push_front::<BigInt>(BigInt::parse_bytes(b"0", 10).unwrap());
        t.push_front::<Tuple>({
            let mut t1 = Tuple::new();
            t1.push_front::<Versionstamp>(Versionstamp::incomplete(0));
            t1
        });

        assert!(t.has_incomplete_versionstamp());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NestedTuple(Tuple::from_elements(vec![TupleValue::Versionstamp96Bit(
                    Versionstamp::incomplete(0)
                )])),
                TupleValue::IntZero,
            ]
        );
    }

    #[test]
    fn push_front_versionstamp() {
        let mut t = Tuple::new();

        t.push_front::<Versionstamp>(Versionstamp::complete(
            Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
            657,
        ));

        assert!(!t.has_incomplete_versionstamp());

        t.push_front::<Versionstamp>(Versionstamp::incomplete(0));

        assert!(t.has_incomplete_versionstamp());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::Versionstamp96Bit(Versionstamp::incomplete(0)),
                TupleValue::Versionstamp96Bit(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                ))
            ]
        );
    }

    #[test]
    fn append() {
        let mut t = Tuple::new();

        t.append({
            let mut t1 = Tuple::new();
            t1.push_back::<Null>(Null);
            t1
        });

        t.append({
            let mut t1 = Tuple::new();
            t1.push_back::<Versionstamp>(Versionstamp::incomplete(0));
            t1
        });

        assert!(t.has_incomplete_versionstamp());

        assert_eq!(
            t.elements,
            vec![
                TupleValue::NullValue,
                TupleValue::Versionstamp96Bit(Versionstamp::incomplete(0))
            ]
        );
    }

    #[test]
    fn has_incomplete_versionstamp() {
        let mut t = Tuple::new();

        assert!(!t.has_incomplete_versionstamp());

        t.push_back::<Versionstamp>(Versionstamp::incomplete(0));

        assert!(t.has_incomplete_versionstamp());
    }

    #[test]
    fn get_bytes_ref() {
        let t = Tuple::new();

        assert_eq!(t.get::<&Bytes>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<Bytes>(Bytes::from_static(b"hello_world"));

        assert_eq!(t.get::<&Bytes>(0), None);
        assert_eq!(
            t.get::<&Bytes>(1),
            Some(&Bytes::from_static(b"hello_world"))
        );
    }

    #[test]
    fn get_string_ref() {
        let t = Tuple::new();

        assert_eq!(t.get::<&String>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<String>("hello world".to_string());

        assert_eq!(t.get::<&String>(0), None);
        assert_eq!(t.get::<&String>(1), Some(&"hello world".to_string()));
    }

    #[test]
    fn get_uuid_ref() {
        let t = Tuple::new();

        assert_eq!(t.get::<&Uuid>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<Uuid>(Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap());

        assert_eq!(t.get::<&Uuid>(0), None);
        assert_eq!(
            t.get::<&Uuid>(1),
            Some(&Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap())
        );
    }

    #[test]
    fn get_bigint() {
        let t = Tuple::new();

        assert_eq!(t.get::<BigInt>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap()); // i64::MIN
        t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775807", 10).unwrap()); // i64::MAX
        t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
        t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());

        assert_eq!(t.get::<BigInt>(0), None);
        assert_eq!(
            t.get::<BigInt>(1),
            Some(BigInt::parse_bytes(b"-18446744073709551616", 10).unwrap())
        );
        assert_eq!(
            t.get::<BigInt>(2),
            Some(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap())
        );
        assert_eq!(
            t.get::<BigInt>(3),
            Some(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap()),
        );
        assert_eq!(
            t.get::<BigInt>(4),
            Some(BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap()),
        );
        assert_eq!(
            t.get::<BigInt>(5),
            Some(BigInt::parse_bytes(b"9223372036854775807", 10).unwrap()),
        );
        assert_eq!(
            t.get::<BigInt>(6),
            Some(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap()),
        );
        assert_eq!(
            t.get::<BigInt>(7),
            Some(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap()),
        );
        assert_eq!(
            t.get::<BigInt>(8),
            Some(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap()),
        );
    }

    #[test]
    fn get_bool() {
        let t = Tuple::new();

        assert_eq!(t.get::<bool>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<bool>(true);
        t.push_back::<bool>(false);

        assert_eq!(t.get::<bool>(0), None);
        assert_eq!(t.get::<bool>(1), Some(true));
        assert_eq!(t.get::<bool>(2), Some(false));
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn get_f32() {
        let t = Tuple::new();

        assert_eq!(t.get::<f32>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<f32>(3.14f32);

        assert_eq!(t.get::<f32>(0), None);
        assert_eq!(t.get::<f32>(1), Some(3.14f32));
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn get_f64() {
        let t = Tuple::new();

        assert_eq!(t.get::<f64>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<f64>(3.14f64);

        assert_eq!(t.get::<f64>(0), None);
        assert_eq!(t.get::<f64>(1), Some(3.14f64));
    }

    #[test]
    fn get_i16() {
        let t = Tuple::new();

        assert_eq!(t.get::<i16>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<i32>(-32769);
        t.push_back::<i16>(i16::MIN);
        t.push_back::<i16>(-256);
        t.push_back::<i16>(-255);
        t.push_back::<i16>(-129);
        t.push_back::<i16>(-128); // i8::MIN
        t.push_back::<i16>(127); // i8::MAX
        t.push_back::<i16>(128);
        t.push_back::<i16>(255);
        t.push_back::<i16>(256);
        t.push_back::<i16>(i16::MAX);
        t.push_back::<i32>(32768);

        assert_eq!(t.get::<i16>(0), None);
        assert_eq!(t.get::<i16>(1), None);
        assert_eq!(t.get::<i16>(2), Some(i16::MIN));
        assert_eq!(t.get::<i16>(3), Some(-256));
        assert_eq!(t.get::<i16>(4), Some(-255));
        assert_eq!(t.get::<i16>(5), Some(-129));
        assert_eq!(t.get::<i16>(6), Some(-128));
        assert_eq!(t.get::<i16>(7), Some(127));
        assert_eq!(t.get::<i16>(8), Some(128));
        assert_eq!(t.get::<i16>(9), Some(255));
        assert_eq!(t.get::<i16>(10), Some(256));
        assert_eq!(t.get::<i16>(11), Some(i16::MAX));
        assert_eq!(t.get::<i16>(12), None);
    }

    #[test]
    fn get_i32() {
        let t = Tuple::new();

        assert_eq!(t.get::<i32>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<i64>(-2147483649);
        t.push_back::<i32>(i32::MIN);
        t.push_back::<i32>(-16777216);
        t.push_back::<i32>(-16777215);
        t.push_back::<i32>(-65536);
        t.push_back::<i32>(-65535);
        t.push_back::<i32>(-32769);
        t.push_back::<i32>(-32768); // i16::MIN
        t.push_back::<i32>(32767); // i16::MAX
        t.push_back::<i32>(32768);
        t.push_back::<i32>(65535);
        t.push_back::<i32>(65536);
        t.push_back::<i32>(16777215);
        t.push_back::<i32>(16777216);
        t.push_back::<i32>(i32::MAX);
        t.push_back::<i64>(2147483648);

        assert_eq!(t.get::<i32>(0), None);
        assert_eq!(t.get::<i32>(1), None);
        assert_eq!(t.get::<i32>(2), Some(i32::MIN));
        assert_eq!(t.get::<i32>(3), Some(-16777216));
        assert_eq!(t.get::<i32>(4), Some(-16777215));
        assert_eq!(t.get::<i32>(5), Some(-65536));
        assert_eq!(t.get::<i32>(6), Some(-65535));
        assert_eq!(t.get::<i32>(7), Some(-32769));
        assert_eq!(t.get::<i32>(8), Some(-32768));
        assert_eq!(t.get::<i32>(9), Some(32767));
        assert_eq!(t.get::<i32>(10), Some(32768));
        assert_eq!(t.get::<i32>(11), Some(65535));
        assert_eq!(t.get::<i32>(12), Some(65536));
        assert_eq!(t.get::<i32>(13), Some(16777215));
        assert_eq!(t.get::<i32>(14), Some(16777216));
        assert_eq!(t.get::<i32>(15), Some(i32::MAX));
        assert_eq!(t.get::<i32>(16), None);
    }

    #[test]
    fn get_i64() {
        let t = Tuple::new();

        assert_eq!(t.get::<i64>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<BigInt>(BigInt::parse_bytes(b"-9223372036854775809", 10).unwrap());
        t.push_back::<i64>(i64::MIN);
        t.push_back::<i64>(-72057594037927936);
        t.push_back::<i64>(-72057594037927935);
        t.push_back::<i64>(-281474976710656);
        t.push_back::<i64>(-281474976710655);
        t.push_back::<i64>(-1099511627776);
        t.push_back::<i64>(-1099511627775);
        t.push_back::<i64>(-4294967296);
        t.push_back::<i64>(-4294967295);
        t.push_back::<i64>(-2147483649);
        t.push_back::<i64>(-2147483648); // i32::MIN
        t.push_back::<i64>(2147483647); // i32::MAX
        t.push_back::<i64>(2147483648);
        t.push_back::<i64>(4294967295);
        t.push_back::<i64>(4294967296);
        t.push_back::<i64>(1099511627775);
        t.push_back::<i64>(1099511627776);
        t.push_back::<i64>(281474976710655);
        t.push_back::<i64>(281474976710656);
        t.push_back::<i64>(72057594037927935);
        t.push_back::<i64>(72057594037927936);
        t.push_back::<i64>(i64::MAX);
        t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());

        assert_eq!(t.get::<i64>(0), None);
        assert_eq!(t.get::<i64>(1), None);
        assert_eq!(t.get::<i64>(2), Some(i64::MIN));
        assert_eq!(t.get::<i64>(3), Some(-72057594037927936));
        assert_eq!(t.get::<i64>(4), Some(-72057594037927935));
        assert_eq!(t.get::<i64>(5), Some(-281474976710656));
        assert_eq!(t.get::<i64>(6), Some(-281474976710655));
        assert_eq!(t.get::<i64>(7), Some(-1099511627776));
        assert_eq!(t.get::<i64>(8), Some(-1099511627775));
        assert_eq!(t.get::<i64>(9), Some(-4294967296));
        assert_eq!(t.get::<i64>(10), Some(-4294967295));
        assert_eq!(t.get::<i64>(11), Some(-2147483649));
        assert_eq!(t.get::<i64>(12), Some(-2147483648));
        assert_eq!(t.get::<i64>(13), Some(2147483647));
        assert_eq!(t.get::<i64>(14), Some(2147483648));
        assert_eq!(t.get::<i64>(15), Some(4294967295));
        assert_eq!(t.get::<i64>(16), Some(4294967296));
        assert_eq!(t.get::<i64>(17), Some(1099511627775));
        assert_eq!(t.get::<i64>(18), Some(1099511627776));
        assert_eq!(t.get::<i64>(19), Some(281474976710655));
        assert_eq!(t.get::<i64>(20), Some(281474976710656));
        assert_eq!(t.get::<i64>(21), Some(72057594037927935));
        assert_eq!(t.get::<i64>(22), Some(72057594037927936));
        assert_eq!(t.get::<i64>(23), Some(i64::MAX));
        assert_eq!(t.get::<i64>(24), None);
    }

    #[test]
    fn get_i8() {
        let t = Tuple::new();

        assert_eq!(t.get::<i8>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<i16>(-129);
        t.push_back::<i8>(i8::MIN);
        t.push_back::<i8>(0);
        t.push_back::<i8>(i8::MAX);
        t.push_back::<i16>(128);

        assert_eq!(t.get::<i8>(0), None);
        assert_eq!(t.get::<i8>(1), None);
        assert_eq!(t.get::<i8>(2), Some(i8::MIN));
        assert_eq!(t.get::<i8>(3), Some(0));
        assert_eq!(t.get::<i8>(4), Some(i8::MAX));
        assert_eq!(t.get::<i8>(5), None);
    }

    #[test]
    fn get_tuple_ref() {
        let t = Tuple::new();

        assert_eq!(t.get::<&Tuple>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<Tuple>({
            let mut t1 = Tuple::new();
            t1.push_back::<Versionstamp>(Versionstamp::incomplete(0));
            t1
        });

        assert_eq!(t.get::<&Tuple>(0), None);
        assert_eq!(
            t.get::<&Tuple>(1),
            Some(&{
                let mut t1 = Tuple::new();
                t1.push_back::<Versionstamp>(Versionstamp::incomplete(0));
                t1
            })
        );
    }

    #[test]
    fn get_versionstamp_ref() {
        let t = Tuple::new();

        assert_eq!(t.get::<&Versionstamp>(0), None);

        let mut t = Tuple::new();
        t.push_back::<Null>(Null);
        t.push_back::<Versionstamp>(Versionstamp::complete(
            Bytes::from_static(b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"),
            657,
        ));

        assert_eq!(t.get::<&Versionstamp>(0), None);
        assert_eq!(
            t.get::<&Versionstamp>(1),
            Some(&Versionstamp::complete(
                Bytes::from_static(b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"),
                657,
            ))
        );
    }

    #[test]
    fn get_null() {
        let t = Tuple::new();

        assert_eq!(t.get::<Null>(0), None);

        let mut t = Tuple::new();
        t.push_back::<bool>(true);
        t.push_back::<Null>(Null);

        assert_eq!(t.get::<Null>(0), None);
        assert_eq!(t.get::<Null>(1), Some(Null));
    }

    #[test]
    fn is_empty() {
        let mut t = Tuple::new();

        assert!(t.is_empty());

        t.push_back::<Null>(Null);

        assert!(!t.is_empty());
    }

    #[test]
    fn size() {
        let mut t = Tuple::new();

        assert_eq!(t.size(), 0);

        t.push_back::<Null>(Null);

        assert_eq!(t.size(), 1);
    }

    // `3.14` is copied from Java binding tests
    #[allow(clippy::approx_constant)]
    #[test]
    fn pack() {
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(0);
                t
            }
            .pack(),
            Bytes::from_static(&b"\x14"[..])
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"0", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x14")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(1);
                t
            }
            .pack(),
            Bytes::from_static(b"\x15\x01")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"1", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x15\x01")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(-1);
                t
            }
            .pack(),
            Bytes::from_static(b"\x13\xFE")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"-1", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x13\xFE")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(255);
                t
            }
            .pack(),
            Bytes::from_static(b"\x15\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"255", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x15\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(-255);
                t
            }
            .pack(),
            Bytes::from_static(b"\x13\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"-255", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x13\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(256);
                t
            }
            .pack(),
            Bytes::from_static(b"\x16\x01\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"256", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x16\x01\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i32>(65536);
                t
            }
            .pack(),
            Bytes::from_static(b"\x17\x01\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i32>(-65536);
                t
            }
            .pack(),
            Bytes::from_static(b"\x11\xFE\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(i64::MAX);
                t
            }
            .pack(),
            Bytes::from_static(b"\x1C\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775807", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x1C\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"9223372036854775808", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x1C\x80\x00\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551615", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x1C\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"18446744073709551616", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x1D\x09\x01\x00\x00\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(-4294967295);
                t
            }
            .pack(),
            Bytes::from_static(b"\x10\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"-4294967295", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x10\x00\x00\x00\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(i64::MIN + 2);
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x80\x00\x00\x00\x00\x00\x00\x01"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(i64::MIN + 1);
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x80\x00\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(
                    // i64::MIN + 1
                    BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap() + 1,
                );
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x80\x00\x00\x00\x00\x00\x00\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i64>(i64::MIN);
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(
                    // i64::MIN
                    BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap(),
                );
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(
                    // i64::MIN - 1
                    BigInt::parse_bytes(b"-9223372036854775808", 10).unwrap() - 1,
                );
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFE")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<BigInt>(BigInt::parse_bytes(b"-18446744073709551615", 10).unwrap());
                t
            }
            .pack(),
            Bytes::from_static(b"\x0C\x00\x00\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(3.14f32);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\xC0\x48\xF5\xC3")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(-3.14f32);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\x3F\xB7\x0A\x3C")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(3.14f64);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\xC0\x09\x1E\xB8\x51\xEB\x85\x1F")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(-3.14f64);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\x3F\xF6\xE1\x47\xAE\x14\x7A\xE0")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(0.0f32);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\x80\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(-0.0f32);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\x7F\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(0.0f64);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\x80\x00\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(-0.0f64);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\x7F\xFF\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(f32::INFINITY);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\xFF\x80\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f32>(f32::NEG_INFINITY);
                t
            }
            .pack(),
            Bytes::from_static(b"\x20\x00\x7F\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(f64::INFINITY);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\xFF\xF0\x00\x00\x00\x00\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<f64>(f64::NEG_INFINITY);
                t
            }
            .pack(),
            Bytes::from_static(b"\x21\x00\x0F\xFF\xFF\xFF\xFF\xFF\xFF")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Bytes>(Bytes::new());
                t
            }
            .pack(),
            Bytes::from_static(b"\x01\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Bytes>(Bytes::from_static(b"\x01\x02\x03"));
                t
            }
            .pack(),
            Bytes::from_static(b"\x01\x01\x02\x03\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Bytes>(Bytes::from_static(b"\x00\x00\x00\x04"));
                t
            }
            .pack(),
            Bytes::from_static(b"\x01\x00\xFF\x00\xFF\x00\xFF\x04\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x02\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("hello".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x02hello\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("中文".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x02\xE4\xB8\xAD\xE6\x96\x87\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("μάθημα".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x02\xCE\xBC\xCE\xAC\xCE\xB8\xCE\xB7\xCE\xBC\xCE\xB1\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("\u{10ffff}".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x02\xF4\x8F\xBF\xBF\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<Null>(Null);
                    t1
                });
                t
            }
            .pack(),
            Bytes::from_static(b"\x05\x00\xFF\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<Null>(Null);
                    t1.push_back::<String>("hello".to_string());
                    t1
                });
                t
            }
            .pack(),
            Bytes::from_static(b"\x05\x00\xFF\x02hello\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<Null>(Null);
                    t1.push_back::<String>("hell\x00".to_string());
                    t1
                });
                t
            }
            .pack(),
            Bytes::from_static(b"\x05\x00\xFF\x02hell\x00\xFF\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<Null>(Null);
                    t1
                });
                t.push_back::<String>("hello".to_string());
                t
            }
            .pack(),
            Bytes::from_static(b"\x05\x00\xFF\x00\x02hello\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<Null>(Null);
                    t1
                });
                t.push_back::<String>("hello".to_string());
                t.push_back::<Bytes>(Bytes::from_static(b"\x01\x00"));
                t.push_back::<Bytes>(Bytes::new());
                t
            }
            .pack(),
            Bytes::from_static(b"\x05\x00\xFF\x00\x02hello\x00\x01\x01\x00\xFF\x00\x01\x00"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Uuid>(
                    Uuid::parse_str("ffffffff-ba5e-ba11-0000-00005ca1ab1e").unwrap(),
                );
                t
            }
            .pack(),
            Bytes::from_static(
                b"\x30\xFF\xFF\xFF\xFF\xBA\x5E\xBA\x11\x00\x00\x00\x00\x5C\xA1\xAB\x1E"
            )
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<bool>(false);
                t
            }
            .pack(),
            Bytes::from_static(b"\x26")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<bool>(true);
                t
            }
            .pack(),
            Bytes::from_static(b"\x27"),
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<i8>(3);
                t
            }
            .pack(),
            Bytes::from_static(b"\x15\x03")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Versionstamp>(Versionstamp::complete(
                    Bytes::from_static(b"\xAA\xBB\xCC\xDD\xEE\xFF\x00\x01\x02\x03"),
                    0,
                ));
                t
            }
            .pack(),
            Bytes::from_static(b"\x33\xAA\xBB\xCC\xDD\xEE\xFF\x00\x01\x02\x03\x00\x00")
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Versionstamp>(Versionstamp::complete(
                    Bytes::from_static(&b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"[..]),
                    657,
                ));
                t
            }
            .pack(),
            Bytes::from_static(b"\x33\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A\x02\x91")
        );
    }

    #[test]
    fn pack_with_versionstamp() {
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<String>("foo".to_string());
                t.push_back::<Versionstamp>(Versionstamp::incomplete(0));
                t
            }
            .pack_with_versionstamp(Bytes::new()),
            Ok(Bytes::from_static(
                b"\x02foo\x00\x33\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\x00\x00\x06\x00\x00\x00"
            ))
        );
        assert_eq!(
            Tuple::new().pack_with_versionstamp(Bytes::new()),
            Err(FdbError::new(TUPLE_PACK_WITH_VERSIONSTAMP_NOT_FOUND))
        );
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Null>(Null);
                t.push_back::<Versionstamp>(Versionstamp::incomplete(0));
                t.push_back::<Tuple>({
                    let mut t1 = Tuple::new();
                    t1.push_back::<String>("foo".to_string());
                    t1.push_back::<Versionstamp>(Versionstamp::incomplete(1));
                    t1
                });
                t
            }
            .pack_with_versionstamp(Bytes::new()),
            Err(FdbError::new(TUPLE_PACK_WITH_VERSIONSTAMP_MULTIPLE_FOUND))
        );
    }

    #[test]
    fn range() {
        assert!(std::panic::catch_unwind(|| {
            {
                let mut t = Tuple::new();
                t.push_back::<Versionstamp>(Versionstamp::incomplete(0));
                t
            }
            .range(Bytes::new());
        })
        .is_err());
        assert_eq!(
            {
                let mut t = Tuple::new();
                t.push_back::<Bytes>(Bytes::from_static(b"bar"));
                t
            }
            .range(Bytes::from_static(b"foo")),
            Range::new(
                Bytes::from_static(b"foo\x01bar\x00\x00"),
                Bytes::from_static(b"foo\x01bar\x00\xFF")
            )
        );
    }

    #[test]
    fn from_elements() {
        let mut t1 = Tuple::new();
        t1.push_back::<Null>(Null);

        let t = Tuple::from_elements(t1.elements.into());

        assert!(!t.has_incomplete_versionstamp());
        assert_eq!(t.elements, vec![TupleValue::NullValue]);

        let mut t1 = Tuple::new();
        t1.push_back::<Null>(Null);

        let mut t2 = Tuple::new();
        t2.push_back::<Versionstamp>(Versionstamp::incomplete(0));
        t1.push_back::<Tuple>(t2);

        let t = Tuple::from_elements(t1.elements.into());

        assert!(t.has_incomplete_versionstamp());
        assert_eq!(
            t.elements,
            vec![
                TupleValue::NullValue,
                // We don't want to use `Tuple::from_elements` here.
                TupleValue::NestedTuple({
                    let mut x = Tuple::new();
                    x.push_back::<Versionstamp>(Versionstamp::incomplete(0));
                    x
                }),
            ]
        );

        let mut t1 = Tuple::new();
        t1.push_back::<Null>(Null);
        t1.push_back::<Versionstamp>(Versionstamp::incomplete(0));

        let t = Tuple::from_elements(t1.elements.into());

        assert!(t.has_incomplete_versionstamp());
        assert_eq!(
            t.elements,
            vec![
                TupleValue::NullValue,
                // We don't want to use `Tuple::from_elements` here.
                TupleValue::Versionstamp96Bit(Versionstamp::incomplete(0)),
            ]
        );
    }
}

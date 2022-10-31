/// Used to represent values of [`null`] type that can be contained
/// within a [`Tuple`].
///
/// [`null`]: https://github.com/apple/foundationdb/blob/release-6.3/design/tuple.md#null-value
/// [`Tuple`]: crate::tuple::Tuple
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Null;

#[cfg(test)]
mod tests {
    use super::Null;

    #[test]
    fn new() {
        let null = Null;

        assert_eq!(null, Null);
    }
}

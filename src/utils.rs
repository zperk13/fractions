use num_traits::PrimInt;

pub(crate) fn is_power_of_two<T: PrimInt>(x: T) -> bool {
    // Algorithm from https://stackoverflow.com/a/600306/10821659
    (!x.is_zero()) && ((x & (x - T::one())).is_zero())
}

// Still needed even if we don't allow signed numbers because 0 is neither negative nor positive, but can be unsigned
pub(crate) fn is_positive<T: PrimInt>(x: T) -> bool {
    x >= T::one()
}

// Greatest Common Divisor
pub(crate) fn gcd<T: PrimInt>(a: T, b: T) -> T {
    if b.is_zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(clippy::bool_assert_comparison)]
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_is_power_of_two() {
        assert_eq!(is_power_of_two(0), false);
        assert_eq!(is_power_of_two(1), true);
        assert_eq!(is_power_of_two(2), true);
        assert_eq!(is_power_of_two(3), false);
        assert_eq!(is_power_of_two(4), true);
        assert_eq!(is_power_of_two(5), false);
        assert_eq!(is_power_of_two(6), false);
        assert_eq!(is_power_of_two(7), false);
        assert_eq!(is_power_of_two(8), true);
        assert_eq!(is_power_of_two(9), false);
    }
    #[test]
    fn test_gcd() {
        assert_eq!(gcd(54, 24), 6);
        assert_eq!(gcd(54, 26), 2);
        assert_eq!(gcd(3, 2), 1);
        assert_eq!(gcd(63, 462), 21);
    }
}

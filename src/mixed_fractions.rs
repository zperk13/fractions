use crate::fraction::Fraction;
use num_traits::{PrimInt, Unsigned};

#[derive(Debug, Clone, Copy)]
pub struct MixedFraction<T: Unsigned + PrimInt> {
    pub whole_part: T,
    pub fraction: Fraction<T>,
}

impl<T: Unsigned + PrimInt> MixedFraction<T> {
    pub fn new(whole_part: T, fraction: Fraction<T>) -> Self {
        Self {
            whole_part,
            fraction,
        }
    }

    pub fn checked_mul_mixed_fraction(self, rhs: Self) -> Option<Fraction<T>> {
        Self::checked_mul_fraction(self, Fraction::from(rhs))
    }

    pub fn checked_mul_fraction(self, rhs: Fraction<T>) -> Option<Fraction<T>> {
        Fraction::from(self).checked_mul_fraction(rhs)
    }

    pub fn checked_mul_whole_num(self, rhs: T) -> Option<Fraction<T>> {
        Fraction::from(self).checked_mul_whole_num(rhs)
    }
}

impl<T: Unsigned + PrimInt> From<Fraction<T>> for MixedFraction<T> {
    fn from(f: Fraction<T>) -> Self {
        let (quotient, remainder) = f.div_with_remainder();
        Self {
            whole_part: quotient,
            fraction: Fraction::new(remainder, f.denominator),
        }
    }
}

impl<T: Unsigned + PrimInt + std::fmt::Display> std::fmt::Display for MixedFraction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{} {:#}", self.whole_part, self.fraction)
        } else {
            write!(f, "{} {}", self.whole_part, self.fraction)
        }
    }
}

impl<T: Unsigned + PrimInt> std::ops::Mul for MixedFraction<T> {
    type Output = Fraction<T>;

    fn mul(self, rhs: Self) -> Self::Output {
        self.checked_mul_mixed_fraction(rhs).expect(
            "Failed to multiply. Reducing mixed fractions before multiplying may fix the issue.",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fraction;
    #[test]
    fn test_from_fraction() {
        let f = Fraction::new(11_u32, 4);
        let mf = MixedFraction::from(f);
        assert_eq!(mf.whole_part, 2);
        assert_eq!(mf.fraction.numerator, 3);
        assert_eq!(mf.fraction.denominator, 4);
    }

    #[test]
    fn test_mul() {
        let f = MixedFraction::new(2_u32, fraction!(3 / 4)).checked_mul_whole_num(3);
        assert_eq!(f, Some(fraction!(33 / 4)));
        /*let f = MixedFraction::from(f.unwrap());
        assert_eq!(f, MixedFraction::new(8, fraction!(1 / 4)))*/
    }
}

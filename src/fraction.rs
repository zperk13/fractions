use crate::{mixed_fraction::MixedFraction, utils};
use num_traits::{PrimInt, Unsigned};

#[derive(Debug, Clone, Copy)]
pub struct Fraction<T: Unsigned + PrimInt> {
    pub numerator: T,
    pub denominator: T,
}

impl<T: Unsigned + PrimInt> Fraction<T> {
    pub fn new(numerator: T, denominator: T) -> Self {
        assert!(!denominator.is_zero(), "Denominator must not be zero");
        Self {
            numerator,
            denominator,
        }
    }

    pub fn try_new(numerator: T, denominator: T) -> Option<Self> {
        if denominator.is_zero() {
            None
        } else {
            Some(Self {
                numerator,
                denominator,
            })
        }
    }

    pub fn is_unit_fraction(&self) -> bool {
        self.numerator.is_one()
    }

    pub fn is_dyadic_fraction(&self) -> bool {
        utils::is_power_of_two(self.denominator)
    }

    pub fn unicode_number_form(&self) -> Option<char> {
        let two = T::from(2).expect("Failed to get turn 2 {integer} into T: Unsigned + PrimInt");
        let three = T::from(3).expect("Failed to get turn 3 {integer} into T: Unsigned + PrimInt");
        let four = T::from(4).expect("Failed to get turn 4 {integer} into T: Unsigned + PrimInt");
        let five = T::from(5).expect("Failed to get turn 5 {integer} into T: Unsigned + PrimInt");
        let six = T::from(6).expect("Failed to get turn 6 {integer} into T: Unsigned + PrimInt");
        let seven = T::from(7).expect("Failed to get turn 7 {integer} into T: Unsigned + PrimInt");
        let eight = T::from(8).expect("Failed to get turn 8 {integer} into T: Unsigned + PrimInt");
        let nine = T::from(9).expect("Failed to get turn 9 {integer} into T: Unsigned + PrimInt");
        let ten = T::from(10).expect("Failed to get turn 10 {integer} into T: Unsigned + PrimInt");

        if self.numerator.is_one() && self.denominator == four {
            Some('¼')
        } else if self.numerator.is_one() && self.denominator == two {
            Some('½')
        } else if self.numerator == three && self.denominator == four {
            Some('¾')
        } else if self.numerator.is_one() && self.denominator == seven {
            Some('⅐')
        } else if self.numerator.is_one() && self.denominator == nine {
            Some('⅑')
        } else if self.numerator.is_one() && self.denominator == ten {
            Some('⅒')
        } else if self.numerator.is_one() && self.denominator == three {
            Some('⅓')
        } else if self.numerator == two && self.denominator == three {
            Some('⅔')
        } else if self.numerator.is_one() && self.denominator == five {
            Some('⅕')
        } else if self.numerator == two && self.denominator == five {
            Some('⅖')
        } else if self.numerator == three && self.denominator == five {
            Some('⅗')
        } else if self.numerator == four && self.denominator == five {
            Some('⅘')
        } else if self.numerator.is_one() && self.denominator == six {
            Some('⅙')
        } else if self.numerator == five && self.denominator == six {
            Some('⅚')
        } else if self.numerator.is_one() && self.denominator == eight {
            Some('⅛')
        } else if self.numerator == three && self.denominator == eight {
            Some('⅜')
        } else if self.numerator == five && self.denominator == eight {
            Some('⅝')
        } else if self.numerator == seven && self.denominator == eight {
            Some('⅞')
        } else if self.numerator.is_zero() && self.denominator == three {
            Some('↉')
        } else {
            None
        }
    }

    pub fn is_proper(&self) -> bool {
        use utils::is_positive;
        is_positive(self.numerator)
            && is_positive(self.denominator)
            && (self.numerator < self.denominator)
    }

    pub fn is_improper(&self) -> bool {
        !self.is_proper()
    }

    // Returns None if 0
    pub fn reciprocal(&self) -> Option<Fraction<T>> {
        Self::try_new(self.denominator, self.numerator)
    }

    // Returns (quotient: T, remainder: T)
    pub fn div_with_remainder(&self) -> (T, T) {
        (
            self.numerator / self.denominator,
            self.numerator % self.denominator,
        )
    }

    pub fn is_reduced(&self) -> bool {
        utils::gcd(self.numerator, self.denominator) == T::one()
    }

    pub fn reduced(&self) -> Self {
        let gcd = utils::gcd(self.numerator, self.denominator);
        if gcd == T::one() {
            // Already fully reduced
            *self
        } else {
            Fraction::new(self.numerator / gcd, self.denominator / gcd)
        }
    }

    pub fn reduce(&mut self) {
        *self = self.reduced();
    }

    pub fn min_value() -> Self {
        Self::new(T::one(), T::max_value())
    }

    pub fn max_value() -> Self {
        Self::new(T::max_value(), T::one())
    }

    // Returns None if overflow occurred
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        let mut new_self = self.reduced();
        let mut new_rhs = rhs.reduced();
        if new_self.denominator != new_rhs.denominator {
            let new_self_denominator = new_self.denominator;
            let new_rhs_denominator = new_rhs.denominator;
            new_self.numerator = new_self.numerator.checked_mul(&new_rhs_denominator)?;
            new_self.denominator = new_self.denominator.checked_mul(&new_rhs_denominator)?;
            new_rhs.numerator = new_rhs.numerator.checked_mul(&new_self_denominator)?;
            new_rhs.denominator = new_rhs.denominator.checked_mul(&new_self_denominator)?;
        }
        Some(Self::new(
            new_self.numerator.checked_add(&new_rhs.numerator)?,
            new_self.denominator,
        ))
    }

    // Returns None if overflow occurred
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        let mut new_self = self.reduced();
        let mut new_rhs = rhs.reduced();
        if new_self.denominator != new_rhs.denominator {
            let new_self_denominator = new_self.denominator;
            let new_rhs_denominator = new_rhs.denominator;
            new_self.numerator = new_self.numerator.checked_mul(&new_rhs_denominator)?;
            new_self.denominator = new_self.denominator.checked_mul(&new_rhs_denominator)?;
            new_rhs.numerator = new_rhs.numerator.checked_mul(&new_self_denominator)?;
            new_rhs.denominator = new_rhs.denominator.checked_mul(&new_self_denominator)?;
        }
        Some(Self::new(
            new_self.numerator.checked_sub(&new_rhs.numerator)?,
            new_self.denominator,
        ))
    }

    // Returns None if overflow occurred
    pub fn checked_mul_fraction(self, rhs: Self) -> Option<Self> {
        Some(Self::new(
            self.numerator.checked_mul(&rhs.numerator)?,
            self.denominator.checked_mul(&rhs.denominator)?,
        ))
    }

    // Returns None if overflow occurred
    pub fn checked_mul_whole_num(self, rhs: T) -> Option<Self> {
        Some(Self::new(
            self.numerator.checked_mul(&rhs)?,
            self.denominator,
        ))
    }

    // Returns None if rhs == 0 or overflow occurred
    pub fn checked_div_by_whole_num(self, rhs: T) -> Option<Self> {
        if rhs.is_zero() {
            None
        } else {
            Some(Self::new(self.numerator, self.denominator * rhs))
        }
    }

    // Returns None if whole_num == 0 or overflow occurred
    pub fn checked_whole_num_div_fraction(whole_num: T, f: Self) -> Option<Self> {
        Self::from(whole_num).reciprocal()?.checked_mul_fraction(f)
    }

    // Returns None if rhs.numerator == 0 or overflow occurred
    pub fn checked_div_fraction(self, rhs: Self) -> Option<Self> {
        self.checked_mul_fraction(rhs.reciprocal()?)
    }
}

#[macro_export]
macro_rules! fraction {
    ($numerator:literal / $denominator:literal) => {
        Fraction::new($numerator, $denominator)
    };

    ($numerator:literal , $denominator:literal) => {
        Fraction::new($numerator, $denominator)
    };
}

impl<T: Unsigned + PrimInt> PartialEq for Fraction<T> {
    fn eq(&self, other: &Self) -> bool {
        let reduced_self = self.reduced();
        let reduced_other = other.reduced();
        reduced_self.numerator == reduced_other.numerator
            && reduced_self.denominator == reduced_other.denominator
    }
}

impl<T: Unsigned + PrimInt> Eq for Fraction<T> {}

// If you ever add the ability to use negative numbers, some stuff will have to change in how you check if fractions are greater than or less than each other
impl<T: Unsigned + PrimInt> PartialOrd for Fraction<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Unsigned + PrimInt> Ord for Fraction<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let reduced_self = self.reduced();
        let reduced_other = other.reduced();
        if reduced_self.denominator == reduced_other.denominator {
            reduced_self.numerator.cmp(&reduced_other.numerator)
        } else if reduced_self.numerator == reduced_other.numerator {
            reduced_self
                .denominator
                .cmp(&reduced_other.denominator)
                .reverse()
        } else {
            (reduced_self.numerator * reduced_other.denominator)
                .cmp(&(reduced_other.numerator * reduced_self.denominator))
        }
    }
}

macro_rules! impl_from_primitive_fraction_for_float {
    ($T:ty) => {
        impl From<Fraction<$T>> for f32 {
            fn from(val: Fraction<$T>) -> Self {
                let numerator: f32 = val.numerator as f32;
                let denominator: f32 = val.denominator as f32;
                numerator / denominator
            }
        }
        impl From<Fraction<$T>> for f64 {
            fn from(val: Fraction<$T>) -> Self {
                let numerator: f64 = val.numerator as f64;
                let denominator: f64 = val.denominator as f64;
                numerator / denominator
            }
        }
    };
}

crate::macros::macro_all_unsigned_primitive_ints!(impl_from_primitive_fraction_for_float);

impl<T: Unsigned + PrimInt> From<T> for Fraction<T> {
    fn from(val: T) -> Self {
        Fraction {
            numerator: val,
            denominator: T::one(),
        }
    }
}

impl<T: Unsigned + PrimInt + std::fmt::Display> std::fmt::Display for Fraction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            let numerator_string = format!("{}", self.numerator);
            let denominator_string = format!("{}", self.denominator);
            let mut resulting_string =
                String::with_capacity(numerator_string.len() + denominator_string.len() + 1);
            for c in numerator_string.chars() {
                resulting_string.push(match c {
                    '0' => '⁰',
                    '1' => '¹',
                    '2' => '²',
                    '3' => '³',
                    '4' => '⁴',
                    '5' => '⁵',
                    '6' => '⁶',
                    '7' => '⁷',
                    '8' => '⁸',
                    '9' => '⁹',
                    _ => panic!("Digit from turning a Unsigned+PrimInt+Display was somehow not 0, 1, 2, 3, 4, 5, 6, 7, 8, or 9"),
                })
            }
            resulting_string.push('⁄');
            for c in denominator_string.chars() {
                resulting_string.push(match c {
                    '0' => '₀',
                    '1' => '₁',
                    '2' => '₂',
                    '3' => '₃',
                    '4' => '₄',
                    '5' => '₅',
                    '6' => '₆',
                    '7' => '₇',
                    '8' => '₈',
                    '9' => '₉',
                    _ => panic!("Digit from turning a Unsigned+PrimInt+Display was somehow not 0, 1, 2, 3, 4, 5, 6, 7, 8, or 9"),
                })
            }
            write!(f, "{resulting_string}")
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl<T: Unsigned + PrimInt> std::ops::Add for Fraction<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
            .expect("Overflow occurred when adding")
    }
}

impl<T: Unsigned + PrimInt> std::ops::AddAssign for Fraction<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl<T: Unsigned + PrimInt> std::ops::Sub for Fraction<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("Overflow occurred when subbing")
    }
}

impl<T: Unsigned + PrimInt> std::ops::SubAssign for Fraction<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs
    }
}

impl<T: Unsigned + PrimInt> std::ops::Mul for Fraction<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.checked_mul_fraction(rhs)
            .expect("Overflow occurred when multiplying. Reducing fractions before multiplying may fix the issue.")
    }
}

impl<T: Unsigned + PrimInt> std::ops::MulAssign for Fraction<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs
    }
}

impl<T: Unsigned + PrimInt> std::ops::Div for Fraction<T> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.checked_div_fraction(rhs).expect("Overflow occurred when dividing. Reducing fractions before dividing may fix the issue.")
    }
}

impl<T: Unsigned + PrimInt> std::ops::DivAssign for Fraction<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs
    }
}

impl<T: Unsigned + PrimInt> From<MixedFraction<T>> for Fraction<T> {
    fn from(mf: MixedFraction<T>) -> Self {
        Self::new(
            mf.whole_part * mf.fraction.denominator + mf.fraction.numerator,
            mf.fraction.denominator,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macros::macro_all_unsigned_primitive_ints;

    #[test]
    fn test_fraction_macro() {
        assert_eq!(fraction!(1 / 2), Fraction::new(1_u32, 2));
        assert_eq!(fraction!(3, 4), Fraction::new(3_u32, 4));
    }

    #[cfg(test)]
    mod one_over_two_to_float {
        use super::*;
        macro_rules! test_with_type {
            ($T:ty) => {
                paste::item! {
                    #[test]
                    fn [<test_ $T>]() {
                        let fraction: Fraction<$T> = Fraction::new(1, 2);
                        let float32 = f32::from(fraction);
                        let float64 = f64::from(fraction);
                        assert_eq!(float32, 0.5);
                        assert_eq!(float64, 0.5);
                    }
                }
            };
        }
        macro_all_unsigned_primitive_ints!(test_with_type);
    }
    #[cfg(test)]
    mod test_primitive_into_to_fraction {
        use super::*;
        macro_rules! test_with_type {
            ($T:ty) => {
                paste::item! {
                    #[test]
                    fn [<test_ $T>]() {
                        let i: $T = 13;
                        let fraction = Fraction::from(i);
                        assert_eq!(fraction.numerator, i);
                        assert_eq!(fraction.denominator, 1);
                    }
                }
            };
        }
        macro_all_unsigned_primitive_ints!(test_with_type);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", fraction!(1023456789_u32 / 1)), "1023456789/1");
        assert_eq!(
            format!("{:#}", fraction!(1023456789_u32 / 1)),
            "¹⁰²³⁴⁵⁶⁷⁸⁹⁄₁"
        );
    }

    #[test]
    fn test_reciprocal() {
        let num: u32 = 13;
        let f = Fraction::from(num).reciprocal();
        assert!(f.is_some());
        let f = f.unwrap();
        assert_eq!(f.numerator, 1);
        assert_eq!(f.denominator, num);
        assert!(Fraction::new(0, num).reciprocal().is_none());
    }

    #[test]
    fn test_div_with_remainder() {
        assert_eq!(fraction!(7_u32 / 3).div_with_remainder(), (2, 1));
    }

    #[test]
    fn test_reduce() {
        assert_eq!(fraction!(63_u32 / 462).reduced(), fraction!(3 / 22));
    }

    #[test]
    fn test_eq() {
        assert_eq!(fraction!(1_u32 / 2), fraction!(2 / 4));
    }

    #[test]
    fn test_ord() {
        assert!(fraction!(3_u32 / 4) > fraction!(2 / 4));
        assert!(fraction!(13_u32 / 2) > fraction!(13 / 3));
        assert!(fraction!(15_u32 / 18) > fraction!(4 / 17));
    }

    #[test]
    fn test_add() {
        assert_eq!(
            fraction!(2_u32 / 4).checked_add(fraction!(3 / 4)),
            Some(fraction!(5 / 4))
        );
        assert_eq!(
            fraction!(1_u32 / 4).checked_add(fraction!(1 / 3)),
            Some(fraction!(7 / 12))
        );
        assert_eq!(
            fraction!(3_u32 / 5).checked_add(fraction!(2 / 3)),
            Some(fraction!(19 / 15))
        );
        assert_eq!(
            fraction!(3_u32 / 4).checked_add(fraction!(5 / 6)),
            Some(fraction!(19 / 12))
        );
    }

    #[test]
    fn test_sub() {
        assert_eq!(
            fraction!(2_u32 / 3).checked_sub(fraction!(1 / 2)),
            Some(fraction!(1 / 6))
        );
    }

    #[test]
    fn test_mul() {
        assert_eq!(
            fraction!(2_u32 / 3).checked_mul_fraction(fraction!(3 / 4)),
            Some(fraction!(6 / 12))
        );
        assert_eq!(
            fraction!(3_u32 / 4).checked_mul_whole_num(6),
            Some(fraction!(18 / 4))
        );
    }

    #[test]
    fn test_div() {
        assert_eq!(
            fraction!(10_u32 / 3).checked_div_by_whole_num(5),
            Some(fraction!(10 / 15))
        );
        assert_eq!(
            fraction!(1_u32 / 2).checked_div_fraction(fraction!(3 / 4)),
            Some(fraction!(2 / 3))
        );
    }

    #[test]
    fn temp_test() {
        println!(
            "{}",
            f64::from(fraction!(1_u64 / 10) + fraction!(2_u64 / 10))
        )
    }
}

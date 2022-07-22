pub mod fraction;
mod macros;
pub mod mixed_fraction;
mod utils;

pub mod prelude {
    pub use super::fraction;
    pub use super::fraction::Fraction;
    pub use super::mixed_fraction::MixedFraction;
}

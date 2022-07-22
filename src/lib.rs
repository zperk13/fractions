pub mod fraction;
mod macros;
mod utils;

pub mod prelude {
    pub use super::fraction;
    pub use super::fraction::Fraction;
}

//! The MIPS module contains the implementation of the [InstrumentedState] and the MIPS emulator.

mod instrumented;
pub use instrumented::InstrumentedState;

mod mips_vm;

mod mips_isa;

mod mips_linux;

/// Defines an enum type with underlying [u32] representation on variants, and a [TryFrom]
/// implementation automatically generated.
macro_rules! def_enum {
    ($enum:ident { $($variant:ident = $value:expr),* $(,)? }) => {
        #[doc = concat!("Supported ", stringify!($enum), "s within Howitzer.")]
        #[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
        #[allow(clippy::upper_case_acronyms)]
        #[repr(u32)]
        pub enum $enum {
            $( $variant = $value ),*
        }

        impl TryFrom<u32> for $enum {
            type Error = anyhow::Error;

            fn try_from(value: u32) -> Result<Self, Self::Error> {
                match value {
                    $(
                        $value => Ok(Self::$variant),
                    )*
                    _ => anyhow::bail!("Invalid {}: {:02x}", stringify!($enum), value),
                }
            }
        }
    }
}

pub(crate) use def_enum;

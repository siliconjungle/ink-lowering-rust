pub use ink_core::*;
pub mod definition_native;
pub mod machine_native;
mod ownership;
mod pure_rust;
pub mod snapshot_code;
pub mod state_native;

pub mod representation_program;

mod representation_ffi;



#[cfg(test)]
mod packed_spine_tests;



#[cfg(test)]
mod identity_memo_tests;

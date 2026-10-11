pub use ink_core::*;
pub mod definition_native;
pub mod machine_native;
mod ownership;
mod pure_rust;
pub mod snapshot_code;
pub mod state_native;

pub mod representation_program;

mod representation_ffi;

/// Compile-time read-only observation projection.
pub mod representation_query;


#[cfg(test)]
mod packed_spine_tests;

/// Compile-time elimination of private observations with independent next state.
pub mod representation_transition;


#[cfg(test)]
mod identity_memo_tests;

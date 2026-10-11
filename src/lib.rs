pub use ink_core::*;
pub mod definition_native;
pub mod machine_native;
mod ownership;
mod pure_rust;
pub mod snapshot_code;
pub mod state_native;

pub mod representation_native;
pub mod representation_program;

mod representation_ffi;

/// Compile-time read-only observation projection.
pub mod representation_query;

mod representation_bounds;

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

mod representation_bounds;

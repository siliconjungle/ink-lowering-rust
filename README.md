# Ink Rust lowering

Rust emission for Ink's executable pure/stateful language and checked first-order database
definitions. `definition_native::lower` accepts a core-owned `CheckedDefinition`;
`machine_native::lower` accepts a core-owned `CheckedMachine`. Neither witness can
be deserialised or constructed by assigning public fields. Proof checking and
selection authority live in ink-core.

`cargo run --release -- DEFINITIONS.json -o program.rs` rechecks an
`ink-definition-lowering-input-v1` request, emits Rust and prints its receipt.
The request contains schema 1, semantics, bundle, exports and optional selection.
Generated definitions use boxed algebraic data. Generated Machine keeps physical
state private across calls, supports logical snapshots/restoration and rejects
malformed requests before mutation. These are total-value sequential contracts,
not a proof of native memory layout, durability, concurrency or host failures.

The legacy state emitter still consumes admitted maintenance/storage choices and
contains bounded-representation analysis. That is documented migration debt;
putting it in this repository does not turn it into database proof authority.
Rust lowering, codecs, protocol control, num-bigint and Rust/LLVM remain trusted.

Part of the personal siliconjungle Ink repositories. The distribution pins this
repository as a submodule. Core schema/toolchain compatibility must be explicit;
repository identities do not establish correctness.

Pure helpers support all currently executable compute expressions, including i32/f32, vectors, collections and recursive records. Existing i32/f32 and fixed numerical vectors also cross state/action/keep/event boundaries. Scalar float comparisons use IEEE semantics; aggregate action equality compares stored float bits. Portable checkpoints preserve numerical representations, including NaN payloads and signed zero.

`state_native::emit_selected` accepts the shared checked semantic selection witness. Only proved pure helpers are changed; transaction bodies, state declarations and the existing maintenance obligations remain intact.

Stateful emission embeds `ink_core::TRANSACTION_RUST_SOURCE` verbatim for the
base commit decision, sticky nested-change errors and ordered event coordinates.
This is shared fixed semantics, not an optimisation or an action-body proof.
Physical rollback, codecs, payload lowering and Rust/LLVM remain trusted.

Current complete execution coverage, GPU exclusions and integration evidence are documented in the [lowering parity contract](https://github.com/siliconjungle/ink-lang/blob/main/docs/lowering-parity.md).
Pure compute functions and stateful code can coexist. Full-width values and recursive record fields use native Rust representations without changing Ink types. The runtime adds the portable native/Wasm host ABI.

`state_native::emit_selected` and `emit_selected_with_storage` retain the core-authenticated original checkpoint layout while emitting selected code. Bare Program emission keeps its own namespace. Selected code generation remains trusted; the witness does not verify machine code.

Standalone proof-selected representations use the compile-time checked witness
and emit literal functions with native state retained between calls. Generated
applications carry no proof package, checker context, source AST or Ink runtime
dependency. See ink-lang/docs/database-representations.md and the shared
`representation_parity` conformance gate. Recursive GPU state uses the complete
host lane; device eligibility remains separate.

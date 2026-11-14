import Lake
set_option autoImplicit false
open Lake DSL
-- Release integration for the byte-identical sources retained in ../nonsofic.
-- Excludes its unrelated root Statements/Proofs/Audit modules, whose names collide.
package FiniteLean where
  buildDir := "../nonsofic/.lake/build"
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
lean_lib FiniteLean where
  srcDir := "../nonsofic/vendor/finite-lean"
  globs := #[.submodules `FiniteLean]
lean_lib NonSofic where
  srcDir := "../nonsofic"
  globs := #[.andSubmodules `NonSofic]

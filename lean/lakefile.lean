import Lake
set_option autoImplicit false
open Lake DSL
package DomainNonembedding where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #["-j1", "-M5000"]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
require FiniteLean from "deps/finitelean-release"
lean_lib Statements where
  roots := #[`Statements]
lean_lib Main where
  roots := #[`Main]
@[default_target]
lean_lib DomainNonembedding where
  roots := #[`DomainNonembedding, `Main]

-- Comparator files remain outside the default library.
target Challenge pkg : Unit := do
  Job.async do
    proc { cmd := "python3"
           args := #["-I", (pkg.dir / "scripts/build-comparator-module.py").toString, "Challenge"]
           cwd := some pkg.dir }
target Solution pkg : Unit := do
  Job.async do
    proc { cmd := "python3"
           args := #["-I", (pkg.dir / "scripts/build-comparator-module.py").toString, "Solution"]
           cwd := some pkg.dir }

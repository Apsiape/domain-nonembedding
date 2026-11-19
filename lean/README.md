# Domain nonembedding Lean core (unchanged since paper version 1.1.0)

This package proves the nonembedding clauses of Theorems A and B of
*Group algebras that are domains but embed in no division ring* (Mghirbi–Douglas).
For every prime p, admissible marked-line data exist, and every admissible datum
gives a transparently presented group whose group algebra over every field of
characteristic p has no injective unital ring map to any division ring. The
secondary shear presentation has the same nonembedding property.

`DomainNonembedding.Main.nonembedding` and
`DomainNonembedding.Main.shear_nonembedding` prove the selected-witness headlines;
`Main.nonembedding_data` proves the all-admissible permutation form.
The all-admissible shear form is `ShearNonembedding.nonembedding_data`.
All names after the first in this paragraph have prefix `DomainNonembedding.`.
The selected witness is not asserted equal to the paper's numbered presentation.

## Reproduce

Use the Lean 4.35.0 toolchain pinned in `lean-toolchain`, with Git and Mathlib's
cache prerequisites available. From this directory run:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M5000 Audit.lean
lake env lean -j1 -M5000 -o .lake/build/lib/lean/Solution.olean Solution.lean
lake env lean -j1 -M5000 SolutionAudit.lean
```

On PowerShell set `$env:LEAN_NUM_THREADS = '1'`. The default target is the
`DomainNonembedding` library including Main. The generated manifest pins Mathlib
at `56a005855ea17e0b0958f73ec801ae140b0a1679` and its inherited dependencies.
The stock Mathlib cache tool is unchanged. No other checkout is a source dependency.
The source-preserving `deps/finitelean-release` package exposes the byte-identical
reused files in `deps/nonsofic` without that package's unrelated root release modules.
All 79 original reused files retain their recorded hashes.

Use one Lean compiler process on the entire machine at a time, at least 8 GiB
available memory, and `-j1 -M5000`. `LEAN_NUM_THREADS=1` is not a machine-wide
process lock. Check Windows tasklist and WSL `pgrep -a lean; pgrep -a lake` before compiling;
serialize dependency compilers externally as well. Allow at least 50 GB free
disk space. The root Lake package supplies `-j1 -M5000`; this Lake version has
no `lake build -j1` option. Do not edit sources during a build.

`Challenge.lean`, `Solution.lean`, `Audit.lean`, and `SolutionAudit.lean` are ordinary checking files,
outside the default library. Challenge imports only Mathlib and has exactly three
intentional holes. The development and default build have zero admissions.
The three comparator targets are data existence plus both all-admissible,
all-field nonembedding statements. Solution proves these with no named hypotheses.
`lake comparator --config comparator.json` uses this toolchain's comparator;
Linux bubblewrap must be available. The checked release sandbox disables networking and supplies no exports.
The comparator and independent replay commands are separate from the default build.

## Scope and checks

Only the nonembedding half is formalized. Hyperbolicity, diffuseness, concentration,
the domain property, finite presentability, torsion-freeness, and the shear
retraction/kernel/orderability claims are outside this core, as are Theorem D and
its corollary (added in paper version 2.0.0). The imported
`NonSofic.rankD` is left row rank; the bridge to the paper's right column rank
is proved as `DivisionRingRank.row_eq_column` / `rowRank_eq_columnRank`.
`AXIOMS.txt` records the axioms of every declaration: only `propext`,
`Classical.choice` and `Quot.sound` occur.

For version 1.1.0 the following checks passed: the default build, a full
declaration and axiom audit, the sandboxed comparator, independent kernel replay
of the exported proofs by `leanchecker` and `nanoda` with a missing-choice negative
control, release lint, and a fresh-clone build with cache retrieval. Their full
records are archived with release v1.1.0 (tag `v1.1.0` and its Zenodo record).
The Lean code is unchanged since then; version 2.0.0 removes those records and two
comment references to them from this folder.

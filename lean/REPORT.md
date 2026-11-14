# Release report — paper version 1.1.0

This core proves the nonembedding clauses of Theorems A and B of
Mghirbi–Douglas, *Group algebras that are domains but embed in no division ring*.
For every prime p, admissible data exist. EVERY admissible datum gives the
explicit permutation-glued group and the explicit shear group; over every
field K of characteristic p neither group algebra embeds into a division ring.
The all-admissible formulation includes the paper's data. The selected Lean
witness is not identified with the paper's numbered presentation.
No external mathematical hypothesis is used.

## Statements and paper correspondence

All names below have prefix `DomainNonembedding.`. Main proves the 11 frozen
propositions after their authorized conversion to Prop-valued definitions.

| Lean proof | Paper coverage |
| --- | --- |
| `Main.paperData_exists` | Lemma 3.1 and the finite two-block construction in Section 3 |
| `Main.interpolation_identity` | Interpolation identity in the proof of Lemma 3.2 |
| `Main.rank_certificate` | Lemma 3.2, the universal rank certificate |
| `Main.universal_rank_ceiling` | Proposition 4.3, including its strict numerical budget |
| `Main.line_free` | Lemma 4.2, the line-core freeness needed for the normalized line subgroup |
| `Main.central_injective` | Theorem A's vertex-injection step in Section 5 |
| `Main.copied_injective` | Theorem A's copied-vertex injection step in Section 5 |
| `Main.nonembedding_prime_data` | Theorem A(2), prime-field core, every admissible datum |
| `Main.nonembedding_data` | Theorem A(2), every characteristic-p field and every admissible datum |
| `Main.nonembedding` | Theorem A(2), a witness for each prime |
| `Main.shear_nonembedding` | Theorem B's nonembedding clause, a witness for each prime |

`Permutation.average` and `Permutation.exists_common_normalized` supply
Lemma 5.1 and its common-arrangement consequence. The all-admissible shear
form is `ShearNonembedding.nonembedding_data`.
`ShearNonembedding.shear_rank_bound` proves n ≤ 2 rank(M) from its displayed
noncommutative shear relations and nonidentity assumption. This suffices for
the quarter-budget contradiction; it does not claim Lemma 2.1's full-rank
central-eigenvalue argument or Theorem C in full.

## Proof and imported rank primitive

The dimension-103 incidence construction and finite partitions prove admissible
data exist. Extension-field interpolation is descended through a regular
representation over the prime field and matrix amplification; the target
division ring is never assumed to contain that extension field. The split
presentation gives the universal ceiling under every unital map.

Line freeness and Mathlib pushout/HNN normal forms prove the required vertex
injections for the exact presented quotient. In a faithful group-algebra map,
central entries minus 1 are distinct and nonzero, including in characteristic
two. A common permutation gives a large total rank. Diagonal normalization,
row subtraction, and one shared conjugator per line compare this with the
strict ceiling and yield the contradiction. Injective restriction of prime-field
coefficients proves the statement for every characteristic-p field.

For shear, a map from the exact presentation to an auxiliary HNN construction
proves the added s generators nonidentity. Subtracting a conjugated matrix
produces an invertible diagonal matrix and gives the half-rank lower bound,
which contradicts the same quarter-budget. No isomorphism or injection of the
whole shear group into that auxiliary construction is claimed.

The imported `NonSofic.rankD` is LEFT ROW rank from the byte-identical
FiniteLean RankD module. The paper's RIGHT COLUMN rank is related by the proved
`DivisionRingRank.row_eq_column` / `rowRank_eq_columnRank` bridge. Both primitive
and bridge are in the full axiom audit; the bridge is also an export root.
The 79 original reused files and Git blobs retain their recorded hashes.

## Historical release checks

The release form was committed as `3236d7a`. The final package source snapshot
for the fresh clone is `2fec5f6`. Subsequent report/evidence updates do not
change the mathematical proof sources or Lake integration tested there.

| Check | Result and evidence |
| --- | --- |
| Exact authorized release diff | PASS; `evidence/RELEASE-FORM.json` |
| All 11 proposition bodies | PASS, byte-identical to the frozen bodies |
| Helper types before/after | PASS, identical `#check` output |
| Construction source/import policy | PASS for all 14 project/vendored import modules; pinned Mathlib/Lean trusted; full axiom dependency audit also covers every construction declaration |
| Original freeze history | PASS historically; manifests unchanged, current comment edits recorded in PUBLIC-PACKAGING.json |
| Development/default-build admissions | PASS, 0; Challenge has 3 explicit intentional template holes outside the default target |
| Applied default build | PASS, 3657 jobs |
| Full declaration audit | PASS, 2792 declarations including generated/private helpers and imported reuse declarations, plus all 3 Solution wrappers; only propext, Classical.choice, Quot.sound |
| Mathlib-only Challenge | PASS; verbatim transparent PaperData definitions except imports; existence plus both all-admissible headline forms |
| `lake comparator` | PASS, bubblewrap, no supplied exports, network disabled; “Your solution is okay!” |
| Proof-closure export | PASS, 16 proof roots: all 11 Main proofs, 3 release targets, row/column bridge, general shear bound |
| leanchecker replay | PASS, exit 0 |
| nanoda replay | PASS, exit 0; exactly the three standard axioms permitted |
| Negative control | PASS, exit 1: removing Classical.choice gives an unpermitted-axiom rejection |
| Release lint | PASS (`python -I .../lean_release_lint.py ...`) |
| Final clean-clone cache/build/audit | PASS; all 8 commands exit 0, 3657 jobs, audit 2792 plus 3 wrapper declarations, compiled admissions 0, unchanged Git tree/manifest, temporary workspace deleted |

The session-6 proof closure has 197,288,510 bytes and SHA-256
`4a5a95d170a5aa6314f1f74635e827275a0ca52cda7ba497e8ea8ae6d366681b`.
Binary hashes, commands, exit codes, sandbox invocations, and replay logs are
recorded under evidence/session6-release/ and the retained session-6 evidence.
The final clean-clone receipt is evidence/session6-clean-clone/receipt.json.

## Public folder revalidation

This lean/ folder accompanies the paper's version 1.1.0 and is packaged from
source commit 7da3efc6504f61e0733b654e61a91a8b65d69716. Only Lean comments, public
documentation, and raw-byte packaging attributes are edited; no Lean definition,
statement, or proof changes.
The two historical freeze/release manifests and all retained receipts are
unchanged. evidence/PUBLIC-PACKAGING.json records the full public edit history.

A clean copy with no pre-existing build artifacts was tested in the new
/opt/domain-public-2026-11-13/ workspace. The following commands and comparisons
passed; raw logs and isolated-runner scripts are in evidence/public-validation/.

| Public check | Result |
| --- | --- |
| `lake exe cache get` | PASS, exit 0; 9031 cache files retrieved |
| `lake build` | PASS, exit 0; 3657 jobs |
| Full `Audit.lean` | PASS, exit 0; 2792 declarations, only the three standard axioms |
| Solution compilation and `SolutionAudit.lean` | PASS, exits 0; all 3 wrappers |
| Declaration and axiom comparison | PASS; identical to session 6, including complete audit output |
| Source census and reused files | PASS; 0 admissions outside Challenge's 3 intentional holes; 79 reused files verified |
| Sandboxed `lake comparator --config comparator.json` | PASS, exit 0; no supplied exports, network disabled |
| 16-root proof-closure export | PASS, exit 0; 197,288,510 bytes, identical SHA-256 to session 6 |
| Independent kernel checks | PASS by identical-export carryover of leanchecker, nanoda, and the missing-choice negative control |
| Release lint on a throwaway tracked copy | PASS, exit 0 |
| Clean-copy integrity | PASS; source tree and manifest unchanged during all gates |
| Resource serialization | PASS; one native Lean process at a time, -j1 -M5000, memory/disk floors enforced |
| Sandbox and workspace cleanup | PASS; no new filesystem-root entries after sandboxing, temporary WSL workspace deleted |

The identical export makes the session-6 independent replay receipts applicable
without repeating the kernel replays. The public validation comparison receipt
is evidence/public-validation/comparison.json. Final result documents and
validation receipts were added after testing; all retained Lean/build inputs
match the clean tested copy. The first sandbox-wrapper attempt is retained
beside the successful retry in the public validation logs.

## Scope

NOT formalized: hyperbolicity, diffuseness, concentration, the domain property,
finite presentability, torsion-freeness, the shear retraction and free-product
kernel description, bi-orderability/left-orderability, characteristic zero,
or the full general attachment principle (Theorem C). See `SCOPE.md`.
The paper's complete geometric/domain headline is not claimed formalized.

Two fields of `evidence/STATEMENT-FREEZE.json` (`verdict_file`, `freeze_record`) name paths in the
authors' private working records. Those records are not part of this release; the receipt is kept byte-identical
because its hashes are the freeze record.

# Proof blueprint

Source: Douglas--Mghirbi, *Group algebras that are domains but embed in no
division ring*, 12 November 2026, paper/main.tex and sections in the read-only
source repository. Labels below are the source LaTeX labels.

## Exact target and representation

PaperData.lean defines finite marked-line data, its split triangle
presentation, and the permutation graph-of-groups presentation explicitly;
Statements.lean states the targets.
Gamma is a PresentedGroup quotient of a FreeGroup, with one central generator
per (line,entry), copied base generators, and one stable letter per edge.
For a distinguished line i*, all t_(pi,i*) are killed. Every other edge uses
ONE stable letter for its entire array. No direct simultaneous amalgamation
that accidentally kills graph cycles is substituted.

The authors accepted the all-admissible-data formulation.
Every admissible datum, including the paper's, is a nonembedding target, and
admissible data must exist for every prime. A witness is selected only for the
headline corollary. No equality to the paper's numbered presentation is claimed.
No lexicographically first selector or first-tree convention is required.
The transparent definitions are now in DomainNonembedding/PaperData.lean;
Statements.lean imports them. An independent blind fidelity read found the
formulation faithful. The original freeze is recorded in
evidence/STATEMENT-FREEZE.json; the applied release form is in
evidence/RELEASE-FORM.json and public comment edits in evidence/PUBLIC-PACKAGING.json.

The scalar field is packaged with a numbering equivalence to Fin(p^a), not
assumed to sit inside a target division ring. S is the initial numbered segment,
so distinct extension-field elements are never confused with integer residues.

## Nodes

| ID | Status | Lean node / source | Dependencies | Estimate |
| --- | --- | --- | --- | --- |
| R0 | REUSE (CHECKED) | NonSofic.rankD and its Sylvester rank inequalities | vendored Sylvester.lean, mathlib | copied, working/blob hashes verified, built |
| R1 | ADAPT (PROVED) | DivisionRingRank.row_eq_column; rowRank_eq_columnRank (Statements.lean) | R0; row-space factorization and opposite ring | done |
| P0 | NEW (PROVED) | Permutation.bad_border_corner_unique for arbitrary singular old squares | R0, row-space projection | done |
| P1 | NEW (PROVED) | Permutation.leading_bad_corner_unique, exposed_unused, leading_bad_count; swap injection | finite permutations, P0 | done |
| P2 | NEW (PROVED) | Permutation.average_integer and average, public permutation_average | P1, monotone rank increments | done |
| P3 | NEW (PROVED) | Permutation.exists_common_normalized: common permutation bound card(I)(n+1)/2 | P2, sum interchange and attainment | done |
| I0 | NEW (PROVED) | FiniteFieldData.exists_large_power, number, grid_card | Mathlib GaloisField, finite equivalences | done |
| I1 | ADAPT (PROVED) | Incidence.retained_girth, mean_grid_lower, large_field_outcome; exists_markedLines (d=103, g=100) | I0; generic OAI finite expectations/cycle encoding | done |
| I2 | REUSE/NEW (PROVED) | MarkedLines.partition; Construction.exists_withBlocks / paperData_exists | I1; generic exists_two_cartesian_blocks | done; protected wrapper unchanged |
| C0 | REUSE/ADAPT (PROVED) | Interpolation.degree_cutoff / interpolation_identity, from arbitrary-finite-field grid_line_certificate | I0; Admissible marks/directions | done; protected wrapper unchanged |
| C1 | NEW (PROVED) | MatrixDescent.exists_regular_representation: prime-field basis, actual matrix-ring map, scalar commutation | Mathlib Algebra.leftMulMatrix | done |
| C2 | NEW (PROVED) | MatrixDescent.flatten_mul, rank_amplification, certificate_identity, rank_certificate_of_rep / rank_certificate | R0,C0,C1 | done; protected wrapper unchanged |
| G0 | NEW (CHECKED) | Protected split generators/tree/words; LocalRank.triangle_relation | I2; transparent definitions | algebra done; split link interfaces in G1 |
| G1 | ADAPT (PROVED) | CollapsedLines: actual block schemes, 101-edge link separation, dipole-free filling contradiction, auxiliary lineSubgroup_free | G0,I1; generic OAI ShiftScheme/fillings, NonSofic word proof | done |
| G2 | ADAPT (PROVED) | LineFree.line_free: map from frozen split quotient, checked tree relations, retraction onto the (r-1)^2 normalized words | G1; NonSofic.LineFreeWord.exists_core | done |
| C3 | ADAPT (PROVED) | LocalRank.block_rank_le_one, point_rank_bound, rank_budget, universal_rank_ceiling | G0,C2,I2 | done; protected wrapper unchanged |
| H0 | ADAPT (PROVED) | GraphNormalForms.central_injective / copied_injective: distinguished-edge wide pushout, finite successive HNN extensions, map from exact frozen quotient | G2; REUSE Monoid.PushoutI.of_injective and HNNExtension.of_injective | done |
| H1 | NEW (PROVED) | Headline.entries_injective / entries_ne_zero, via central and group-algebra injections, including char 2 | H0 | done |
| H2 | NEW (PROVED) | Headline.normalized_difference_rank_le / copied_line_rank: diagonal normalization, zero-row subtraction, exact shared conjugator | R0,G0,H0 | done |
| T0 | NEW (PROVED) | Headline.nonembedding_prime_data: common arrangement contradicts every copied universal ceiling | P3,C3,H1,H2 | done |
| T1 | NEW (PROVED) | Headline.coefficient_injective / nonembedding_data / nonembedding with proved existence certificate | T0, MonoidAlgebra coefficient map | done |

All permutation-core nodes H1/H2/T0/T1 are proved, and so is the secondary
shear branch. All 11 frozen targets have audited replacements. There are 31
new proof theorems, all audited with standard axioms only. The default
public clean-copy build passes (3657 jobs).

All 11 proposition bodies are preserved by the applied release form.
Main.lean proves each obligation. The development admission census is zero;
Challenge.lean has three intentional comparator holes outside the default build.

## Reuse audit

The whole permitted source package is preserved byte-for-byte under deps/nonsofic;
evidence/nonsofic-sha256.json records every copied file. The source-preserving deps/finitelean-release facade exposes the imported
closure locally without the unrelated root release modules. There are no
outside-repository package dependencies beyond the pinned mathlib Git package.

NonSofic.rankD is LEFT ROW rank, finrank of range(vecMulLinear). The new paper
states RIGHT COLUMN rank. Their agreement over every division ring is now proved explicitly in R1,
via row-space basis factorization and the opposite ring. The target uses the
reused rank together with that checked bridge. Never use Matrix.rank as a
substitute requiring commutativity.

NonSofic.collapse and collapse_groupRing fix dimension 20 and q prime, with a
central map ZMod q -> R. They do not prove the extension-field descent.
NonSofic.linnell obstructs Linnell/Hughes-free conditions, not arbitrary faithful
embeddings, and cannot stand in for the new conclusion.
NonSofic.LineFree.lineSubgroup_free has r^2-1 unsplit generators
x_uv x_00^-1. The new split complex uses (r-1)^2 generators
x_u0^-1 x_uv x_0v^-1 x_00. Its freeness must be re-proved.

## Hypothesis policy

Hypotheses.lean admits no external theorem assumptions. Every source-paper
lemma above is proved. Pinned Mathlib supplies indexed group pushouts with
normal form and HNN extensions; the proof iterates these over the explicit
quotient presentations. No additional normal-form assumption is used.

## Shear branch (PROVED)

ShearNormalForms uses BaseGroup x Multiplicative Z and the two injective edge
maps (w,z) -> (lineHom_i(w),z) and (w,z) -> (lineHom_i(w),degree(w)*z).
GraphNormalForms.exists_conjugators supplies all HNN letters and preserves the
nonidentity common s. A map out of the exact frozen shear quotient checks every
relator, proving each s_i nonidentity. No global shear injection is needed.

ShearNonembedding.shear_rank_bound proves the general algebraic forcing:
conjugation minus the matrix is an invertible diagonal, so n <= 2 rank(M).
Normalization, the universal ceiling and coefficient restriction give the
all-admissible all-field shear theorem and selected shear_nonembedding.
Division-closure or eigenvalue-independence nodes were unnecessary for this
rank inequality. Geometry, orderability and domainhood remain out of scope.

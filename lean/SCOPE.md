# Scope

The nonembedding clauses of Theorem A and Theorem B of Mghirbi–Douglas,
*Group algebras that are domains but embed in no division ring*, are proved:
for every prime p, admissible marked-line data exist; EVERY admissible datum,
including the paper's, gives an explicit permutation-glued presentation and an
explicit shear presentation whose group algebras over every characteristic-p
field admit no injective unital ring homomorphism to any division ring.
No equality between a selected witness and the paper's numbered presentation
is asserted. The authors accepted this formulation; an independent blind fidelity read found it faithful.

The proof includes dimension-103 incidence data and two-block partitions,
extension-field interpolation, matrix-ring descent without assuming an embedding
of that field in the target, a universal rank ceiling, noncommutative permutation
averaging, line freeness and graph vertex injections, faithful entries, exact
shared-conjugator normalization, the contradiction, and prime-field coefficient
restriction. Our results are proved, not named hypotheses. Hypotheses.lean is empty
of admitted inputs. Only propext, Classical.choice, and Quot.sound are permitted.

The reused `NonSofic.rankD` primitive is left row rank, from the byte-identical
FiniteLean RankD module. The paper uses right column rank. The bridge is proved
in `DomainNonembedding.DivisionRingRank.row_eq_column` and exported by
`DomainNonembedding.rowRank_eq_columnRank`. Both are included in the axiom audit;
the bridge is also a proof-export root. The imported rank primitive is not an
unchecked new assumption.

The shear proof proves nonidentity of the added s generators through a map from
the exact presentation to an auxiliary HNN construction. No identification or
injection of the whole shear group into that auxiliary group is asserted.
`ShearNonembedding.shear_rank_bound` proves the general bound n ≤ 2 rank(M)
under its displayed shear relations and nonidentity condition. This suffices
for the strict quarter-budget contradiction. It does not formalize Lemma 2.1's
full-rank/central-eigenvalue argument or Theorem C in full.

NOT formalized: hyperbolicity, diffuseness, concentration, the domain property,
finite presentability, torsion-freeness, the shear retraction and free-product
kernel description, bi-orderability/left-orderability, or characteristic zero.
The paper's full headline, including its domain and geometric assertions, is
not claimed as a formalized theorem here.

This public lean/ folder accompanies paper version 1.1.0.
The exact authorized release form is applied. All 11 target proposition bodies
are byte-identical to the freeze; the two helper types are unchanged. The original
freeze manifest and RELEASE-FORM.json remain historical and unchanged.
Comment-only public edits and current file hashes are recorded in
evidence/PUBLIC-PACKAGING.json. The development census is 0. Challenge's three
intentional template holes are excluded from that census and the default build.

The public clean-copy build, full audit, Solution audit, sandboxed comparator,
and export comparison pass. All 2792 audited declarations and their axiom records
match session 6; the three Solution wrappers use only the standard axioms. These
checks do not extend the mathematical scope listed above. See REPORT.md and
evidence/public-validation/comparison.json.

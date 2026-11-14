# Checked proof notes

The headline and secondary shear nonembedding theorems are now proved.
All completed nodes below have standard axioms only. See the axiom audits.

## Arbitrary singular borders

Permutation.bad_border_corner_unique works for every old square T, including
singular T and the empty square. Let W be the left row space of [T u].
Projection to the old coordinates maps W onto the row space of T. If bordering
with corner z does not increase rank, W equals the new row space and has the
same dimension as its projected image, so the projection is injective on W.
The two last rows for bad corners z and w lie in W and have equal projections;
therefore z=w. No determinant or invertibility of T is assumed.

The separate LDU/Schur leaves in Permutation.lean also compile, but the full
average uses the arbitrary-singular-border theorem.

## Exposure and integer aggregation

PermutationAverage.lean defines Initial n k, leading, leadingRank and exposed.
The exposed set is the leading (k+1)-square minus its corner. Its complement
has cardinal unusedCount n (k+1) = n^2 - ((k+1)^2 - 1).
The explicit initialStep equivalence identifies the next square with a border.

Equal exposed arrangements and two bad rank increments imply equal old corner
values by the border theorem and injectivity of b. The injection
  (bad pi, unused a) -> pi composed with swap(corner,a)
then bounds the bad count by the reciprocal unused count. At stages
k=0,...,n-2 that count is at least 2n. The rank sequence is monotone and starts
at zero, so integer increments telescope. average_integer proves
  (n-1)(2n-1) #Perm <= 2n sum_pi rank(B_pi).
Casting to rationals proves average, the strong bound in the paper.
The implementation only needs distinctness; the public wrapper retains the
paper's additional nonzero premise. No success-history event is assumed.

exists_common_normalized combines the weaker half-bound with finite-sum
linearity and attainment: one common permutation satisfies
  card(I)(n+1)/2 <= sum_i (1 + rank(B_i_pi)).
No independence between the line arrays is asserted.

## Row/column bridge

DivisionRingRank.exists_rank_factorization writes M=A B through a basis of
its left row space of dimension rankD M. Opposite transpose reverses the
product, so its left row rank is at most rankD M. Repeat in the opposite
ring and identify the double opposite via a ring equivalence. Semilinear
transport preserves dimension. row_eq_column, and its public wrapper
rowRank_eq_columnRank, are proved for all rectangular finite matrices.

## Dimension 103 incidence and two blocks (I1/I2)

Incidence.lean adapts the generic OAI alteration to half-cycle lengths 2..50.
Actual simple cycles are encoded by the reused bipartite cycle normal form;
every mark on every occurring encoded short cycle is deleted. The retained
incidence graph has egirth greater than 100. Deletion changes no degree outside
the union of the discarded geometric lines.

IncidenceBounds.lean proves the projective-direction estimates Q^102 <= J <=
2 Q^102, the numbered grid's lower bound, and mean >= Q/(4*2060^103).
The expected deleted-label count is at most 2450 Q^100. The finite cost

    4 r L + r(4Q+1) D

has expectation at most Q^103 at the paper's Q threshold. An outcome with cost
less than Q^103+1 has integer cost at most Q^103. alteration_arith then proves
2 r |E| <= Q^103, Q^103 <= 2*2060^103*N, and the strict rank budget.
This is a simultaneous finite existence proof; no probabilistic hypothesis is
added to PaperData. The estimates are stronger than the needed E budget.

MarkedLines.lean transports the retained labels to Fin N and proves the exact
puncturing equivalence used by PaperData. DataConstruction.lean uses the
already-general exists_two_cartesian_blocks result, numbers Regular x Bool,
and proves the coverage, disjointness and exact two-block uniqueness clauses.
Construction.paperData_exists has exactly the protected existence target type.
The finite-field numbering is arbitrary, as accepted by the authors; no canonical witness
or equality to the paper's numbered presentation is claimed.

## Interpolation (C0)

The vendored grid_line_certificate is already general over arbitrary finite
fields and arbitrary finite coordinate types. Interpolation.lean proves the
paper's degree cutoff from the numbered grid cardinality and identifies its
lineIncidence and gridLagrange with the protected definitions. This yields
Interpolation.interpolation_identity for every admissible datum. No scalar
field in a target division ring is assumed.

## Matrix-ring descent (C1/C2)

RegularRepresentation.lean proves that every finite field K of characteristic
p has a ring map into M_n(D), for a positive n, commuting with every scalar yI.
It derives primality of p from finite K, chooses a prime-field basis, uses
Algebra.leftMulMatrix, and maps its F_p entries into D. The dimension used is
n=finrank(F_p,K); its equality with the supplied exponent is unnecessary for
rank cancellation. Coefficients commute with y because prime-field elements
are natural casts. No extension-field embedding in D enters the proof.

MatrixAmplification.lean flattens blocks via Matrix.comp, respects rectangular
multiplication/sums/negation, and proves exact block-diagonal rank. Flattening
a matrix with scalar identity entries produces a block diagonal of n copies,
so its rank is n times the original rank.

RankCertificate.lean proves the certificate identity with commutation only
against the displayed Y entries. This property holds for the represented field
and scalar matrices from D. Factorization bounds each flattened weighted term
by the amplified local rank. Subadditivity, block-diagonal additivity and
cancellation of positive n prove MatrixDescent.rank_certificate with exactly
the protected target's hypotheses, including no Fact p.Prime parameter.

## Local algebra and the ceiling (G0/C3)

LocalRank.triangle_relation is a consequence of the actual protected relator,
not a group embedding assumption. A block sum factors as a column times a row
by reindexing along the shifted Cartesian coordinate bijection. Its rank is at
most one. A regular point has two such blocks, hence local rank at most two;
exceptional local rank is at most r. Summing gives the exact

    2*(Q^103 - |E|) + r*|E|

ceiling. The two Admissible cardinality budgets imply the strict numerical
inequality. Under an arbitrary unital group-algebra map, the coefficient field
maps injectively to the division ring, establishing CharP D p. Applying the
proved rank certificate gives LocalRank.universal_rank_ceiling, with the exact
protected target type. Line/vertex freeness is not needed for this upper bound.

## Split line freeness (G1/G2)

CollapsedLines.lean builds an auxiliary three-vertex BlockPresentation from
the frozen blocks. Its two ShiftSchemes use the admissible two-block partition;
block_unique follows from disjointness and the exact two-block clause. The
egirth condition gives length at least 101 for cycles and for internally
reduced link paths between distinct same-label germs.

Generic OAI filling, dipole-removal and ribbon-curvature arguments rule out
nonempty cyclically reduced x-words. The preserved
NonSofic.LineFreeWord.exists_core supplies their cyclic cores. This proves
freeness of the auxiliary r^2-1 generators x_uv*x_00^-1 over the actual
extension field. It does not invoke the old dimension-20 freeness theorem.

LineFree.lean maps the exact frozen split quotient to the auxiliary group
using explicit endpoint paths:

    P_V(u) = x_i*00 * x_i*u0^-1,
    P_W(v) = x_i*0v,
    P_O(b) = L_b00^-1.

An edge maps to P_source * edge * P_target^-1. edgeImage_relators checks every
triangle and every frozen spanning-tree relator. No geometric assertion about
identifying vertices is assumed. A normalized word maps to its auxiliary
normalized word, conjugated at W_0.

In the free auxiliary y_uv basis, the interior words
y_u0^-1*y_uv*y_0v^-1 are independent: retractLetter kills the zero row and
column and sends each interior generator to its shifted pair. Its lift is a
left inverse to normalizedBasis. Combining this retraction with auxiliary
line freeness proves LineFree.line_free with exactly the frozen target type.

## Graph injections (H0)

GraphNormalForms.lean forms a wide Monoid.PushoutI indexed by Option Arrangement.
The none factor is central; some pi is the copied base group. The common group
is FreeGroup Entry. Its central map is the distinguished-line inclusion; its
pi map is lineHom i* composed with FreeGroup.map pi.symm. All are proved
injective using LineFree.line_free. Mathlib's of_injective embeds every factor.
The relation evaluated on of(pi q) is the frozen distinguished-edge relation.

exists_conjugators inducts over a finite set of non-tree edges. The ranges of
the two injective edge maps are isomorphic via MonoidHom.ofInjective. One
HNNExtension stable letter conjugates the whole edge group; of_injective
preserves the prior embedding. Previous stable letters and relations pass
through that embedding. There is one letter per (pi,i), not one per entry.

generatorImage maps the exact frozen Gamma quotient to the resulting group.
generatorImage_relators checks copied base relations, every gluing word, and
distinguished stable letters. Composing with centralHom/copiedHom gives the
already injective factor maps. This proves GraphNormalForms.central_injective
and copied_injective. An isomorphism with the auxiliary construction is not
needed or claimed; the map out of the exact quotient suffices for injections.

## Faithful entries and exact normalization (H1/H2)

Headline.groupMap_injective composes the injectivity of the ring map with
MonoidAlgebra.of_injective. Central vertex injectivity and the FreeGroup basis
then make each central array q -> chi(c_iq)-1 injective and nonzero. These are
additive cancellation arguments, so characteristic two causes no exception.

For group-valued X, left/right diagonal multiplication gives the normalized
array N_uv=chi(X_u0^-1 X_uv X_0v^-1 X_00), with rank(N)<=rank(Y). Its zero row
is 1. A rectangular row-difference matrix subtracts row zero, and an interior
submatrix has entries N_uv-1. Thus normalized_difference_rank_le proves
rank(e-1)<=rank(Y), including noncommutative order of every factor.

The frozen gluingWord supplies one common stable letter for the entire line
array. Conjugating all entries, including the constant 1, is again left/right
diagonal multiplication. gluing_relation and copied_line_rank connect the
permuted central e-1 array to each actual copied line matrix. No unproved graph
identity or assumption about separate conjugators enters.

## Prime-field and all-field contradiction (T0/T1)

Permutation.exists_common_normalized supplies one arrangement pi with
N*r/2 <= N + sum_i rank(e_i,pi-1). Each rank is at most the corresponding
copied line rank. The copied ring map is the original map composed with
MonoidAlgebra.mapDomainRingHom of copiedHom. LocalRank.universal_rank_ceiling
bounds the sum by B and proves 4B<Nr. Since r>=4 these inequalities contradict.

Headline.nonembedding_prime_data and nonembedding_data have the exact frozen
all-admissible target types. The coefficient map F_p[Gamma] -> K[Gamma] is
MonoidAlgebra.mapRingHom of ZMod.castHom; injectivity is proved pointwise by
the coefficient-map API and injectivity of the field map. It makes no assumption
on the size of K or on embedding the extension field into D.

Headline.paperData chooses the proved Construction.paperData_exists witness.
Headline.nonembedding then covers every prime and every characteristic-p field
with no unfinished existence dependency. Main.lean checks the frozen selected-witness target; no equality
with the paper's numbered presentation is claimed.

## Shear normal forms and general rank forcing

ShearNormalForms uses G=BaseGroup x Multiplicative Z and
H=FreeGroup Entry x Multiplicative Z. degree sends a diagonal free generator
to ofAdd(1), and an off-diagonal generator to 1. The two edge maps are

    a_i(w,z) = (lineHom_i(w),z),
    b_i(w,z) = (lineHom_i(w),degree(w)*z).

Both are injective by proved line freeness. The finite HNN construction gives
one whole-edge conjugator per line and preserves G. The image of every s_i
is the same s=(1,ofAdd 1), which remains nonidentity. The map from the exact
frozen shear quotient checks copied base relations, commutation with the
letters, commutation with every line generator, and every shear relation.
Using a common image for all s_i is sufficient to prove their nonidentity;
no injection of the whole shear group is asserted.

ShearNonembedding.shear_rank_bound is general over any group map chi into a
division ring and any array x with

    t*x_uv*t^-1 = s^(if u=v then 1 else 0)*x_uv,
    chi(s) != 1.

Conjugating the matrix and subtracting the original gives

    diag((chi(s)-1)*chi(x_uu)).

Each diagonal entry is nonzero: chi(s)-1 is nonzero and a group image is a
unit. An explicit diagonal inverse proves full diagonal rank. Conjugation
cannot increase rank, and rank subadditivity gives n<=2 rank(M).
No coefficient centrality or division-closure hypothesis is used.

For the frozen shear group, normalize the actual base line and restrict to
its interior; this cannot increase rank(Y_i). The shear relation forces
r-1<=2 rank(Y_i). Summing and using the same universal prime-field ceiling
contradicts 4B<Nr. The prime coefficient map into any K supplies the ceiling.
ShearNonembedding.nonembedding_data covers every admissible datum and every
characteristic-p field; shear_nonembedding uses the proved selected witness.

## Checked wrappers and release boundary

Main.lean proves all 11 frozen proposition bodies in the applied release form.
The full declaration audit includes generated/private helpers and imported reuse
declarations. The three Solution wrappers are audited separately. Only propext,
Classical.choice, and Quot.sound are permitted. The development admission census
is zero; Challenge.lean retains three intentional comparator holes outside the
default build. See REPORT.md and evidence/RELEASE-FORM.json.

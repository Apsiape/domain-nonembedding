import DomainNonembedding.PaperData
import DomainNonembedding.DataConstruction
import DomainNonembedding.PermutationAverage

set_option autoImplicit false

/-!
Statements frozen in November 2026 after an independent blind fidelity read.
The transparent data and presentations
are in DomainNonembedding/PaperData.lean. Every admissible datum, including the
paper's, is a nonembedding target; no equality to its numbered presentation is claimed.
-/

namespace DomainNonembedding
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Incidence construction and finite block partition are OUR obligations. -/
def paperData_exists (p : ℕ) [Fact p.Prime] : Prop :=
    ∃ d : PaperData p, d.Admissible

noncomputable def paperData (p : ℕ) [Fact p.Prime] : PaperData p :=
  Classical.choose (Construction.paperData_exists p)

theorem paperData_admissible (p : ℕ) [Fact p.Prime] : (paperData p).Admissible :=
  Classical.choose_spec (Construction.paperData_exists p)

abbrev Gamma (p : ℕ) [Fact p.Prime] := (paperData p).Gamma
abbrev Lambda (p : ℕ) [Fact p.Prime] := (paperData p).Shear

/-- Strong form of the paper's noncommutative permutation lemma. -/
theorem permutation_average {D : Type*} [DivisionRing D] (n : ℕ) (hn : 2 ≤ n)
    (b : Fin n × Fin n → D) (hb : Function.Injective b) (hb₀ : ∀ q, b q ≠ 0) :
    ((n - 1 : ℕ) : ℚ) * (1 - 1 / (2 * (n : ℚ))) ≤
      (∑ π : Equiv.Perm (Fin n × Fin n),
        (NonSofic.rankD (fun u v => b (π (u, v))) : ℚ)) /
      Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
  exact Permutation.average n hn b hb

/-- Right column rank, encoded as left row rank over the opposite division ring. -/
noncomputable def columnRank {D : Type*} [DivisionRing D] {m n : Type*} [Fintype n]
    (M : Matrix m n D) : ℕ :=
  NonSofic.rankD (M.transpose.map MulOpposite.op)

theorem rowRank_eq_columnRank {D : Type*} [DivisionRing D] {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n D) :
    NonSofic.rankD M = columnRank M := by
  exact DivisionRingRank.row_eq_column M

/-- Extension-field identity before descent to matrices over a division ring. -/
def interpolation_identity {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    (i j k : d.Label) : Prop :=
    (∑ z ∈ Finset.univ.filter (fun z => d.Incident z i), d.lagrange j z * d.lagrange k z) =
      if j = i ∧ k = i then -1 else 0

/-- Universal certificate: D is NOT assumed to contain d.Scalar. -/
def rank_certificate {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    {D : Type*} [DivisionRing D] [CharP D p] (r : ℕ)
    (Y : d.Label → Matrix (Fin r) (Fin r) D) : Prop :=
    ∑ i, NonSofic.rankD (Y i) ≤
      ∑ z : d.Point, NonSofic.rankD (∑ i ∈ d.incidences z, Y i)

def line_free {p : ℕ} (d : PaperData p) (hd : d.Admissible) (i : d.Label) : Prop :=
    Function.Injective (d.lineHom i)

/-- Under EVERY unital map, without injectivity or extra independence. -/
def universal_rank_ceiling {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) {D : Type*} [DivisionRing D]
    (φ : MonoidAlgebra (ZMod p) d.BaseGroup →+* D) : Prop :=
    (∑ i, NonSofic.rankD (d.lineMatrix ((φ : _ →* D).comp
      (MonoidAlgebra.of (ZMod p) d.BaseGroup)) i)) ≤
        2 * ((p ^ d.exponent) ^ dimension - d.exceptional.card) + rankSize * d.exceptional.card ∧
    4 * (2 * ((p ^ d.exponent) ^ dimension - d.exceptional.card) +
      rankSize * d.exceptional.card) < d.lineCount * rankSize

def central_injective {p : ℕ} (d : PaperData p) (hd : d.Admissible) : Prop :=
    Function.Injective d.centralHom

def copied_injective {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    (π : PaperData.Arrangement) : Prop := Function.Injective (d.copiedHom π)

/-- Prime-field core, for every admissible realization of the paper's data. -/
def nonembedding_prime_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) {D : Type*} [DivisionRing D]
    (φ : MonoidAlgebra (ZMod p) d.Gamma →+* D) : Prop := ¬ Function.Injective φ

/-- All-field form for every admissible datum, including the paper's.
No equality to the paper's numbered presentation is asserted. -/
def nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Gamma →+* D) : Prop :=
    ¬ Function.Injective φ

/-- Headline core: all fields of characteristic p, arbitrary division ring target. -/
def nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Gamma p) →+* D) : Prop :=
    ¬ Function.Injective φ

/-- Secondary branch: the paper's explicit retractive shear group. -/
def shear_nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Lambda p) →+* D) : Prop :=
    ¬ Function.Injective φ

end DomainNonembedding

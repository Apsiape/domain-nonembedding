import DomainNonembedding.MatrixAmplification
import DomainNonembedding.RegularRepresentation

set_option autoImplicit false

/-!
Matrix-ring descent. The algebraic certificate calculation adapts the
byte-identical NonSofic/RankCertificate source (Apache-2.0). Centrality is
required only against the displayed matrices and is proved by the regular
representation, rather than postulating an extension field inside the target.
-/

namespace DomainNonembedding.MatrixDescent
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Identity
variable {K R : Type*} [Field K] [Ring R]

/-- `H(z) ⊗ Z` for `H(z) = f(z) f(z)ᵀ` (block index second). -/
def weighted (c : K →+* R) {I : Type*} {r : ℕ} (f : I → K)
    (Z : Matrix (Fin r) (Fin r) R) : Matrix (Fin r × I) (Fin r × I) R :=
  Matrix.of fun x y => c (f x.2) * Z x.1 y.1 * c (f y.2)

/-- `f ⊗ I_r`. -/
def weightLeft (c : K →+* R) {I : Type*} {r : ℕ} (f : I → K) :
    Matrix (Fin r × I) (Fin r) R :=
  Matrix.of fun x a' => if x.1 = a' then c (f x.2) else 0

/-- `fᵀ ⊗ I_r`. -/
def weightRight (c : K →+* R) {I : Type*} {r : ℕ} (f : I → K) :
    Matrix (Fin r) (Fin r × I) R :=
  Matrix.of fun b' y => if b' = y.1 then c (f y.2) else 0

/-- `H(z) ⊗ Z = (f ⊗ I) Z (fᵀ ⊗ I)`. -/
theorem weighted_eq (c : K →+* R) {I : Type*} [Fintype I] {r : ℕ} (f : I → K)
    (Z : Matrix (Fin r) (Fin r) R) :
    weighted c f Z = weightLeft c f * Z * weightRight c f := by
  ext ⟨a, j⟩ ⟨b, k⟩
  simp [weighted, weightLeft, weightRight, Matrix.mul_apply, ite_mul, mul_ite]

/-- **The certificate identity over `R`**: `∑_z H(z) ⊗ Z(z) = -⊕_i Y_i`. -/
theorem certificate_identity (c : K →+* R) {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] {r : ℕ} (inc : P → Finset I) (f : P → I → K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (Y : I → Matrix (Fin r) (Fin r) R)
    (hcomm : ∀ (x : K) i u v, Y i u v * c x = c x * Y i u v) :
    (∑ z, weighted c (f z) (∑ i ∈ inc z, Y i)) = -Matrix.blockDiagonal Y := by
  have hZ (z : P) (u v : Fin r) (x : K) :
      (∑ i ∈ inc z, Y i) u v * c x = c x * (∑ i ∈ inc z, Y i) u v := by
    simp only [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hcomm x i u v)
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [Matrix.sum_apply, Matrix.neg_apply, Matrix.blockDiagonal_apply']
  simp only [weighted, Matrix.of_apply]
  calc ∑ z, c (f z j) * (∑ i ∈ inc z, Y i) a b * c (f z k)
      = ∑ z, ∑ i, (if i ∈ inc z then c (f z j * f z k) else 0) * Y i a b := by
        apply Finset.sum_congr rfl
        intro z _
        rw [mul_assoc, hZ z a b, ← mul_assoc, ← map_mul c, Matrix.sum_apply,
          Finset.mul_sum]
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i, (∑ z, if i ∈ inc z then c (f z j * f z k) else 0) * Y i a b := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = ∑ i, (if j = i ∧ k = i then -Y i a b else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have hc : (∑ z, if i ∈ inc z then c (f z j * f z k) else 0) =
            c (-(if j = i ∧ k = i then 1 else 0)) := by
          rw [← hline i j k, map_sum]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> simp
        rw [hc]
        split_ifs <;> simp
    _ = -(if j = k then Y j a b else 0) := by
        by_cases hjk : j = k
        · subst hjk
          simp
        · rw [if_neg hjk]
          simp only [neg_zero]
          exact Finset.sum_eq_zero (fun i _ => if_neg (fun h => hjk (h.1.trans h.2.symm)))


end Identity

/-- Descent cancels the positive amplification dimension in an integer rank bound. -/
theorem rank_certificate_of_rep {K D P I : Type*} [Field K] [DivisionRing D]
    [Fintype P] [Fintype I] [DecidableEq I] (a : ℕ) (ha : 0 < a)
    (c : K →+* Matrix (Fin a) (Fin a) D)
    (hcomm : ∀ (x : K) (y : D), c x * Matrix.scalar (Fin a) y =
      Matrix.scalar (Fin a) y * c x)
    (inc : P → Finset I) (f : P → I → K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j*f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0))
    (r : ℕ) (Y : I → Matrix (Fin r) (Fin r) D) :
    ∑ i, NonSofic.rankD (Y i) ≤ ∑ z, NonSofic.rankD (∑ i ∈ inc z, Y i) := by
  let δ := Matrix.scalar (Fin a) (α := D)
  let Y' := fun i => (Y i).map δ
  let Z := fun z => ∑ i ∈ inc z, Y i
  have hc : ∀ (x : K) i u v, Y' i u v*c x = c x*Y' i u v := by
    intro x i u v
    exact (hcomm x (Y i u v)).symm
  have hid := certificate_identity c inc f hline Y' hc
  have hbd : Matrix.blockDiagonal Y' = (Matrix.blockDiagonal Y).map δ := by
    ext ⟨u, i⟩ ⟨v, j⟩
    by_cases hij : i = j <;> simp [Y', Matrix.blockDiagonal_apply, hij]
  have hZ (z : P) : (∑ i ∈ inc z, Y' i) = (Z z).map δ := by
    ext u v
    simp [Y', Z, Matrix.sum_apply, map_sum]
  have hz (z : P) : NonSofic.rankD (flatten a (weighted c (f z) (∑ i ∈ inc z, Y' i))) ≤
      a*NonSofic.rankD (Z z) := by
    rw [weighted_eq, flatten_mul, flatten_mul]
    calc
      _ ≤ NonSofic.rankD (flatten a (weightLeft c (f z)) * flatten a (∑ i ∈ inc z, Y' i)) :=
        NonSofic.rankD_mul_le_left _ _
      _ ≤ NonSofic.rankD (flatten a (∑ i ∈ inc z, Y' i)) := NonSofic.rankD_mul_le_right _ _
      _ = a*NonSofic.rankD (Z z) := by rw [hZ, rank_amplification]
  have hbd' : Matrix.blockDiagonal Y' = -(∑ z, weighted c (f z) (∑ i ∈ inc z, Y' i)) := by
    rw [hid, neg_neg]
  have hnat : a*(∑ i, NonSofic.rankD (Y i)) ≤ a*(∑ z, NonSofic.rankD (Z z)) := by
    calc
      _ = NonSofic.rankD (flatten a (Matrix.blockDiagonal Y')) := by
        rw [hbd, rank_amplification, rank_blockDiagonal]
      _ = NonSofic.rankD (flatten a (-(∑ z, weighted c (f z) (∑ i ∈ inc z, Y' i)))) := by
        rw [hbd']
      _ = NonSofic.rankD (∑ z, flatten a (weighted c (f z) (∑ i ∈ inc z, Y' i))) := by
        rw [flatten_neg, rank_neg, flatten_sum]
      _ ≤ ∑ z, NonSofic.rankD (flatten a (weighted c (f z) (∑ i ∈ inc z, Y' i))) :=
        rank_sum_le _ _
      _ ≤ ∑ z, a*NonSofic.rankD (Z z) := Finset.sum_le_sum (fun z _ => hz z)
      _ = _ := by rw [Finset.mul_sum]
  by_contra h
  have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) ha
  exact (not_lt_of_ge hnat) hlt

/-- The protected rank-certificate target, without an extension-field assumption on `D`. -/
theorem rank_certificate {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    {D : Type*} [DivisionRing D] [CharP D p] (r : ℕ)
    (Y : d.Label → Matrix (Fin r) (Fin r) D) :
    ∑ i, NonSofic.rankD (Y i) ≤
      ∑ z : d.Point, NonSofic.rankD (∑ i ∈ d.incidences z, Y i) := by
  obtain ⟨a, ha, c, hc⟩ := exists_regular_representation (K := d.Scalar) (D := D) (p := p)
  refine rank_certificate_of_rep a ha c hc d.incidences (fun z i => d.lagrange i z) ?_ r Y
  intro i j k
  have h := Interpolation.interpolation_identity d hd i j k
  simp only [Finset.sum_filter] at h
  have hh : (∑ z : d.Point, if i ∈ d.incidences z then
      d.lagrange j z*d.lagrange k z else 0) = if j = i ∧ k = i then -1 else 0 := by
    simpa only [PaperData.incidences, Finset.mem_filter, Finset.mem_univ, true_and] using h
  have hneg : (if j = i ∧ k = i then (-1 : d.Scalar) else 0) =
      -(if j = i ∧ k = i then 1 else 0) := by
    by_cases hjk : j = i ∧ k = i <;> simp [hjk]
  exact hh.trans hneg

end DomainNonembedding.MatrixDescent

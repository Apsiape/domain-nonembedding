import DomainNonembedding.PermutationAverage
import DomainNonembedding.GraphNormalForms
import DomainNonembedding.LocalRank
import DomainNonembedding.DataConstruction
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false

namespace DomainNonembedding.Headline
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open PaperData

section Rank
variable {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]

/-- Multiplication of individual rows and columns cannot increase rank. -/
theorem rank_row_column_le (M : Matrix m n D) (a : m → D) (b : n → D) :
    NonSofic.rankD (fun i j => a i * M i j * b j) ≤ NonSofic.rankD M := by
  have h : (fun i j => a i * M i j * b j) = Matrix.diagonal a * M * Matrix.diagonal b := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [h]
  exact (NonSofic.rankD_mul_le_left _ _).trans (NonSofic.rankD_mul_le_right _ _)

/-- Subtract a fixed row, then restrict the columns. -/
theorem rank_row_difference_le {k l : Type*} [Fintype k] [Fintype l]
    (M : Matrix m n D) (z : m) (e : k → m) (f : l → n) :
    NonSofic.rankD (fun i j => M (e i) (f j) - M z (f j)) ≤ NonSofic.rankD M := by
  let L : Matrix k m D := fun i a => (if a = e i then 1 else 0) -
    (if a = z then 1 else 0)
  have h : (fun i j => M (e i) (f j) - M z (f j)) = (L * M).submatrix id f := by
    ext i j
    change M (e i) (f j) - M z (f j) = ∑ a, L i a * M a (f j)
    simp [L, sub_mul, Finset.sum_sub_distrib]
  rw [h]
  exact (NonSofic.rankD_submatrix_le _ _ _).trans (NonSofic.rankD_mul_le_right _ _)

variable {G r : Type*} [Group G] [Fintype r]

/-- The noncommutative normalization uses the displayed order of all four factors. -/
theorem normalized_difference_rank_le (χ : G →* D) (X : r → r → G)
    (z : r) (e : m → r) :
    NonSofic.rankD (fun i j =>
      χ ((X (e i) z)⁻¹ * X (e i) (e j) * (X z (e j))⁻¹ * X z z) - 1) ≤
        NonSofic.rankD (fun u v => χ (X u v)) := by
  let N : Matrix r r D := fun u v => χ ((X u z)⁻¹ * X u v * (X z v)⁻¹ * X z z)
  have hN : NonSofic.rankD N ≤ NonSofic.rankD (fun u v => χ (X u v)) := by
    simpa only [N, map_mul, mul_assoc] using
      rank_row_column_le (fun u v => χ (X u v))
        (fun u => χ ((X u z)⁻¹)) (fun v => χ ((X z v)⁻¹ * X z z))
  have hz (v : r) : N z v = 1 := by
    change χ ((X z z)⁻¹ * X z v * (X z v)⁻¹ * X z z) = 1
    rw [show (X z z)⁻¹ * X z v * (X z v)⁻¹ * X z z = 1 by group, map_one]
  have h := rank_row_difference_le N z e e
  simp only [hz] at h
  exact h.trans hN

/-- A common group conjugator acts on the whole matrix, including its constant part. -/
theorem conjugated_difference_rank_le (χ : G →* D) (X : r → r → G)
    (z : r) (e : m → r) (t : G) :
    NonSofic.rankD (fun i j =>
      χ (t * ((X (e i) z)⁻¹ * X (e i) (e j) * (X z (e j))⁻¹ * X z z) * t⁻¹) - 1) ≤
        NonSofic.rankD (fun u v => χ (X u v)) := by
  have hcancel : χ t * χ t⁻¹ = 1 := by rw [← map_mul]; simp
  have h (g : G) : χ (t * g * t⁻¹) - 1 = χ t * (χ g - 1) * χ t⁻¹ := by
    simp only [map_mul, mul_sub, sub_mul, mul_one, hcancel]
  simp_rw [h]
  exact (rank_row_column_le _ (fun _ => χ t) (fun _ => χ t⁻¹)).trans
    (normalized_difference_rank_le χ X z e)
end Rank

variable {p : ℕ} (d : PaperData p)

def central (i : d.Label) (q : Entry) : d.Gamma :=
  d.centralHom (FreeGroup.of (i,q))

def stable (π : Arrangement) (i : d.Label) : d.Gamma :=
  PresentedGroup.mk d.gammaRelators (d.stableWord π i)

theorem gluing_relation (π : Arrangement) (i : d.Label) (q : Entry) :
    stable d π i * d.copiedHom π (d.lineHom i (FreeGroup.of q)) * (stable d π i)⁻¹ =
      central d i (π q) := by
  have h := PresentedGroup.one_of_mem (rels := d.gammaRelators)
    (x := d.gluingWord π i q) (Or.inr (Or.inl ⟨π,i,q,rfl⟩))
  apply mul_inv_eq_one.mp
  change PresentedGroup.mk d.gammaRelators (d.stableWord π i) *
    PresentedGroup.mk d.gammaRelators (d.copyWord π (d.lineWord i q)) *
      (PresentedGroup.mk d.gammaRelators (d.stableWord π i))⁻¹ *
      (PresentedGroup.mk d.gammaRelators (FreeGroup.of (.central i (π q))))⁻¹ = 1
  simpa only [gluingWord, map_mul, map_inv] using h

section Entries
variable (hd : d.Admissible) {K D : Type*} [Field K] [DivisionRing D]
    (φ : MonoidAlgebra K d.Gamma →+* D) (hφ : Function.Injective φ)

noncomputable def groupMap : d.Gamma →* D :=
  (φ : _ →* D).comp (MonoidAlgebra.of K d.Gamma)

include hφ in
theorem groupMap_injective : Function.Injective (groupMap d φ) :=
  hφ.comp MonoidAlgebra.of_injective

noncomputable def entries (i : d.Label) (q : Entry) : D :=
  groupMap d φ (central d i q) - 1

include hd hφ in
theorem entries_injective (i : d.Label) : Function.Injective (entries d φ i) := by
  intro a b hab
  have h := sub_left_inj.mp hab
  have hc := GraphNormalForms.central_injective d hd (groupMap_injective d φ hφ h)
  exact congrArg Prod.snd (FreeGroup.of_injective hc)

include hd hφ in
theorem entries_ne_zero (i : d.Label) (q : Entry) : entries d φ i q ≠ 0 := by
  intro h
  have h' : groupMap d φ (central d i q) = groupMap d φ 1 := by
    simpa only [map_one] using sub_eq_zero.mp h
  have hc := groupMap_injective d φ hφ h'
  have hf : FreeGroup.of (i,q) = 1 :=
    GraphNormalForms.central_injective d hd (hc.trans d.centralHom.map_one.symm)
  exact FreeGroup.of_ne_one _ hf
end Entries

section CopiedRanks
variable {D : Type*} [DivisionRing D] (χ : d.Gamma →* D)

set_option maxRecDepth 2048 in
theorem copied_line_rank (π : Arrangement) (i : d.Label) :
    NonSofic.rankD (fun u v => χ (central d i (π (u,v))) - 1) ≤
      NonSofic.rankD (d.lineMatrix (χ.comp (d.copiedHom π)) i) := by
  have h := conjugated_difference_rank_le χ
    (fun u v => d.copiedHom π (d.x i u v)) zeroIndex interior (stable d π i)
  have heq (q : Entry) :
      stable d π i *
        ((d.copiedHom π (d.x i (interior q.1) zeroIndex))⁻¹ *
          d.copiedHom π (d.x i (interior q.1) (interior q.2)) *
          (d.copiedHom π (d.x i zeroIndex (interior q.2)))⁻¹ *
          d.copiedHom π (d.x i zeroIndex zeroIndex)) * (stable d π i)⁻¹ =
        central d i (π q) := by
    simpa only [lineHom, FreeGroup.lift_apply_of, lineWord, map_mul, map_inv,
      xWord, x, PresentedGroup.of] using gluing_relation d π i q
  have hentries : (fun u v => χ (central d i (π (u,v))) - 1) =
      (fun u v => χ (stable d π i *
        ((d.copiedHom π (d.x i (interior u) zeroIndex))⁻¹ *
          d.copiedHom π (d.x i (interior u) (interior v)) *
          (d.copiedHom π (d.x i zeroIndex (interior v)))⁻¹ *
          d.copiedHom π (d.x i zeroIndex zeroIndex)) * (stable d π i)⁻¹) - 1) := by
    funext u v
    rw [heq (u,v)]
  rw [hentries]
  exact h
end CopiedRanks


section Nonembedding
variable [Fact p.Prime] (hd : d.Admissible) {D : Type*} [DivisionRing D]

include hd in
/-- Exact prime-field target, proved from the common arrangement and copied ceilings. -/
theorem nonembedding_prime_data (φ : MonoidAlgebra (ZMod p) d.Gamma →+* D) :
    ¬ Function.Injective φ := by
  intro hφ
  have hr : 4 ≤ rankSize := by
    have h : 0 < (2060 : ℕ) ^ 103 := by positivity
    unfold rankSize
    omega
  obtain ⟨π,havg⟩ := Permutation.exists_common_normalized (rankSize-1) (by omega)
    (entries d φ) (entries_injective d hd φ hφ)
  let ψ : MonoidAlgebra (ZMod p) d.BaseGroup →+* D :=
    φ.comp (MonoidAlgebra.mapDomainRingHom (ZMod p) (d.copiedHom π))
  have hmap (g : d.BaseGroup) :
      ((ψ : _ →* D).comp (MonoidAlgebra.of (ZMod p) d.BaseGroup)) g =
        groupMap d φ (d.copiedHom π g) := by
    simp [ψ, groupMap, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom]
  have hχ : ((ψ : _ →* D).comp (MonoidAlgebra.of (ZMod p) d.BaseGroup)) =
      (groupMap d φ).comp (d.copiedHom π) := by
    ext g
    exact hmap g
  obtain ⟨hceiling,hbudget⟩ := LocalRank.universal_rank_ceiling d hd ψ
  let B := 2*((p^d.exponent)^dimension-d.exceptional.card)+rankSize*d.exceptional.card
  have hsum : (∑ i, NonSofic.rankD (fun u v => entries d φ i (π (u,v)))) ≤ B := by
    apply (Finset.sum_le_sum (fun i _ => copied_line_rank d (groupMap d φ) π i)).trans
    simpa only [hχ] using hceiling
  have hsumq : (∑ i, (NonSofic.rankD (fun u v => entries d φ i (π (u,v))) : ℚ)) ≤ (B : ℚ) := by
    exact_mod_cast hsum
  have hbudgetq : 4*(B : ℚ) < (d.lineCount : ℚ)*rankSize := by exact_mod_cast hbudget
  have hrq : (4 : ℚ) ≤ rankSize := by exact_mod_cast hr
  have hpred : ((rankSize-1 : ℕ) : ℚ)+1 = (rankSize : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ rankSize), Nat.cast_one]
    ring
  simp only [Fintype.card_fin, hpred, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at havg
  change (d.lineCount : ℚ) * rankSize / 2 ≤ (d.lineCount : ℚ) +
    ∑ i, (NonSofic.rankD (fun u v => entries d φ i (π (u,v))) : ℚ) at havg
  have hnonneg : (0 : ℚ) ≤ d.lineCount := by positivity
  nlinarith

/-- Injective extension of coefficients, with no assumption on the size of the field. -/
theorem coefficient_injective (K : Type*) [Field K] [CharP K p] :
    Function.Injective (MonoidAlgebra.mapRingHom d.Gamma (ZMod.castHom (dvd_refl p) K)) := by
  exact MonoidAlgebra.map_injective _ (ZMod.castHom (dvd_refl p) K).injective

include hd in
/-- Exact all-field target for every admissible datum. -/
theorem nonembedding_data (K : Type*) [Field K] [CharP K p]
    (φ : MonoidAlgebra K d.Gamma →+* D) : ¬ Function.Injective φ := by
  intro hφ
  exact nonembedding_prime_data d hd
    (φ.comp (MonoidAlgebra.mapRingHom d.Gamma (ZMod.castHom (dvd_refl p) K)))
    (hφ.comp (coefficient_injective d K))
end Nonembedding

/-- A witness selected from the proved existence certificate, independent of frozen stubs. -/
noncomputable def paperData (p : ℕ) [Fact p.Prime] : PaperData p :=
  Classical.choose (Construction.paperData_exists p)

theorem paperData_admissible (p : ℕ) [Fact p.Prime] : (paperData p).Admissible :=
  Classical.choose_spec (Construction.paperData_exists p)

abbrev Gamma (p : ℕ) [Fact p.Prime] := (paperData p).Gamma

/-- Headline core with a proved existence certificate: every characteristic-p field. -/
theorem nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Gamma p) →+* D) :
    ¬ Function.Injective φ :=
  nonembedding_data (paperData p) (paperData_admissible p) K φ

end DomainNonembedding.Headline

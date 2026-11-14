import DomainNonembedding.ShearNormalForms

set_option autoImplicit false

namespace DomainNonembedding.ShearNonembedding
open scoped BigOperators
open PaperData
attribute [local instance] Classical.propDecidable Classical.decEq

section Rank
variable {D G : Type*} [DivisionRing D] [Group G]

theorem groupMap_ne_zero (χ : G →* D) (g : G) : χ g ≠ 0 := by
  intro h
  have hh : χ g * χ g⁻¹ = 1 := by rw [← map_mul]; simp
  rw [h,zero_mul] at hh
  exact zero_ne_one hh

theorem diagonal_rank_ge (n : ℕ) (a : Fin n → D) (ha : ∀ i, a i ≠ 0) :
    n ≤ NonSofic.rankD (Matrix.diagonal a) := by
  have hinv : Matrix.diagonal (fun i => (a i)⁻¹) * Matrix.diagonal a = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [ha]
    · simp [Matrix.diagonal_apply,hij]
  have h := NonSofic.rankD_mul_le_right (Matrix.diagonal (fun i => (a i)⁻¹)) (Matrix.diagonal a)
  simpa only [hinv,NonSofic.rankD_one,Fintype.card_fin] using h

/-- General rank forcing from one shear conjugator; all coefficients may be noncentral. -/
theorem shear_rank_bound (χ : G →* D) (n : ℕ) (x : Fin n → Fin n → G) (t s : G)
    (hs : χ s ≠ 1)
    (hrel : ∀ u v, t*x u v*t⁻¹ = s^(if u=v then 1 else 0)*x u v) :
    n ≤ 2*NonSofic.rankD (fun u v => χ (x u v)) := by
  let M : Matrix (Fin n) (Fin n) D := fun u v => χ (x u v)
  let C : Matrix (Fin n) (Fin n) D := fun u v => χ (t*x u v*t⁻¹)
  have hC : NonSofic.rankD C ≤ NonSofic.rankD M := by
    simpa only [C,M,map_mul] using
      Headline.rank_row_column_le M (fun _ => χ t) (fun _ => χ t⁻¹)
  have hneg : NonSofic.rankD (-M) ≤ NonSofic.rankD M := by
    have heq : (fun i j => -M i j) = -M := by ext i j; rfl
    simpa only [mul_one,neg_one_mul,heq] using
      Headline.rank_row_column_le M (fun _ => -1) (fun _ => 1)
  have hdiff : C-M = Matrix.diagonal (fun u => (χ s-1)*χ (x u u)) := by
    ext u v
    change χ (t*x u v*t⁻¹)-χ (x u v) = Matrix.diagonal (fun u => (χ s-1)*χ (x u u)) u v
    rw [hrel]
    by_cases huv : u = v
    · subst v
      simp only [ite_true,pow_one,map_mul,Matrix.diagonal_apply_eq]
      noncomm_ring
    · simp [huv,Matrix.diagonal_apply]
  have hlow := diagonal_rank_ge n (fun u => (χ s-1)*χ (x u u))
    (fun u => mul_ne_zero (sub_ne_zero.mpr hs) (groupMap_ne_zero χ (x u u)))
  rw [← hdiff] at hlow
  have hup : NonSofic.rankD (C-M) ≤ NonSofic.rankD C+NonSofic.rankD (-M) :=
    by simpa only [sub_eq_add_neg] using LocalRank.rank_add_le C (-M)
  change n ≤ 2*NonSofic.rankD M
  omega

/-- Taking the normalized interior cannot increase the original line rank. -/
theorem normalized_rank_le {r m : Type*} [Fintype r] [Fintype m]
    (χ : G →* D) (X : r → r → G) (z : r) (e : m → r) :
    NonSofic.rankD (fun u v => χ ((X (e u) z)⁻¹*X (e u) (e v)*(X z (e v))⁻¹*X z z)) ≤
      NonSofic.rankD (fun u v => χ (X u v)) := by
  let N : Matrix r r D := fun u v => χ ((X u z)⁻¹*X u v*(X z v)⁻¹*X z z)
  have hN : NonSofic.rankD N ≤ NonSofic.rankD (fun u v => χ (X u v)) := by
    simpa only [N,map_mul,mul_assoc] using
      Headline.rank_row_column_le (fun u v => χ (X u v))
        (fun u => χ ((X u z)⁻¹)) (fun v => χ ((X z v)⁻¹*X z z))
  exact (NonSofic.rankD_submatrix_le N e e).trans hN
end Rank

variable {p : ℕ} (d : PaperData p)

def baseHom : d.BaseGroup →* d.Shear :=
  PresentedGroup.map d.shearBaseWord (by intro v hv; exact Or.inl ⟨v,hv,rfl⟩)

def s (i : d.Label) : d.Shear := PresentedGroup.of (.s i)
def gamma (i : d.Label) : d.Shear := PresentedGroup.of (.gamma i)
def line (i : d.Label) (q : Entry) : d.Shear := baseHom d (d.lineHom i (FreeGroup.of q))

theorem line_relation (i : d.Label) (q : Entry) :
    gamma d i*line d i q*(gamma d i)⁻¹ = s d i^(if q.1=q.2 then 1 else 0)*line d i q := by
  have h := PresentedGroup.one_of_mem (rels := d.shearRelators)
    (x := FreeGroup.of (.gamma i)*d.shearBaseWord (d.lineWord i q)*
      (FreeGroup.of (.gamma i))⁻¹*
      (FreeGroup.of (.s i)^(if q.1=q.2 then 1 else 0)*d.shearBaseWord (d.lineWord i q))⁻¹)
    (Or.inr (Or.inr (Or.inr ⟨i,q,rfl⟩)))
  apply mul_inv_eq_one.mp
  change PresentedGroup.mk d.shearRelators (FreeGroup.of (.gamma i)) *
    PresentedGroup.mk d.shearRelators (d.shearBaseWord (d.lineWord i q)) *
    (PresentedGroup.mk d.shearRelators (FreeGroup.of (.gamma i)))⁻¹ *
    ((PresentedGroup.mk d.shearRelators (FreeGroup.of (.s i)))^(if q.1=q.2 then 1 else 0)*
      PresentedGroup.mk d.shearRelators (d.shearBaseWord (d.lineWord i q)))⁻¹ = 1
  simpa only [map_mul,map_inv,map_pow] using h

theorem normalized_line_rank {D : Type*} [DivisionRing D] (χ : d.Shear →* D) (i : d.Label) :
    NonSofic.rankD (fun u v => χ (line d i (u,v))) ≤
      NonSofic.rankD (d.lineMatrix (χ.comp (baseHom d)) i) := by
  have h := normalized_rank_le χ (fun u v => baseHom d (d.x i u v)) zeroIndex interior
  have heq (u v : Fin (rankSize-1)) : line d i (u,v) =
      (baseHom d (d.x i (interior u) zeroIndex))⁻¹ *
        baseHom d (d.x i (interior u) (interior v)) *
        (baseHom d (d.x i zeroIndex (interior v)))⁻¹ * baseHom d (d.x i zeroIndex zeroIndex) := by
    simp only [line,lineHom,FreeGroup.lift_apply_of,lineWord,map_mul,map_inv,xWord,x,PresentedGroup.of]
  have hm : (fun u v => χ (line d i (u,v))) =
      (fun u v => χ ((baseHom d (d.x i (interior u) zeroIndex))⁻¹ *
        baseHom d (d.x i (interior u) (interior v)) *
        (baseHom d (d.x i zeroIndex (interior v)))⁻¹ * baseHom d (d.x i zeroIndex zeroIndex))) := by
    funext u v
    rw [heq]
  rw [hm]
  exact h

section Nonembedding
variable [Fact p.Prime] (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D]

include hd in
/-- All-field nonembedding for the exact frozen shear presentation of every admissible datum. -/
theorem nonembedding_data (φ : MonoidAlgebra K d.Shear →+* D) : ¬ Function.Injective φ := by
  intro hφ
  let χ : d.Shear →* D := (φ : _ →* D).comp (MonoidAlgebra.of K d.Shear)
  have hχ : Function.Injective χ := hφ.comp MonoidAlgebra.of_injective
  have hs (i : d.Label) : χ (s d i) ≠ 1 := by
    intro heq
    have heq' : χ (s d i) = χ 1 := heq.trans χ.map_one.symm
    exact ShearNormalForms.s_ne_one d hd i (hχ heq')
  have hlower (i : d.Label) : rankSize-1 ≤
      2*NonSofic.rankD (d.lineMatrix (χ.comp (baseHom d)) i) := by
    have h := shear_rank_bound χ (rankSize-1) (fun u v => line d i (u,v))
      (gamma d i) (s d i) (hs i) (fun u v => line_relation d i (u,v))
    exact h.trans (Nat.mul_le_mul_left 2 (normalized_line_rank d χ i))
  let ψ : MonoidAlgebra (ZMod p) d.BaseGroup →+* D :=
    (φ.comp (MonoidAlgebra.mapDomainRingHom K (baseHom d))).comp
      (MonoidAlgebra.mapRingHom d.BaseGroup (ZMod.castHom (dvd_refl p) K))
  have hmap (g : d.BaseGroup) :
      ((ψ : _ →* D).comp (MonoidAlgebra.of (ZMod p) d.BaseGroup)) g = χ (baseHom d g) := by
    simp [ψ,χ,MonoidAlgebra.of_apply,MonoidAlgebra.mapDomainRingHom]
  have hmaps : ((ψ : _ →* D).comp (MonoidAlgebra.of (ZMod p) d.BaseGroup)) = χ.comp (baseHom d) := by
    ext g
    exact hmap g
  obtain ⟨hceiling,hbudget⟩ := LocalRank.universal_rank_ceiling d hd ψ
  rw [hmaps] at hceiling
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset d.Label)) => hlower i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Finset.mul_sum] at hsum
  have hr : 3 ≤ rankSize := by
    have h : 0 < (2060 : ℕ)^103 := by positivity
    unfold rankSize
    omega
  have hpred : rankSize-1+1 = rankSize := by omega
  nlinarith
end Nonembedding

abbrev Lambda (p : ℕ) [Fact p.Prime] := (Headline.paperData p).Shear

/-- Secondary headline with the same proved existence certificate as the permutation core. -/
theorem shear_nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Lambda p) →+* D) :
    ¬ Function.Injective φ :=
  nonembedding_data (Headline.paperData p) (Headline.paperData_admissible p) K φ

end DomainNonembedding.ShearNonembedding

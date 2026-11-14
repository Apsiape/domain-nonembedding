import DomainNonembedding.PaperData
import DomainNonembedding.PermutationAverage

set_option autoImplicit false

namespace DomainNonembedding.FiniteFieldData

/-- A positive prime power can exceed any prescribed finite threshold. -/
theorem exists_large_power (p bound : ℕ) [Fact p.Prime] :
    ∃ a : ℕ, 0 < a ∧ bound < p ^ a := by
  refine ⟨bound + 1, by omega, ?_⟩
  exact (Nat.lt_succ_self bound).trans
    (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)

/-- Number the actual extension field, rather than casting consecutive integers. -/
noncomputable def number (p a : ℕ) [Fact p.Prime] (ha : 0 < a) :
    GaloisField p a ≃ Fin (p ^ a) := by
  letI : Fintype (GaloisField p a) := Fintype.ofFinite _
  apply Fintype.equivFinOfCardEq
  rw [← Nat.card_eq_fintype_card, GaloisField.card p a (ne_of_gt ha)]

/-- The numbered initial segment has exactly the paper's required size. -/
theorem grid_card {p : ℕ} (d : PaperData p) :
    d.grid.card = p ^ d.exponent / (10 * dimension) := by
  classical
  let Q := p ^ d.exponent
  let k := Q / (10 * dimension)
  let e : {x : d.Scalar // (d.number x).val < k} ≃ Permutation.Initial Q k :=
    { toFun := fun x => ⟨d.number x.val, x.property⟩
      invFun := fun y => ⟨d.number.symm y.val, by simpa using y.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  change (Finset.univ.filter fun x : d.Scalar => (d.number x).val < k).card = k
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans
    ((Fintype.card_congr (Permutation.initialEquiv Q k (Nat.div_le_self _ _)).symm).trans
      (Fintype.card_fin k))

end DomainNonembedding.FiniteFieldData

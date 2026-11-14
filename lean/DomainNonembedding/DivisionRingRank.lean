import DomainNonembedding.Permutation

set_option autoImplicit false

namespace DomainNonembedding.DivisionRingRank
open scoped BigOperators

theorem rank_le_columns {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (M : Matrix m n D) : NonSofic.rankD M ≤ Fintype.card n := by
  have h := Submodule.finrank_mono
    (show LinearMap.range M.vecMulLinear ≤ ⊤ from le_top)
  simpa [NonSofic.rankD] using h

/-- Factoring through a basis of the left row space uses exactly its dimension. -/
theorem exists_rank_factorization {D m n : Type*} [DivisionRing D]
    [Fintype m] [Fintype n] (M : Matrix m n D) :
    ∃ (A : Matrix m (Fin (NonSofic.rankD M)) D)
      (B : Matrix (Fin (NonSofic.rankD M)) n D), M = A * B := by
  classical
  let W := LinearMap.range M.vecMulLinear
  let row (i : m) : W := ⟨M.row i, ⟨Pi.single i 1, Matrix.single_one_vecMul i M⟩⟩
  let basis := Module.finBasis D W
  let A : Matrix m (Fin (NonSofic.rankD M)) D := Matrix.of fun i j => basis.repr (row i) j
  let B : Matrix (Fin (NonSofic.rankD M)) n D := Matrix.of fun j k => (basis j).val k
  refine ⟨A, B, ?_⟩
  ext i k
  have h := congrArg (fun w : W => w.val k) (basis.sum_repr (row i))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

/-- Transpose into the opposite ring reverses matrix multiplication. -/
theorem opTranspose_mul {D l m n : Type*} [DivisionRing D] [Fintype m]
    (A : Matrix l m D) (B : Matrix m n D) :
    (A * B).transpose.map MulOpposite.op =
      B.transpose.map MulOpposite.op * A.transpose.map MulOpposite.op := by
  ext i j
  simp [Matrix.mul_apply, Finset.op_sum]

theorem opposite_rank_le {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (M : Matrix m n D) :
    NonSofic.rankD (M.transpose.map MulOpposite.op) ≤ NonSofic.rankD M := by
  obtain ⟨A, B, hM⟩ := exists_rank_factorization M
  have h : NonSofic.rankD (M.transpose.map MulOpposite.op) ≤
      Fintype.card (Fin (NonSofic.rankD M)) := by
    calc
      NonSofic.rankD (M.transpose.map MulOpposite.op) =
          NonSofic.rankD (B.transpose.map MulOpposite.op * A.transpose.map MulOpposite.op) := by
        conv_lhs => rw [hM, opTranspose_mul]
      _ ≤ NonSofic.rankD (B.transpose.map MulOpposite.op) := NonSofic.rankD_mul_le_left _ _
      _ ≤ Fintype.card (Fin (NonSofic.rankD M)) := rank_le_columns _
  simpa only [Fintype.card_fin] using h

/-- Relabeling scalars through a ring equivalence preserves left row rank. -/
theorem rank_map_equiv {D E m n : Type*} [DivisionRing D] [DivisionRing E]
    [Fintype m] [Fintype n] (e : D ≃+* E) (M : Matrix m n D) :
    NonSofic.rankD (M.map e) = NonSofic.rankD M := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (↑e : D →+* E) (e.symm : E →+* D)
  let v : (n → D) ≃ₛₗ[RingHomClass.toRingHom e] (n → E) :=
    { toFun := fun x i => e (x i)
      invFun := fun x i => e.symm (x i)
      left_inv := by intro x; ext i; simp
      right_inv := by intro x; ext i; simp
      map_add' := by intro x y; ext i; simp
      map_smul' := by
        intro c x
        funext i
        change e (c * x i) = e c * e (x i)
        exact e.map_mul c (x i) }
  have hv : (LinearMap.range M.vecMulLinear).map v.toLinearMap =
      LinearMap.range (M.map e).vecMulLinear := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨fun i => e (x i), ?_⟩
      ext j
      simp [v, Matrix.vecMul, dotProduct, map_sum]
    · rintro ⟨x, rfl⟩
      refine ⟨M.vecMulLinear (fun i => e.symm (x i)), LinearMap.mem_range_self _ _, ?_⟩
      ext j
      simp [v, Matrix.vecMul, dotProduct, map_sum]
  let w := v.submoduleMap (LinearMap.range M.vecMulLinear)
  have h := lift_rank_eq_of_equiv_equiv e w.toAddEquiv e.bijective
    (fun r x => w.map_smulₛₗ r x)
  have hf := congrArg Cardinal.toNat h
  have hf' : Module.finrank D (LinearMap.range M.vecMulLinear) =
      Module.finrank E ((LinearMap.range M.vecMulLinear).map v.toLinearMap) := by
    simpa only [Module.finrank, Cardinal.toNat_lift] using hf
  rw [hv] at hf'
  exact hf'.symm

/-- Left row dimension equals right column dimension over every division ring. -/
theorem row_eq_column {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (M : Matrix m n D) :
    NonSofic.rankD M = NonSofic.rankD (M.transpose.map MulOpposite.op) := by
  apply le_antisymm _ (opposite_rank_le M)
  have h := opposite_rank_le (M.transpose.map MulOpposite.op)
  have hd : (M.transpose.map MulOpposite.op).transpose.map MulOpposite.op =
      M.map (RingEquiv.opOp D) := by
    ext i j
    rfl
  rw [hd, rank_map_equiv] at h
  exact h

end DomainNonembedding.DivisionRingRank

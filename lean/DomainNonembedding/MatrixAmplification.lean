import DomainNonembedding.DivisionRingRank
import Mathlib.Data.Matrix.Composition

set_option autoImplicit false

namespace DomainNonembedding.MatrixDescent
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def flatten {D m n : Type*} (a : ℕ) (M : Matrix m n (Matrix (Fin a) (Fin a) D)) :
    Matrix (m × Fin a) (n × Fin a) D := Matrix.comp _ _ _ _ _ M

theorem flatten_mul {D l m n : Type*} [Semiring D] [Fintype m] (a : ℕ)
    (A : Matrix l m (Matrix (Fin a) (Fin a) D))
    (B : Matrix m n (Matrix (Fin a) (Fin a) D)) :
    flatten a (A*B) = flatten a A * flatten a B := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp only [flatten, Matrix.comp_apply, Matrix.mul_apply, Matrix.sum_apply]
  exact (Fintype.sum_prod_type (fun x : m × Fin a => A i x.1 u x.2 * B x.1 j x.2 v)).symm

theorem flatten_sum {D m n τ : Type*} [AddCommMonoid D] (a : ℕ) (s : Finset τ)
    (M : τ → Matrix m n (Matrix (Fin a) (Fin a) D)) :
    flatten a (∑ t ∈ s, M t) = ∑ t ∈ s, flatten a (M t) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  simp [flatten, Matrix.comp_apply, Matrix.sum_apply]

theorem flatten_neg {D m n : Type*} [Neg D] (a : ℕ)
    (M : Matrix m n (Matrix (Fin a) (Fin a) D)) : flatten a (-M) = -flatten a M := rfl

theorem rank_blockDiagonal {D m n o : Type*} [DivisionRing D]
    [Fintype m] [Fintype n] [Fintype o] [DecidableEq o] (Y : o → Matrix m n D) :
    NonSofic.rankD (Matrix.blockDiagonal Y) = ∑ i, NonSofic.rankD (Y i) := by
  have h := (NonSofic.rankDRankFunction D).rkF_blockDiagonal' Y
  simp only [NonSofic.rankDRankFunction_rkF] at h
  exact_mod_cast h

theorem rank_neg {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (M : Matrix m n D) : NonSofic.rankD (-M) = NonSofic.rankD M := by
  have h := (NonSofic.rankDRankFunction D).rkF_neg M
  simpa only [NonSofic.rankDRankFunction_rkF, Nat.cast_inj] using h

theorem rank_sum_le {D m n τ : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (s : Finset τ) (M : τ → Matrix m n D) :
    NonSofic.rankD (∑ t ∈ s, M t) ≤ ∑ t ∈ s, NonSofic.rankD (M t) := by
  have h := (NonSofic.rankDRankFunction D).rkF_sum_le s M
  simp only [NonSofic.rankDRankFunction_rkF] at h
  exact_mod_cast h

/-- Amplifying a matrix by scalar identity blocks multiplies its rank by `a`. -/
theorem rank_amplification {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (a : ℕ) (M : Matrix m n D) :
    NonSofic.rankD (flatten a (M.map (Matrix.scalar (Fin a)))) = a*NonSofic.rankD M := by
  have he : flatten a (M.map (Matrix.scalar (Fin a))) =
      Matrix.blockDiagonal (fun _ : Fin a => M) := by
    ext ⟨i, u⟩ ⟨j, v⟩
    simp [flatten, Matrix.comp_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
  rw [he, rank_blockDiagonal]
  simp [mul_comm]

end DomainNonembedding.MatrixDescent

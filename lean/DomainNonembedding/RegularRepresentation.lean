import DomainNonembedding.Interpolation

set_option autoImplicit false

namespace DomainNonembedding.MatrixDescent
open scoped BigOperators

/-- A finite field of characteristic `p` acts in a matrix ring over any such division ring.
Its matrices commute with every scalar matrix from the division ring. -/
theorem exists_regular_representation {p : ℕ} {K D : Type*} [Field K] [Fintype K]
    [DivisionRing D] [CharP K p] [CharP D p] :
    ∃ a : ℕ, 0 < a ∧ ∃ c : K →+* Matrix (Fin a) (Fin a) D,
      ∀ (x : K) (y : D), c x * Matrix.scalar (Fin a) y = Matrix.scalar (Fin a) y * c x := by
  classical
  letI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) K := (ZMod.castHom (dvd_refl p) K).toAlgebra
  let a := Module.finrank (ZMod p) K
  let b := Module.finBasis (ZMod p) K
  let cD : ZMod p →+* D := ZMod.castHom (dvd_refl p) D
  let c : K →+* Matrix (Fin a) (Fin a) D :=
    cD.mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom
  have ha : 0 < a := (Module.finrank_pos_iff_of_free (ZMod p) K).mpr inferInstance
  refine ⟨a, ha, c, ?_⟩
  intro x y
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change cD (Algebra.leftMulMatrix b x i j) * y = y * cD (Algebra.leftMulMatrix b x i j)
  generalize Algebra.leftMulMatrix b x i j = z
  rw [← ZMod.natCast_zmod_val z, map_natCast]
  exact (Nat.cast_commute z.val y).eq

end DomainNonembedding.MatrixDescent

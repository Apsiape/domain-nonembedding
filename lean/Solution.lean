import Main

set_option autoImplicit false

namespace DomainNonembedding.Release

theorem paperData_exists (p : ℕ) [Fact p.Prime] :
    ∃ d : PaperData p, d.Admissible := by
  exact Construction.paperData_exists p

theorem nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Gamma →+* D) :
    ¬ Function.Injective φ := by
  exact Headline.nonembedding_data d hd K φ

theorem shear_nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Shear →+* D) :
    ¬ Function.Injective φ := by
  exact ShearNonembedding.nonembedding_data d hd K φ

end DomainNonembedding.Release

import Statements
import DomainNonembedding.ShearNonembedding

set_option autoImplicit false

namespace DomainNonembedding.Main
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem paperData_exists (p : ℕ) [Fact p.Prime] : DomainNonembedding.paperData_exists p := by
  exact Construction.paperData_exists p

theorem interpolation_identity {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    (i j k : d.Label) : DomainNonembedding.interpolation_identity d hd i j k := by
  exact Interpolation.interpolation_identity d hd i j k

theorem rank_certificate {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    {D : Type*} [DivisionRing D] [CharP D p] (r : ℕ)
    (Y : d.Label → Matrix (Fin r) (Fin r) D) : DomainNonembedding.rank_certificate d hd r Y := by
  exact MatrixDescent.rank_certificate d hd r Y

theorem line_free {p : ℕ} (d : PaperData p) (hd : d.Admissible) (i : d.Label) : DomainNonembedding.line_free d hd i := by
  exact LineFree.line_free d hd i

theorem universal_rank_ceiling {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) {D : Type*} [DivisionRing D]
    (φ : MonoidAlgebra (ZMod p) d.BaseGroup →+* D) : DomainNonembedding.universal_rank_ceiling d hd φ := by
  exact LocalRank.universal_rank_ceiling d hd φ

theorem central_injective {p : ℕ} (d : PaperData p) (hd : d.Admissible) : DomainNonembedding.central_injective d hd := by
  exact GraphNormalForms.central_injective d hd

theorem copied_injective {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    (π : PaperData.Arrangement) : DomainNonembedding.copied_injective d hd π := by
  exact GraphNormalForms.copied_injective d hd π

theorem nonembedding_prime_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) {D : Type*} [DivisionRing D]
    (φ : MonoidAlgebra (ZMod p) d.Gamma →+* D) : DomainNonembedding.nonembedding_prime_data d hd φ := by
  exact Headline.nonembedding_prime_data d hd φ

theorem nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Gamma →+* D) : DomainNonembedding.nonembedding_data d hd K φ := by
  exact Headline.nonembedding_data d hd K φ

theorem nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Gamma p) →+* D) : DomainNonembedding.nonembedding p K φ := by
  exact Headline.nonembedding p K φ

theorem shear_nonembedding (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K (Lambda p) →+* D) : DomainNonembedding.shear_nonembedding p K φ := by
  exact ShearNonembedding.shear_nonembedding p K φ

end DomainNonembedding.Main

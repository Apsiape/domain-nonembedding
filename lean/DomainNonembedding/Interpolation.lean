import DomainNonembedding.FiniteFieldData
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.MatrixRank

set_option autoImplicit false

namespace DomainNonembedding.Interpolation
open OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem scalar_card {p : ℕ} (d : PaperData p) : Fintype.card d.Scalar = p^d.exponent :=
  (Fintype.card_congr d.number).trans (Fintype.card_fin _)

theorem degree_cutoff {p : ℕ} (d : PaperData p) :
    2*(Fintype.card (Fin dimension)*(d.grid.card-1)) < Fintype.card d.Scalar-1 := by
  have htwo : 2 ≤ Fintype.card d.Scalar := Fintype.one_lt_card
  rw [FiniteFieldData.grid_card, scalar_card] at *
  simp only [Fintype.card_fin]
  change 2*(103*(p^d.exponent/1030-1)) < p^d.exponent-1
  omega

theorem lagrange_eq_grid {p : ℕ} (d : PaperData p) (i : d.Label) (z : d.Point) :
    d.lagrange i z = gridLagrange d.grid (d.mark i) z := rfl

theorem mem_lineIncidence {p : ℕ} (d : PaperData p) (i : d.Label) (z : d.Point) :
    i ∈ lineIncidence d.mark d.direction z ↔ d.Incident z i := by
  simp only [lineIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
    puncturedLine, Finset.mem_image, Finset.mem_erase, and_true]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, ht, fun j => (congrFun hz j).symm⟩
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, ht, funext (fun j => (hz j).symm)⟩

/-- The protected interpolation target, proved over the actual extension field. -/
theorem interpolation_identity {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    (i j k : d.Label) :
    (∑ z ∈ Finset.univ.filter (fun z => d.Incident z i), d.lagrange j z*d.lagrange k z) =
      if j = i ∧ k = i then -1 else 0 := by
  have h := grid_line_certificate d.grid d.mark d.direction hd.2.1 hd.1 hd.2.2.1
    (degree_cutoff d) i j k
  have hh : (∑ z ∈ Finset.univ.filter (fun z => d.Incident z i),
      d.lagrange j z*d.lagrange k z) = -(if j = i ∧ k = i then 1 else 0) := by
    simpa only [Finset.sum_filter, mem_lineIncidence, lagrange_eq_grid] using h
  rw [hh]
  split_ifs <;> simp

end DomainNonembedding.Interpolation

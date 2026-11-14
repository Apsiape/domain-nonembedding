import DomainNonembedding.MarkedLines

set_option autoImplicit false

namespace DomainNonembedding
open OAI.Release075
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MarkedLines
variable {K : Type} [Field K] [Fintype K] (l : MarkedLines K)

structure Partition (z : Fin dimension → K) where
  zero : CartesianBlock (Fin l.lineCount) rankSize
  one : CartesianBlock (Fin l.lineCount) rankSize
  disjoint : Disjoint zero.labels one.labels
  cover : zero.labels ∪ one.labels = l.incidences z

abbrev Regular := {z : Fin dimension → K // z ∉ l.exceptional}
abbrev BlockIndex := l.Regular × Bool

def partition {S : Finset K} (hl : l.Good S) (z : l.Regular) : l.Partition z := by
  apply Classical.choice
  obtain ⟨b₀, b₁, hd, hu⟩ := exists_two_cartesian_blocks rankSize
    (by unfold rankSize; positivity) (l.incidences z) (hl.2.2.2.2.1 z z.property)
  exact ⟨⟨b₀, b₁, hd, hu⟩⟩

def block {S : Finset K} (hl : l.Good S) (b : l.BlockIndex) :
    CartesianBlock (Fin l.lineCount) rankSize :=
  if b.2 then (l.partition hl b.1).one else (l.partition hl b.1).zero

theorem block_subset {S : Finset K} (hl : l.Good S) (b : l.BlockIndex) :
    (l.block hl b).labels ⊆ l.incidences b.1 := by
  rw [← (l.partition hl b.1).cover]
  intro i hi
  rcases b with ⟨z, e⟩
  cases e with
  | false => exact Finset.mem_union_left _ hi
  | true => exact Finset.mem_union_right _ hi

end MarkedLines

namespace Construction

/-- Cardinality of the initial segment under an arbitrary field numbering. -/
theorem numbered_grid_card {K : Type} [Fintype K] (q k : ℕ) (e : K ≃ Fin q)
    (hk : k ≤ q) : (Finset.univ.filter (fun x : K => (e x).val < k)).card = k := by
  let ec : {x : K // (e x).val < k} ≃ Permutation.Initial q k :=
    { toFun := fun x => ⟨e x.val, x.property⟩
      invFun := fun y => ⟨e.symm y.val, by simpa using y.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr ec).trans
    ((Fintype.card_congr (Permutation.initialEquiv q k hk).symm).trans (Fintype.card_fin k))

/-- Add exactly two disjoint Cartesian blocks at every regular point. -/
theorem exists_withBlocks {p : ℕ} (a : ℕ) (ha : 0 < a)
    (hlarge : fieldThreshold < p^a) {K : Type} [Field K] [Fintype K] [CharP K p]
    (number : K ≃ Fin (p^a)) (l : MarkedLines K)
    (hl : l.Good (Finset.univ.filter (fun x : K => (number x).val < p^a/1030))) :
    ∃ d : PaperData p, d.Admissible := by
  let e : Fin (Fintype.card l.BlockIndex) ≃ l.BlockIndex := (Fintype.equivFin _).symm
  let block := fun b : Fin (Fintype.card l.BlockIndex) => l.block hl (e b)
  have hcard : Fintype.card K = p^a := (Fintype.card_congr number).trans (Fintype.card_fin _)
  obtain ⟨z, hz⟩ := l.exists_regular hl
  have hpos : 0 < l.lineCount := by
    have hN := hl.2.2.2.2.2.1
    have hm : 0 < (Fintype.card K)^103 := pow_pos Fintype.card_pos _
    by_contra hn
    have hn' : l.lineCount = 0 := by omega
    rw [hn', Nat.mul_zero] at hN
    omega
  let d : PaperData p :=
    { exponent := a
      exponent_pos := ha
      large := hlarge
      Scalar := K
      number := number
      lineCount := l.lineCount
      mark := l.mark
      direction := l.direction
      exceptional := l.exceptional
      blockCount := Fintype.card l.BlockIndex
      blockPoint := fun b => (e b).1.val
      blockS := fun b => (block b).s
      blockT := fun b => (block b).t
      blockLabels := fun b => (block b).labels
      coordinates := fun b => (block b).coordinates
      distinguishedLine := ⟨0, hpos⟩
      distinguishedBlock := e.symm (⟨z, hz⟩, false) }
  refine ⟨d, hl.1, hl.2.1, hl.2.2.1, ?_, hl.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · have hg : d.incidenceGraph = l.graph := by
      ext x y
      cases x <;> cases y <;> rfl
    rw [hg]
    exact hl.2.2.2.1
  · change (p^a)^dimension ≤ 2*2060^103*l.lineCount
    simpa only [hcard] using hl.2.2.2.2.2.1
  · change 2*rankSize*l.exceptional.card ≤ (p^a)^dimension
    simpa only [hcard] using hl.2.2.2.2.2.2
  · intro b
    exact ⟨(block b).hs, (block b).ht, (e b).1.property, l.block_subset hl (e b)⟩
  · intro z hz
    let zr : l.Regular := ⟨z, hz⟩
    let b₀ := e.symm (zr, false)
    let b₁ := e.symm (zr, true)
    have he₀ : e b₀ = (zr, false) := e.apply_symm_apply _
    have he₁ : e b₁ = (zr, true) := e.apply_symm_apply _
    refine ⟨b₀, b₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have hh := congrArg (fun b => (e b).2) h
      rw [he₀, he₁] at hh
      cases hh
    · change (e b₀).1.val = z
      rw [he₀]
    · change (e b₁).1.val = z
      rw [he₁]
    · change Disjoint (l.block hl (e b₀)).labels (l.block hl (e b₁)).labels
      rw [he₀, he₁]
      simpa only [MarkedLines.block, Bool.false_eq_true, ↓reduceIte] using
        (l.partition hl zr).disjoint
    · change (l.block hl (e b₀)).labels ∪ (l.block hl (e b₁)).labels = l.incidences z
      rw [he₀, he₁]
      simpa only [MarkedLines.block, Bool.false_eq_true, ↓reduceIte] using
        (l.partition hl zr).cover
    · intro b hb
      have hz' : (e b).1 = zr := Subtype.ext hb
      cases hbool : (e b).2 with
      | false =>
        left
        apply e.injective
        rw [he₀]
        exact Prod.ext hz' hbool
      | true =>
        right
        apply e.injective
        rw [he₁]
        exact Prod.ext hz' hbool

/-- Admissible data exist for every prime, with the protected target's exact type. -/
theorem paperData_exists (p : ℕ) [Fact p.Prime] : ∃ d : PaperData p, d.Admissible := by
  obtain ⟨a, ha, hlarge⟩ := FiniteFieldData.exists_large_power p fieldThreshold
  let K := GaloisField p a
  letI : Fintype K := Fintype.ofFinite _
  let number : K ≃ Fin (p^a) := FiniteFieldData.number p a ha
  have hcard : Fintype.card K = p^a := (Fintype.card_congr number).trans (Fintype.card_fin _)
  let S : Finset K := Finset.univ.filter (fun x => (number x).val < p^a/1030)
  have hS : S.card = Fintype.card K/1030 := by
    rw [hcard]
    exact numbered_grid_card (p^a) (p^a/1030) number (Nat.div_le_self _ _)
  obtain ⟨l, hl⟩ := Incidence.exists_markedLines (hcard ▸ hlarge) S hS
  exact exists_withBlocks a ha hlarge number l hl

end Construction
end
end DomainNonembedding

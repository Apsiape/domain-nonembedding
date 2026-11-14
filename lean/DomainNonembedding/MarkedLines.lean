import DomainNonembedding.IncidenceBounds

set_option autoImplicit false

namespace DomainNonembedding
open OAI.Release075
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Raw marked lines before the independent two-block construction. -/
structure MarkedLines (K : Type) where
  lineCount : ℕ
  mark : Fin lineCount → Fin dimension → K
  direction : Fin lineCount → Fin dimension → K
  exceptional : Finset (Fin dimension → K)

namespace MarkedLines
variable {K : Type} [Field K] [Fintype K] (l : MarkedLines K)

def Incident (z : Fin dimension → K) (i : Fin l.lineCount) : Prop :=
  ∃ t : K, t ≠ 0 ∧ ∀ j, z j = l.mark i j + t*l.direction i j

def incidences (z : Fin dimension → K) : Finset (Fin l.lineCount) :=
  Finset.univ.filter (l.Incident z)

def graph : SimpleGraph ((Fin dimension → K) ⊕ Fin l.lineCount) :=
  relationGraph l.Incident

def Good (S : Finset K) : Prop :=
  Function.Injective l.mark ∧ (∀ i j, l.mark i j ∈ S) ∧
  (∀ i, l.direction i ≠ 0) ∧ (100 : ℕ∞) < l.graph.egirth ∧
  (∀ z, z ∉ l.exceptional → 4*rankSize^2 ≤ (l.incidences z).card) ∧
  (Fintype.card K)^103 ≤ 2*2060^103*l.lineCount ∧
  2*rankSize*l.exceptional.card ≤ (Fintype.card K)^103

theorem exists_regular {S : Finset K} (hl : l.Good S) : ∃ z, z ∉ l.exceptional := by
  by_contra! h
  have hE : l.exceptional = Finset.univ := Finset.eq_univ_of_forall h
  have hcard : l.exceptional.card = (Fintype.card K)^103 := by
    simp [hE, Fintype.card_fun]
  have hr : 1 ≤ rankSize := Nat.succ_le_of_lt (by unfold rankSize; positivity)
  have hm : 0 < (Fintype.card K)^103 := pow_pos Fintype.card_pos _
  have hb := hl.2.2.2.2.2.2
  rw [hcard] at hb
  nlinarith

end MarkedLines

namespace Incidence

theorem parameter_incidence_iff {K : Type} [Field K]
    (a z : Fin dimension → K) (d : Projectivization K (Fin dimension → K)) :
    (∃ t : K, t ≠ 0 ∧ ∀ j, z j = a j + t*d.rep j) ↔ PuncturedIncidence a z d := by
  constructor
  · rintro ⟨t, ht, hz⟩
    have he : a + t • d.rep = z := by ext j; exact (hz j).symm
    refine ⟨?_, t, he⟩
    intro h
    have hh : a + t • d.rep = a + (0 : K) • d.rep := by simpa [h] using he
    exact ht (lineMap_injective a d hh)
  · rintro ⟨hz, t, ht⟩
    refine ⟨t, ?_, fun j => (congrFun ht j).symm⟩
    intro h
    subst t
    simp only [zero_smul, add_zero] at ht
    exact hz ht.symm

/-- The dimension-103 incidence family, before introducing any blocks or groups. -/
theorem exists_markedLines {K : Type} [Field K] [Fintype K]
    (hlarge : fieldThreshold < Fintype.card K) (S : Finset K)
    (hS : S.card = Fintype.card K/1030) : ∃ l : MarkedLines K, l.Good S := by
  letI : Fintype (Projectivization K (Fin dimension → K)) := Fintype.ofFinite _
  obtain ⟨ω, hE, hN, _⟩ := large_field_outcome hlarge S hS
  let I := Retained (gridMarks S) ω
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let l : MarkedLines K :=
    { lineCount := Fintype.card I
      mark := fun i => (e i).val.val
      direction := fun i => (ω (e i).val).rep
      exceptional := exceptionalPoints (gridMarks S) ω (4*rankSize^2) }
  have hi (z : Fin dimension → K) (i : Fin l.lineCount) :
      l.Incident z i ↔ PuncturedIncidence (e i).val.val z (ω (e i).val) :=
    parameter_incidence_iff _ _ _
  have hc (z : Fin dimension → K) :
      (l.incidences z).card = (retainedIncidence (gridMarks S) ω z).card := by
    let ec : {i : Fin l.lineCount // l.Incident z i} ≃
        {i : I // PuncturedIncidence i.val.val z (ω i.val)} := e.subtypeEquiv (hi z)
    have h := Fintype.card_congr ec
    simpa only [Fintype.card_subtype, MarkedLines.incidences, retainedIncidence] using h
  let f : l.graph →g relationGraph (fun z (i : I) =>
      PuncturedIncidence i.val.val z (ω i.val)) :=
    { toFun := Sum.map id e
      map_rel' := by
        intro x y h
        cases x <;> cases y
        · exact h.elim
        · exact (hi _ _).mp h
        · exact (hi _ _).mp h
        · exact h.elim }
  have hf : Function.Injective f := Function.injective_id.sumMap e.injective
  refine ⟨l, ?_, ?_, ?_, ?_, ?_, hN, hE⟩
  · intro i j h
    apply e.injective
    exact Subtype.ext (Subtype.ext h)
  · intro i j
    exact Fintype.mem_piFinset.mp (e i).val.property j
  · intro i
    exact (ω (e i).val).rep_nonzero
  · have hg : (101 : ℕ∞) ≤ l.graph.egirth := SimpleGraph.le_egirth.mpr (by
      intro a w hw
      have h := retained_girth (gridMarks S) ω (f a) (w.map f) (hw.map hf)
      simp only [SimpleGraph.Walk.length_map] at h
      exact_mod_cast (show 101 ≤ w.length by omega))
    exact lt_of_lt_of_le (by norm_num : (100 : ℕ∞) < 101) hg
  · intro z hz
    rw [hc]
    exact retainedIncidence_card_ge (gridMarks S) ω (4*rankSize^2) z hz

end Incidence
end
end DomainNonembedding

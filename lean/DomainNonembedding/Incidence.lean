import DomainNonembedding.FiniteFieldData
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Incidence

set_option autoImplicit false

/-!
The dimension-103, girth-100 alteration. The finite expectation, projective
line and cycle-encoding lemmas are reused from the byte-identical OAI package.
The deletion/retention proofs below adapt its dimension-independent alteration
from half-length 6 to 50 (Apache-2.0, openai/math @adc7f12).
-/

namespace DomainNonembedding.Incidence
open OAI.Release075
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V]

/-- All marks lying on an occurring short-cycle attempt are discarded. -/
def deletedMarks (S : Finset V) (ω : S → Projectivization K V) : Finset S :=
  (Finset.Icc 2 50).biUnion fun s =>
    (badCycles S (finRotate s) ω).biUnion fun c => Finset.univ.image c.marks

theorem deletedMarks_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedMarks S ω).card ≤ 50 * ∑ s ∈ Finset.Icc 2 50, (badCycles S (finRotate s) ω).card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ s ∈ Finset.Icc 2 50, 50 * (badCycles S (finRotate s) ω).card := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _c ∈ badCycles S (finRotate s) ω, 50 := by
          apply Finset.sum_le_sum
          intro c _
          have hcard : (Finset.univ.image c.marks).card ≤ s := by
            exact Finset.card_image_le.trans (by simp)
          exact hcard.trans (Finset.mem_Icc.mp hs).2
        _ = _ := by simp [mul_comm]
    _ = _ := by rw [Finset.mul_sum]

def Retained (S : Finset V) (ω : S → Projectivization K V) := {a : S // a ∉ deletedMarks S ω}

/-- Deletion creates no cycle; exact girth >100 is obtained, including repeated
geometric lines with distinct labels. -/
theorem retained_girth (S : Finset V) (ω : S → Projectivization K V)
    (a : V ⊕ Retained S ω)
    (w : (relationGraph (fun z (i : Retained S ω) =>
      PuncturedIncidence i.val.val z (ω i.val))).Walk a a) (hw : w.IsCycle) : 100 < w.length := by
  by_contra hlen
  obtain ⟨s,hs,p,l,heq,hp,hl,h⟩ := relationGraph_any_cycle_encoding _ w hw
  have hs50 : s ≤ 50 := by omega
  let l' : Fin s → S := fun i => (l i).val
  have hl' : Function.Injective l' := by
    intro i j hh; apply hl; exact Subtype.ext hh
  obtain ⟨c,hc,hcl⟩ := cycleCandidate_of_incidence ω hs p l' hp hl' h
  let i : Fin s := ⟨0,by omega⟩
  have hdel : c.marks i ∈ deletedMarks S ω := by
    apply Finset.mem_biUnion.mpr
    refine ⟨s,Finset.mem_Icc.mpr ⟨hs,hs50⟩,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [hcl] at hdel
  exact (l i).property hdel

instance (S : Finset V) (ω : S → Projectivization K V) : Fintype (Retained S ω) := by
  unfold Retained
  infer_instance

def chosenLinePoints (a : V) (d : Projectivization K V) : Finset V :=
  Finset.univ.image (fun t : K => a+t • d.rep)

omit [Fintype V] in
theorem mem_chosenLinePoints (a z : V) (d : Projectivization K V) :
    z ∈ chosenLinePoints a d ↔ OnChosenLine a z d := by
  simp only [chosenLinePoints, Finset.mem_image, Finset.mem_univ, true_and, OnChosenLine]

omit [Fintype V] in
theorem chosenLinePoints_card (a : V) (d : Projectivization K V) :
    (chosenLinePoints a d).card = Fintype.card K := by
  exact (Finset.card_image_iff.mpr (lineMap_injective a d).injOn).trans (Finset.card_univ)

def deletedPoints (S : Finset V) (ω : S → Projectivization K V) : Finset V :=
  (deletedMarks S ω).biUnion (fun a => chosenLinePoints a.val (ω a))

theorem deletedPoints_card_le (S : Finset V) (ω : S → Projectivization K V) :
    (deletedPoints S ω).card ≤ Fintype.card K * (deletedMarks S ω).card := by
  apply Finset.card_biUnion_le.trans
  simp only [chosenLinePoints_card,Finset.sum_const,nsmul_eq_mul, Nat.cast_id]
  exact le_of_eq (Nat.mul_comm _ _)

def exceptionalPoints (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) : Finset V :=
  Finset.univ.filter (fun z => pointDegree S ω z < T) ∪ deletedPoints S ω

theorem exceptionalPoints_card_le (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) :
    (exceptionalPoints S ω T).card ≤
      (Finset.univ.filter (fun z => pointDegree S ω z < T)).card +
        Fintype.card K * (deletedMarks S ω).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (deletedPoints_card_le S ω) _)

def retainedIncidence (S : Finset V) (ω : S → Projectivization K V) (z : V) : Finset (Retained S ω) :=
  Finset.univ.filter (fun a => PuncturedIncidence a.val.val z (ω a.val))

theorem incidence_not_deleted (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) (a : S) (ha : PuncturedIncidence a.val z (ω a)) :
    a ∉ deletedMarks S ω := by
  intro hdel
  apply hz
  exact Finset.mem_biUnion.mpr ⟨a,hdel,(mem_chosenLinePoints a.val z (ω a)).mpr ha.2⟩

/-- Outside the discarded geometric lines, no incidence is changed by alteration. -/
theorem retainedIncidence_card (S : Finset V) (ω : S → Projectivization K V) (z : V)
    (hz : z ∉ deletedPoints S ω) : (retainedIncidence S ω z).card = pointDegree S ω z := by
  let e : {a : Retained S ω // PuncturedIncidence a.val.val z (ω a.val)} ≃
      {a : S // PuncturedIncidence a.val z (ω a)} :=
    {toFun := fun a => ⟨a.val.val,a.property⟩
     invFun := fun a => ⟨⟨a.val,incidence_not_deleted S ω z hz a.val a.property⟩,a.property⟩
     left_inv := fun a => rfl
     right_inv := fun a => rfl}
  have h := Fintype.card_congr e
  simpa only [Fintype.card_subtype,pointDegree,retainedIncidence] using h

/-- The exact degree threshold needed for the two-block partition. -/
theorem retainedIncidence_card_ge (S : Finset V) (ω : S → Projectivization K V) (T : ℕ)
    (z : V) (hz : z ∉ exceptionalPoints S ω T) : T ≤ (retainedIncidence S ω z).card := by
  have hz' := not_or.mp ((Finset.mem_union).not.mp hz)
  rw [retainedIncidence_card S ω z hz'.2]
  have hh := hz'.1
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hh

theorem retained_card (S : Finset V) (ω : S → Projectivization K V) :
    Fintype.card (Retained S ω) = S.card - (deletedMarks S ω).card := by
  change Fintype.card {a : S // ¬ a ∈ deletedMarks S ω} = _
  rw [Fintype.card_subtype_compl]
  simp

variable [Nontrivial V] [Fintype (Projectivization K V)]

/-- A uniform expectation bound for all removed labels. -/
theorem expect_deletedMarks_le (S : Finset V) (q : ℝ)
    (hcycle : ∀ s ∈ Finset.Icc 2 50,
      (Fintype.card V : ℝ)^s * (Fintype.card K : ℝ)^s *
        (1 / Fintype.card (Projectivization K V) : ℝ)^s ≤ q^100) :
    (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ 2450*q^100 := by
  have hpoint (ω : S → Projectivization K V) : ((deletedMarks S ω).card : ℝ) ≤
      50 * ∑ s ∈ Finset.Icc 2 50, ((badCycles S (finRotate s) ω).card : ℝ) := by
    exact_mod_cast deletedMarks_card_le S ω
  calc
    _ ≤ 𝔼 ω : S → Projectivization K V,
        50 * ∑ s ∈ Finset.Icc 2 50, ((badCycles S (finRotate s) ω).card : ℝ) :=
      Finset.expect_le_expect (fun ω _ => hpoint ω)
    _ = 50 * ∑ s ∈ Finset.Icc 2 50, 𝔼 ω : S → Projectivization K V,
        ((badCycles S (finRotate s) ω).card : ℝ) := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ 50 * ∑ _s ∈ Finset.Icc 2 50, q^100 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      have hh := expect_badCycles_le (K := K) S (finRotate s)
      simp only [Fintype.card_fin] at hh
      exact hh.trans (hcycle s hs)
    _ = 2450*q^100 := by norm_num [Finset.sum_const]; ring


end Alteration
end
end DomainNonembedding.Incidence

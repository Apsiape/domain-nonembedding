import DomainNonembedding.LineFree
import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.HNNExtension

set_option autoImplicit false

namespace DomainNonembedding.GraphNormalForms
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An honest group extension, with its injection already proved. -/
structure Extension (G : Type) [Group G] where
  Carrier : Type
  [group : Group Carrier]
  embed : G →* Carrier
  injective : Function.Injective embed

attribute [instance] Extension.group

/-- Adjoin a single stable letter per whole edge group, finitely many times.
The injection is Mathlib's HNN normal form theorem at every step. -/
theorem exists_conjugators {G H E : Type} [Group G] [Group H] [Fintype E]
    (a b : E → H →* G) (ha : ∀ e, Function.Injective (a e))
    (hb : ∀ e, Function.Injective (b e)) :
    ∃ X : Extension G, ∃ t : E → X.Carrier,
      ∀ e h, t e * X.embed (a e h) * (t e)⁻¹ = X.embed (b e h) := by
  have aux : ∀ s : Finset E, ∃ X : Extension G, ∃ t : E → X.Carrier,
      ∀ e ∈ s, ∀ h, t e * X.embed (a e h) * (t e)⁻¹ = X.embed (b e h) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      let X : Extension G := @Extension.mk G _ G _ (MonoidHom.id G) (fun _ _ h => h)
      refine ⟨X, fun _ => 1, ?_⟩
      simp
    | @insert e s hnot ih =>
      obtain ⟨X,t,ht⟩ := ih
      let L := X.embed.comp (a e)
      let R := X.embed.comp (b e)
      have hL : Function.Injective L := X.injective.comp (ha e)
      have hR : Function.Injective R := X.injective.comp (hb e)
      let φ : L.range ≃* R.range :=
        (MonoidHom.ofInjective hL).symm.trans (MonoidHom.ofInjective hR)
      let K := HNNExtension X.Carrier L.range R.range φ
      let f : X.Carrier →* K := HNNExtension.of
      let τ : K := HNNExtension.t
      have new_relation (h : H) : τ * f (L h) * τ⁻¹ = f (R h) := by
        have heq : (φ ((MonoidHom.ofInjective hL) h) : X.Carrier) = R h := by
          change R ((MonoidHom.ofInjective hL).symm ((MonoidHom.ofInjective hL) h)) = R h
          rw [MulEquiv.symm_apply_apply]
        have hh := (HNNExtension.equiv_eq_conj (φ := φ)
          ((MonoidHom.ofInjective hL) h)).symm
        rw [heq] at hh
        exact hh
      let Y : Extension G := @Extension.mk G _ K _ (f.comp X.embed)
        ((HNNExtension.of_injective φ).comp X.injective)
      refine ⟨Y, fun j => if j = e then τ else f (t j), ?_⟩
      intro j hj h
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa [Y, L, R] using new_relation h
      · have hje : j ≠ e := by intro he; subst j; exact hnot hj
        have hh := congrArg f (ht j hj h)
        simpa [Y, hje] using hh
  obtain ⟨X,t,ht⟩ := aux Finset.univ
  exact ⟨X,t,fun e h => ht e (Finset.mem_univ e) h⟩

open PaperData
variable {p : ℕ} (d : PaperData p) (hd : d.Admissible)

abbrev Central := FreeGroup (d.Label × Entry)

def centralLine (i : d.Label) : FreeGroup Entry →* Central d :=
  FreeGroup.map fun q => (i,q)

theorem centralLine_injective (i : d.Label) : Function.Injective (centralLine d i) :=
  FreeGroup.map_injective (by intro a b h; exact (Prod.mk.inj h).2)

def vertex : Option Arrangement → Type
  | none => Central d
  | some _ => d.BaseGroup

instance vertexGroup (v : Option Arrangement) : Group (vertex d v) := by
  cases v <;> dsimp [vertex] <;> infer_instance

def treeMap : (v : Option Arrangement) → FreeGroup Entry →* vertex d v
  | none => centralLine d d.distinguishedLine
  | some π => (d.lineHom d.distinguishedLine).comp (FreeGroup.map π.symm)

include hd in
theorem treeMap_injective (v : Option Arrangement) : Function.Injective (treeMap d v) := by
  cases v with
  | none => exact centralLine_injective d d.distinguishedLine
  | some π =>
    exact (LineFree.line_free d hd d.distinguishedLine).comp
      (FreeGroup.map_injective π.symm.injective)

abbrev Tree := Monoid.PushoutI (treeMap d)

def central : Central d →* Tree d := Monoid.PushoutI.of (φ := treeMap d) none
def copy (π : Arrangement) : d.BaseGroup →* Tree d := Monoid.PushoutI.of (φ := treeMap d) (some π)

include hd in
theorem central_injective_tree : Function.Injective (central d) :=
  Monoid.PushoutI.of_injective (treeMap_injective d hd) none

include hd in
theorem copy_injective_tree (π : Arrangement) : Function.Injective (copy d π) :=
  Monoid.PushoutI.of_injective (treeMap_injective d hd) (some π)

theorem tree_relation (π : Arrangement) (q : Entry) :
    copy d π (d.lineHom d.distinguishedLine (FreeGroup.of q)) =
      central d (FreeGroup.of (d.distinguishedLine,π q)) := by
  have h₁ := Monoid.PushoutI.of_apply_eq_base (treeMap d) (some π) (FreeGroup.of (π q))
  have h₂ := Monoid.PushoutI.of_apply_eq_base (treeMap d) none (FreeGroup.of (π q))
  change copy d π (d.lineHom d.distinguishedLine
    (FreeGroup.map π.symm (FreeGroup.of (π q)))) = _ at h₁
  change central d (FreeGroup.map (fun q => (d.distinguishedLine,q))
    (FreeGroup.of (π q))) = _ at h₂
  rw [FreeGroup.map.of, Equiv.symm_apply_apply] at h₁
  rw [FreeGroup.map.of] at h₂
  exact h₁.trans h₂.symm

abbrev NonTreeEdge := Arrangement × {i : d.Label // i ≠ d.distinguishedLine}

def leftMap (e : NonTreeEdge d) : FreeGroup Entry →* Tree d :=
  (copy d e.1).comp (d.lineHom e.2.val)

def rightMap (e : NonTreeEdge d) : FreeGroup Entry →* Tree d :=
  (central d).comp ((centralLine d e.2.val).comp (FreeGroup.map e.1))

include hd in
theorem leftMap_injective (e : NonTreeEdge d) : Function.Injective (leftMap d e) :=
  (copy_injective_tree d hd e.1).comp (LineFree.line_free d hd e.2.val)

include hd in
theorem rightMap_injective (e : NonTreeEdge d) : Function.Injective (rightMap d e) :=
  (central_injective_tree d hd).comp
    ((centralLine_injective d e.2.val).comp (FreeGroup.map_injective e.1.injective))

def realization : Extension (Tree d) :=
  Classical.choose (exists_conjugators (leftMap d) (rightMap d)
    (leftMap_injective d hd) (rightMap_injective d hd))

def letters : NonTreeEdge d → (realization d hd).Carrier :=
  Classical.choose (Classical.choose_spec (exists_conjugators (leftMap d) (rightMap d)
    (leftMap_injective d hd) (rightMap_injective d hd)))

theorem letters_relation (e : NonTreeEdge d) (g : FreeGroup Entry) :
    letters d hd e * (realization d hd).embed (leftMap d e g) * (letters d hd e)⁻¹ =
      (realization d hd).embed (rightMap d e g) :=
  Classical.choose_spec (Classical.choose_spec (exists_conjugators (leftMap d) (rightMap d)
    (leftMap_injective d hd) (rightMap_injective d hd))) e g

def stable (π : Arrangement) (i : d.Label) : (realization d hd).Carrier :=
  if h : i = d.distinguishedLine then 1 else letters d hd (π,⟨i,h⟩)

theorem edge_relation (π : Arrangement) (i : d.Label) (q : Entry) :
    stable d hd π i * (realization d hd).embed (copy d π (d.lineHom i (FreeGroup.of q))) *
        (stable d hd π i)⁻¹ =
      (realization d hd).embed (central d (FreeGroup.of (i,π q))) := by
  by_cases hi : i = d.distinguishedLine
  · subst i
    simpa [stable] using congrArg (realization d hd).embed (tree_relation d π q)
  · have h := letters_relation d hd (π,⟨i,hi⟩) (FreeGroup.of q)
    change letters d hd (π,⟨i,hi⟩) *
        (realization d hd).embed (copy d π (d.lineHom i (FreeGroup.of q))) *
          (letters d hd (π,⟨i,hi⟩))⁻¹ =
      (realization d hd).embed (central d
        (FreeGroup.map (fun q => (i,q)) (FreeGroup.map π (FreeGroup.of q)))) at h
    rw [FreeGroup.map.of, FreeGroup.map.of] at h
    simpa only [stable, dif_neg hi] using h

def generatorImage : d.GammaGenerator → (realization d hd).Carrier
  | .central i q => (realization d hd).embed (central d (FreeGroup.of (i,q)))
  | .copy π e => (realization d hd).embed (copy d π (PresentedGroup.of e))
  | .stable π i => stable d hd π i

theorem generatorImage_copyWord (π : Arrangement) (w : d.BaseWord) :
    FreeGroup.lift (generatorImage d hd) (d.copyWord π w) =
      (realization d hd).embed (copy d π (PresentedGroup.mk d.baseRelators w)) := by
  have h : (FreeGroup.lift (generatorImage d hd)).comp (d.copyWord π) =
      (realization d hd).embed.comp ((copy d π).comp (PresentedGroup.mk d.baseRelators)) := by
    ext e
    simp only [MonoidHom.comp_apply, copyWord, FreeGroup.lift_apply_of, generatorImage]
    rfl
  exact DFunLike.congr_fun h w

theorem generatorImage_relators (w : d.GammaWord) (hw : w ∈ d.gammaRelators) :
    FreeGroup.lift (generatorImage d hd) w = 1 := by
  rcases hw with ⟨π,v,hv,rfl⟩ | ⟨π,i,q,rfl⟩ | ⟨π,rfl⟩
  · rw [generatorImage_copyWord, PresentedGroup.one_of_mem hv, map_one, map_one]
  · simp only [gluingWord, stableWord, map_mul, map_inv, FreeGroup.lift_apply_of,
      generatorImage_copyWord, generatorImage]
    have h := edge_relation d hd π i q
    simp only [lineHom, FreeGroup.lift_apply_of] at h
    rw [h]
    exact mul_inv_cancel _
  · simp [stableWord, generatorImage, stable]

/-- Map from the exact frozen quotient to the pushout/HNN construction. -/
def toRealization : d.Gamma →* (realization d hd).Carrier :=
  PresentedGroup.toGroup (generatorImage_relators d hd)

theorem central_composition : (toRealization d hd).comp d.centralHom =
    (realization d hd).embed.comp (central d) := by
  ext q
  simp only [MonoidHom.comp_apply, centralHom, FreeGroup.lift_apply_of,
    toRealization, PresentedGroup.toGroup.of, generatorImage]

theorem copy_composition (π : Arrangement) : (toRealization d hd).comp (d.copiedHom π) =
    (realization d hd).embed.comp (copy d π) := by
  ext e
  change toRealization d hd (PresentedGroup.mk d.gammaRelators (d.copyWord π (FreeGroup.of e))) = _
  simp only [copyWord, FreeGroup.lift_apply_of]
  exact PresentedGroup.toGroup.of _

include hd in
theorem central_injective : Function.Injective d.centralHom := by
  have h : Function.Injective ((toRealization d hd).comp d.centralHom) := by
    rw [central_composition]
    exact (realization d hd).injective.comp (central_injective_tree d hd)
  intro a b hab
  exact h (congrArg (toRealization d hd) hab)

include hd in
theorem copied_injective (π : Arrangement) : Function.Injective (d.copiedHom π) := by
  have h : Function.Injective ((toRealization d hd).comp (d.copiedHom π)) := by
    rw [copy_composition]
    exact (realization d hd).injective.comp (copy_injective_tree d hd π)
  intro a b hab
  exact h (congrArg (toRealization d hd) hab)

end
end DomainNonembedding.GraphNormalForms

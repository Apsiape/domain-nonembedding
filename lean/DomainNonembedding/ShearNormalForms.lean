import DomainNonembedding.Headline

set_option autoImplicit false

namespace DomainNonembedding.ShearNormalForms
noncomputable section
open PaperData
attribute [local instance] Classical.propDecidable Classical.decEq

variable {p : ℕ} (d : PaperData p) (hd : d.Admissible)

abbrev Ambient := d.BaseGroup × Multiplicative ℤ
abbrev Edge := FreeGroup Entry × Multiplicative ℤ

def degree : FreeGroup Entry →* Multiplicative ℤ :=
  FreeGroup.lift fun q => if q.1 = q.2 then Multiplicative.ofAdd 1 else 1

def base : d.BaseGroup →* Ambient d where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := rfl

def s : Ambient d := (1,Multiplicative.ofAdd 1)

def leftMap (i : d.Label) : Edge →* Ambient d where
  toFun w := (d.lineHom i w.1,w.2)
  map_one' := by simp
  map_mul' _ _ := by simp

def rightMap (i : d.Label) : Edge →* Ambient d where
  toFun w := (d.lineHom i w.1,degree w.1*w.2)
  map_one' := by simp
  map_mul' a b := by
    apply Prod.ext
    · simp
    · simp [mul_assoc, mul_left_comm, mul_comm]

include hd in
theorem leftMap_injective (i : d.Label) : Function.Injective (leftMap d i) := by
  intro a b h
  apply Prod.ext
  · exact LineFree.line_free d hd i (congrArg Prod.fst h)
  · exact congrArg (fun g : Ambient d => g.2) h

include hd in
theorem rightMap_injective (i : d.Label) : Function.Injective (rightMap d i) := by
  intro a b h
  have hab : a.1 = b.1 := LineFree.line_free d hd i (congrArg Prod.fst h)
  refine Prod.ext hab ?_
  have hs := congrArg Prod.snd h
  change degree a.1*a.2 = degree b.1*b.2 at hs
  rw [hab] at hs
  exact mul_left_cancel hs

def realization : GraphNormalForms.Extension (Ambient d) :=
  Classical.choose (GraphNormalForms.exists_conjugators (leftMap d) (rightMap d)
    (leftMap_injective d hd) (rightMap_injective d hd))

def letters : d.Label → (realization d hd).Carrier :=
  Classical.choose (Classical.choose_spec (GraphNormalForms.exists_conjugators
    (leftMap d) (rightMap d) (leftMap_injective d hd) (rightMap_injective d hd)))

theorem letters_relation (i : d.Label) (w : Edge) :
    letters d hd i * (realization d hd).embed (leftMap d i w) * (letters d hd i)⁻¹ =
      (realization d hd).embed (rightMap d i w) :=
  Classical.choose_spec (Classical.choose_spec (GraphNormalForms.exists_conjugators
    (leftMap d) (rightMap d) (leftMap_injective d hd) (rightMap_injective d hd))) i w

theorem s_commutes_base (g : d.BaseGroup) : s d * base d g = base d g * s d := by
  apply Prod.ext <;> simp [s,base]

theorem letters_commute_s (i : d.Label) :
    (realization d hd).embed (s d) * letters d hd i =
      letters d hd i * (realization d hd).embed (s d) := by
  have h := letters_relation d hd i (1,Multiplicative.ofAdd 1)
  have h' : letters d hd i * (realization d hd).embed (s d) * (letters d hd i)⁻¹ =
      (realization d hd).embed (s d) := by
    simpa [leftMap,rightMap,s] using h
  exact (mul_inv_eq_iff_eq_mul.mp h').symm

theorem line_relation (i : d.Label) (q : Entry) :
    letters d hd i * (realization d hd).embed (base d (d.lineHom i (FreeGroup.of q))) *
      (letters d hd i)⁻¹ =
      (realization d hd).embed (s d) ^ (if q.1 = q.2 then 1 else 0) *
        (realization d hd).embed (base d (d.lineHom i (FreeGroup.of q))) := by
  have h := letters_relation d hd i (FreeGroup.of q,1)
  have hr : rightMap d i (FreeGroup.of q,1) =
      s d ^ (if q.1 = q.2 then 1 else 0) * base d (d.lineHom i (FreeGroup.of q)) := by
    apply Prod.ext <;> by_cases he : q.1 = q.2 <;> simp [rightMap,degree,s,base,he]
  rw [hr,map_mul,map_pow] at h
  exact h

def generatorImage : d.ShearGenerator → (realization d hd).Carrier
  | .base e => (realization d hd).embed (base d (PresentedGroup.of e))
  | .s _ => (realization d hd).embed (s d)
  | .gamma i => letters d hd i

theorem generatorImage_baseWord (w : d.BaseWord) :
    FreeGroup.lift (generatorImage d hd) (d.shearBaseWord w) =
      (realization d hd).embed (base d (PresentedGroup.mk d.baseRelators w)) := by
  have h : (FreeGroup.lift (generatorImage d hd)).comp d.shearBaseWord =
      (realization d hd).embed.comp ((base d).comp (PresentedGroup.mk d.baseRelators)) := by
    ext e
    simp only [MonoidHom.comp_apply,shearBaseWord,FreeGroup.lift_apply_of,generatorImage]
    rfl
  exact DFunLike.congr_fun h w

theorem generatorImage_relators (w : d.ShearWord) (hw : w ∈ d.shearRelators) :
    FreeGroup.lift (generatorImage d hd) w = 1 := by
  rcases hw with ⟨v,hv,rfl⟩ | ⟨i,rfl⟩ | ⟨i,q,rfl⟩ | ⟨i,q,rfl⟩
  · rw [generatorImage_baseWord,PresentedGroup.one_of_mem hv,map_one,map_one]
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of,generatorImage]
    rw [letters_commute_s]
    group
  · simp only [map_mul,map_inv,FreeGroup.lift_apply_of,generatorImage_baseWord,generatorImage]
    have h := congrArg (realization d hd).embed
      (s_commutes_base d (PresentedGroup.mk d.baseRelators (d.lineWord i q)))
    simp only [map_mul] at h
    rw [h]
    group
  · simp only [map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,generatorImage_baseWord,generatorImage]
    have h := line_relation d hd i q
    simp only [lineHom,FreeGroup.lift_apply_of] at h
    rw [h]
    exact mul_inv_cancel _

def toRealization : d.Shear →* (realization d hd).Carrier :=
  PresentedGroup.toGroup (generatorImage_relators d hd)

include hd in
theorem s_ne_one (i : d.Label) :
    (PresentedGroup.of (.s i) : d.Shear) ≠ 1 := by
  intro h
  have h' := congrArg (toRealization d hd) h
  simp only [toRealization,PresentedGroup.toGroup.of,generatorImage,map_one] at h'
  have hs : s d = 1 := (realization d hd).injective (h'.trans (realization d hd).embed.map_one.symm)
  have hz := congrArg (fun g : Ambient d => Multiplicative.toAdd g.2) hs
  exact (by norm_num : (1 : ℤ) ≠ 0) hz

end
end DomainNonembedding.ShearNormalForms

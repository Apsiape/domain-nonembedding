import DomainNonembedding.CollapsedLines

set_option autoImplicit false

namespace DomainNonembedding.LineFree
open OAI.Release075
open PaperData
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {p : ℕ} (d : PaperData p) (hd : d.Admissible)

abbrev Auxiliary := (CollapsedLines.presentation d hd).GroupType

def rawX (i : d.Label) (u v : Fin rankSize) : Auxiliary d hd :=
  (CollapsedLines.presentation d hd).x i u v

def vPath (u : Fin rankSize) : Auxiliary d hd :=
  rawX d hd d.distinguishedLine zeroIndex zeroIndex *
    (rawX d hd d.distinguishedLine u zeroIndex)⁻¹

def wPath (v : Fin rankSize) : Auxiliary d hd :=
  rawX d hd d.distinguishedLine zeroIndex v

def oPath (b : d.Block) : Auxiliary d hd :=
  ((CollapsedLines.presentation d hd).l b zeroIndex 0)⁻¹

def edgeImage : d.BaseGenerator → Auxiliary d hd
  | .x i u v => vPath d hd u * rawX d hd i u v * (wPath d hd v)⁻¹
  | .left b u j => oPath d hd b * (CollapsedLines.presentation d hd).l b u j *
      (vPath d hd u)⁻¹
  | .right b v k => oPath d hd b * (CollapsedLines.presentation d hd).rr b v k *
      (wPath d hd v)⁻¹

theorem edgeImage_relators (w : d.BaseWord) (hw : w ∈ d.baseRelators) :
    FreeGroup.lift (edgeImage d hd) w = 1 := by
  rcases hw with ⟨b,i,u,v,rfl⟩ | ⟨e,he,rfl⟩
  · simp only [triangleWord, xWord, map_mul, map_inv, FreeGroup.lift_apply_of, edgeImage]
    have ht := (CollapsedLines.presentation d hd).triangle_relation b i u v
    change rawX d hd i.val u v =
      ((CollapsedLines.presentation d hd).l b u ((d.coordinates b i).1 +
        (v.val : ZMod (d.blockS b))))⁻¹ *
      (CollapsedLines.presentation d hd).rr b v ((d.coordinates b i).2 +
        (u.val : ZMod (d.blockT b))) at ht
    rw [ht]
    group
  · simp only [FreeGroup.lift_apply_of]
    cases e with
    | x i u v =>
      obtain ⟨rfl,hu | hv⟩ := he
      · have hu' : u = zeroIndex := Fin.ext hu
        subst u
        simp [edgeImage, vPath, wPath]
      · have hv' : v = zeroIndex := Fin.ext hv
        subst v
        simp [edgeImage, vPath, wPath, mul_assoc]
    | left b u j =>
      obtain ⟨hu,rfl⟩ := he
      have hu' : u = zeroIndex := Fin.ext hu
      subst u
      simp [edgeImage, oPath, vPath]
      exact inv_mul_cancel _
    | right b v k => exact he.elim

/-- A map out of the actual frozen presentation; every tree relator is checked. -/
def toAuxiliary : d.BaseGroup →* Auxiliary d hd :=
  PresentedGroup.toGroup (edgeImage_relators d hd)

theorem toAuxiliary_mk_of (e : d.BaseGenerator) :
    toAuxiliary d hd (PresentedGroup.mk d.baseRelators (FreeGroup.of e)) =
      edgeImage d hd e :=
  PresentedGroup.toGroup.of _

abbrev FullEntry := {q : Fin rankSize × Fin rankSize // q ≠ (zeroIndex, zeroIndex)}

def rowEntry (q : Entry) : FullEntry :=
  ⟨(interior q.1, zeroIndex), by
    intro h
    have hh := congrArg (fun a : Fin rankSize × Fin rankSize => a.1.val) h
    simp [PaperData.interior, zeroIndex] at hh⟩

def colEntry (q : Entry) : FullEntry :=
  ⟨(zeroIndex, interior q.2), by
    intro h
    have hh := congrArg (fun a : Fin rankSize × Fin rankSize => a.2.val) h
    simp [PaperData.interior, zeroIndex] at hh⟩

def innerEntry (q : Entry) : FullEntry :=
  ⟨(interior q.1, interior q.2), by
    intro h
    have hh := congrArg (fun a : Fin rankSize × Fin rankSize => a.1.val) h
    simp [PaperData.interior, zeroIndex] at hh⟩

def normalizedBasis : FreeGroup Entry →* FreeGroup FullEntry :=
  FreeGroup.lift fun q =>
    (FreeGroup.of (rowEntry q))⁻¹ * FreeGroup.of (innerEntry q) *
      (FreeGroup.of (colEntry q))⁻¹

def retractLetter (a : FullEntry) : FreeGroup Entry :=
  if h : a.val.1.val = 0 ∨ a.val.2.val = 0 then 1 else
    FreeGroup.of (⟨a.val.1.val - 1, by have := a.val.1.isLt; omega⟩,
      ⟨a.val.2.val - 1, by have := a.val.2.isLt; omega⟩)

theorem retract_row (q : Entry) : retractLetter (rowEntry q) = 1 := by
  simp [retractLetter, rowEntry, zeroIndex]

theorem retract_col (q : Entry) : retractLetter (colEntry q) = 1 := by
  simp [retractLetter, colEntry, zeroIndex]

theorem retract_inner (q : Entry) : retractLetter (innerEntry q) = FreeGroup.of q := by
  simp [retractLetter, innerEntry, PaperData.interior]

theorem normalizedBasis_injective : Function.Injective normalizedBasis := by
  have h : (FreeGroup.lift retractLetter).comp normalizedBasis = MonoidHom.id _ := by
    ext q
    simp [normalizedBasis, retract_row, retract_col, retract_inner]
  exact Function.LeftInverse.injective (fun g => DFunLike.congr_fun h g)

def fullLine (i : d.Label) : FreeGroup FullEntry →* Auxiliary d hd :=
  FreeGroup.lift fun a => rawX d hd i a.val.1 a.val.2 *
    (rawX d hd i zeroIndex zeroIndex)⁻¹

theorem fullLine_injective (i : d.Label) : Function.Injective (fullLine d hd i) :=
  CollapsedLines.lineSubgroup_free d hd i

def normalizedImage (i : d.Label) : FreeGroup Entry →* Auxiliary d hd :=
  (fullLine d hd i).comp normalizedBasis

theorem normalizedImage_injective (i : d.Label) :
    Function.Injective (normalizedImage d hd i) :=
  (fullLine_injective d hd i).comp normalizedBasis_injective

theorem toAuxiliary_lineHom (i : d.Label) (g : FreeGroup Entry) :
    toAuxiliary d hd (d.lineHom i g) =
      (wPath d hd zeroIndex * (rawX d hd i zeroIndex zeroIndex)⁻¹) *
        normalizedImage d hd i g *
      (wPath d hd zeroIndex * (rawX d hd i zeroIndex zeroIndex)⁻¹)⁻¹ := by
  let c := wPath d hd zeroIndex * (rawX d hd i zeroIndex zeroIndex)⁻¹
  have h : (toAuxiliary d hd).comp (d.lineHom i) =
      (MulAut.conj c).toMonoidHom.comp (normalizedImage d hd i) := by
    ext q
    simp only [MonoidHom.comp_apply, lineHom, FreeGroup.lift_apply_of,
      lineWord, map_mul, map_inv, xWord, toAuxiliary_mk_of,
      edgeImage, normalizedImage, fullLine,
      normalizedBasis, rowEntry, colEntry, innerEntry,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    dsimp [c]
    group
  exact DFunLike.congr_fun h g

include hd in
/-- Exact replacement for the frozen `line_free` target, for every admissible datum. -/
theorem line_free (i : d.Label) : Function.Injective (d.lineHom i) := by
  intro a b hab
  apply normalizedImage_injective d hd i
  have h := congrArg (toAuxiliary d hd) hab
  rw [toAuxiliary_lineHom, toAuxiliary_lineHom] at h
  exact mul_left_cancel (mul_right_cancel h)

end
end DomainNonembedding.LineFree

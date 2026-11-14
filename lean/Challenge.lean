/- Mathlib-only comparator challenge. The transparent frozen PaperData definitions
are copied verbatim except imports, with their original defining module name.
The three intentional holes express existence plus all-admissible, all-field
nonembedding for both presentations. No project proof is imported. -/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

set_option autoImplicit false
run_cmd Lean.modifyEnv (fun env => env.setMainModule `DomainNonembedding.PaperData)
run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})
-- BEGIN verbatim PaperData (excluding import lines)

set_option autoImplicit false

/-!
Definitions frozen in November 2026 after an independent blind fidelity read;
the theorem obligations are stated in Statements.lean and proved in Main.lean.
Every admissible datum, including the paper's, is covered by the target.
See BLUEPRINT.md for data choices; DivisionRingRank.lean proves the bridge
from reused left row rank to the paper's right column rank.
-/

namespace DomainNonembedding
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev dimension : ℕ := 103
abbrev girthBound : ℕ := 100
def rankSize : ℕ := 100 * 2060 ^ 103
def fieldThreshold : ℕ := 320000 * 2060 ^ 309

/-- Raw finite data only. Incidence/freeness/rank conclusions are not fields. -/
structure PaperData (p : ℕ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  large : fieldThreshold < p ^ exponent
  Scalar : Type
  [scalarField : Field Scalar]
  [scalarFintype : Fintype Scalar]
  [scalarChar : CharP Scalar p]
  number : Scalar ≃ Fin (p ^ exponent)
  lineCount : ℕ
  mark : Fin lineCount → Fin dimension → Scalar
  direction : Fin lineCount → Fin dimension → Scalar
  exceptional : Finset (Fin dimension → Scalar)
  blockCount : ℕ
  blockPoint : Fin blockCount → Fin dimension → Scalar
  blockS : Fin blockCount → ℕ
  blockT : Fin blockCount → ℕ
  blockLabels : Fin blockCount → Finset (Fin lineCount)
  coordinates : ∀ b, {i // i ∈ blockLabels b} ≃ ZMod (blockS b) × ZMod (blockT b)
  distinguishedLine : Fin lineCount
  distinguishedBlock : Fin blockCount

attribute [instance] PaperData.scalarField PaperData.scalarFintype PaperData.scalarChar

namespace PaperData
variable {p : ℕ} (d : PaperData p)
abbrev Point := Fin dimension → d.Scalar
abbrev Label := Fin d.lineCount
abbrev Block := Fin d.blockCount
abbrev Entry := Fin (rankSize - 1) × Fin (rankSize - 1)
abbrev Arrangement := Equiv.Perm (Entry)

noncomputable def grid : Finset d.Scalar :=
  Finset.univ.filter fun x => (d.number x).val < p ^ d.exponent / (10 * dimension)

/-- A punctured affine line, with a nonzero affine parameter. -/
def Incident (z : d.Point) (i : d.Label) : Prop :=
  ∃ t : d.Scalar, t ≠ 0 ∧ ∀ j, z j = d.mark i j + t * d.direction i j

noncomputable def incidences (z : d.Point) : Finset d.Label :=
  Finset.univ.filter (d.Incident z)

noncomputable def incidenceGraph : SimpleGraph (d.Point ⊕ d.Label) where
  Adj x y := match x, y with
    | .inl z, .inr i => d.Incident z i
    | .inr i, .inl z => d.Incident z i
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- Precisely the incidence and block conditions needed from the paper.
No line freeness or rank theorem is included in this predicate. -/
def Admissible : Prop :=
  Function.Injective d.mark ∧
  (∀ i j, d.mark i j ∈ d.grid) ∧
  (∀ i, d.direction i ≠ 0) ∧
  (100 : ℕ∞) < d.incidenceGraph.egirth ∧
  (∀ z, z ∉ d.exceptional → 4 * rankSize ^ 2 ≤ (d.incidences z).card) ∧
  (p ^ d.exponent) ^ dimension ≤ 2 * 2060 ^ 103 * d.lineCount ∧
  2 * rankSize * d.exceptional.card ≤ (p ^ d.exponent) ^ dimension ∧
  (∀ b, rankSize ≤ d.blockS b ∧ rankSize ≤ d.blockT b ∧
    d.blockPoint b ∉ d.exceptional ∧
    d.blockLabels b ⊆ d.incidences (d.blockPoint b)) ∧
  (∀ z, z ∉ d.exceptional →
    ∃ b₀ b₁ : d.Block, b₀ ≠ b₁ ∧ d.blockPoint b₀ = z ∧ d.blockPoint b₁ = z ∧
      Disjoint (d.blockLabels b₀) (d.blockLabels b₁) ∧
      d.blockLabels b₀ ∪ d.blockLabels b₁ = d.incidences z ∧
      ∀ b, d.blockPoint b = z → b = b₀ ∨ b = b₁)

/-- Edges are all displayed orientations of the split triangle complex. -/
inductive BaseGenerator where
  | x (i : d.Label) (u v : Fin rankSize)
  | left (b : d.Block) (u : Fin rankSize) (j : ZMod (d.blockS b))
  | right (b : d.Block) (v : Fin rankSize) (k : ZMod (d.blockT b))

abbrev BaseWord := FreeGroup d.BaseGenerator

def xWord (i : d.Label) (u v : Fin rankSize) : d.BaseWord :=
  FreeGroup.of (.x i u v)

def triangleWord (b : d.Block) (i : {i // i ∈ d.blockLabels b})
    (u v : Fin rankSize) : d.BaseWord :=
  FreeGroup.of (.left b u ((d.coordinates b i).1 + (v.val : ZMod (d.blockS b)))) *
    d.xWord i.val u v *
    (FreeGroup.of (.right b v ((d.coordinates b i).2 + (u.val : ZMod (d.blockT b)))))⁻¹

/-- Explicit spanning tree: row/column zero at i*, and one L edge per apex. -/
def TreeEdge : d.BaseGenerator → Prop
  | .x i u v => i = d.distinguishedLine ∧ (u.val = 0 ∨ v.val = 0)
  | .left _ u j => u.val = 0 ∧ j = 0
  | .right _ _ _ => False

def baseRelators : Set d.BaseWord :=
  {w | (∃ b i u v, w = d.triangleWord b i u v) ∨
    ∃ e, d.TreeEdge e ∧ w = FreeGroup.of e}

abbrev BaseGroup := PresentedGroup d.baseRelators

def x (i : d.Label) (u v : Fin rankSize) : d.BaseGroup :=
  PresentedGroup.of (.x i u v)

/-- Paper eq:free-generators; zero is represented with an explicit positive bound. -/
def zeroIndex : Fin rankSize := ⟨0, by unfold rankSize; positivity⟩
def interior (u : Fin (rankSize - 1)) : Fin rankSize :=
  ⟨u.val + 1, by
    have hu := u.isLt
    have hr : 0 < rankSize := by unfold rankSize; positivity
    omega⟩

def lineWord (i : d.Label) (q : Entry) : d.BaseWord :=
  (d.xWord i (interior q.1) zeroIndex)⁻¹ *
    d.xWord i (interior q.1) (interior q.2) *
    (d.xWord i zeroIndex (interior q.2))⁻¹ * d.xWord i zeroIndex zeroIndex

def lineHom (i : d.Label) : FreeGroup Entry →* d.BaseGroup :=
  FreeGroup.lift fun q => PresentedGroup.mk d.baseRelators (d.lineWord i q)

noncomputable def lineMatrix {R : Type*} [Ring R] (χ : d.BaseGroup →* R) (i : d.Label) :
    Matrix (Fin rankSize) (Fin rankSize) R := fun u v => χ (d.x i u v)

/-- Central free basis, copied base edges, and all graph-edge stable letters. -/
inductive GammaGenerator where
  | central (i : d.Label) (q : Entry)
  | copy (π : Arrangement) (e : d.BaseGenerator)
  | stable (π : Arrangement) (i : d.Label)

abbrev GammaWord := FreeGroup d.GammaGenerator

def copyWord (π : Arrangement) : d.BaseWord →* d.GammaWord :=
  FreeGroup.lift fun e => FreeGroup.of (.copy π e)

def stableWord (π : Arrangement) (i : d.Label) : d.GammaWord :=
  FreeGroup.of (.stable π i)

def gluingWord (π : Arrangement) (i : d.Label) (q : Entry) : d.GammaWord :=
  d.stableWord π i * d.copyWord π (d.lineWord i q) * (d.stableWord π i)⁻¹ *
    (FreeGroup.of (.central i (π q)))⁻¹

def gammaRelators : Set d.GammaWord :=
  {w | (∃ π v, v ∈ d.baseRelators ∧ w = d.copyWord π v) ∨
    (∃ π i q, w = d.gluingWord π i q) ∨
    ∃ π, w = d.stableWord π d.distinguishedLine}

/-- Explicit graph-of-groups quotient, with all parallel edges retained. -/
abbrev Gamma := PresentedGroup d.gammaRelators

def copiedHom (π : Arrangement) : d.BaseGroup →* d.Gamma :=
  PresentedGroup.map (d.copyWord π) (by
    intro v hv
    exact Or.inl ⟨π, v, hv, rfl⟩)

def centralHom : FreeGroup (d.Label × Entry) →* d.Gamma :=
  FreeGroup.lift fun q => PresentedGroup.of (.central q.1 q.2)

/-- The shear branch adds the paper's two generators for each line. -/
inductive ShearGenerator where
  | base (e : d.BaseGenerator)
  | s (i : d.Label)
  | gamma (i : d.Label)

abbrev ShearWord := FreeGroup d.ShearGenerator

def shearBaseWord : d.BaseWord →* d.ShearWord :=
  FreeGroup.lift fun e => FreeGroup.of (.base e)

def shearRelators : Set d.ShearWord :=
  {w | (∃ v, v ∈ d.baseRelators ∧ w = d.shearBaseWord v) ∨
    (∃ i, w = FreeGroup.of (.s i) * FreeGroup.of (.gamma i) *
      (FreeGroup.of (.s i))⁻¹ * (FreeGroup.of (.gamma i))⁻¹) ∨
    (∃ i q, w = FreeGroup.of (.s i) * d.shearBaseWord (d.lineWord i q) *
      (FreeGroup.of (.s i))⁻¹ * (d.shearBaseWord (d.lineWord i q))⁻¹) ∨
    ∃ i q, w = FreeGroup.of (.gamma i) * d.shearBaseWord (d.lineWord i q) *
      (FreeGroup.of (.gamma i))⁻¹ *
      (FreeGroup.of (.s i) ^ (if q.1 = q.2 then 1 else 0) *
        d.shearBaseWord (d.lineWord i q))⁻¹}

abbrev Shear := PresentedGroup d.shearRelators

/-- Actual product Lagrange evaluations, not certificate coefficients as an input. -/
noncomputable def lagrange (i : d.Label) (z : d.Point) : d.Scalar :=
  ∏ j, ∏ σ ∈ d.grid.erase (d.mark i j), (z j - σ) / (d.mark i j - σ)

end PaperData

end DomainNonembedding
-- END verbatim PaperData
run_cmd Lean.modifyEnv (fun env => env.setMainModule `Challenge)
namespace DomainNonembedding.Release

theorem paperData_exists (p : ℕ) [Fact p.Prime] :
    ∃ d : PaperData p, d.Admissible := by
  sorry

theorem nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Gamma →+* D) :
    ¬ Function.Injective φ := by
  sorry

theorem shear_nonembedding_data {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) (K : Type*) [Field K] [CharP K p]
    {D : Type*} [DivisionRing D] (φ : MonoidAlgebra K d.Shear →+* D) :
    ¬ Function.Injective φ := by
  sorry

end DomainNonembedding.Release

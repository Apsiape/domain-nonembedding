import DomainNonembedding.PaperData
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.Ribbons
import FiniteLean.GroupTheory.OAI.GroupTheory.Hyperbolic.BasedWords
import NonSofic.LineFreeWord

set_option autoImplicit false

/-! Auxiliary three-vertex presentation for proving freeness of the frozen
split presentation. This is not a replacement definition of the base group.
The link/filling arguments adapt the byte-preserved OAI and NonSofic proofs
to the actual dimension-103 data over an arbitrary finite extension field. -/
namespace DomainNonembedding.CollapsedLines
open OAI.Release075
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {p : ℕ} (d : PaperData p) (hd : d.Admissible)
include hd

def block (b : d.Block) : CartesianBlock d.Label rankSize where
  s := d.blockS b
  t := d.blockT b
  hs := (hd.2.2.2.2.2.2.2.1 b).1
  ht := (hd.2.2.2.2.2.2.2.1 b).2.1
  spos := lt_of_lt_of_le (by unfold rankSize; positivity) (hd.2.2.2.2.2.2.2.1 b).1
  tpos := lt_of_lt_of_le (by unfold rankSize; positivity) (hd.2.2.2.2.2.2.2.1 b).2.1
  labels := d.blockLabels b
  coordinates := d.coordinates b

def presentation : BlockPresentation d.Label d.Block rankSize where
  block := block d hd
  baseBlock := d.distinguishedBlock
  baseIndex := PaperData.zeroIndex

theorem block_incident (b : d.Block) (i : d.Label) (hi : i ∈ d.blockLabels b) :
    i ∈ d.incidences (d.blockPoint b) :=
  (hd.2.2.2.2.2.2.2.1 b).2.2.2 hi

theorem block_unique (b c : d.Block) (i : d.Label)
    (hz : d.blockPoint b = d.blockPoint c)
    (hi : i ∈ d.blockLabels b) (hi' : i ∈ d.blockLabels c) : b = c := by
  obtain ⟨b₀,b₁,hne,h₀,h₁,hdisj,hcover,honly⟩ :=
    hd.2.2.2.2.2.2.2.2 (d.blockPoint b) (hd.2.2.2.2.2.2.2.1 b).2.2.1
  rcases honly b rfl with hb | hb <;> rcases honly c hz.symm with hc | hc
  · exact hb.trans hc.symm
  · subst b; subst c
    exact ((Finset.disjoint_left.mp hdisj) hi hi').elim
  · subst b; subst c
    exact ((Finset.disjoint_left.mp hdisj) hi' hi).elim
  · exact hb.trans hc.symm

def vShift : ShiftScheme d.Label d.Point d.Block rankSize d.incidences where
  size := d.blockS
  size_ge b := (block d hd b).hs
  labels := d.blockLabels
  coord b i := (d.coordinates b i).1
  point := d.blockPoint
  incident := block_incident d hd
  unique := block_unique d hd

def wShift : ShiftScheme d.Label d.Point d.Block rankSize d.incidences where
  size := d.blockT
  size_ge b := (block d hd b).ht
  labels := d.blockLabels
  coord b i := (d.coordinates b i).2
  point := d.blockPoint
  incident := block_incident d hd
  unique := block_unique d hd

def swapIncidence : relationGraph (fun i z => i ∈ d.incidences z) →g d.incidenceGraph where
  toFun := Sum.swap
  map_rel' := by
    intro x y h
    cases x <;> cases y <;>
      simpa [relationGraph, PaperData.incidenceGraph, PaperData.incidences] using h

theorem incidences_girth (a : d.Label ⊕ d.Point)
    (w : (relationGraph (fun i z => i ∈ d.incidences z)).Walk a a)
    (hw : w.IsCycle) : 101 ≤ w.length := by
  have hi : Function.Injective (swapIncidence d) := by
    intro x y h
    have hh := congrArg Sum.swap h
    simpa [swapIncidence] using hh
  have hh := (hw.map hi).egirth_le_length
  have hb := lt_of_lt_of_le hd.2.2.2.1 hh
  simp only [SimpleGraph.Walk.length_map] at hb
  have : 100 < w.length := by exact_mod_cast hb
  omega

theorem v_link_girth (a) (w : (vShift d hd).link.Walk a a) (hw : w.IsCycle) :
    101 ≤ w.length :=
  (vShift d hd).link_cycle_length 101 (incidences_girth d hd) a w hw

theorem w_link_girth (a) (w : (wShift d hd).link.Walk a a) (hw : w.IsCycle) :
    101 ≤ w.length :=
  (wShift d hd).link_cycle_length 101 (incidences_girth d hd) a w hw

abbrev ODirections := (presentation d hd).LEdge ⊕ (presentation d hd).REdge
abbrev VDirections := ShiftScheme.XDirection (I := d.Label) (r := rankSize) ⊕ (vShift d hd).LDirection
abbrev WDirections := ShiftScheme.XDirection (I := d.Label) (r := rankSize) ⊕ (wShift d hd).LDirection
abbrev AllDirections := ODirections d hd ⊕ (VDirections d hd ⊕ WDirections d hd)

/-- At O a larger complete bipartite graph suffices for the four-edge girth bound;
at V and W we use precisely the shifted incidence links. -/
noncomputable def allLink : SimpleGraph (AllDirections d hd) :=
  (relationGraph (fun (_ : (presentation d hd).LEdge) (_ : (presentation d hd).REdge) => True)).sum
    ((vShift d hd).link.sum (wShift d hd).link)

def linkDirection : (presentation d hd).OrientedEdge → AllDirections d hd
  | (.inl (i,u,v),false) => .inr (.inl (.inl (i,u,v)))
  | (.inl (i,u,v),true) => .inr (.inr (.inl (i,v,u)))
  | (.inr (.inl l),false) => .inl (.inl l)
  | (.inr (.inl l),true) => .inr (.inl (.inr l))
  | (.inr (.inr s),false) => .inl (.inr s)
  | (.inr (.inr s),true) => .inr (.inr (.inr s))

def linkColor : AllDirections d hd → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

 theorem linkDirection_color (a : (presentation d hd).OrientedEdge) :
    linkColor d hd (linkDirection d hd a) =
      (presentation d hd).vertexColor ((presentation d hd).edgeTarget a) := by
  rcases a with ⟨a,s⟩
  rcases a with ⟨i,u,v⟩|l|s' <;> cases s <;> rfl

 theorem linkDirection_injective : Function.Injective (linkDirection d hd) := by
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  rcases a with ⟨i,u,v⟩|l|s'
  all_goals rcases b with ⟨j,u',v'⟩|l'|t'
  all_goals cases s <;> cases t <;> simp_all [linkDirection]
  all_goals exact Sum.inr.inj h

 theorem face_corner_adj {a b c : (presentation d hd).OrientedEdge}
    (h : (presentation d hd).TriangleFace a b c) :
    (allLink d hd).Adj (linkDirection d hd a)
      (linkDirection d hd ((presentation d hd).flipEdge b)) := by
  cases h <;>
    simp only [BlockPresentation.orientedL,BlockPresentation.orientedX,
      BlockPresentation.orientedR,BlockPresentation.flipEdge, Bool.not_true,
      Bool.not_false, linkDirection,allLink,SimpleGraph.sum_adj_inl,SimpleGraph.sum_adj_inr]
  all_goals first | exact True.intro | exact ⟨Subtype.prop _,rfl,rfl⟩

 theorem allLink_closed (a : AllDirections d hd) (p : (allLink d hd).Walk a a)
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight (linkColor d hd a) * p.length := by
  rcases a with a|a|a
  · let p' := SumWalk.left p
    have hlen : p'.length = p.length := SumWalk.left_length p
    have hg := reduced_closed_length_ge 4 (relationGraph_cycle_length _) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced hp)
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,Fin.zero_eta,ite_true]
    exact_mod_cast (by omega : 12 ≤ 3*p.length)
  · let p' := SumWalk.left (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 101 (v_link_girth d hd) p'
      (by rw [hlen]; exact hn) (SumWalk.left_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (1 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)
  · let p' := SumWalk.right (SumWalk.right p)
    have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
    have hg := reduced_closed_length_ge 101 (w_link_girth d hd) p'
      (by rw [hlen]; exact hn) (SumWalk.right_reduced (SumWalk.right_reduced hp))
    rw [hlen] at hg
    norm_num only [linkColor,TriangleRibbon.weight,show (2 : Fin 3) ≠ 0 by decide,ite_false,one_mul]
    exact_mod_cast (by omega : 12 ≤ p.length)

 theorem v_reduced_same_label (i : d.Label) (u v u' v' : Fin rankSize)
    (hne : (u,v) ≠ (u',v'))
    (p : (allLink d hd).Walk (.inr (.inl (.inl (i,u,v)))) (.inr (.inl (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 101 ≤ p.length := by
  let p' := SumWalk.left (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.left_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (vShift d hd).projection
    (vShift d hd).projection_locallyInjective 101 (incidences_girth d hd)
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.left_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh

 theorem w_reduced_same_label (i : d.Label) (u v u' v' : Fin rankSize)
    (hne : (u,v) ≠ (u',v'))
    (p : (allLink d hd).Walk (.inr (.inr (.inl (i,u,v)))) (.inr (.inr (.inl (i,u',v')))))
    (hp : ReducedWalk p) : 101 ≤ p.length := by
  let p' := SumWalk.right (SumWalk.right p)
  have hr' : ReducedWalk p' := SumWalk.right_reduced (SumWalk.right_reduced hp)
  have hh := immersion_fiber_distance (wShift d hd).projection
    (wShift d hd).projection_locallyInjective 101 (incidences_girth d hd)
    (a := .inl (i,u,v)) (b := .inl (i,u',v'))
    (by simpa only [ne_eq,Sum.inl.injEq,Prod.mk.injEq,true_and] using hne) rfl p' hr'
  have hlen : p'.length = p.length := (SumWalk.right_length _).trans (SumWalk.right_length p)
  exact hlen ▸ hh


open Equiv PermCycles
 theorem x_turn_large (i : d.Label) (u v u' v' : Fin rankSize) (s t : Bool)
    (ht : (presentation d hd).edgeTarget ((presentation d hd).flipEdge (.inl (i,u',v'),t)) =
      (presentation d hd).edgeTarget (.inl (i,u,v),s))
    (hne : (u,v) ≠ (u',v'))
    (p : (allLink d hd).Walk
      (linkDirection d hd ((presentation d hd).flipEdge (.inl (i,u',v'),t)))
      (linkDirection d hd (.inl (i,u,v),s)))
    (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (linkColor d hd (linkDirection d hd (.inl (i,u,v),s))) * p.length := by
  cases s <;> cases t <;>
    simp only [BlockPresentation.flipEdge,BlockPresentation.edgeTarget,Bool.not_false,Bool.not_true] at ht
  · cases ht
  · have hh := v_reduced_same_label d hd i u' v' u v hne.symm p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 101 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 101) hh)
  · have hh := w_reduced_same_label d hd i v' u' v u
      (by simpa only [ne_eq,Prod.mk.injEq,and_comm] using hne.symm) p hp
    change (5 : ℝ) ≤ 1 * p.length
    rw [one_mul]
    change 101 ≤ p.length at hh
    exact_mod_cast (le_trans (by decide : 5 ≤ 101) hh)
  · cases ht

variable {w : List (presentation d hd).OrientedEdge}
variable (D : TriangleFilling (presentation d hd).flipEdge (presentation d hd).edgeTarget
  (presentation d hd).TriangleFace w) (b : D.Dart) (hb : b ∈ D.boundary)

noncomputable abbrev concreteRibbon := D.ribbon (presentation d hd).vertexColor
  (fun _ _ _ => BlockPresentation.TriangleFace.colors _) b hb

def dartDirection (a : D.ActiveDart) : AllDirections d hd :=
  linkDirection d hd (D.label a)

theorem ribbon_outer_iff (a : D.ActiveDart) :
    (concreteRibbon d hd D b hb).IsOuter a ↔ a.val ∈ D.boundary :=
  D.active_boundary_iff hb a

theorem ribbon_color (a : D.ActiveDart) :
    (concreteRibbon d hd D b hb).color (cl (concreteRibbon d hd D b hb).vertexPerm a) =
      linkColor d hd (dartDirection d hd D a) := by
  change (D.activeColor (presentation d hd).vertexColor) (cl (D.activeReverse*D.activeNext) a) = _
  rw [TriangleFilling.activeColor,descend_cl]
  exact (linkDirection_color d hd (D.label a)).symm

theorem ribbon_direction_step (a : D.ActiveDart) :
    dartDirection d hd D ((concreteRibbon d hd D b hb).vertexPerm a) =
      linkDirection d hd ((presentation d hd).flipEdge (D.label (D.next a))) := by
  change linkDirection d hd (D.label (D.reverse (D.next a))) = _
  rw [D.reverse_label]

theorem ribbon_adj (a : D.ActiveDart)
    (ha : ¬(concreteRibbon d hd D b hb).IsOuter a) :
    (allLink d hd).Adj (dartDirection d hd D a)
      (dartDirection d hd D ((concreteRibbon d hd D b hb).vertexPerm a)) := by
  rw [ribbon_direction_step d hd D b hb a]
  exact face_corner_adj d hd (D.triangular a a.property
    (fun h => ha ((ribbon_outer_iff d hd D b hb a).mpr h))).2.2

theorem ribbon_reduced (hD : IsEmpty D.Dipole) (a : D.ActiveDart)
    (ha : ¬(concreteRibbon d hd D b hb).IsOuter a)
    (ha' : ¬(concreteRibbon d hd D b hb).IsOuter ((concreteRibbon d hd D b hb).vertexPerm a)) :
    dartDirection d hd D a ≠
      dartDirection d hd D ((concreteRibbon d hd D b hb).vertexPerm
        ((concreteRibbon d hd D b hb).vertexPerm a)) := by
  intro he
  apply D.noDipole_link_reduced
    (fun _ _ _ => BlockPresentation.TriangleFace.colors _)
    (presentation d hd).flipEdge_flipEdge
    (fun _ _ _ => BlockPresentation.TriangleFace.mirror _)
    (fun _ _ _ _ => BlockPresentation.TriangleFace.unique _) hD a a.property
    (fun h => ha ((ribbon_outer_iff d hd D b hb a).mpr h))
    (fun h => ha' ((ribbon_outer_iff d hd D b hb _).mpr h))
  exact linkDirection_injective d hd he

theorem ribbon_closed (a : D.ActiveDart)
    (p : (allLink d hd).Walk (dartDirection d hd D a) (dartDirection d hd D a))
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    10 ≤ TriangleRibbon.weight ((concreteRibbon d hd D b hb).color
      (cl (concreteRibbon d hd D b hb).vertexPerm a)) * p.length := by
  rw [ribbon_color d hd D b hb a]
  exact le_trans (by norm_num) (allLink_closed d hd _ p hn hp)


/-- One boundary turn between two x-edges of label `i` which is not a backtrack. -/
theorem x_turn_large' (i : d.Label) (a b : (presentation d hd).OrientedEdge)
    (ha : ∃ u v s, a = (.inl (i, u, v), s)) (hb : ∃ u v s, b = (.inl (i, u, v), s))
    (hnb : b ≠ (presentation d hd).flipEdge a)
    (ht : (presentation d hd).edgeTarget ((presentation d hd).flipEdge b) =
      (presentation d hd).edgeTarget a)
    (p : (allLink d hd).Walk (linkDirection d hd ((presentation d hd).flipEdge b))
      (linkDirection d hd a)) (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (linkColor d hd (linkDirection d hd a)) * p.length := by
  obtain ⟨u, v, s, rfl⟩ := ha
  obtain ⟨u', v', t, rfl⟩ := hb
  refine x_turn_large d hd i u v u' v' s t ht ?_ p hp
  intro heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  apply hnb
  cases s <;> cases t <;>
    simp_all [BlockPresentation.flipEdge, BlockPresentation.edgeTarget]

/-- **Closed x-paths of one label are not null-homotopic.**  A nonempty word `w` in the oriented
x-edges of a single label `i`, which is cyclically reduced (no letter is followed, cyclically,
by its own reverse), has no planar triangle filling. -/
theorem xword_not_fillable (i : d.Label) (w : List (presentation d hd).OrientedEdge)
    (hx : ∀ e ∈ w, ∃ u v s, e = ((.inl (i, u, v) : (presentation d hd).Edge), s))
    (hne : w ≠ [])
    (hcyc : ∀ n, n < w.length → ∀ e e', w[n]? = some e → w[(n + 1) % w.length]? = some e' →
      e' ≠ (presentation d hd).flipEdge e)
    (hf : Fillable (presentation d hd).flipEdge (presentation d hd).edgeTarget
      (presentation d hd).TriangleFace w) : False := by
  obtain ⟨D, hD⟩ := TriangleFilling.exists_noDipole hf
  have hn : D.boundary ≠ [] := by
    intro hz
    apply hne
    have hw := D.boundary_word
    rw [hz, List.map_nil] at hw
    exact hw.symm
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil D.boundary hn
  apply (concreteRibbon d hd D b hb).not_all_turns_geodesic
    (allLink d hd) (dartDirection d hd D)
    (ribbon_adj d hd D b hb) (ribbon_reduced d hd D b hb hD)
    (ribbon_closed d hd D b hb)
  intro a ha p hp
  have ha' : a.val ∈ D.boundary := (ribbon_outer_iff d hd D b hb a).mp ha
  have hb' : D.next a.val ∈ D.boundary := (D.boundary_cycle.mem_iff a.val).mpr ha'
  have hal : D.label a.val ∈ w := by
    have hm : D.label a.val ∈ D.boundary.map D.label := List.mem_map.mpr ⟨a.val, ha', rfl⟩
    rwa [D.boundary_word] at hm
  have hbl : D.label (D.next a.val) ∈ w := by
    have hm : D.label (D.next a.val) ∈ D.boundary.map D.label :=
      List.mem_map.mpr ⟨D.next a.val, hb', rfl⟩
    rwa [D.boundary_word] at hm
  -- the position of `a` on the boundary, and of its successor
  obtain ⟨n, hna⟩ := List.mem_iff_getElem?.mp ha'
  obtain ⟨hn, hna'⟩ := List.getElem?_eq_some_iff.mp hna
  have hlen : D.boundary.length = w.length := by
    have h := congrArg List.length D.boundary_word
    simpa using h
  have hpos : 0 < D.boundary.length := by omega
  have hnext : D.boundary[(n + 1) % D.boundary.length]? = some (D.next a.val) := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hpos)]
    congr 1
    rw [D.boundary_cycle.2 _ ha', ← hna', List.formPerm_apply_getElem _ D.boundary_cycle.1]
  have h1 : (D.boundary.map D.label)[n]? = some (D.label a.val) := by
    simp [hna]
  have h2 : (D.boundary.map D.label)[(n + 1) % (D.boundary.map D.label).length]? =
      some (D.label (D.next a.val)) := by
    simp [hnext]
  rw [D.boundary_word] at h1 h2
  have hnb : D.label (D.next a.val) ≠ (presentation d hd).flipEdge (D.label a.val) :=
    hcyc n (by omega) _ _ h1 h2
  -- the turn at `a`
  rw [ribbon_color d hd D b hb a]
  have ht : (presentation d hd).edgeTarget ((presentation d hd).flipEdge (D.label (D.next a.val))) =
      (presentation d hd).edgeTarget (D.label a.val) := by
    rw [← D.reverse_label]
    exact D.color_next a.val
  have hs := ribbon_direction_step d hd D b hb a
  let p' := p.copy hs rfl
  have hp' : ReducedWalk p' := by
    intro j hj
    simpa only [p', SimpleGraph.Walk.getVert_copy] using
      hp j (by simpa only [p', SimpleGraph.Walk.length_copy] using hj)
  have hh := x_turn_large' d hd i _ _ (hx _ hal) (hx _ hbl) hnb ht p' hp'
  have hlen' : p'.length = p.length := SimpleGraph.Walk.length_copy p hs rfl
  change 5 ≤ TriangleRibbon.weight (linkColor d hd (linkDirection d hd (D.label a.val))) *
    p'.length at hh
  rw [hlen'] at hh
  exact hh



/-- The oriented x-edge of label `i` for a free-group letter `((u, v), s)`. -/
noncomputable def xEdge (i : d.Label) (x : (Fin rankSize × Fin rankSize) × Bool) : (presentation d hd).OrientedEdge :=
  ((.inl (i, x.1.1, x.1.2) : (presentation d hd).Edge), x.2)

/-- The source vertex of an x-letter of sign `s`. -/
noncomputable def vert : Bool → (presentation d hd).Vertex
  | true => .v
  | false => .w

theorem tgt_xEdge (i : d.Label) (x : (Fin rankSize × Fin rankSize) × Bool) :
    (presentation d hd).edgeTarget (xEdge d hd i x) = vert d hd (!x.2) := by
  obtain ⟨a, s⟩ := x
  cases s <;> rfl

theorem src_xEdge (i : d.Label) (x : (Fin rankSize × Fin rankSize) × Bool) :
    (presentation d hd).edgeTarget ((presentation d hd).flipEdge (xEdge d hd i x)) =
      vert d hd x.2 := by
  obtain ⟨a, s⟩ := x
  cases s <;> rfl

theorem flip_xEdge (i : d.Label) (x : (Fin rankSize × Fin rankSize) × Bool) :
    (presentation d hd).flipEdge (xEdge d hd i x) = xEdge d hd i (x.1, !x.2) := rfl

theorem xEdge_injective (i : d.Label) : Function.Injective (xEdge d hd i) := by
  rintro ⟨⟨u, v⟩, s⟩ ⟨⟨u', v'⟩, s'⟩ h
  simp only [xEdge, Prod.mk.injEq, Sum.inl.injEq] at h
  obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := h
  rfl

theorem wp_congr {a a' b b' : (presentation d hd).Vertex}
    {w : List (presentation d hd).OrientedEdge} (ha : a = a') (hb : b = b')
    (h : WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget a b w) :
    WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget a' b' w := by
  subst ha
  subst hb
  exact h

theorem wordPath_cons_x (i : d.Label) (a : Fin rankSize × Fin rankSize) (t : Bool)
    {c : (presentation d hd).Vertex} {w : List (presentation d hd).OrientedEdge}
    (h : WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget
      (vert d hd (!t)) c w) :
    WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget (vert d hd t) c
      (xEdge d hd i (a, t) :: w) := by
  have h1 : WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget
      ((presentation d hd).edgeTarget (xEdge d hd i (a, t))) c w := by
    rw [tgt_xEdge]
    exact h
  have h2 := WordPath.cons (xEdge d hd i (a, t)) h1
  rw [src_xEdge] at h2
  exact h2

/-- An alternating x-word of even length starting with sign `s` is a closed edge path. -/
theorem wordPath_even (i : d.Label) (s : Bool) : ∀ (R : List ((Fin rankSize × Fin rankSize) × Bool)),
    (∀ y ∈ R.head?, y.2 = s) → NonSofic.LineFreeWord.Alt R → Even R.length →
    WordPath (presentation d hd).flipEdge (presentation d hd).edgeTarget (vert d hd s)
      (vert d hd s) (R.map (xEdge d hd i))
  | [], _, _, _ => WordPath.nil _
  | [_], _, _, he => absurd he (by simp)
  | (xa, xs) :: (ya, ys) :: R, hs, hA, he => by
    have hx : xs = s := hs (xa, xs) rfl
    obtain ⟨hxy, hA'⟩ := List.isChain_cons_cons.mp hA
    have hy : ys = !s := by
      rw [← hx]
      revert hxy
      cases xs <;> cases ys <;> simp
    have hR : ∀ z ∈ R.head?, z.2 = s := by
      intro z hz
      rcases R with _ | ⟨w, ws⟩
      · simp at hz
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        rw [← hz]
        have hyz := (List.isChain_cons_cons.mp hA').1
        obtain ⟨wa, wb⟩ := w
        rw [hy] at hyz
        revert hyz
        cases s <;> cases wb <;> simp
    have hE : Even R.length := by
      simp only [List.length_cons] at he
      rcases he with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
    have ih := wordPath_even i s R hR hA'.tail hE
    have h2 := wordPath_cons_x d hd i ya ys
      (wp_congr d hd (by rw [hy, Bool.not_not]) rfl ih)
    have h3 := wordPath_cons_x d hd i xa xs (wp_congr d hd (by rw [hx, hy]) rfl h2)
    exact wp_congr d hd (by rw [hx]) rfl h3

/-- The value of an x-word in `G`. -/
theorem wordValue_xEdge (i : d.Label) (R : List ((Fin rankSize × Fin rankSize) × Bool)) :
    (presentation d hd).wordValue (R.map (xEdge d hd i)) =
      FreeGroup.lift (fun a : Fin rankSize × Fin rankSize => (presentation d hd).x i a.1 a.2)
        (FreeGroup.mk R) := by
  rw [FreeGroup.lift_mk]
  unfold BlockPresentation.wordValue
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, s⟩ -
  cases s <;> rfl

/-- **Lemma `lem:free`.**  The line subgroup `A_i = ⟨x_{iuv} x_{i00}⁻¹⟩` is free on the
`y_{uv} = x_{iuv} x_{i00}⁻¹`, `(u, v) ≠ (0, 0)`. -/
theorem lineSubgroup_free (i : d.Label) :
    Function.Injective (FreeGroup.lift
      (fun p : {p : Fin rankSize × Fin rankSize // p ≠ (PaperData.zeroIndex, PaperData.zeroIndex)} =>
        (presentation d hd).x i p.val.1 p.val.2 *
          ((presentation d hd).x i PaperData.zeroIndex PaperData.zeroIndex)⁻¹)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨R, C, hRne, hcyc, hAlt, hEven, hconj⟩ :=
    NonSofic.LineFreeWord.exists_core ((PaperData.zeroIndex, PaperData.zeroIndex) : Fin rankSize × Fin rankSize) g hne
  -- the value of the core is `1`
  have hval : FreeGroup.lift (fun a : Fin rankSize × Fin rankSize => (presentation d hd).x i a.1 a.2)
      (FreeGroup.mk R) = 1 := by
    have h1 := NonSofic.LineFreeWord.lift_psi ((PaperData.zeroIndex, PaperData.zeroIndex) : Fin rankSize × Fin rankSize)
      (fun a : Fin rankSize × Fin rankSize => (presentation d hd).x i a.1 a.2) g
    rw [hconj, map_mul, map_mul, map_inv] at h1
    have h2 := h1.trans hg
    have key : ∀ A B : (presentation d hd).GroupType, A * B * A⁻¹ = 1 → B = 1 := by
      intro A B h
      have h3 : B = A⁻¹ * (A * B * A⁻¹) * A := by group
      rw [h3, h]
      group
    exact key _ _ h2
  -- it is a closed, cyclically reduced x-path of label `i`
  obtain ⟨x, R', rfl⟩ := List.exists_cons_of_ne_nil hRne
  have hwp := wordPath_even d hd i x.2 (x :: R') (fun y hy => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [hy]) hAlt hEven
  have hwv : (presentation d hd).wordValue ((x :: R').map (xEdge d hd i)) = 1 := by
    rw [wordValue_xEdge]
    exact hval
  have hfill : Fillable (presentation d hd).flipEdge (presentation d hd).edgeTarget
      (presentation d hd).TriangleFace ((x :: R').map (xEdge d hd i)) := by
    obtain ⟨p, hp⟩ := BlockPresentation.WordPath.exists_raw (presentation d hd) hwp
    rw [← hp]
    exact (presentation d hd).nullhomotopic_fillable
      ((presentation d hd).rawWord_nullhomotopic p (by rw [hp]; exact hwv))
  apply xword_not_fillable d hd i ((x :: R').map (xEdge d hd i)) ?_ (by simp) ?_ hfill
  · intro e he
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp he
    exact ⟨y.1.1, y.1.2, y.2, rfl⟩
  · intro n hn e e' he he' heq
    rw [List.length_map] at hn he'
    rw [List.getElem?_map] at he he'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp he'
    rw [flip_xEdge] at heq
    have hab := xEdge_injective d hd i heq
    exact NonSofic.LineFreeWord.cyc_step hcyc n hn a b ha hb ⟨by rw [hab], by rw [hab]⟩




end
end DomainNonembedding.CollapsedLines

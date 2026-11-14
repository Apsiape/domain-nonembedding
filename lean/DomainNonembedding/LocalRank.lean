import DomainNonembedding.RankCertificate

set_option autoImplicit false

namespace DomainNonembedding.LocalRank
open OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

-- The block sum calculation adapts the byte-identical NonSofic source (Apache-2.0).
variable {R : Type*} [Ring R]

theorem block_sum_factor {I : Type} {r : ℕ} (b : CartesianBlock I r)
    (Y : I → Matrix (Fin r) (Fin r) R) (L : Fin r → ZMod b.s → R) (Rr : Fin r → ZMod b.t → R)
    (hY : ∀ (i : b.labels) u v, Y i u v =
      L u ((b.coordinates i).1 + (v.val : ZMod b.s)) *
        Rr v ((b.coordinates i).2 + (u.val : ZMod b.t))) :
    ∑ i ∈ b.labels, Y i =
      (Matrix.of fun u (_ : Fin 1) => ∑ j, L u j) * (Matrix.of fun (_ : Fin 1) v => ∑ k, Rr v k) := by
  ext u v
  rw [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [Matrix.of_apply]
  calc (∑ i ∈ b.labels, Y i u v) = ∑ i : b.labels, Y i u v :=
        (Finset.sum_coe_sort b.labels (fun i => Y i u v)).symm
    _ = ∑ i : b.labels, (fun p : ZMod b.s × ZMod b.t => L u p.1 * Rr v p.2) (b.shifted u v i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hY i u v).trans rfl
    _ = ∑ p : ZMod b.s × ZMod b.t, L u p.1 * Rr v p.2 :=
        Equiv.sum_comp (b.shifted u v) (fun p : ZMod b.s × ZMod b.t => L u p.1 * Rr v p.2)
    _ = ∑ j, ∑ k, L u j * Rr v k := Fintype.sum_prod_type _
    _ = (∑ j, L u j) * (∑ k, Rr v k) := by rw [Finset.sum_mul_sum]

theorem rank_add_le {D m n : Type*} [DivisionRing D] [Fintype m] [Fintype n]
    (A B : Matrix m n D) : NonSofic.rankD (A+B) ≤ NonSofic.rankD A+NonSofic.rankD B := by
  have h := (NonSofic.rankDRankFunction D).rkF_add_le A B
  simp only [NonSofic.rankDRankFunction_rkF] at h
  exact_mod_cast h

def left {p : ℕ} (d : PaperData p) (b : d.Block) (u : Fin rankSize)
    (j : ZMod (d.blockS b)) : d.BaseGroup := PresentedGroup.of (.left b u j)

def right {p : ℕ} (d : PaperData p) (b : d.Block) (v : Fin rankSize)
    (k : ZMod (d.blockT b)) : d.BaseGroup := PresentedGroup.of (.right b v k)

theorem triangle_relation {p : ℕ} (d : PaperData p) (b : d.Block)
    (i : {i // i ∈ d.blockLabels b}) (u v : Fin rankSize) :
    d.x i.val u v =
      (left d b u ((d.coordinates b i).1+(v.val : ZMod (d.blockS b))))⁻¹ *
        right d b v ((d.coordinates b i).2+(u.val : ZMod (d.blockT b))) := by
  have h := PresentedGroup.one_of_mem (rels := d.baseRelators)
    (x := d.triangleWord b i u v) (Or.inl ⟨b, i, u, v, rfl⟩)
  have hh : left d b u ((d.coordinates b i).1+(v.val : ZMod (d.blockS b))) *
      d.x i.val u v * (right d b v ((d.coordinates b i).2+(u.val : ZMod (d.blockT b))))⁻¹ = 1 := by
    simpa only [left, right, PaperData.triangleWord, PaperData.x, PaperData.xWord,
      PresentedGroup.of, map_mul, map_inv] using h
  exact eq_inv_mul_iff_mul_eq.mpr (mul_inv_eq_one.mp hh)

noncomputable def blockData {p : ℕ} (d : PaperData p) (hd : d.Admissible) (b : d.Block) :
    CartesianBlock d.Label rankSize where
  s := d.blockS b
  t := d.blockT b
  hs := (hd.2.2.2.2.2.2.2.1 b).1
  ht := (hd.2.2.2.2.2.2.2.1 b).2.1
  spos := (by unfold rankSize; positivity : 0 < rankSize).trans_le (hd.2.2.2.2.2.2.2.1 b).1
  tpos := (by unfold rankSize; positivity : 0 < rankSize).trans_le (hd.2.2.2.2.2.2.2.1 b).2.1
  labels := d.blockLabels b
  coordinates := d.coordinates b

theorem block_rank_le_one {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    {D : Type*} [DivisionRing D] (χ : d.BaseGroup →* D) (b : d.Block) :
    NonSofic.rankD (∑ i ∈ d.blockLabels b, d.lineMatrix χ i) ≤ 1 := by
  letI : NeZero (d.blockS b) := ⟨((blockData d hd b).spos).ne'⟩
  letI : NeZero (d.blockT b) := ⟨((blockData d hd b).tpos).ne'⟩
  let B := blockData d hd b
  let L := fun u j => χ ((left d b u j)⁻¹)
  let Rr := fun v k => χ (right d b v k)
  have hf := block_sum_factor B (d.lineMatrix χ) L Rr (by
    intro i u v
    change χ (d.x i.val u v) = χ ((left d b u _)⁻¹) * χ (right d b v _)
    exact (congrArg χ (triangle_relation d b i u v)).trans (map_mul χ _ _))
  change NonSofic.rankD (∑ i ∈ B.labels, d.lineMatrix χ i) ≤ 1
  rw [hf]
  refine (NonSofic.rankD_mul_le_left _ _).trans ?_
  exact DivisionRingRank.rank_le_columns _

theorem point_rank_bound {p : ℕ} (d : PaperData p) (hd : d.Admissible)
    {D : Type*} [DivisionRing D] (χ : d.BaseGroup →* D) (z : d.Point) :
    NonSofic.rankD (∑ i ∈ d.incidences z, d.lineMatrix χ i) ≤
      if z ∈ d.exceptional then rankSize else 2 := by
  by_cases hz : z ∈ d.exceptional
  · rw [if_pos hz]
    simpa using DivisionRingRank.rank_le_columns (∑ i ∈ d.incidences z, d.lineMatrix χ i)
  · rw [if_neg hz]
    obtain ⟨b₀, b₁, _, _, _, hdis, hu, _⟩ := hd.2.2.2.2.2.2.2.2 z hz
    rw [← hu, Finset.sum_union hdis]
    exact (rank_add_le _ _).trans (by
      have h₀ := block_rank_le_one d hd χ b₀
      have h₁ := block_rank_le_one d hd χ b₁
      omega)

/-- The strict numerical half of the ceiling holds for every admissible datum. -/
theorem rank_budget {p : ℕ} (d : PaperData p) (hd : d.Admissible) :
    4*(2*((p^d.exponent)^dimension-d.exceptional.card)+rankSize*d.exceptional.card) <
      d.lineCount*rankSize := by
  let m := (p^d.exponent)^dimension
  have hN := hd.2.2.2.2.2.1
  have hE := hd.2.2.2.2.2.2.1
  have hNr : 50*m ≤ d.lineCount*rankSize := by
    have h := Nat.mul_le_mul_left 50 hN
    convert h using 1 <;> unfold rankSize <;> ring
  have hm : 0 < m := by
    have hc := Interpolation.scalar_card d
    dsimp [m]
    rw [← hc]
    exact pow_pos Fintype.card_pos _
  have hs : m-d.exceptional.card ≤ m := Nat.sub_le _ _
  change 4*(2*(m-d.exceptional.card)+rankSize*d.exceptional.card) < d.lineCount*rankSize
  change 2*rankSize*d.exceptional.card ≤ m at hE
  nlinarith only [hNr, hE, hm, hs]

theorem universal_rank_ceiling {p : ℕ} [Fact p.Prime] (d : PaperData p)
    (hd : d.Admissible) {D : Type*} [DivisionRing D]
    (φ : MonoidAlgebra (ZMod p) d.BaseGroup →+* D) :
    (∑ i, NonSofic.rankD (d.lineMatrix ((φ : _ →* D).comp
      (MonoidAlgebra.of (ZMod p) d.BaseGroup)) i)) ≤
        2*((p^d.exponent)^dimension-d.exceptional.card)+rankSize*d.exceptional.card ∧
    4*(2*((p^d.exponent)^dimension-d.exceptional.card)+rankSize*d.exceptional.card) <
      d.lineCount*rankSize := by
  let c : ZMod p →+* D := φ.comp MonoidAlgebra.singleOneRingHom
  letI : CharP D p := charP_of_injective_ringHom c.injective p
  let χ := (φ : _ →* D).comp (MonoidAlgebra.of (ZMod p) d.BaseGroup)
  have hcert := MatrixDescent.rank_certificate d hd rankSize (d.lineMatrix χ)
  have hcard : Fintype.card d.Point = (p^d.exponent)^dimension := by
    simp only [Fintype.card_fun, Fintype.card_fin, Interpolation.scalar_card]
  have hsum : (∑ z : d.Point, if z ∈ d.exceptional then rankSize else 2) =
      2*((p^d.exponent)^dimension-d.exceptional.card)+rankSize*d.exceptional.card := by
    rw [Finset.sum_ite]
    have hmem : Finset.univ.filter (fun z : d.Point => z ∈ d.exceptional) = d.exceptional := by
      ext z; simp
    have hnot : Finset.univ.filter (fun z : d.Point => z ∉ d.exceptional) = d.exceptionalᶜ := by
      ext z; simp
    rw [hmem, hnot]
    simp [Finset.card_compl, hcard, Nat.add_comm, Nat.mul_comm]
  refine ⟨hcert.trans ?_, rank_budget d hd⟩
  exact (Finset.sum_le_sum (fun z _ => point_rank_bound d hd χ z)).trans_eq hsum

end DomainNonembedding.LocalRank

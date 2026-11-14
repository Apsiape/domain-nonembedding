import DomainNonembedding.Incidence

set_option autoImplicit false

namespace DomainNonembedding.Incidence
open OAI.Release075
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

section Cost
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

/-- An alteration whose cost is at most its expectation (up to `+1`).  The expectation bound
`hexp` is copied from the proof of the finite expectation argument. -/
theorem exists_alteration_cost (S : Finset V) (r T : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z)
    (hdel : (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ B) :
    ∃ ω : S → Projectivization K V,
      4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
        r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ) <
      16*r*(Fintype.card V : ℝ)/μ + r*(4*(Fintype.card K : ℝ)+1)*B + 1 := by
  let cost : (S → Projectivization K V) → ℝ := fun ω =>
    4*r*((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ) +
    r*(4*(Fintype.card K : ℝ)+1)*((deletedMarks S ω).card : ℝ)
  -- copied from OAI (`exists_alteration_budget`, Incidence.lean)
  have hexp : (𝔼 ω, cost ω) ≤ 16*r*(Fintype.card V : ℝ)/μ +
      r*(4*(Fintype.card K : ℝ)+1)*B := by
    simp only [cost, Finset.expect_add_distrib, ← Finset.mul_expect]
    have hlow := expect_lowDegree_le (K := K) S T μ hμ hT hlower
    have h₁ := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4*(r : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hdel
      (show 0 ≤ (r : ℝ)*(4*(Fintype.card K : ℝ)+1) by positivity)
    convert add_le_add h₁ h₂ using 2; first | rfl | ring
  exact exists_of_expect_lt cost _ (by linarith)


end Cost

/-- Numerical estimates at the paper's dimension and girth. -/
theorem numeric_halves {q C r : ℝ} (hC : 10 ≤ C) (hr : r = 100*C)
    (hq : 32*C*r^2 ≤ q) :
    0 < q/(4*C) ∧ 8*r^2 ≤ q/(4*C) ∧
    2*(16*r*q^103/(q/(4*C))) ≤ q^103 ∧
    2*(r*(4*q+1)*(2450*q^100)) ≤ q^103 := by
  have hC0 : 0 < C := by linarith
  have hr1 : 1000 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := by linarith
  have hrr : 4*r ≤ r^2 := by nlinarith
  have hq128 : 128*r*C ≤ q := by
    have h := mul_le_mul_of_nonneg_left hrr (show 0 ≤ 32*C by positivity)
    nlinarith only [h, hq]
  have hq24500 : 24500*r ≤ q := by
    have hrr' : 1000*r ≤ r^2 := by nlinarith
    calc
      _ ≤ 32*C*(1000*r) := by nlinarith
      _ ≤ 32*C*r^2 := mul_le_mul_of_nonneg_left hrr' (by positivity)
      _ ≤ q := hq
  have hq1 : 1 ≤ q := by nlinarith only [hq24500, hr1]
  have hq0 : 0 < q := by linarith
  refine ⟨by positivity, (le_div_iff₀ (by positivity : 0 < 4*C)).mpr ?_, ?_, ?_⟩
  · nlinarith only [hq]
  · have heq : 16*r*q^103/(q/(4*C)) = 64*r*C*q^102 := by
      field_simp
      ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right hq128 (pow_nonneg hq0.le 102)
    convert h using 1 <;> ring
  · calc
      _ ≤ 24500*r*q^101 := by
        have h := mul_nonneg (show 0 ≤ 4900*r*q^100 by positivity)
          (show 0 ≤ q-1 by linarith)
        nlinarith only [h]
      _ ≤ q^2*q^101 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hq24500.trans (by nlinarith : q ≤ q^2)
      _ = q^103 := by ring

theorem alteration_arith (C r q m L D E S N : ℕ) (hC : 0 < C)
    (hr : r = 100*C) (hm : 0 < m)
    (hcost : 4*r*L + r*(4*q+1)*D ≤ m) (hE : E ≤ L + q*D)
    (hS : m ≤ C*S) (hDS : D ≤ S) (hN : N = S-D) :
    2*r*E ≤ m ∧ m ≤ 2*C*N ∧ 4*(2*m+r*E) < N*r := by
  subst r
  have h1 := Nat.mul_le_mul_left (400*C) hE
  have hCD : 100*C*D ≤ 100*C*(4*q+1)*D :=
    Nat.mul_le_mul_right D (Nat.le_mul_of_pos_right (100*C) (by omega))
  have hNS : N+D = S := by omega
  have h2 : 2*C*(N+D) = 2*C*S := by rw [hNS]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The projective-direction bounds in dimension 103. -/
theorem geom_sum_bounds {q : ℝ} (hq : 2 ≤ q) :
    q^102 ≤ ∑ i ∈ Finset.range 103, q^i ∧
      ∑ i ∈ Finset.range 103, q^i ≤ 2*q^102 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact Finset.single_le_sum (fun i _ => pow_nonneg hq0.le i) (by norm_num)
  · have hg := geom_sum_mul q 103
    have hh : 2*q^102*(q-1) ≥ q^103-1 := by
      have h := mul_nonneg (pow_nonneg hq0.le 102) (show 0 ≤ q-2 by linarith)
      nlinarith only [h]
    exact (mul_le_mul_iff_left₀ (show 0 < q-1 by linarith)).mp (by nlinarith only [hg, hh])

theorem cycle_numeric_bound {q J : ℝ} (hq : 1 ≤ q) (hJ : q^102 ≤ J)
    {s : ℕ} (hs : s ≤ 50) : (q^103)^s*q^s*(1/J)^s ≤ q^100 := by
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 < J := (pow_pos hq0 102).trans_le hJ
  have hf : q^103*q/J ≤ q^2 := by
    apply (div_le_iff₀ hJ0).mpr
    have h := mul_le_mul_of_nonneg_left hJ (sq_nonneg q)
    convert h using 1 <;> ring
  calc
    _ = (q^103*q/J)^s := by simp only [div_pow, mul_pow, one_pow]; ring
    _ ≤ (q^2)^s := pow_le_pow_left₀ (by positivity) hf s
    _ = q^(2*s) := by rw [pow_mul]
    _ ≤ q^100 := pow_le_pow_right₀ hq (by omega)

def gridMarks {K : Type*} (S : Finset K) : Finset (Fin dimension → K) :=
  Fintype.piFinset (fun _ => S)

theorem gridMarks_card {K : Type*} (S : Finset K) :
    (gridMarks S).card = S.card^103 := by
  simp [gridMarks, Fintype.card_piFinset]

theorem floor_grid_lower {q : ℕ} (hq : 2060 ≤ q) :
    (q : ℝ)^103 ≤ (2060 : ℝ)^103*((q/1030 : ℕ) : ℝ)^103 := by
  have hh : q ≤ 2060*(q/1030) := by omega
  have hh' : (q : ℝ) ≤ 2060*((q/1030 : ℕ) : ℝ) := by exact_mod_cast hh
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ q) hh' 103

section FiniteField
variable {K : Type} [Field K] [Fintype K]
  [Fintype (Projectivization K (Fin dimension → K))]

theorem directions_card :
    Fintype.card (Projectivization K (Fin dimension → K)) =
      ∑ i ∈ Finset.range 103, (Fintype.card K)^i := by
  simpa only [Nat.card_eq_fintype_card] using
    Projectivization.card_of_finrank K (Fin dimension → K) (Module.finrank_fin_fun K)

theorem mean_grid_lower (hq : 2060 ≤ Fintype.card K)
    (S : Finset K) (hS : S.card = Fintype.card K/1030) (z : Fin dimension → K) :
    (Fintype.card K : ℝ)/(4*(2060 : ℝ)^103) ≤ pointMean (K := K) (gridMarks S) z := by
  let q := Fintype.card K
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hJ := geom_sum_bounds hq2
  have hJcast : (Fintype.card (Projectivization K (Fin dimension → K)) : ℝ) =
      ∑ i ∈ Finset.range 103, (q : ℝ)^i := by rw [directions_card]; push_cast; rfl
  rw [← hJcast] at hJ
  have hJpos : (0 : ℝ) < Fintype.card (Projectivization K (Fin dimension → K)) :=
    (pow_pos (by linarith : (0 : ℝ) < q) 102).trans_le hJ.1
  have hM : (q : ℝ)^103 ≤ (2060 : ℝ)^103*(gridMarks S).card := by
    rw [gridMarks_card, hS, Nat.cast_pow]
    exact floor_grid_lower hq
  have hM2 : 2 ≤ (gridMarks S).card := by
    rw [gridMarks_card, hS]
    exact (show 2 ≤ q/1030 by omega).trans (Nat.le_pow (by norm_num))
  have he : ((gridMarks S).card : ℝ) ≤ 2*((gridMarks S).erase z).card := by
    by_cases hz : z ∈ gridMarks S
    · rw [Finset.card_erase_of_mem hz, Nat.cast_sub (by omega), Nat.cast_one]
      have hh : (2 : ℝ) ≤ (gridMarks S).card := by exact_mod_cast hM2
      linarith
    · rw [Finset.erase_eq_of_notMem hz]
      have hh : (0 : ℝ) ≤ (gridMarks S).card := by positivity
      linarith
  rw [pointMean_formula]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4*(2060 : ℝ)^103) hJpos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hJ.2 (show (0 : ℝ) ≤ q by positivity)
  have h₂ := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ (2060 : ℝ)^103 by positivity)
  calc
    _ ≤ (q : ℝ)*(2*(q : ℝ)^102) := h₁
    _ = 2*(q : ℝ)^103 := by ring
    _ ≤ 2*((2060 : ℝ)^103*(gridMarks S).card) := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ ≤ 2*((2060 : ℝ)^103*(2*((gridMarks S).erase z).card)) :=
      mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = _ := by ring_nf; congr 3; ext i; simp

end FiniteField

set_option exponentiation.threshold 512 in
/-- A simultaneous finite outcome with all three cardinality budgets. -/
theorem large_field_outcome {K : Type} [Field K] [Fintype K]
    [Fintype (Projectivization K (Fin dimension → K))]
    (hlarge : fieldThreshold < Fintype.card K)
    (S : Finset K) (hS : S.card = Fintype.card K/1030) :
    ∃ ω : gridMarks S → Projectivization K (Fin dimension → K),
      2*rankSize*(exceptionalPoints (gridMarks S) ω (4*rankSize^2)).card ≤
        (Fintype.card K)^103 ∧
      (Fintype.card K)^103 ≤ 2*2060^103*Fintype.card (Retained (gridMarks S) ω) ∧
      4*(2*(Fintype.card K)^103 +
        rankSize*(exceptionalPoints (gridMarks S) ω (4*rankSize^2)).card) <
          Fintype.card (Retained (gridMarks S) ω)*rankSize := by
  let q := Fintype.card K
  have hq2060 : 2060 ≤ q := by
    have h : 2060 ≤ fieldThreshold := by norm_num [fieldThreshold]
    omega
  have hq32 : 32*2060^103*rankSize^2 ≤ q := by
    have he : 32*2060^103*rankSize^2 = fieldThreshold := by norm_num [rankSize, fieldThreshold]
    rw [he]
    exact hlarge.le
  have hn := numeric_halves (by norm_num : (10 : ℝ) ≤ (2060 : ℝ)^103)
    (by norm_num [rankSize] : (rankSize : ℝ) = 100*(2060 : ℝ)^103)
    (by exact_mod_cast hq32 : 32*(2060 : ℝ)^103*(rankSize : ℝ)^2 ≤ (q : ℝ))
  have hJ : (q : ℝ)^102 ≤ Fintype.card (Projectivization K (Fin dimension → K)) := by
    rw [directions_card]
    push_cast
    exact (geom_sum_bounds (by exact_mod_cast (show 2 ≤ q by omega))).1
  have hcycle := expect_deletedMarks_le (K := K) (gridMarks S) (q : ℝ) (by
    intro s hs
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    exact cycle_numeric_bound (by exact_mod_cast (show 1 ≤ q by omega)) hJ
      (Finset.mem_Icc.mp hs).2)
  obtain ⟨ω, hω⟩ := exists_alteration_cost (gridMarks S) rankSize (4*rankSize^2)
    ((q : ℝ)/(4*(2060 : ℝ)^103)) (2450*(q : ℝ)^100) hn.1
    (by push_cast; nlinarith only [hn.2.1])
    (mean_grid_lower hq2060 S hS) hcycle
  have hcost : 4*rankSize*(Finset.univ.filter
      (fun z : Fin dimension → K => pointDegree (gridMarks S) ω z < 4*rankSize^2)).card +
      rankSize*(4*q+1)*(deletedMarks (gridMarks S) ω).card ≤ q^103 := by
    have hreal : (4 : ℝ)*rankSize*(Finset.univ.filter
        (fun z : Fin dimension → K => pointDegree (gridMarks S) ω z < 4*rankSize^2)).card +
        rankSize*(4*q+1)*(deletedMarks (gridMarks S) ω).card < (q : ℝ)^103+1 := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hω
      linarith only [hω, hn.2.2.1, hn.2.2.2]
    have hnat : 4*rankSize*(Finset.univ.filter
        (fun z : Fin dimension → K => pointDegree (gridMarks S) ω z < 4*rankSize^2)).card +
        rankSize*(4*q+1)*(deletedMarks (gridMarks S) ω).card < q^103+1 := by
      exact_mod_cast hreal
    omega
  have hgrid : q^103 ≤ 2060^103*(gridMarks S).card := by
    have h := floor_grid_lower hq2060
    rw [← hS] at h
    rw [gridMarks_card]
    exact_mod_cast h
  refine ⟨ω, ?_⟩
  exact alteration_arith (2060^103) rankSize q (q^103) _ _ _ _ _
    (by positivity) rfl (by positivity) hcost
    (exceptionalPoints_card_le (gridMarks S) ω (4*rankSize^2)) hgrid
    ((Finset.card_le_univ _).trans_eq (Fintype.card_coe _))
    (retained_card (gridMarks S) ω)

end
end DomainNonembedding.Incidence

import DomainNonembedding.DivisionRingRank

set_option autoImplicit false

namespace DomainNonembedding.Permutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The first k row indices, also meaningful when k exceeds n. -/
abbrev Initial (n k : ℕ) := {i : Fin n // i.val < k}

def initialEquiv (n k : ℕ) (hk : k ≤ n) : Fin k ≃ Initial n k where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def initialStep (n k : ℕ) (hk : k < n) : Initial n k ⊕ Unit ≃ Initial n (k + 1) where
  toFun q := match q with
    | .inl i => ⟨i.val, Nat.lt_succ_of_lt i.property⟩
    | .inr _ => ⟨⟨k, hk⟩, Nat.lt_succ_self k⟩
  invFun i := if h : i.val.val < k then .inl ⟨i.val, h⟩ else .inr ()
  left_inv q := by
    cases q with
    | inl i => simp [i.property]
    | inr i => cases i; simp
  right_inv i := by
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      change k = i.val.val
      have hi := i.property
      omega

noncomputable def leading {D : Type*} {n : ℕ} (b : Fin n × Fin n → D)
    (π : Equiv.Perm (Fin n × Fin n)) (k : ℕ) :
    Matrix (Initial n k) (Initial n k) D :=
  Matrix.of fun i j => b (π (i.val, j.val))

noncomputable def leadingRank {D : Type*} [DivisionRing D] {n : ℕ}
    (b : Fin n × Fin n → D) (π : Equiv.Perm (Fin n × Fin n)) (k : ℕ) : ℕ :=
  NonSofic.rankD (leading b π k)

theorem leadingRank_mono {D : Type*} [DivisionRing D] {n : ℕ}
    (b : Fin n × Fin n → D) (π : Equiv.Perm (Fin n × Fin n)) :
    Monotone (leadingRank b π) := by
  intro k l hkl
  let f : Initial n k → Initial n l := fun i => ⟨i.val, lt_of_lt_of_le i.property hkl⟩
  exact NonSofic.rankD_submatrix_le (leading b π l) f f

theorem leadingRank_zero {D : Type*} [DivisionRing D] {n : ℕ}
    (b : Fin n × Fin n → D) (π : Equiv.Perm (Fin n × Fin n)) :
    leadingRank b π 0 = 0 := by
  have : IsEmpty (Initial n 0) := ⟨fun i => Nat.not_lt_zero _ i.property⟩
  have h := LinearMap.finrank_range_le (leading b π 0).vecMulLinear
  simpa [leadingRank, NonSofic.rankD] using h

theorem leadingRank_le {D : Type*} [DivisionRing D] {n : ℕ}
    (b : Fin n × Fin n → D) (π : Equiv.Perm (Fin n × Fin n)) (k : ℕ) :
    leadingRank b π k ≤ NonSofic.rankD (Matrix.of fun u v => b (π (u, v))) := by
  let M : Matrix (Fin n) (Fin n) D := Matrix.of fun u v => b (π (u, v))
  exact NonSofic.rankD_submatrix_le M
    (fun i : Initial n k => i.val) (fun i : Initial n k => i.val)

noncomputable def exposed (n k : ℕ) (hk : k < n) : Finset (Fin n × Fin n) :=
  ((Finset.univ.filter fun q => q.1.val < k + 1 ∧ q.2.val < k + 1)).erase
    (⟨k, hk⟩, ⟨k, hk⟩)

theorem exposed_unused (n k : ℕ) (hk : k < n) :
    Fintype.card {q // q ∉ exposed n k hk} = unusedCount n (k + 1) := by
  have hcard : (Finset.univ.filter (fun q : Fin n × Fin n =>
      q.1.val < k + 1 ∧ q.2.val < k + 1)).card = (k + 1) ^ 2 := by
    have heq : (Finset.univ.filter (fun q : Fin n × Fin n =>
        q.1.val < k + 1 ∧ q.2.val < k + 1)) =
        (Finset.univ.filter fun i : Fin n => i.val < k + 1) ×ˢ
          (Finset.univ.filter fun i : Fin n => i.val < k + 1) := by ext q; simp
    have hi : (Finset.univ.filter fun i : Fin n => i.val < k + 1).card = k + 1 := by
      rw [← Fintype.card_subtype]
      exact (Fintype.card_congr (initialEquiv n (k + 1) hk).symm).trans (Fintype.card_fin _)
    rw [heq, Finset.card_product, hi, pow_two]
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  unfold exposed
  rw [Finset.card_erase_of_mem (by simp), hcard]
  simp [unusedCount, pow_two]

/-- Equal exposed values force equal bad corners, even after earlier rank failures. -/
theorem leading_bad_corner_unique {D : Type*} [DivisionRing D] {n : ℕ}
    (b : Fin n × Fin n → D) (hb : Function.Injective b) (k : ℕ) (hk : k < n)
    (π ρ : Equiv.Perm (Fin n × Fin n))
    (hπ : leadingRank b π (k + 1) ≤ leadingRank b π k)
    (hρ : leadingRank b ρ (k + 1) ≤ leadingRank b ρ k)
    (he : ∀ q ∈ exposed n k hk, π q = ρ q) :
    π (⟨k, hk⟩, ⟨k, hk⟩) = ρ (⟨k, hk⟩, ⟨k, hk⟩) := by
  let c : Fin n := ⟨k, hk⟩
  let T := leading b π k
  let u : Matrix (Initial n k) Unit D := Matrix.of fun i _ => b (π (i.val, c))
  let v : Matrix Unit (Initial n k) D := Matrix.of fun _ j => b (π (c, j.val))
  have he' (i j : Initial n (k + 1)) (hij : (i.val, j.val) ≠ (c, c)) :
      b (π (i.val, j.val)) = b (ρ (i.val, j.val)) := by
    apply congrArg b (he _ ?_)
    simp only [exposed, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hij, i.property, j.property⟩
  have hT : leading b ρ k = T := by
    ext i j
    apply (he' ⟨i.val, Nat.lt_succ_of_lt i.property⟩
      ⟨j.val, Nat.lt_succ_of_lt j.property⟩ ?_).symm
    intro h
    have hi := congrArg (fun q : Fin n × Fin n => q.1.val) h
    have := i.property
    dsimp [c] at hi
    omega
  have hB (σ : Equiv.Perm (Fin n × Fin n))
      (hσ : σ = π ∨ σ = ρ) :
      (leading b σ (k + 1)).submatrix (initialStep n k hk) (initialStep n k hk) =
        Matrix.fromBlocks T u v (Matrix.of fun _ _ : Unit => b (σ (c, c))) := by
    ext (i | i) (j | j)
    · rcases hσ with rfl | rfl
      · rfl
      · exact congrFun (congrFun hT i) j
    · cases j
      rcases hσ with rfl | rfl
      · rfl
      · apply (he' ⟨i.val, Nat.lt_succ_of_lt i.property⟩ ⟨c, Nat.lt_succ_self k⟩ ?_).symm
        intro h
        have hi := congrArg (fun q : Fin n × Fin n => q.1.val) h
        have := i.property
        dsimp [c] at hi
        omega
    · cases i
      rcases hσ with rfl | rfl
      · rfl
      · apply (he' ⟨c, Nat.lt_succ_self k⟩ ⟨j.val, Nat.lt_succ_of_lt j.property⟩ ?_).symm
        intro h
        have hj := congrArg (fun q : Fin n × Fin n => q.2.val) h
        have := j.property
        dsimp [c] at hj
        omega
    · cases i; cases j; rfl
  have hrπ := NonSofic.rankD_submatrix_equiv (leading b π (k + 1))
    (initialStep n k hk) (initialStep n k hk)
  have hrρ := NonSofic.rankD_submatrix_equiv (leading b ρ (k + 1))
    (initialStep n k hk) (initialStep n k hk)
  rw [hB π (Or.inl rfl)] at hrπ
  rw [hB ρ (Or.inr rfl)] at hrρ
  apply hb
  apply bad_border_corner_unique T u v
  · rw [hrπ]
    exact hπ
  · rw [hrρ]
    simpa only [leadingRank, hT] using hρ

/-- An unconditional stage bound. No event asserting previous pivot success appears. -/
theorem leading_bad_count {D : Type*} [DivisionRing D] {n : ℕ}
    (hn : 2 ≤ n) (b : Fin n × Fin n → D) (hb : Function.Injective b)
    (k : ℕ) (hk : k + 1 < n) :
    2 * n * (∑ π : Equiv.Perm (Fin n × Fin n),
      if leadingRank b π (k + 1) - leadingRank b π k = 0 then 1 else 0) ≤
      Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
  let Bad (π : Equiv.Perm (Fin n × Fin n)) :=
    leadingRank b π (k + 1) - leadingRank b π k = 0
  have hkn : k < n := by omega
  have hcount := bad_count_mul_unused_le (exposed n k hkn)
    (⟨k, hkn⟩, ⟨k, hkn⟩) (by simp [exposed]) Bad (by
      intro π ρ hπ hρ he
      exact leading_bad_corner_unique b hb k hkn π ρ
        (Nat.sub_eq_zero_iff_le.mp hπ) (Nat.sub_eq_zero_iff_le.mp hρ) he)
  rw [exposed_unused] at hcount
  have hcount' : (∑ π : Equiv.Perm (Fin n × Fin n),
      if leadingRank b π (k + 1) - leadingRank b π k = 0 then 1 else 0) *
      unusedCount n (k + 1) ≤ Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
    simpa [Fintype.card_subtype, Bad] using hcount
  have hu := unusedCount_ge n (k + 1) hn (by omega) hk
  have hmul := Nat.mul_le_mul_left
    (∑ π : Equiv.Perm (Fin n × Fin n),
      if leadingRank b π (k + 1) - leadingRank b π k = 0 then 1 else 0) hu
  apply le_trans _ hcount'
  simpa [Nat.mul_comm] using hmul

/-- Integer form of the strong permutation average, before any division. -/
theorem average_integer {D : Type*} [DivisionRing D] {n : ℕ}
    (hn : 2 ≤ n) (b : Fin n × Fin n → D) (hb : Function.Injective b) :
    (n - 1) * (2 * n - 1) * Fintype.card (Equiv.Perm (Fin n × Fin n)) ≤
      2 * n * ∑ π : Equiv.Perm (Fin n × Fin n),
        NonSofic.rankD (Matrix.of fun u v => b (π (u, v))) := by
  let growth (s : Fin (n - 1)) (π : Equiv.Perm (Fin n × Fin n)) :=
    leadingRank b π (s.val + 1) - leadingRank b π s.val
  have hg := sum_growth_ge (2 * n) (by omega : 1 ≤ 2 * n) growth (by
    intro s
    exact leading_bad_count hn b hb s.val (by have := s.isLt; omega))
  have htel (π : Equiv.Perm (Fin n × Fin n)) :
      (∑ s, growth s π) = leadingRank b π (n - 1) := by
    have h := sum_increments (leadingRank b π) (leadingRank_mono b π) (n - 1)
    change (∑ s : Fin (n - 1),
      (leadingRank b π (s.val + 1) - leadingRank b π s.val)) = _
    rw [Fin.sum_univ_eq_sum_range (fun k => leadingRank b π (k + 1) - leadingRank b π k)]
    simpa [leadingRank_zero] using h
  simp only [Fintype.card_fin, htel] at hg
  exact hg.trans (Nat.mul_le_mul_left (2 * n)
    (Finset.sum_le_sum fun π _ => leadingRank_le b π (n - 1)))

/-- The strong permutation bound; distinct entries suffice without nonzero assumptions. -/
theorem average {D : Type*} [DivisionRing D] (n : ℕ) (hn : 2 ≤ n)
    (b : Fin n × Fin n → D) (hb : Function.Injective b) :
    ((n - 1 : ℕ) : ℚ) * (1 - 1 / (2 * (n : ℚ))) ≤
      (∑ π : Equiv.Perm (Fin n × Fin n),
        (NonSofic.rankD (Matrix.of fun u v => b (π (u, v))) : ℚ)) /
      Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
  have h := average_integer hn b hb
  have hq := (Nat.cast_le (α := ℚ)).mpr h
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * n)] at hq
  have hnq : (0 : ℚ) < 2 * n := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    positivity
  have hc : (0 : ℚ) < Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hc).mpr
  have heq : ((n - 1 : ℕ) : ℚ) * (1 - 1 / (2 * (n : ℚ))) *
      Fintype.card (Equiv.Perm (Fin n × Fin n)) =
      (((n - 1 : ℕ) : ℚ) * (2 * n - 1) *
        Fintype.card (Equiv.Perm (Fin n × Fin n))) / (2 * n) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ hnq).mpr
  nlinarith [hq]

/-- One arrangement works for all line arrays, with the normalization rank added. -/
theorem exists_common_normalized {D I : Type*} [DivisionRing D] [Fintype I]
    (n : ℕ) (hn : 2 ≤ n) (b : I → Fin n × Fin n → D)
    (hb : ∀ i, Function.Injective (b i)) :
    ∃ π : Equiv.Perm (Fin n × Fin n),
      (Fintype.card I : ℚ) * ((n : ℚ) + 1) / 2 ≤
        ∑ i, (1 + (NonSofic.rankD (Matrix.of fun u v => b i (π (u, v))) : ℚ)) := by
  have hc : (0 : ℚ) < Fintype.card (Equiv.Perm (Fin n × Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hpred : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hline (i : I) := (strong_bound_ge_half n hn).trans (average n hn (b i) (hb i))
  have hex := exists_arrangement_ge
    (fun (i : I) (π : Equiv.Perm (Fin n × Fin n)) =>
      1 + (NonSofic.rankD (Matrix.of fun u v => b i (π (u, v))) : ℚ))
    (((n : ℚ) + 1) / 2) (by
      intro i
      have h := (le_div_iff₀ hc).mp (hline i)
      rw [hpred] at h
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      nlinarith)
  simpa only [mul_div_assoc] using hex

end DomainNonembedding.Permutation

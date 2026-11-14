import FiniteLean.GroupTheory.DivisionRing.RankD
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

set_option autoImplicit false

namespace DomainNonembedding.Permutation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exchange a corner with one unexposed position, then read the arrangement. -/
def swapCorner {α : Type*} [DecidableEq α] (c : α) (π : Equiv.Perm α) (a : α) :
    Equiv.Perm α := (Equiv.swap c a).trans π

/-- Double counting replaces conditional probability. A bad arrangement is
sent to each possible corner exchange. Uniqueness of a bad corner makes this
map injective, so at most one out of the unused positions can be bad. -/
theorem bad_count_mul_unused_le {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (c : α) (hc : c ∉ E) (Bad : Equiv.Perm α → Prop)
    (hunique : ∀ π ρ, Bad π → Bad ρ →
      (∀ e ∈ E, π e = ρ e) → π c = ρ c) :
    Fintype.card {π // Bad π} * Fintype.card {a // a ∉ E} ≤
      Fintype.card (Equiv.Perm α) := by
  classical
  let f : ({π // Bad π} × {a // a ∉ E}) → Equiv.Perm α :=
    fun q => swapCorner c q.1.val q.2.val
  have hf : Function.Injective f := by
    rintro ⟨⟨π, hπ⟩, ⟨a, ha⟩⟩ ⟨⟨ρ, hρ⟩, ⟨b, hb⟩⟩ heq
    change swapCorner c π a = swapCorner c ρ b at heq
    have hexposed : ∀ e ∈ E, π e = ρ e := by
      intro e he
      have hec : e ≠ c := by intro h; subst e; exact hc he
      have hea : e ≠ a := by intro h; subst e; exact ha he
      have heb : e ≠ b := by intro h; subst e; exact hb he
      have hv := congrArg (fun σ : Equiv.Perm α => σ e) heq
      simpa [swapCorner, Equiv.trans_apply, Equiv.swap_apply_def, hec, hea, heb] using hv
    have hcorner : π c = ρ c := hunique π ρ hπ hρ hexposed
    have hab : a = b := by
      apply (swapCorner c π a).injective
      calc
        swapCorner c π a a = π c := by simp [swapCorner]
        _ = ρ c := hcorner
        _ = swapCorner c ρ b b := by simp [swapCorner]
        _ = swapCorner c π a b := congrArg (fun σ : Equiv.Perm α => σ b) heq.symm
    subst b
    have hperm : π = ρ := by
      ext x
      have hv := congrArg (fun σ : Equiv.Perm α => σ (Equiv.swap c a x)) heq
      simpa [swapCorner] using hv
    subst ρ
    rfl
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective f hf

/-- The actual number of entries available after exposing a k-square except its corner. -/
def unusedCount (n k : ℕ) : ℕ := n ^ 2 - (k ^ 2 - 1)

/-- The paper's denominator bound, with natural-number subtraction made explicit. -/
theorem unusedCount_ge (n k : ℕ) (hn : 2 ≤ n) (hk₀ : 1 ≤ k) (hk : k < n) :
    2 * n ≤ unusedCount n k := by
  unfold unusedCount
  have hkn : k + 1 ≤ n := hk
  have hkpos : 1 ≤ k ^ 2 := by nlinarith
  have hk' : k ≤ n - 1 := by omega
  have hn' : n = (n - 1) + 1 := by omega
  have hsq : k * k ≤ (n - 1) * (n - 1) := Nat.mul_le_mul hk' hk'
  have hbound : k ^ 2 + 2 * n ≤ n ^ 2 + 1 := by nlinarith
  omega

/-- Natural-number increments telescope for a monotone rank sequence. -/
theorem sum_increments (r : ℕ → ℕ) (hr : Monotone r) (n : ℕ) :
    (∑ k ∈ Finset.range n, (r (k + 1) - r k)) + r 0 = r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm : r n ≤ r (n + 1) := hr (Nat.le_succ n)
    change (∑ k ∈ Finset.range n, (r (k + 1) - r k)) +
      (r (n + 1) - r n) + r 0 = r (n + 1)
    omega

/-- Sum integer rank increments using only a bound on zero increments.
The stage events may be arbitrarily dependent. -/
theorem sum_growth_ge {Perms S : Type*} [Fintype Perms] [Fintype S]
    (N : ℕ) (hN : 1 ≤ N) (growth : S → Perms → ℕ)
    (hbad : ∀ s, N * (∑ π, if growth s π = 0 then 1 else 0) ≤ Fintype.card Perms) :
    Fintype.card S * (N - 1) * Fintype.card Perms ≤ N * ∑ π, ∑ s, growth s π := by
  classical
  have hstage (s : S) : (N - 1) * Fintype.card Perms ≤ N * ∑ π, growth s π := by
    have hsum : Fintype.card Perms ≤
        (∑ π, growth s π) + ∑ π, if growth s π = 0 then 1 else 0 := by
      calc
        Fintype.card Perms = ∑ _π : Perms, 1 := by simp
        _ ≤ ∑ π, (growth s π + if growth s π = 0 then 1 else 0) := by
          apply Finset.sum_le_sum
          intro π _
          split_ifs <;> omega
        _ = _ := Finset.sum_add_distrib
    have hmult := Nat.mul_le_mul_left N hsum
    have hb := hbad s
    have hpred : N = N - 1 + 1 := by omega
    nlinarith
  calc
    Fintype.card S * (N - 1) * Fintype.card Perms =
        ∑ _s : S, (N - 1) * Fintype.card Perms := by simp; ring
    _ ≤ ∑ s, N * ∑ π, growth s π := Finset.sum_le_sum fun s _ => hstage s
    _ = N * ∑ π, ∑ s, growth s π := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- Enumerating arrangements really uses all (n^2)! entry permutations. -/
theorem arrangement_card (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n × Fin n)) = (n ^ 2).factorial := by
  simp [Fintype.card_perm, pow_two]

/-- The strong paper lower bound implies the weaker bound used in the contradiction. -/
theorem strong_bound_ge_half (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℚ) / 2 ≤
      ((n - 1 : ℕ) : ℚ) * (1 - 1 / (2 * (n : ℚ))) := by
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℚ) < 2 * n := by positivity
  have hfrac : (1 : ℚ) / (2 * n) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℚ) < 2)).2
    nlinarith
  have hnonneg : (0 : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by positivity
  nlinarith

/-- Linearity of finite averaging permits the SAME arrangement for every line. -/
theorem sum_arrangements_ge {I Perms : Type*} [Fintype I] [Fintype Perms]
    (f : I → Perms → ℚ) (c : ℚ)
    (h : ∀ i, (Fintype.card Perms : ℚ) * c ≤ ∑ π, f i π) :
    (Fintype.card Perms : ℚ) * (Fintype.card I : ℚ) * c ≤ ∑ π, ∑ i, f i π := by
  calc
    (Fintype.card Perms : ℚ) * (Fintype.card I : ℚ) * c =
        ∑ _i : I, (Fintype.card Perms : ℚ) * c := by simp; ring
    _ ≤ ∑ i, ∑ π, f i π := Finset.sum_le_sum fun i _ => h i
    _ = ∑ π, ∑ i, f i π := Finset.sum_comm

/-- A common arrangement attains the total lower bound; no independence is assumed. -/
theorem exists_arrangement_ge {I Perms : Type*} [Fintype I] [Fintype Perms] [Nonempty Perms]
    (f : I → Perms → ℚ) (c : ℚ)
    (h : ∀ i, (Fintype.card Perms : ℚ) * c ≤ ∑ π, f i π) :
    ∃ π, (Fintype.card I : ℚ) * c ≤ ∑ i, f i π := by
  classical
  by_contra hnone
  push Not at hnone
  have hlt : (∑ π, ∑ i, f i π) <
      ∑ _π : Perms, (Fintype.card I : ℚ) * c :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun π _ => hnone π)
  have hge := sum_arrangements_ge f c h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  nlinarith

/-- Noncommutative LDU factorization. The order C A^-1 B is essential. -/
theorem block_factorization {R m l : Type*} [Ring R] [Fintype m] [Fintype l]
    [DecidableEq m] [DecidableEq l] (A : (Matrix m m R)ˣ)
    (B : Matrix m l R) (C : Matrix l m R) (Z : Matrix l l R) :
    Matrix.fromBlocks (A : Matrix m m R) B C Z =
      Matrix.fromBlocks 1 0 (C * (↑A⁻¹ : Matrix m m R)) 1 *
        Matrix.fromBlocks (A : Matrix m m R) 0 0
          (Z - C * (↑A⁻¹ : Matrix m m R) * B) *
        Matrix.fromBlocks 1 ((↑A⁻¹ : Matrix m m R) * B) 0 1 := by
  have hleft : (A : Matrix m m R) * ((↑A⁻¹ : Matrix m m R) * B) = B := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hright : C * (↑A⁻¹ : Matrix m m R) * (A : Matrix m m R) = C := by
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, hleft, hright,
    Matrix.mul_assoc, add_sub_cancel]

/-- With a fixed invertible old block, a vanishing Schur complement determines
at most one corner, over any division ring (indeed any ring). -/
theorem schur_corner_unique {R m : Type*} [Ring R] [Fintype m] [DecidableEq m]
    (A : (Matrix m m R)ˣ) (B : Matrix m Unit R) (C : Matrix Unit m R)
    {z w : R}
    (hz : (Matrix.of fun _ _ : Unit => z) - C * (↑A⁻¹ : Matrix m m R) * B = 0)
    (hw : (Matrix.of fun _ _ : Unit => w) - C * (↑A⁻¹ : Matrix m m R) * B = 0) : z = w := by
  have hz' := sub_eq_zero.mp hz
  have hw' := sub_eq_zero.mp hw
  exact congrFun (congrFun (hz'.trans hw'.symm) ()) ()

/-- The full bordering claim, including a singular old block: if bordering
fails to increase rank for two corner values, those values are equal. -/
theorem bad_border_corner_unique {D m : Type*} [DivisionRing D] [Fintype m]
    [DecidableEq m] (T : Matrix m m D) (u : Matrix m Unit D) (v : Matrix Unit m D)
    {z w : D}
    (hz : NonSofic.rankD (Matrix.fromBlocks T u v (Matrix.of fun _ _ : Unit => z)) ≤ NonSofic.rankD T)
    (hw : NonSofic.rankD (Matrix.fromBlocks T u v (Matrix.of fun _ _ : Unit => w)) ≤ NonSofic.rankD T) :
    z = w := by
  let A : Matrix m (m ⊕ Unit) D := Matrix.of fun i j => Sum.elim (T i) (u i) j
  let B (q : D) : Matrix (m ⊕ Unit) (m ⊕ Unit) D :=
    Matrix.fromBlocks T u v (fun _ _ : Unit => q)
  let W := LinearMap.range A.vecMulLinear
  let f : W →ₗ[D] (m → D) := NonSofic.sumProjL m Unit ∘ₗ W.subtype
  have hproj : LinearMap.range T.vecMulLinear ≤ LinearMap.range f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨A.vecMulLinear x, LinearMap.mem_range_self _ _⟩, ?_⟩
    ext i
    simp [f, A, NonSofic.sumProjL, Matrix.vecMul, dotProduct]
  have hdim : NonSofic.rankD T ≤ Module.finrank D W :=
    (Submodule.finrank_mono hproj).trans (LinearMap.finrank_range_le f)
  have hle (q : D) : W ≤ LinearMap.range (B q).vecMulLinear := by
    rintro _ ⟨x, rfl⟩
    refine ⟨Sum.elim x 0, ?_⟩
    simp only [B, Matrix.vecMulLinear_apply]
    ext (i | i) <;> simp [A, Matrix.vecMul, dotProduct, Matrix.fromBlocks]
  have heq (q : D) (hq : NonSofic.rankD (B q) ≤ NonSofic.rankD T) :
      W = LinearMap.range (B q).vecMulLinear :=
    Submodule.eq_of_le_of_finrank_le (hle q) (hq.trans hdim)
  have hW : Module.finrank D W ≤ NonSofic.rankD T :=
    (Submodule.finrank_mono (hle z)).trans hz
  have hrn := f.finrank_range_add_finrank_ker
  have hpdim := Submodule.finrank_mono hproj
  have hker : Module.finrank D (LinearMap.ker f) = 0 := by
    change NonSofic.rankD T ≤ Module.finrank D (LinearMap.range f) at hpdim
    omega
  have hf : Function.Injective f :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  have hrow (q : D) (hq : NonSofic.rankD (B q) ≤ NonSofic.rankD T) :
      B q (Sum.inr ()) ∈ W := by
    rw [heq q hq]
    refine ⟨Pi.single (Sum.inr ()) 1, ?_⟩
    simp [Matrix.row]
  have hout := hf (show f ⟨B z (Sum.inr ()), hrow z hz⟩ =
      f ⟨B w (Sum.inr ()), hrow w hw⟩ from rfl)
  have hv := congrArg (fun y : W => (y : m ⊕ Unit → D) (Sum.inr ())) hout
  exact hv

/-- Lower and upper unitriangular matrices work over a noncommutative ring. -/
def lowerUnit {R m l : Type*} [Ring R] [Fintype m] [Fintype l]
    [DecidableEq m] [DecidableEq l] (C : Matrix l m R) :
    (Matrix (m ⊕ l) (m ⊕ l) R)ˣ where
  val := Matrix.fromBlocks 1 0 C 1
  inv := Matrix.fromBlocks 1 0 (-C) 1
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

def upperUnit {R m l : Type*} [Ring R] [Fintype m] [Fintype l]
    [DecidableEq m] [DecidableEq l] (B : Matrix m l R) :
    (Matrix (m ⊕ l) (m ⊕ l) R)ˣ where
  val := Matrix.fromBlocks 1 B 0 1
  inv := Matrix.fromBlocks 1 (-B) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- A nonzero scalar is an invertible one-entry matrix, without a determinant. -/
def scalarUnit {D : Type*} [DivisionRing D] (z : D) (hz : z ≠ 0) :
    (Matrix Unit Unit D)ˣ where
  val := Matrix.of fun _ _ => z
  inv := Matrix.of fun _ _ => z⁻¹
  val_inv := by ext i j; simp [Matrix.mul_apply, hz]
  inv_val := by ext i j; simp [Matrix.mul_apply, hz]

/-- Block diagonal units, again with no commutativity assumption. -/
def diagonalUnit {R m l : Type*} [Ring R] [Fintype m] [Fintype l]
    [DecidableEq m] [DecidableEq l] (A : (Matrix m m R)ˣ) (Z : (Matrix l l R)ˣ) :
    (Matrix (m ⊕ l) (m ⊕ l) R)ˣ where
  val := Matrix.fromBlocks (A : Matrix m m R) 0 0 (Z : Matrix l l R)
  inv := Matrix.fromBlocks (↑A⁻¹ : Matrix m m R) 0 0 (↑Z⁻¹ : Matrix l l R)
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/-- Excluding the unique Schur corner gives an invertible border over any division ring. -/
theorem border_isUnit_of_corner_ne {D m : Type*} [DivisionRing D] [Fintype m]
    [DecidableEq m] (A : (Matrix m m D)ˣ) (B : Matrix m Unit D)
    (C : Matrix Unit m D) (z : D)
    (hz : z ≠ (C * (↑A⁻¹ : Matrix m m D) * B) () ()) :
    IsUnit (Matrix.fromBlocks (A : Matrix m m D) B C (Matrix.of fun _ _ : Unit => z)) := by
  let c : D := z - (C * (↑A⁻¹ : Matrix m m D) * B) () ()
  have hc : c ≠ 0 := sub_ne_zero.mpr hz
  have hcorner : (Matrix.of fun _ _ : Unit => z) - C * (↑A⁻¹ : Matrix m m D) * B =
      (scalarUnit c hc : Matrix Unit Unit D) := by
    ext i j
    cases i
    cases j
    rfl
  rw [block_factorization A B C (Matrix.of fun _ _ : Unit => z), hcorner]
  exact ((lowerUnit (C * (↑A⁻¹ : Matrix m m D))).isUnit.mul
    (diagonalUnit A (scalarUnit c hc)).isUnit).mul
      (upperUnit ((↑A⁻¹ : Matrix m m D) * B)).isUnit

end DomainNonembedding.Permutation

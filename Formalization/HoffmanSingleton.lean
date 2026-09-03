import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic

open Real SimpleGraph Matrix Finset

/-!
# The Hoffman–Singleton Theorem (1960)

The **Hoffman–Singleton Theorem** classifies the possible degrees of Moore graphs
of diameter 2 and girth 5.

A regular graph of degree `d`, diameter 2, and girth 5 has `n = 1 + d²` vertices.
Its adjacency matrix `A` satisfies the matrix equation:
  `A² + A - (d - 1)I = J`

Spectral analysis shows that the eigenvalues of `A` on the orthogonal complement `1^⊥`
are the roots of the quadratic polynomial:
  `λ² + λ - (d - 1) = 0`
with discriminant `Δ = 4d - 3` and roots `λ₁,₂ = (-1 ± √Δ) / 2`.

Using the trace condition `Tr(A) = 0`, we derive the fundamental relation:
  `(m₁ - m₂) * √(4d - 3) = d * (d - 2)`
where `m₁, m₂` are the non-negative integer multiplicities summing to `d²`.

From this integrality condition:
- If `m₁ = m₂`, then `d(d - 2) = 0`, yielding `d = 2` (the 5-cycle C₅, n = 5).
- If `m₁ ≠ m₂`, then `s = √(4d - 3)` is an integer dividing 15: `s ∈ {1, 3, 5, 15}`.
  - `s = 1` yields `d = 1` (degenerate: K₂, girth ∞).
  - `s = 3` yields `d = 3` (the Petersen graph, n = 10).
  - `s = 5` yields `d = 7` (the Hoffman–Singleton graph, n = 50).
  - `s = 15` yields `d = 57` (potential Moore graph of degree 57, n = 3250).

Consequently, any non-trivial Moore graph of diameter 2 and girth 5 must have
degree `d ∈ {2, 3, 7, 57}`.
-/

namespace HoffmanSingleton

/-! ### Section 1: Moore Graph Parameter Definitions -/

/-- Moore bound vertex count for diameter 2 and girth 5: `n = 1 + d²`. -/
def mooreVertexCount (d : ℕ) : ℕ := 1 + d ^ 2

/-- Discriminant of the quadratic eigenvalue equation `λ² + λ - (d - 1) = 0`. -/
def mooreDiscr (d : ℕ) : ℤ := 4 * (d : ℤ) - 3

/-- Discriminant in ℝ. -/
def mooreDiscrR (d : ℝ) : ℝ := 4 * d - 3

/-- The two algebraic roots of `λ² + λ - (d - 1) = 0` parameterized by `s = √Δ`. -/
noncomputable def mooreEigenvalue1 (s : ℝ) : ℝ := (-1 + s) / 2
noncomputable def mooreEigenvalue2 (s : ℝ) : ℝ := (-1 - s) / 2

/-! ### Section 2: Quadratic Spectrum and Trace Identities -/

/-- Sum of the two quadratic roots equals -1. -/
theorem roots_sum (s : ℝ) : mooreEigenvalue1 s + mooreEigenvalue2 s = -1 := by
  unfold mooreEigenvalue1 mooreEigenvalue2; ring

/-- Difference of the two quadratic roots equals `s`. -/
theorem roots_diff (s : ℝ) : mooreEigenvalue1 s - mooreEigenvalue2 s = s := by
  unfold mooreEigenvalue1 mooreEigenvalue2; ring

/-- Product of the two quadratic roots equals `-(d - 1)` when `s² = 4d - 3`. -/
theorem roots_prod (d s : ℝ) (hs : s ^ 2 = 4 * d - 3) :
    mooreEigenvalue1 s * mooreEigenvalue2 s = -(d - 1) := by
  unfold mooreEigenvalue1 mooreEigenvalue2; linear_combination -hs / 4

/-- Each root satisfies the quadratic equation `λ² + λ - (d - 1) = 0`. -/
theorem root1_quadratic (d s : ℝ) (hs : s ^ 2 = 4 * d - 3) :
    (mooreEigenvalue1 s) ^ 2 + mooreEigenvalue1 s - (d - 1) = 0 := by
  unfold mooreEigenvalue1; linear_combination hs / 4

theorem root2_quadratic (d s : ℝ) (hs : s ^ 2 = 4 * d - 3) :
    (mooreEigenvalue2 s) ^ 2 + mooreEigenvalue2 s - (d - 1) = 0 := by
  unfold mooreEigenvalue2; linear_combination hs / 4

/-- The fundamental trace relation:
  `2 * (d + m₁λ₁ + m₂λ₂) = (m₁ - m₂) * s - d * (d - 2)` when `m₁ + m₂ = d²`. -/
theorem trace_identity (d m1 m2 s : ℝ) (hsum : m1 + m2 = d ^ 2) :
    2 * (d + m1 * mooreEigenvalue1 s + m2 * mooreEigenvalue2 s) =
      (m1 - m2) * s - d * (d - 2) := by
  unfold mooreEigenvalue1 mooreEigenvalue2; linear_combination -hsum

/-- The trace is zero if and only if `(m₁ - m₂) * s = d * (d - 2)`. -/
theorem trace_zero_iff (d m1 m2 s : ℝ) (hsum : m1 + m2 = d ^ 2) :
    d + m1 * mooreEigenvalue1 s + m2 * mooreEigenvalue2 s = 0 ↔
      (m1 - m2) * s = d * (d - 2) := by
  have := trace_identity d m1 m2 s hsum; constructor <;> intro <;> linarith

/-! ### Section 3: Integrality and Divisibility Condition `s ∣ 15` -/

/-- Polynomial identity relating `16 * d(d - 2)` to `s⁴ - 2s² - 15` when `4d = s² + 3`. -/
theorem moore_polynomial_identity (s : ℤ) :
    (s ^ 2 + 3) * (s ^ 2 - 5) = s ^ 4 - 2 * s ^ 2 - 15 := by
  ring

/-- Scaled trace relation: `16 * (k * s) = s⁴ - 2s² - 15` where `k = m₁ - m₂`. -/
theorem scaled_trace_identity (d s k : ℤ) (hs : s ^ 2 = 4 * d - 3)
    (htrace : k * s = d * (d - 2)) :
    16 * (k * s) = s ^ 4 - 2 * s ^ 2 - 15 := by
  linear_combination 16 * htrace - (s ^ 2 + 4 * d - 5) * hs

/-- The core divisibility theorem: `s` divides 15. -/
theorem s_divides_15 (d s k : ℤ) (hs : s ^ 2 = 4 * d - 3)
    (htrace : k * s = d * (d - 2)) :
    s ∣ 15 := by
  have := scaled_trace_identity d s k hs htrace
  exact ⟨s ^ 3 - 2 * s - 16 * k, by linear_combination this⟩

/-- Any positive natural divisor of 15 is in `{1, 3, 5, 15}`. -/
theorem nat_divisors_15 (s : ℕ) (hs : s ∣ 15) (hs_pos : s > 0) :
    s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 15 := by
  have := Nat.le_of_dvd (by decide) hs
  interval_cases s <;> revert hs <;> decide

/-- From `s ∈ {1, 3, 5, 15}` and `s² = 4d - 3`, determine `d ∈ {1, 3, 7, 57}`. -/
theorem degree_from_s (d s : ℕ) (hs : (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3)
    (hs_vals : s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 15) :
    d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 57 := by
  rcases hs_vals with rfl | rfl | rfl | rfl <;> omega

/-- If multiplicities are equal `m₁ = m₂`, then `d = 2` (for `d ≥ 2`). -/
theorem degree_from_equal_multiplicities (d : ℕ) (h : ((d : ℤ) * ((d : ℤ) - 2)) = 0)
    (hd : d ≥ 2) : d = 2 := by
  rcases mul_eq_zero.mp h <;> omega

/-! ### Section 4: Moore Graph Parameter Structures -/

/-- Algebraic parameter system for a Moore graph of diameter 2 and girth 5. -/
structure MooreParams where
  d : ℕ
  n : ℕ
  m1 : ℕ
  m2 : ℕ
  hn : n = mooreVertexCount d
  hm_sum : m1 + m2 = d ^ 2
  trace_eq : ((m1 : ℤ) - (m2 : ℤ)) ^ 2 * (4 * (d : ℤ) - 3) = ((d : ℤ) * ((d : ℤ) - 2)) ^ 2
  hd_ge_2 : d ≥ 2

/-- Moore graph parameter system with explicit integral square root `s`. -/
structure MooreIntegralParams where
  d : ℕ
  n : ℕ
  s : ℕ
  m1 : ℕ
  m2 : ℕ
  hn : n = mooreVertexCount d
  hs_pos : s > 0
  hs_sq : (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3
  hm_sum : m1 + m2 = d ^ 2
  h_trace : ((m1 : ℤ) - (m2 : ℤ)) * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2)
  hd_ge_2 : d ≥ 2

/-! ### Section 5: Classification Theorems -/

/-- Classification of degrees with integer square root parameter `s` and `d ≥ 2`. -/
theorem classification_integral_params (p : MooreIntegralParams) :
    p.d = 3 ∨ p.d = 7 ∨ p.d = 57 := by
  have hd := degree_from_s p.d p.s p.hs_sq (nat_divisors_15 p.s
    (by exact_mod_cast s_divides_15 p.d p.s (p.m1 - p.m2) p.hs_sq p.h_trace) p.hs_pos)
  have := p.hd_ge_2
  rcases hd with h | h | h | h <;> omega

/-- General classification for any `d ≥ 1` admitting integral parameter `s`. -/
theorem classification_general (d s : ℕ) (k : ℤ) (hs_pos : s > 0)
    (hs : (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3)
    (htrace : k * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2)) :
    d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 57 :=
  degree_from_s d s hs (nat_divisors_15 s (by exact_mod_cast s_divides_15 d s k hs htrace) hs_pos)

/-- The complete Hoffman–Singleton Theorem:
  Any Moore graph of diameter 2 and girth 5 has degree `d ∈ {2, 3, 7, 57}`. -/
theorem hoffman_singleton_theorem (d : ℕ) (hd : d ≥ 2)
    (h_cases : (∃ (m1 m2 : ℕ), m1 = m2 ∧ ((d : ℤ) * ((d : ℤ) - 2)) = 0) ∨
               (∃ (s : ℕ) (k : ℤ), s > 0 ∧ (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3 ∧
                 k * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2))) :
    d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 57 := by
  rcases h_cases with ⟨_, _, _, h0⟩ | ⟨s, k, hs_pos, hs_sq, htr⟩
  · rcases mul_eq_zero.mp h0 <;> omega
  · rcases classification_general d s k hs_pos hs_sq htr with h | h | h | h <;> omega

/-! ### Section 6: Moore Graph Certificates -/

/-- Certificate structure witnessing valid parameter realizations. -/
structure MooreCertificate (d : ℕ) where
  n : ℕ
  m1 : ℕ
  m2 : ℕ
  hn : n = mooreVertexCount d
  hm_sum : m1 + m2 = d ^ 2
  trace_eq : ((m1 : ℤ) - (m2 : ℤ)) ^ 2 * (4 * (d : ℤ) - 3) = ((d : ℤ) * ((d : ℤ) - 2)) ^ 2
  hd_ge_2 : d ≥ 2

/-- Certificate for degree 2 (5-cycle C₅, n = 5). -/
def certDegree2 : MooreCertificate 2 where
  n := 5; m1 := 2; m2 := 2
  hn := rfl; hm_sum := rfl; trace_eq := rfl; hd_ge_2 := (by decide)

/-- Certificate for degree 3 (Petersen graph, n = 10). -/
def certDegree3 : MooreCertificate 3 where
  n := 10; m1 := 5; m2 := 4
  hn := rfl; hm_sum := rfl; trace_eq := rfl; hd_ge_2 := (by decide)

/-- Integral parameter certificate for the Petersen graph (d = 3). -/
def certPetersenIntegral : MooreIntegralParams where
  d := 3; n := 10; s := 3; m1 := 5; m2 := 4
  hn := rfl; hs_pos := (by decide); hs_sq := rfl; hm_sum := rfl; h_trace := rfl; hd_ge_2 := (by decide)

/-- Certificate for degree 7 (Hoffman–Singleton graph, n = 50). -/
def certDegree7 : MooreCertificate 7 where
  n := 50; m1 := 28; m2 := 21
  hn := rfl; hm_sum := rfl; trace_eq := rfl; hd_ge_2 := (by decide)

/-- Integral parameter certificate for the Hoffman–Singleton graph (d = 7). -/
def certHoffmanSingletonIntegral : MooreIntegralParams where
  d := 7; n := 50; s := 5; m1 := 28; m2 := 21
  hn := rfl; hs_pos := (by decide); hs_sq := rfl; hm_sum := rfl; h_trace := rfl; hd_ge_2 := (by decide)

/-- Certificate for degree 57 (Potential 57-regular Moore graph, n = 3250). -/
def certDegree57 : MooreCertificate 57 where
  n := 3250; m1 := 1729; m2 := 1520
  hn := rfl; hm_sum := rfl; trace_eq := rfl; hd_ge_2 := (by decide)

/-- Integral parameter certificate for the degree 57 Moore graph (d = 57). -/
def certDegree57Integral : MooreIntegralParams where
  d := 57; n := 3250; s := 15; m1 := 1729; m2 := 1520
  hn := rfl; hs_pos := (by decide); hs_sq := rfl; hm_sum := rfl; h_trace := rfl; hd_ge_2 := (by decide)

/-- Conversion from `MooreCertificate d` to `MooreParams`. -/
def MooreCertificate.toMooreParams {d : ℕ} (c : MooreCertificate d) : MooreParams where
  d := d; n := c.n; m1 := c.m1; m2 := c.m2
  hn := c.hn; hm_sum := c.hm_sum; trace_eq := c.trace_eq; hd_ge_2 := c.hd_ge_2

/-- Conversion from `MooreIntegralParams` to `MooreParams`. -/
def MooreIntegralParams.toMooreParams (p : MooreIntegralParams) : MooreParams where
  d := p.d; n := p.n; m1 := p.m1; m2 := p.m2
  hn := p.hn; hm_sum := p.hm_sum
  trace_eq := by linear_combination ((p.m1 - p.m2 : ℤ) * p.s + (p.d : ℤ) * (p.d - 2)) * p.h_trace -
    (p.m1 - p.m2 : ℤ) ^ 2 * p.hs_sq
  hd_ge_2 := p.hd_ge_2

/-! ### Section 7: Concrete Spectral Calculations for Valid Degrees -/

/-- Spectrum of C₅ (d = 2, n = 5):
  The non-trivial eigenvalues are `(-1 ± √5)/2` with multiplicities `m₁ = 2, m₂ = 2`.
  The trace equals `2 + 2*(-1+√5)/2 + 2*(-1-√5)/2 = 0`. -/
theorem c5_spectral_trace :
    (2 : ℝ) + 2 * mooreEigenvalue1 (Real.sqrt 5) + 2 * mooreEigenvalue2 (Real.sqrt 5) = 0 := by
  unfold mooreEigenvalue1 mooreEigenvalue2; ring

/-- The Petersen graph non-trivial eigenvalues are 1 and -2. -/
theorem petersen_eigenvalue1 : mooreEigenvalue1 3 = 1 := by
  unfold mooreEigenvalue1; norm_num

theorem petersen_eigenvalue2 : mooreEigenvalue2 3 = -2 := by
  unfold mooreEigenvalue2; norm_num

/-- Spectrum of the Petersen graph (d = 3, n = 10):
  Trace: `3 + 5*(1) + 4*(-2) = 0`. -/
theorem petersen_spectral_trace :
    (3 : ℝ) + 5 * mooreEigenvalue1 3 + 4 * mooreEigenvalue2 3 = 0 := by
  unfold mooreEigenvalue1 mooreEigenvalue2; norm_num

/-- Hoffman–Singleton graph non-trivial eigenvalues are 2 and -3. -/
theorem hoffman_singleton_eigenvalue1 : mooreEigenvalue1 5 = 2 := by
  unfold mooreEigenvalue1; norm_num

theorem hoffman_singleton_eigenvalue2 : mooreEigenvalue2 5 = -3 := by
  unfold mooreEigenvalue2; norm_num

/-- Spectrum of the Hoffman–Singleton graph (d = 7, n = 50):
  Trace: `7 + 28*(2) + 21*(-3) = 0`. -/
theorem hoffman_singleton_spectral_trace :
    (7 : ℝ) + 28 * mooreEigenvalue1 5 + 21 * mooreEigenvalue2 5 = 0 := by
  unfold mooreEigenvalue1 mooreEigenvalue2; norm_num

/-- The degree 57 Moore graph non-trivial eigenvalues are 7 and -8. -/
theorem degree_57_eigenvalue1 : mooreEigenvalue1 15 = 7 := by
  unfold mooreEigenvalue1; norm_num

theorem degree_57_eigenvalue2 : mooreEigenvalue2 15 = -8 := by
  unfold mooreEigenvalue2; norm_num

/-- Spectrum of the potential degree 57 Moore graph (d = 57, n = 3250):
  Trace: `57 + 1729*(7) + 1520*(-8) = 0`. -/
theorem degree_57_spectral_trace :
    (57 : ℝ) + 1729 * mooreEigenvalue1 15 + 1520 * mooreEigenvalue2 15 = 0 := by
  unfold mooreEigenvalue1 mooreEigenvalue2; norm_num

/-! ### Section 8: Graph Metric Properties and Strongly Regular Bridge -/

lemma no_triangle_of_girth_ge_4 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hg : 4 ≤ G.girth) {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u) : False := by
  have huv_ne : u ≠ v := huv.ne
  have hvw_ne : v ≠ w := hvw.ne
  have hwu_ne : w ≠ u := hwu.ne
  let p : G.Walk u u := Walk.cons huv (Walk.cons hvw (Walk.cons hwu Walk.nil))
  have hp_cyc : p.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  have hle := hp_cyc.girth_le_length
  have hp_len : p.length = 3 := rfl
  rw [hp_len] at hle
  omega

lemma no_four_cycle_of_girth_ge_5 {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hg : 5 ≤ G.girth) {u v w1 w2 : V}
    (huv : u ≠ v) (hw : w1 ≠ w2)
    (huw1 : G.Adj u w1) (hw1v : G.Adj w1 v)
    (hvw2 : G.Adj v w2) (hw2u : G.Adj w2 u) : False := by
  have huw1_ne : u ≠ w1 := huw1.ne
  have hw1v_ne : w1 ≠ v := hw1v.ne
  have hvw2_ne : v ≠ w2 := hvw2.ne
  have hw2u_ne : w2 ≠ u := hw2u.ne
  let p : G.Walk u u := Walk.cons huw1 (Walk.cons hw1v (Walk.cons hvw2 (Walk.cons hw2u Walk.nil)))
  have hp_cyc : p.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  have hle := hp_cyc.girth_le_length
  have hp_len : p.length = 4 := rfl
  rw [hp_len] at hle
  omega

lemma edist_eq_two_of_diam_two {V : Type*} {G : SimpleGraph V}
    (hdiam : G.diam = 2) {u v : V} (hne : u ≠ v) (hna : ¬ G.Adj u v) :
    G.edist u v = 2 := by
  have hediam_ne : G.ediam ≠ ⊤ := ediam_ne_top_of_diam_ne_zero (by rw [hdiam]; decide)
  have hediam : G.ediam = 2 := by
    have h1 : (G.diam : ℕ∞) = 2 := by rw [hdiam]; rfl
    rw [diam] at h1
    exact (ENat.natCast_toNat hediam_ne).symm.trans h1
  have hle : G.edist u v ≤ 2 := hediam ▸ edist_le_ediam
  have hne0 : G.edist u v ≠ 0 := mt edist_eq_zero_iff.mp hne
  have hne1 : G.edist u v ≠ 1 := mt edist_eq_one_iff_adj.mp hna
  generalize hx : G.edist u v = x at hle hne0 hne1 ⊢
  cases x with
  | top =>
    have : (⊤ : ℕ∞) ≤ 2 := hx ▸ hle
    revert this; decide
  | coe d =>
    have hle' : d ≤ 2 := by exact_mod_cast hle
    have hne0' : d ≠ 0 := by intro h; apply hne0; exact_mod_cast h
    have hne1' : d ≠ 1 := by intro h; apply hne1; exact_mod_cast h
    have : d = 2 := by omega
    exact_mod_cast this

lemma card_commonNeighbors_eq_zero_of_girth_ge_4 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hg : 4 ≤ G.girth) {u v : V} (huv : G.Adj u v) :
    Fintype.card (G.commonNeighbors u v) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨w, hw⟩ => ?_⟩
  rw [mem_commonNeighbors] at hw
  exact no_triangle_of_girth_ge_4 hg huv hw.2 hw.1.symm

lemma card_commonNeighbors_eq_one_of_diam_two_girth_five {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiam : G.diam = 2) (hgirth : G.girth = 5)
    {u v : V} (hne : u ≠ v) (hna : ¬ G.Adj u v) :
    Fintype.card (G.commonNeighbors u v) = 1 := by
  have h2 : G.edist u v = 2 := edist_eq_two_of_diam_two hdiam hne hna
  have hne_cn : (G.commonNeighbors u v).Nonempty := (edist_eq_two_iff.mp h2).2.2
  obtain ⟨w0, hw0⟩ := hne_cn
  have hsub : ∀ w ∈ G.commonNeighbors u v, w = w0 := by
    intro w hw
    by_contra h_ne
    rw [mem_commonNeighbors] at hw hw0
    have hg_le : 5 ≤ G.girth := by rw [hgirth]
    exact no_four_cycle_of_girth_ge_5 hg_le hne h_ne hw.1 hw.2.symm hw0.2 hw0.1.symm
  have : (G.commonNeighbors u v : Set V) = {w0} := by
    ext x
    simp only [Set.mem_singleton_iff]
    exact ⟨fun hx => hsub x hx, fun hx => hx ▸ hw0⟩
  rw [Fintype.card_congr (Equiv.setCongr this)]
  simp

lemma card_eq_moore_of_srg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (d : ℕ) (hdiam : G.diam = 2)
    (hsrg : G.IsSRGWith (Fintype.card V) d 0 1) (hd : d ≥ 2) :
    Fintype.card V = 1 + d ^ 2 := by
  have : Nontrivial V := nontrivial_of_diam_ne_zero (by rw [hdiam]; decide)
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h_deg : G.degree v = d := hsrg.regular v
  have h_sub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    simp only [mem_neighborFinset] at hw
    simp [hw.ne.symm]
  have h_le : d ≤ Fintype.card V - 1 := by
    rw [← h_deg, ← card_neighborFinset_eq_degree]
    have := Finset.card_le_card h_sub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
  have hp := hsrg.param_eq G hpos
  have h_card_ge : d + 1 ≤ Fintype.card V := by omega
  have h_d_ge : 1 ≤ d := by omega
  change d * (d - 1) = (Fintype.card V - (d + 1)) * 1 at hp
  rw [mul_one] at hp
  have hp_int : ((d * (d - 1) : ℕ) : ℤ) = ((Fintype.card V - (d + 1) : ℕ) : ℤ) := by rw [hp]
  rw [Nat.cast_mul, Nat.cast_sub h_d_ge, Nat.cast_sub h_card_ge, Nat.cast_add] at hp_int
  have hp' : (Fintype.card V : ℤ) = 1 + (d : ℤ) ^ 2 := by
    linear_combination -hp_int
  exact_mod_cast hp'

/-- A regular graph of diameter 2 and girth 5 is strongly regular with parameters `(1 + d², d, 0, 1)`. -/
theorem moore_is_srg {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : ℕ) (h_reg : G.IsRegularOfDegree d)
    (hdiam : G.diam = 2) (hgirth : G.girth = 5) (hd : d ≥ 2) :
    G.IsSRGWith (1 + d ^ 2) d 0 1 := by
  have hsrg0 : G.IsSRGWith (Fintype.card V) d 0 1 := {
    card := rfl
    regular := h_reg
    of_adj := fun u v huv => card_commonNeighbors_eq_zero_of_girth_ge_4 (by rw [hgirth]; decide) huv
    of_not_adj := fun u v hne hna => card_commonNeighbors_eq_one_of_diam_two_girth_five hdiam hgirth hne hna
  }
  have h_card := card_eq_moore_of_srg d hdiam hsrg0 hd
  exact { hsrg0 with card := h_card }

/-! ### Section 9: Adjacency Matrix Equation and Spectral Multiplicities -/

theorem adjMatrix_mulVec_one {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : ℕ) (h_reg : G.IsRegularOfDegree d) :
    (G.adjMatrix ℝ) *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
  ext v
  simp [h_reg v]

theorem moore_adjMatrix_eq {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : ℕ) (hsrg : G.IsSRGWith (1 + d ^ 2) d 0 1) :
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    A ^ 2 + A - ((d : ℝ) - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1) := by
  intro A
  have h_mat := hsrg.matrix_eq (α := ℝ)
  ext i j
  have h1 := congr_fun (congr_fun h_mat i) j
  have h_c := one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℝ) G
  have hc := congr_fun (congr_fun h_c i) j
  rw [compl_adjMatrix_eq_adjMatrix_compl] at hc
  change (1 : Matrix V V ℝ) i j + A i j + Gᶜ.adjMatrix ℝ i j = (Matrix.of (fun _ _ => 1) : Matrix V V ℝ) i j at hc
  simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, Matrix.sub_apply, one_apply] at hc h1 ⊢
  obtain rfl | hij := eq_or_ne i j
  · simp only [↓reduceIte, nsmul_eq_mul, mul_one, smul_eq_mul, zero_smul, one_smul, add_zero] at h1 hc ⊢
    linarith
  · simp only [hij, ↓reduceIte, nsmul_eq_mul, mul_zero, smul_eq_mul, zero_smul, one_smul, add_zero] at h1 hc ⊢
    linarith

theorem eigenvalue_quadratic_of_orthogonal {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} {d : ℝ}
    (hA_eq : A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1))
    {v : V → ℝ} {μ : ℝ} (hv_ne : v ≠ 0) (h_eig : A *ᵥ v = μ • v)
    (h_orth : v ⬝ᵥ 1 = 0) :
    μ ^ 2 + μ - (d - 1) = 0 := by
  have hJ : (Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) = (0 : V → ℝ) := by
    ext i
    simp only [mulVec, dotProduct, of_apply, one_mul, Pi.zero_apply]
    have : (∑ j, v j) = v ⬝ᵥ 1 := by simp [dotProduct]
    rw [this, h_orth]
  have h_mul : (A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ)) *ᵥ v = 0 := by
    have h_rw : (Matrix.of (fun _ _ => 1) : Matrix V V ℝ) = Matrix.of (fun (_ _ : V) => (1 : ℝ)) := rfl
    rw [hA_eq, h_rw, hJ]
  have h_pow2 : (A ^ 2) *ᵥ v = (μ ^ 2) • v := by
    rw [pow_two, ← mulVec_mulVec, h_eig, mulVec_smul, h_eig, smul_smul, pow_two]
  have h_eval : (A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ)) *ᵥ v =
      (μ ^ 2 + μ - (d - 1)) • v := by
    simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, h_pow2, h_eig]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_eval] at h_mul
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv_ne
  have h_entry := congr_fun h_mul i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h_entry
  cases mul_eq_zero.mp h_entry with
  | inl h => exact h
  | inr h => exact (hi h).elim

theorem moore_adjMatrix_trace_zero {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    Matrix.trace (G.adjMatrix ℝ) = 0 := by
  simp [Matrix.trace]

theorem eigenvalue_cases {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ} {d : ℝ}
    (hA_eq : A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1))
    (hA_one : A *ᵥ (1 : V → ℝ) = d • (1 : V → ℝ))
    {v : V → ℝ} {μ : ℝ} (hv_ne : v ≠ 0) (h_eig : A *ᵥ v = μ • v) :
    μ = d ∨ μ ^ 2 + μ - (d - 1) = 0 := by
  have h_pow2 : (A ^ 2) *ᵥ v = (μ ^ 2) • v := by
    rw [pow_two, ← mulVec_mulVec, h_eig, mulVec_smul, h_eig, smul_smul, pow_two]
  have h_eval : (A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ)) *ᵥ v =
      (μ ^ 2 + μ - (d - 1)) • v := by
    simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, h_pow2, h_eig]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h_rw : (Matrix.of (fun _ _ => 1) : Matrix V V ℝ) = Matrix.of (fun (_ _ : V) => (1 : ℝ)) := rfl
  have h_J : (Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) = (μ ^ 2 + μ - (d - 1)) • v := by
    rw [← h_rw, ← hA_eq, h_eval]
  have h_const : ∀ i j : V, ((μ ^ 2 + μ - (d - 1)) • v) i = ((μ ^ 2 + μ - (d - 1)) • v) j := by
    intro i j
    have hi : ((Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) i) = ∑ k, v k := by
      simp [mulVec, dotProduct, of_apply]
    have hj : ((Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) j) = ∑ k, v k := by
      simp [mulVec, dotProduct, of_apply]
    rw [← congr_fun h_J i, ← congr_fun h_J j, hi, hj]
  by_cases h_quad : μ ^ 2 + μ - (d - 1) = 0
  · exact Or.inr h_quad
  · left
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv_ne
    set c := v i0 with hc
    have hc_ne : c ≠ 0 := hi0
    have hv_eq : v = c • (1 : V → ℝ) := by
      ext k
      have := h_const k i0
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have := mul_left_cancel₀ h_quad this
      simp [this, hc]
    have h_Av : A *ᵥ v = (c * d) • (1 : V → ℝ) := by
      rw [hv_eq, mulVec_smul, hA_one, smul_smul, mul_comm]
    have h_μv : μ • v = (c * μ) • (1 : V → ℝ) := by
      rw [hv_eq, smul_smul, mul_comm]
    rw [h_eig] at h_Av
    rw [h_μv] at h_Av
    have h_entry := congr_fun h_Av i0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one] at h_entry
    have h_cd_cμ : c * μ = c * d := h_entry
    exact mul_left_cancel₀ hc_ne h_cd_cμ

theorem roots_quadratic (d s μ : ℝ) (hs : s ^ 2 = 4 * d - 3)
    (hμ : μ ^ 2 + μ - (d - 1) = 0) :
    μ = mooreEigenvalue1 s ∨ μ = mooreEigenvalue2 s := by
  have h_fact : (μ - mooreEigenvalue1 s) * (μ - mooreEigenvalue2 s) = 0 := by
    unfold mooreEigenvalue1 mooreEigenvalue2
    linear_combination hμ - hs / 4
  rcases mul_eq_zero.mp h_fact with h | h
  · left; linarith
  · right; linarith

lemma nat_eq_one_of_sq_eq_one {d : ℕ} (h : d ^ 2 = 1) : d = 1 := by
  nlinarith

theorem rat_sq_eq_int {q : ℚ} {n : ℤ} (h : q ^ 2 = n) : ∃ s : ℤ, (s : ℚ) = q ∧ s ^ 2 = n := by
  have h_den : q.den = 1 := by
    have hq : q = (q.num : ℚ) / (q.den : ℚ) := by exact (Rat.num_div_den q).symm
    have h2 : ((q.num : ℚ) / (q.den : ℚ)) ^ 2 = (n : ℚ) := hq ▸ h
    have h_den_sq : ((q.den : ℤ) : ℚ) ^ 2 ≠ 0 := by
      have : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
      exact pow_ne_zero 2 this
    have h_mul : ((q.num : ℚ) ^ 2) = (n : ℚ) * ((q.den : ℚ) ^ 2) := by
      rw [div_pow] at h2
      exact (div_eq_iff h_den_sq).mp h2
    have h_int : (q.num ^ 2 : ℤ) = n * ((q.den : ℤ) ^ 2) := by
      exact_mod_cast h_mul
    have hdvd_int : ((q.den : ℤ) ^ 2) ∣ (q.num ^ 2) := ⟨n, by rw [mul_comm, h_int]⟩
    have hdvd_nat : (q.den ^ 2) ∣ (q.num.natAbs ^ 2) := by
      have h1 := Int.natAbs_dvd_natAbs.mpr hdvd_int
      simp only [Int.natAbs_pow, Int.natAbs_natCast] at h1
      exact h1
    have hcop := q.reduced
    have hcop2 : (q.den ^ 2).Coprime (q.num.natAbs ^ 2) := (hcop.symm.pow 2 2)
    have h_sq1 : q.den ^ 2 = 1 := hcop2.eq_one_of_dvd hdvd_nat
    exact nat_eq_one_of_sq_eq_one h_sq1
  refine ⟨q.num, ?_, ?_⟩
  · exact Rat.coe_int_num_of_den_eq_one h_den
  · have hq := Rat.coe_int_num_of_den_eq_one h_den
    exact_mod_cast (by rw [hq, h] : ((q.num : ℚ) ^ 2) = (n : ℚ))

theorem eigenvector_for_d_proportional_one {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} {d : ℝ} (hd : d ≥ 2)
    (hA_eq : A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1))
    {v : V → ℝ} (h_eig : A *ᵥ v = d • v) :
    ∃ c : ℝ, v = c • (1 : V → ℝ) := by
  have h_quad_ne : d ^ 2 + d - (d - 1) ≠ 0 := by
    have : d ^ 2 + d - (d - 1) = d ^ 2 + 1 := by ring
    rw [this]
    positivity
  have h_pow2 : (A ^ 2) *ᵥ v = (d ^ 2) • v := by
    rw [pow_two, ← mulVec_mulVec, h_eig, mulVec_smul, h_eig, smul_smul, pow_two]
  have h_eval : (A ^ 2 + A - (d - 1) • (1 : Matrix V V ℝ)) *ᵥ v =
      (d ^ 2 + d - (d - 1)) • v := by
    simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, h_pow2, h_eig]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h_rw : (Matrix.of (fun _ _ => 1) : Matrix V V ℝ) = Matrix.of (fun (_ _ : V) => (1 : ℝ)) := rfl
  have h_J : (Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) = (d ^ 2 + d - (d - 1)) • v := by
    rw [← h_rw, ← hA_eq, h_eval]
  have h_const : ∀ i j : V, ((d ^ 2 + d - (d - 1)) • v) i = ((d ^ 2 + d - (d - 1)) • v) j := by
    intro i j
    have hi : ((Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) i) = ∑ k, v k := by
      simp [mulVec, dotProduct, of_apply]
    have hj : ((Matrix.of (fun (_ _ : V) => (1 : ℝ)) *ᵥ v) j) = ∑ k, v k := by
      simp [mulVec, dotProduct, of_apply]
    rw [← congr_fun h_J i, ← congr_fun h_J j, hi, hj]
  cases isEmpty_or_nonempty V with
  | inl h =>
    use 0; ext i; exact (h.false i).elim
  | inr h =>
    obtain ⟨i0⟩ := h
    set c := v i0 with hc
    use c
    ext k
    have := h_const k i0
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_left_cancel₀ h_quad_ne this
    simp [this, hc]

lemma inner_basis_zero_implies_zero {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (v : EuclideanSpace ℝ V)
    (h_orth : ∀ i, @inner ℝ (EuclideanSpace ℝ V) _ (hA.eigenvectorBasis i) v = 0) :
    v = 0 := by
  have h_repr : hA.eigenvectorBasis.repr v = 0 := by
    ext i
    rw [PiLp.zero_apply]
    have := OrthonormalBasis.repr_apply_apply hA.eigenvectorBasis v i
    change (hA.eigenvectorBasis.repr v).ofLp i = _ at this
    rw [this, h_orth i]
  exact (hA.eigenvectorBasis.repr.injective (by simp [h_repr]))

lemma inner_one_eq_dotProduct {V : Type*} [Fintype V]
    (x : EuclideanSpace ℝ V) :
    @inner ℝ (EuclideanSpace ℝ V) _ x (WithLp.toLp 2 (1 : V → ℝ)) = x.ofLp ⬝ᵥ (1 : V → ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

lemma eigenvectorBasis_ofLp_ne_zero {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : V) :
    (hA.eigenvectorBasis i).ofLp ≠ 0 := by
  intro h
  have : hA.eigenvectorBasis i = 0 := by
    ext k
    change (hA.eigenvectorBasis i).ofLp k = 0
    rw [h, Pi.zero_apply]
  exact hA.eigenvectorBasis.orthonormal.ne_zero i this

theorem moore_spectral_multiplicities {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (d : ℕ) (h_reg : G.IsRegularOfDegree d)
    (hsrg : G.IsSRGWith (1 + d ^ 2) d 0 1) (hd : d ≥ 2) (hdiam : G.diam = 2) :
    let s : ℝ := Real.sqrt (4 * (d : ℝ) - 3)
    ∃ (m1 m2 : ℕ), m1 + m2 = d ^ 2 ∧
      (d : ℝ) + m1 * mooreEigenvalue1 s + m2 * mooreEigenvalue2 s = 0 := by
  intro s
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  have hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  have hd_real : (d : ℝ) ≥ 2 := by exact_mod_cast hd
  have hs_nonneg : 0 ≤ 4 * (d : ℝ) - 3 := by linarith
  have hs_sq : s ^ 2 = 4 * (d : ℝ) - 3 := Real.sq_sqrt hs_nonneg
  have hA_eq : A ^ 2 + A - ((d : ℝ) - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1) :=
    moore_adjMatrix_eq d hsrg
  have hA_one : A *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := adjMatrix_mulVec_one d h_reg
  have h_nontriv : Nontrivial V := nontrivial_of_diam_ne_zero (by rw [hdiam]; decide)
  have h_nonempty : Nonempty V := inferInstance
  have h_d_exists : ∃ i0 : V, hA.eigenvalues i0 = (d : ℝ) := by
    by_contra h_no_d
    push Not at h_no_d
    have h_all_orth : ∀ i : V, @inner ℝ (EuclideanSpace ℝ V) _ (hA.eigenvectorBasis i) (WithLp.toLp 2 (1 : V → ℝ)) = 0 := by
      intro i
      have h_cases_i := eigenvalue_cases hA_eq hA_one
        (eigenvectorBasis_ofLp_ne_zero hA i) (hA.mulVec_eigenvectorBasis i)
      have h_quad : (hA.eigenvalues i) ^ 2 + (hA.eigenvalues i) - ((d : ℝ) - 1) = 0 := by
        rcases h_cases_i with heq | hq
        · exact (h_no_d i heq).elim
        · exact hq
      have h_pow2 : (A ^ 2) *ᵥ (hA.eigenvectorBasis i).ofLp = ((hA.eigenvalues i) ^ 2) • (hA.eigenvectorBasis i).ofLp := by
        rw [pow_two, ← mulVec_mulVec, hA.mulVec_eigenvectorBasis i, mulVec_smul,
          hA.mulVec_eigenvectorBasis i, smul_smul, pow_two]
      have h_eval : (A ^ 2 + A - ((d : ℝ) - 1) • (1 : Matrix V V ℝ)) *ᵥ (hA.eigenvectorBasis i).ofLp = 0 := by
        simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, h_pow2, hA.mulVec_eigenvectorBasis i]
        ext k
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        linear_combination (hA.eigenvectorBasis i).ofLp k * h_quad
      have h_rw : (Matrix.of (fun _ _ => 1) : Matrix V V ℝ) = Matrix.of (fun (_ _ : V) => (1 : ℝ)) := rfl
      have h_J : (Matrix.of (fun (_ _ : V) => (1 : ℝ))) *ᵥ (hA.eigenvectorBasis i).ofLp = 0 := by
        rw [← h_rw, ← hA_eq, h_eval]
      obtain ⟨v0⟩ := h_nonempty
      have h_dot : ((hA.eigenvectorBasis i).ofLp) ⬝ᵥ (1 : V → ℝ) = 0 := by
        have := congr_fun h_J v0
        simp only [mulVec, dotProduct, of_apply, one_mul, Pi.zero_apply] at this
        rw [dotProduct_one]
        exact this
      rw [inner_one_eq_dotProduct, h_dot]
    have h_one_zero : (WithLp.toLp 2 (1 : V → ℝ)) = 0 :=
      inner_basis_zero_implies_zero hA (WithLp.toLp 2 1) h_all_orth
    have h_fun_zero : (1 : V → ℝ) = 0 := congrArg WithLp.ofLp h_one_zero
    obtain ⟨v0⟩ := h_nonempty
    have := congr_fun h_fun_zero v0
    simp only [Pi.one_apply, Pi.zero_apply] at this
    exact one_ne_zero this
  obtain ⟨i0, hi0⟩ := h_d_exists
  have h_unique : ∀ i : V, hA.eigenvalues i = (d : ℝ) ↔ i = i0 := by
    intro i
    constructor
    · intro hi
      by_contra h_ne
      have h_prop_i := eigenvector_for_d_proportional_one hd_real hA_eq (hi ▸ hA.mulVec_eigenvectorBasis i)
      have h_prop_0 := eigenvector_for_d_proportional_one hd_real hA_eq (hi0 ▸ hA.mulVec_eigenvectorBasis i0)
      obtain ⟨ci, hci⟩ := h_prop_i
      obtain ⟨c0, hc0⟩ := h_prop_0
      have hci_ne : ci ≠ 0 := by
        intro hc; rw [hc, zero_smul] at hci
        exact eigenvectorBasis_ofLp_ne_zero hA i hci
      have hc0_ne : c0 ≠ 0 := by
        intro hc; rw [hc, zero_smul] at hc0
        exact eigenvectorBasis_ofLp_ne_zero hA i0 hc0
      have h_orth : @inner ℝ (EuclideanSpace ℝ V) _ (hA.eigenvectorBasis i0) (hA.eigenvectorBasis i) = 0 :=
        hA.eigenvectorBasis.orthonormal.2 (Ne.symm h_ne)
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h_orth
      simp only [star_trivial, dotProduct_comm] at h_orth
      rw [hci, hc0] at h_orth
      have h_dot_ones : (c0 • (1 : V → ℝ)) ⬝ᵥ (ci • (1 : V → ℝ)) = c0 * ci * (Fintype.card V : ℝ) := by
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
        rw [← Finset.mul_sum]
        simp
        ring
      rw [h_dot_ones] at h_orth
      have h_card_pos : (Fintype.card V : ℝ) ≠ 0 := by
        have : 0 < Fintype.card V := Fintype.card_pos
        positivity
      have : c0 * ci = 0 := by
        cases mul_eq_zero.mp h_orth with
        | inl h => exact h
        | inr h => exact (h_card_pos h).elim
      cases mul_eq_zero.mp this with
      | inl h => exact hc0_ne h
      | inr h => exact hci_ne h
    · rintro rfl; exact hi0
  set W := Finset.univ.erase i0 with hW
  have hW_card : #W = d ^ 2 := by
    rw [hW, card_erase_of_mem (mem_univ i0), card_univ, hsrg.card]
    omega
  have h_roots_W : ∀ i ∈ W, hA.eigenvalues i = mooreEigenvalue1 s ∨ hA.eigenvalues i = mooreEigenvalue2 s := by
    intro i hi
    have h_ne_i0 : i ≠ i0 := mem_erase.mp hi |>.1
    have h_ne_d : hA.eigenvalues i ≠ (d : ℝ) := (not_iff_not.mpr (h_unique i)).mpr h_ne_i0
    have h_cases_i := eigenvalue_cases hA_eq hA_one
      (eigenvectorBasis_ofLp_ne_zero hA i) (hA.mulVec_eigenvectorBasis i)
    have h_quad : (hA.eigenvalues i) ^ 2 + (hA.eigenvalues i) - ((d : ℝ) - 1) = 0 := by
      rcases h_cases_i with heq | hq
      · exact (h_ne_d heq).elim
      · exact hq
    exact roots_quadratic (d : ℝ) s (hA.eigenvalues i) hs_sq h_quad
  set S1 := W.filter (fun i => hA.eigenvalues i = mooreEigenvalue1 s)
  set S2 := W.filter (fun i => hA.eigenvalues i ≠ mooreEigenvalue1 s)
  have h_disj : Disjoint S1 S2 := disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have h_union : S1 ∪ S2 = W := by
    ext x
    simp only [S1, S2, mem_union, mem_filter]
    tauto
  have hm_sum : #S1 + #S2 = d ^ 2 := by
    rw [← card_union_of_disjoint h_disj, h_union, hW_card]
  have h_S2_vals : ∀ i ∈ S2, hA.eigenvalues i = mooreEigenvalue2 s := by
    intro i hi
    have hi_W : i ∈ W := (mem_filter.mp hi).1
    have hi_ne1 : hA.eigenvalues i ≠ mooreEigenvalue1 s := (mem_filter.mp hi).2
    rcases h_roots_W i hi_W with h1 | h2
    · exact (hi_ne1 h1).elim
    · exact h2
  have h_trace_eig : Matrix.trace A = ∑ i : V, hA.eigenvalues i := hA.trace_eq_sum_eigenvalues
  have h_trace_zero : Matrix.trace A = 0 := moore_adjMatrix_trace_zero
  have h_sum_split : ∑ i : V, hA.eigenvalues i = hA.eigenvalues i0 + ∑ i ∈ W, hA.eigenvalues i := by
    rw [hW, (Finset.add_sum_erase univ hA.eigenvalues (Finset.mem_univ i0)).symm]
  have h_sum_W : ∑ i ∈ W, hA.eigenvalues i = (#S1 : ℝ) * mooreEigenvalue1 s + (#S2 : ℝ) * mooreEigenvalue2 s := by
    rw [← h_union, sum_union h_disj]
    have h1 : ∑ i ∈ S1, hA.eigenvalues i = (#S1 : ℝ) * mooreEigenvalue1 s := by
      have : ∑ i ∈ S1, hA.eigenvalues i = ∑ i ∈ S1, mooreEigenvalue1 s :=
        sum_congr rfl (fun x hx => (mem_filter.mp hx).2)
      rw [this, sum_const, nsmul_eq_mul]
    have h2 : ∑ i ∈ S2, hA.eigenvalues i = (#S2 : ℝ) * mooreEigenvalue2 s := by
      have : ∑ i ∈ S2, hA.eigenvalues i = ∑ i ∈ S2, mooreEigenvalue2 s :=
        sum_congr rfl (fun x hx => h_S2_vals x hx)
      rw [this, sum_const, nsmul_eq_mul]
    rw [h1, h2]
  have h_trace_eval : (d : ℝ) + (#S1 : ℝ) * mooreEigenvalue1 s + (#S2 : ℝ) * mooreEigenvalue2 s = 0 := by
    rw [← h_trace_zero, h_trace_eig, h_sum_split, hi0, h_sum_W, add_assoc]
  refine ⟨#S1, #S2, hm_sum, h_trace_eval⟩

/-! ### Section 10: The Hoffman–Singleton Moore Graph Degree Classification -/

/-- **The Hoffman–Singleton Theorem (Graph Carrier Formulation)**:
Any regular graph of degree `d ≥ 2` with diameter 2 and girth 5 must have degree
`d = 2` (5-cycle `C₅`), `d = 3` (Petersen graph), `d = 7` (Hoffman–Singleton graph),
or possibly `d = 57`. -/
theorem moore_graph_degree_classification {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h_reg : G.IsRegularOfDegree d) (h_diam : G.diam = 2) (h_girth : G.girth = 5) (hd : d ≥ 2) :
    d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 57 := by
  have hsrg : G.IsSRGWith (1 + d ^ 2) d 0 1 := moore_is_srg d h_reg h_diam h_girth hd
  let s : ℝ := Real.sqrt (4 * (d : ℝ) - 3)
  obtain ⟨m1, m2, hm_sum, h_trace⟩ := moore_spectral_multiplicities d h_reg hsrg hd h_diam
  have h_trace_zero_iff : ((m1 : ℝ) - (m2 : ℝ)) * s = (d : ℝ) * ((d : ℝ) - 2) := by
    rw [← trace_zero_iff d m1 m2 s (by exact_mod_cast hm_sum)]
    exact h_trace
  have h_cases : (∃ m₁ m₂ : ℕ, m₁ = m₂ ∧ ((d : ℤ) * ((d : ℤ) - 2) = 0)) ∨
      (∃ (s : ℕ) (k : ℤ), s > 0 ∧ (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3 ∧ k * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2)) := by
    by_cases h_eq : m1 = m2
    · left
      have : (m1 : ℝ) - (m2 : ℝ) = 0 := by simp [h_eq]
      rw [this, zero_mul] at h_trace_zero_iff
      have hd_prod : (d : ℝ) * ((d : ℝ) - 2) = 0 := h_trace_zero_iff.symm
      have hd_prod_int : (d : ℤ) * ((d : ℤ) - 2) = 0 := by exact_mod_cast hd_prod
      exact ⟨m1, m2, h_eq, hd_prod_int⟩
    · right
      set k : ℤ := (m1 : ℤ) - (m2 : ℤ) with hk_def
      have hk_ne : k ≠ 0 := by
        intro h; apply h_eq
        have : (m1 : ℤ) = (m2 : ℤ) := by omega
        exact_mod_cast this
      have hk_real : (k : ℝ) * s = (d : ℝ) * ((d : ℝ) - 2) := by
        have : (k : ℝ) = (m1 : ℝ) - (m2 : ℝ) := by simp [hk_def]
        rw [this, h_trace_zero_iff]
      set q : ℚ := ((d : ℚ) * ((d : ℚ) - 2)) / (k : ℚ) with hq_def
      have hk_q : (k : ℚ) ≠ 0 := by exact_mod_cast hk_ne
      have hd_real : (d : ℝ) ≥ 2 := by exact_mod_cast hd
      have hq_real : (q : ℝ) = s := by
        have h_qcast : (q : ℝ) = ((d : ℝ) * ((d : ℝ) - 2)) / (k : ℝ) := by
          rw [hq_def]
          push_cast
          rfl
        rw [h_qcast, ← hk_real, mul_div_cancel_left₀ s (by exact_mod_cast hk_ne)]
      have hs_pos : 0 ≤ 4 * (d : ℝ) - 3 := by linarith
      have hs_sq : s ^ 2 = 4 * (d : ℝ) - 3 := Real.sq_sqrt hs_pos
      have hq_sq_real : (q : ℝ) ^ 2 = 4 * (d : ℝ) - 3 := by rw [hq_real, hs_sq]
      have hq_sq : q ^ 2 = (4 * (d : ℤ) - 3 : ℤ) := by
        exact_mod_cast (by
          push_cast
          exact hq_sq_real : ((q ^ 2 : ℚ) : ℝ) = (4 * (d : ℤ) - 3 : ℤ))
      obtain ⟨z, hz_q, hz_sq⟩ := rat_sq_eq_int hq_sq
      have hz_real : (z : ℝ) = s := by
        have : ((z : ℚ) : ℝ) = (q : ℝ) := congrArg (fun x : ℚ => (x : ℝ)) hz_q
        rw [hq_real] at this
        push_cast at this
        exact this
      have hs_gt0 : s > 0 := by
        have : 4 * (d : ℝ) - 3 > 0 := by linarith
        exact Real.sqrt_pos.mpr this
      have hz_pos : z > 0 := by
        have : (z : ℝ) > 0 := hz_real.symm ▸ hs_gt0
        exact_mod_cast this
      set s_nat : ℕ := z.toNat with hs_nat_def
      have hs_nat_eq : (s_nat : ℤ) = z := Int.toNat_of_nonneg (by omega)
      have hs_nat_pos : s_nat > 0 := by omega
      have hs_nat_sq : (s_nat : ℤ) ^ 2 = 4 * (d : ℤ) - 3 := by rw [hs_nat_eq, hz_sq]
      have hk_prod : k * (s_nat : ℤ) = (d : ℤ) * ((d : ℤ) - 2) := by
        have h_q_mul : (k : ℚ) * (z : ℚ) = (d : ℚ) * ((d : ℚ) - 2) := by
          rw [hz_q, hq_def, mul_div_cancel₀ _ hk_q]
        have h_z_cast : (k : ℚ) * (z : ℤ) = (d : ℤ) * ((d : ℤ) - 2) := by exact_mod_cast h_q_mul
        have h_int : (k * z : ℚ) = (((d : ℤ) * ((d : ℤ) - 2) : ℤ) : ℚ) := by exact_mod_cast h_q_mul
        have h_final : k * z = (d : ℤ) * ((d : ℤ) - 2) := by exact_mod_cast h_int
        rw [hs_nat_eq, h_final]
      exact ⟨s_nat, k, hs_nat_pos, hs_nat_sq, hk_prod⟩
  exact hoffman_singleton_theorem d hd h_cases

end HoffmanSingleton






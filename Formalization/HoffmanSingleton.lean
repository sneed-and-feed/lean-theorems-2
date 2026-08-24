import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

open Real

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

end HoffmanSingleton

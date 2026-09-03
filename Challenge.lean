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
-/

namespace HoffmanSingleton

/-- Moore bound vertex count for diameter 2 and girth 5: `n = 1 + d²`. -/
def mooreVertexCount (d : ℕ) : ℕ := 1 + d ^ 2

/-- Discriminant of the quadratic eigenvalue equation `λ² + λ - (d - 1) = 0`. -/
def mooreDiscr (d : ℕ) : ℤ := 4 * (d : ℤ) - 3

/-- Discriminant in ℝ. -/
def mooreDiscrR (d : ℝ) : ℝ := 4 * d - 3

/-- The two algebraic roots of `λ² + λ - (d - 1) = 0` parameterized by `s = √Δ`. -/
noncomputable def mooreEigenvalue1 (s : ℝ) : ℝ := (-1 + s) / 2
noncomputable def mooreEigenvalue2 (s : ℝ) : ℝ := (-1 - s) / 2

/-- Sum of the two quadratic roots equals -1. -/
theorem roots_sum (s : ℝ) : mooreEigenvalue1 s + mooreEigenvalue2 s = -1 := sorry

/-- Difference of the two quadratic roots equals `s`. -/
theorem roots_diff (s : ℝ) : mooreEigenvalue1 s - mooreEigenvalue2 s = s := sorry

/-- The fundamental trace relation:
  `2 * (d + m₁λ₁ + m₂λ₂) = (m₁ - m₂) * s - d * (d - 2)` when `m₁ + m₂ = d²`. -/
theorem trace_identity (d m1 m2 s : ℝ) (hsum : m1 + m2 = d ^ 2) :
    2 * (d + m1 * mooreEigenvalue1 s + m2 * mooreEigenvalue2 s) =
      (m1 - m2) * s - d * (d - 2) := sorry

/-- The trace is zero if and only if `(m₁ - m₂) * s = d * (d - 2)`. -/
theorem trace_zero_iff (d m1 m2 s : ℝ) (hsum : m1 + m2 = d ^ 2) :
    d + m1 * mooreEigenvalue1 s + m2 * mooreEigenvalue2 s = 0 ↔
      (m1 - m2) * s = d * (d - 2) := sorry

/-- The core divisibility theorem: `s` divides 15. -/
theorem s_divides_15 (d s k : ℤ) (hs : s ^ 2 = 4 * d - 3)
    (htrace : k * s = d * (d - 2)) :
    s ∣ 15 := sorry

/-- Any positive natural divisor of 15 is in `{1, 3, 5, 15}`. -/
theorem nat_divisors_15 (s : ℕ) (hs : s ∣ 15) (hs_pos : s > 0) :
    s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 15 := sorry

/-- From `s ∈ {1, 3, 5, 15}` and `s² = 4d - 3`, determine `d ∈ {1, 3, 7, 57}`. -/
theorem degree_from_s (d s : ℕ) (hs : (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3)
    (hs_vals : s = 1 ∨ s = 3 ∨ s = 5 ∨ s = 15) :
    d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 57 := sorry

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

/-- Classification of degrees with integer square root parameter `s` and `d ≥ 2`. -/
theorem classification_integral_params (p : MooreIntegralParams) :
    p.d = 3 ∨ p.d = 7 ∨ p.d = 57 := sorry

/-- General classification for any `d ≥ 1` admitting integral parameter `s`. -/
theorem classification_general (d s : ℕ) (k : ℤ) (hs_pos : s > 0)
    (hs : (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3)
    (htrace : k * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2)) :
    d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 57 := sorry

/-- The complete Hoffman–Singleton Theorem:
  Any Moore graph of diameter 2 and girth 5 has degree `d ∈ {2, 3, 7, 57}`. -/
theorem hoffman_singleton_theorem (d : ℕ) (hd : d ≥ 2)
    (h_cases : (∃ (m1 m2 : ℕ), m1 = m2 ∧ ((d : ℤ) * ((d : ℤ) - 2)) = 0) ∨
               (∃ (s : ℕ) (k : ℤ), s > 0 ∧ (s : ℤ) ^ 2 = 4 * (d : ℤ) - 3 ∧
                 k * (s : ℤ) = (d : ℤ) * ((d : ℤ) - 2))) :
    d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 57 := sorry

/-- Spectrum of C₅ (d = 2, n = 5). -/
theorem c5_spectral_trace :
    (2 : ℝ) + 2 * mooreEigenvalue1 (Real.sqrt 5) + 2 * mooreEigenvalue2 (Real.sqrt 5) = 0 := sorry

/-- Spectrum of the Petersen graph (d = 3, n = 10). -/
theorem petersen_spectral_trace :
    (3 : ℝ) + 5 * mooreEigenvalue1 3 + 4 * mooreEigenvalue2 3 = 0 := sorry

/-- Spectrum of the Hoffman–Singleton graph (d = 7, n = 50). -/
theorem hoffman_singleton_spectral_trace :
    (7 : ℝ) + 28 * mooreEigenvalue1 5 + 21 * mooreEigenvalue2 5 = 0 := sorry

/-- Spectrum of the potential degree 57 Moore graph (d = 57, n = 3250). -/
theorem degree_57_spectral_trace :
    (57 : ℝ) + 1729 * mooreEigenvalue1 15 + 1520 * mooreEigenvalue2 15 = 0 := sorry

/-- A regular graph of diameter 2 and girth 5 is strongly regular with parameters `(1 + d², d, 0, 1)`. -/
theorem moore_is_srg {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : ℕ) (h_reg : G.IsRegularOfDegree d)
    (hdiam : G.diam = 2) (hgirth : G.girth = 5) (hd : d ≥ 2) :
    G.IsSRGWith (1 + d ^ 2) d 0 1 := sorry

theorem moore_adjMatrix_eq {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (d : ℕ) (hsrg : G.IsSRGWith (1 + d ^ 2) d 0 1) :
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    A ^ 2 + A - ((d : ℝ) - 1) • (1 : Matrix V V ℝ) = Matrix.of (fun _ _ => 1) := sorry

/-- **The Hoffman–Singleton Theorem (Graph Carrier Formulation)**:
Any regular graph of degree `d ≥ 2` with diameter 2 and girth 5 must have degree
`d = 2` (5-cycle `C₅`), `d = 3` (Petersen graph), `d = 7` (Hoffman–Singleton graph),
or possibly `d = 57`. -/
theorem moore_graph_degree_classification {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h_reg : G.IsRegularOfDegree d) (h_diam : G.diam = 2) (h_girth : G.girth = 5) (hd : d ≥ 2) :
    d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 57 := sorry

end HoffmanSingleton

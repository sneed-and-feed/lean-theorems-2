import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open scoped BigOperators ENNReal
open Classical

set_option linter.unusedSectionVars false

/-!
# Blichfeldt's Theorem in the Geometry of Numbers

This module formalizes **Blichfeldt's Theorem** (Hans Frederick Blichfeldt, 1914),
a fundamental principle in the geometry of numbers that generalizes Minkowski's Convex Body Theorem
to arbitrary measurable sets and higher multiplicities.
-/

variable {d : ℕ}

namespace Blichfeldt

/-- The $d$-dimensional Euclidean space $\mathbb{R}^d$. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Predicate asserting that a vector in $\mathbb{R}^d$ has integer coordinates. -/
def IsIntegerVector (v : Space d) : Prop :=
  ∀ i : Fin d, ∃ z : ℤ, v i = (z : ℝ)

/-- The standard fundamental domain (unit half-open cube) $[0, 1)^d \subset \mathbb{R}^d$. -/
def unitCube (d : ℕ) : Set (Space d) :=
  { x : Space d | ∀ i : Fin d, 0 ≤ x i ∧ x i < 1 }

/-- Lattice translate of a set by an integer vector $z$. -/
def latticeShift (S : Set (Space d)) (z : Fin d → ℤ) : Set (Space d) :=
  { x : Space d | ∃ s ∈ S, ∀ i : Fin d, x i = s i + (z i : ℝ) }

/-- Centrally symmetric set: $S = -S$. -/
def IsCentrallySymmetric (S : Set (Space d)) : Prop :=
  ∀ x ∈ S, -x ∈ S

/--
**Blichfeldt's Theorem (1914)**:
Let $S \subset \mathbb{R}^d$ be a Lebesgue measurable set with volume strictly greater
than an integer $k \ge 1$:
$$\operatorname{vol}(S) > k$$
Then there exist $k + 1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that
every pairwise difference $x_i - x_j$ is an integer lattice vector in $\mathbb{Z}^d$:
$$x_i - x_j \in \mathbb{Z}^d \quad (\forall i, j)$$
-/
theorem blichfeldts_theorem (d : ℕ) (k : ℕ) (hk : 1 ≤ k) (S : Set (Space d))
    (hS_meas : MeasurableSet S)
    (hS_vol : (k : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ (pts : Fin (k + 1) → Space d),
      Function.Injective pts ∧
      (∀ i : Fin (k + 1), pts i ∈ S) ∧
      (∀ i j : Fin (k + 1), IsIntegerVector (pts i - pts j)) := sorry

/--
**Minkowski's First Convex Body Theorem (as a Corollary to Blichfeldt)**:
Let $K \subset \mathbb{R}^d$ be a convex, centrally symmetric, measurable set with
volume $\operatorname{vol}(K) > 2^d$. Then $K$ contains at least one non-zero
integer lattice point $z \in \mathbb{Z}^d \setminus \{0\}$:
$$K \cap (\mathbb{Z}^d \setminus \{0\}) 
e \emptyset$$
-/
theorem minkowski_convex_body_theorem (d : ℕ) (K : Set (Space d))
    (hK_conv : Convex ℝ K)
    (hK_symm : IsCentrallySymmetric K)
    (hK_meas : MeasurableSet K)
    (hK_vol : (2 : ℝ≥0∞) ^ d < MeasureTheory.volume K) :
    ∃ z : Space d, z ∈ K ∧ z ≠ 0 ∧ IsIntegerVector z := sorry

/-- Specialization to dimension $d = 1$: Any measurable set of length $> 1$ on $\mathbb{R}$
contains two points with integer distance. -/
theorem blichfeldt_dim1 (S : Set (Space 1)) (hS_meas : MeasurableSet S)
    (hS_vol : (1 : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ x y : Space 1, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ IsIntegerVector (x - y) := sorry

end Blichfeldt

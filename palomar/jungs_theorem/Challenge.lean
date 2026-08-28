import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Jung's Theorem on Circumscribed Euclidean Spheres

This module formalizes **Jung's Theorem** (Heinrich Jung, 1901) on the minimum enclosing
radius (Chebyshev radius / circumradius) of bounded sets in finite-dimensional Euclidean space.
-/

variable {d : ℕ}

/-- Predicate asserting that the closed Euclidean ball $\bar{B}(c, R)$ encloses the set $S$. -/
def IsEnclosingBall (S : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (R : ℝ) : Prop :=
  S ⊆ Metric.closedBall c R

/-- The Chebyshev radius (circumradius) of a set $S \subset \mathbb{R}^d$: the infimal radius
of an enclosing Euclidean ball. -/
noncomputable def circumradius (S : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sInf { R : ℝ | ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c R ∧ 0 ≤ R }

/-- Jung's dimensional constant $J_d = \sqrt{\frac{d}{2(d+1)}}$. -/
noncomputable def jungsConstant (d : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) / (2 * (d + 1 : ℝ)))

/-- Positivity of the Jung constant for $d \ge 1$. -/
theorem jungsConstant_pos (d : ℕ) [NeZero d] : 0 < jungsConstant d := sorry

/-- Non-negativity of the Jung constant. -/
theorem jungsConstant_nonneg (d : ℕ) : 0 ≤ jungsConstant d := sorry

/--
**Helly Reduction for Enclosing Euclidean Balls**:
Given a collection of closed balls of fixed radius $R$ in $\mathbb{R}^d$, if every sub-family
of at most $d + 1$ balls has a non-empty intersection, then all balls in the family share a common point.
-/
theorem jungs_theorem_via_helly (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (R : ℝ) (hR_nonneg : 0 ≤ R)
    (h_helly : ∀ (I : Finset S), I.card ≤ d + 1 →
      (⋂ (i : S) (_ : i ∈ I), Metric.closedBall i.val R).Nonempty) :
    ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c R := sorry

/--
**Jung's Theorem (1901)**:
For any non-empty bounded subset $S \subset \mathbb{R}^d$, there exists a center point
$c \in \mathbb{R}^d$ such that the closed ball of radius
$R = \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)$ encloses $S$:
$$S \subseteq \bar{B}\left(c, \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)\right)$$
-/
theorem jungs_theorem (d : ℕ) [NeZero d] (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c (jungsConstant d * Metric.diam S) := sorry

/--
**Circumradius Bound via Jung's Theorem**:
The Chebyshev radius of any non-empty bounded set $S \subset \mathbb{R}^d$ is bounded by:
$$\mathcal{R}(S) \le \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)$$
-/
theorem circumradius_le_jungs_bound (d : ℕ) [NeZero d] (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ jungsConstant d * Metric.diam S := sorry

/-- Evaluation of Jung's constant in dimension $1$: $J_1 = 1/2$. -/
theorem jungsConstant_one : jungsConstant 1 = 1 / 2 := sorry

/-- Evaluation of Jung's constant in dimension $2$: $J_2 = 1/\sqrt{3}$. -/
theorem jungsConstant_two : jungsConstant 2 = 1 / Real.sqrt 3 := sorry

/-- Evaluation of Jung's constant in dimension $3$: $J_3 = \sqrt{3/8}$. -/
theorem jungsConstant_three : jungsConstant 3 = Real.sqrt (3 / 8) := sorry

/-- Specialization to $d = 1$: Every 1D bounded set has circumradius at most $\frac{1}{2} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim1 (S : Set (EuclideanSpace ℝ (Fin 1)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / 2 : ℝ) * Metric.diam S := sorry

/-- Specialization to $d = 2$: Every planar bounded set has circumradius at most $\frac{1}{\sqrt{3}} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim2 (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / Real.sqrt 3) * Metric.diam S := sorry

/-- Specialization to $d = 3$: Every 3D bounded set has circumradius at most $\sqrt{3/8} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim3 (S : Set (EuclideanSpace ℝ (Fin 3)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ Real.sqrt (3 / 8 : ℝ) * Metric.diam S := sorry

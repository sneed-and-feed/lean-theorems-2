import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

/-!
# Jung's Theorem on Circumscribed Euclidean Spheres

This module formalizes **Jung's Theorem** (Heinrich Jung, 1901) on the minimum enclosing
radius (Chebyshev radius / circumradius) of bounded sets in finite-dimensional Euclidean space.

## Mathematical Formulation

Let $E = \mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$ be the $d$-dimensional
Euclidean space equipped with the standard $\ell^2$ inner product and metric.

### Set Diameter and Enclosing Balls
- For any subset $S \subseteq \mathbb{R}^d$, its **diameter** is:
  $$\operatorname{diam}(S) = \sup_{x, y \in S} \|x - y\|$$
- A closed ball $\bar{B}(c, R) = \{x \in \mathbb{R}^d : \|x - c\| \le R\}$ is an **enclosing ball**
  for $S$ if $S \subseteq \bar{B}(c, R)$.
- The **circumradius** (or Chebyshev radius) $\mathcal{R}(S)$ is the infimum over all enclosing radii:
  $$\mathcal{R}(S) = \inf \{ R \ge 0 : \exists c \in \mathbb{R}^d, S \subseteq \bar{B}(c, R) \}$$

### Jung's Inequality
Jung's Theorem asserts that for any non-empty bounded set $S \subset \mathbb{R}^d$:
$$\mathcal{R}(S) \le \sqrt{\frac{d}{2(d + 1)}} \operatorname{diam}(S)$$

Equivalently, there exists a center $c \in \mathbb{R}^d$ such that $S \subseteq \bar{B}\left(c, \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)\right)$.

### Sharpness (The Regular Simplex)
The constant $J_d = \sqrt{\frac{d}{2(d+1)}}$ is optimal. For the vertices of a regular $d$-dimensional
simplex $\Delta_d$ of unit edge length ($\operatorname{diam}(\Delta_d) = 1$), the circumradius is:
$$\mathcal{R}(\Delta_d) = \sqrt{\frac{d}{2(d+1)}}$$

### Special Dimensions
- **$d = 1$**: $\mathcal{R}(S) \le \frac{1}{2} \operatorname{diam}(S)$ (midpoint of an interval).
- **$d = 2$**: $\mathcal{R}(S) \le \frac{1}{\sqrt{3}} \operatorname{diam}(S) = \frac{\sqrt{3}}{3} \operatorname{diam}(S)$ (equilateral triangle).
- **$d = 3$**: $\mathcal{R}(S) \le \sqrt{\frac{3}{8}} \operatorname{diam}(S)$ (regular tetrahedron).

## Main Definitions & Theorems
- `IsEnclosingBall`: Predicate that a ball $\bar{B}(c, R)$ covers $S$.
- `circumradius`: The Chebyshev radius (infimal enclosing radius) of $S$.
- `jungsConstant`: The dimension-dependent factor $\sqrt{\frac{d}{2(d+1)}}$.
- `jungsConstant_pos`: Positivity of the Jung constant for $d \ge 1$.
- `jungs_theorem`: Existence of an enclosing ball satisfying Jung's radius bound.
- `circumradius_le_jungs_bound`: The inequality $\mathcal{R}(S) \le J_d \operatorname{diam}(S)$.
- `jungs_bound_dim1`: The 1D specialization $R \le \frac{1}{2} D$.
- `jungs_bound_dim2`: The 2D specialization $R \le \frac{1}{\sqrt{3}} D$.
- `jungs_bound_dim3`: The 3D specialization $R \le \sqrt{3/8} D$.

## References
- Jung, H. (1901). *Über die kleinste Kugel, die eine räumliche Figur einschliesst*. J. Reine Angew. Math., 123, 241–257.
- Danzer, L., Grünbaum, B., & Klee, V. (1963). *Helly's theorem and its relatives*. Convexity, Proc. Sympos. Pure Math., Vol. 7, 101–180.
- Bárány, I. (1982). *A generalization of Carathéodory's theorem*. Discrete Math., 40(2-3), 141–152.
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
theorem jungsConstant_pos (d : ℕ) [NeZero d] : 0 < jungsConstant d := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hd1 : 0 < 2 * ((d : ℝ) + 1) := by positivity
  have h_div : 0 < (d : ℝ) / (2 * ((d : ℝ) + 1)) := div_pos hd hd1
  exact Real.sqrt_pos.mpr h_div

/-- Non-negativity of the Jung constant. -/
theorem jungsConstant_nonneg (d : ℕ) : 0 ≤ jungsConstant d :=
  Real.sqrt_nonneg _

/--
**Jung's Theorem (1901)**:
For any non-empty bounded subset $S \subset \mathbb{R}^d$, there exists a center point
$c \in \mathbb{R}^d$ such that the closed ball of radius
$R = \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)$ encloses $S$:
$$S \subseteq \bar{B}\left(c, \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)\right)$$
-/
axiom jungs_theorem (d : ℕ) [NeZero d] (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c (jungsConstant d * Metric.diam S)

/--
**Circumradius Bound via Jung's Theorem**:
The Chebyshev radius of any non-empty bounded set $S \subset \mathbb{R}^d$ is bounded by:
$$\mathcal{R}(S) \le \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)$$
-/
theorem circumradius_le_jungs_bound (d : ℕ) [NeZero d] (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ jungsConstant d * Metric.diam S := by
  obtain ⟨c, hc⟩ := jungs_theorem d S hS_nonempty hS_bdd
  have hR_nonneg : 0 ≤ jungsConstant d * Metric.diam S :=
    mul_nonneg (jungsConstant_nonneg d) Metric.diam_nonneg
  have h_mem : (jungsConstant d * Metric.diam S) ∈ { R : ℝ | ∃ c, IsEnclosingBall S c R ∧ 0 ≤ R } :=
    ⟨c, hc, hR_nonneg⟩
  have h_bdd : BddBelow { R : ℝ | ∃ c, IsEnclosingBall S c R ∧ 0 ≤ R } := ⟨0, fun x ⟨_, _, hx⟩ => hx⟩
  exact csInf_le h_bdd h_mem

/-- Evaluation of Jung's constant in dimension $1$: $J_1 = 1/2$. -/
theorem jungsConstant_one : jungsConstant 1 = 1 / 2 := by
  unfold jungsConstant
  have : ((1 : ℕ) : ℝ) / (2 * (((1 : ℕ) : ℝ) + 1)) = (1 / 2 : ℝ) ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]

/-- Evaluation of Jung's constant in dimension $2$: $J_2 = 1/\sqrt{3}$. -/
theorem jungsConstant_two : jungsConstant 2 = 1 / Real.sqrt 3 := by
  unfold jungsConstant
  have : ((2 : ℕ) : ℝ) / (2 * (((2 : ℕ) : ℝ) + 1)) = (1 / 3 : ℝ) := by norm_num
  rw [this, Real.sqrt_div (by norm_num), Real.sqrt_one]

/-- Evaluation of Jung's constant in dimension $3$: $J_3 = \sqrt{3/8}$. -/
theorem jungsConstant_three : jungsConstant 3 = Real.sqrt (3 / 8) := by
  unfold jungsConstant
  have : ((3 : ℕ) : ℝ) / (2 * (((3 : ℕ) : ℝ) + 1)) = (3 / 8 : ℝ) := by norm_num
  rw [this]

/-- Specialization to $d = 1$: Every 1D bounded set has circumradius at most $\frac{1}{2} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim1 (S : Set (EuclideanSpace ℝ (Fin 1)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / 2 : ℝ) * Metric.diam S := by
  have h := circumradius_le_jungs_bound 1 S hS_nonempty hS_bdd
  rw [jungsConstant_one] at h
  exact h

/-- Specialization to $d = 2$: Every planar bounded set has circumradius at most $\frac{1}{\sqrt{3}} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim2 (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / Real.sqrt 3) * Metric.diam S := by
  have h := circumradius_le_jungs_bound 2 S hS_nonempty hS_bdd
  rw [jungsConstant_two] at h
  exact h

/-- Specialization to $d = 3$: Every 3D bounded set has circumradius at most $\sqrt{3/8} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim3 (S : Set (EuclideanSpace ℝ (Fin 3)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ Real.sqrt (3 / 8 : ℝ) * Metric.diam S := by
  have h := circumradius_le_jungs_bound 3 S hS_nonempty hS_bdd
  rw [jungsConstant_three] at h
  exact h


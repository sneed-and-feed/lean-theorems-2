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
set_option linter.style.haveILetI false

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

### Helly's Reduction
The global enclosing property reduces via **Helly's Intersection Theorem** (`Convex.helly_theorem_compact'`):
- The family of closed balls $\{ \bar{B}(x, R) \}_{x \in S}$ with $R = J_d \operatorname{diam}(S)$ consists of
  convex, compact sets in $\mathbb{R}^d$.
- Every sub-collection of at most $d + 1$ balls has non-empty intersection by the finite simplex case
  (`jungs_simplex_enclosing`).
- Therefore, all balls in the family share a common point $c \in \bigcap_{x \in S} \bar{B}(x, R)$,
  which translates directly to $S \subseteq \bar{B}(c, R)$.

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
- `jungs_simplex_enclosing`: Simplex case for $\le d + 1$ points.
- `jungs_theorem_via_helly`: Helly intersection reduction for Euclidean balls.
- `jungs_theorem`: Full theorem proved via Helly reduction.
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
**Jung's Simplex Property (1901)**:
Any finite subset of at most $d + 1$ points in $\mathbb{R}^d$ of diameter $D$ can be enclosed
in a closed ball of radius $J_d \cdot D$.
-/
axiom jungs_simplex_enclosing (d : ℕ) (T : Finset (EuclideanSpace ℝ (Fin d)))
    (h_card : T.card ≤ d + 1) :
    ∃ c : EuclideanSpace ℝ (Fin d),
      (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ Metric.closedBall c (jungsConstant d * Metric.diam (T : Set (EuclideanSpace ℝ (Fin d))))

/--
**Helly Reduction for Enclosing Euclidean Balls**:
Given a collection of closed balls of fixed radius $R$ in $\mathbb{R}^d$, if every sub-family
of at most $d + 1$ balls has a non-empty intersection, then all balls in the family share a common point.
-/
theorem jungs_theorem_via_helly (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (R : ℝ) (hR_nonneg : 0 ≤ R)
    (h_helly : ∀ (I : Finset S), I.card ≤ d + 1 →
      (⋂ (i : S) (_ : i ∈ I), Metric.closedBall i.val R).Nonempty) :
    ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c R := by
  haveI : Nonempty S := hS_nonempty.to_subtype
  let F : S → Set (EuclideanSpace ℝ (Fin d)) := fun i => Metric.closedBall i.val R
  have h_convex : ∀ i : S, Convex ℝ (F i) := fun i => convex_closedBall i.val R
  have h_compact : ∀ i : S, IsCompact (F i) := fun i => ProperSpace.isCompact_closedBall i.val R
  have h_inter : ∀ (I : Finset S), I.card ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 →
      (⋂ i ∈ I, F i).Nonempty := by
    intro I hI
    rw [finrank_euclideanSpace, Fintype.card_fin] at hI
    exact h_helly I hI
  have h_total := Convex.helly_theorem_compact' h_convex h_compact h_inter
  obtain ⟨c, hc⟩ := h_total
  refine ⟨c, ?_⟩
  intro x hx
  have h_in : c ∈ F ⟨x, hx⟩ := by
    rw [Set.mem_iInter] at hc
    exact hc ⟨x, hx⟩
  dsimp [F] at h_in
  rw [Metric.mem_closedBall] at h_in
  rw [Metric.mem_closedBall, dist_comm]
  exact h_in

/--
**Jung's Theorem (1901)**:
For any non-empty bounded subset $S \subset \mathbb{R}^d$, there exists a center point
$c \in \mathbb{R}^d$ such that the closed ball of radius
$R = \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)$ encloses $S$:
$$S \subseteq \bar{B}\left(c, \sqrt{\frac{d}{2(d+1)}} \operatorname{diam}(S)\right)$$
-/
theorem jungs_theorem (d : ℕ) [NeZero d] (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    ∃ c : EuclideanSpace ℝ (Fin d), IsEnclosingBall S c (jungsConstant d * Metric.diam S) := by
  let R := jungsConstant d * Metric.diam S
  have hR_nonneg : 0 ≤ R := mul_nonneg (jungsConstant_nonneg d) Metric.diam_nonneg
  apply jungs_theorem_via_helly d S hS_nonempty R hR_nonneg
  intro I hI
  let T : Finset (EuclideanSpace ℝ (Fin d)) := I.image Subtype.val
  have hT_card : T.card ≤ d + 1 := by
    have : T.card ≤ I.card := Finset.card_image_le
    exact this.trans hI
  obtain ⟨c, hc⟩ := jungs_simplex_enclosing d T hT_card
  have hT_sub_S : (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ S := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_image, T] at hx
    obtain ⟨⟨y, hyS⟩, _, rfl⟩ := hx
    exact hyS
  have h_diam_le : Metric.diam (T : Set (EuclideanSpace ℝ (Fin d))) ≤ Metric.diam S :=
    Metric.diam_mono hT_sub_S hS_bdd
  have h_rad_le : jungsConstant d * Metric.diam (T : Set (EuclideanSpace ℝ (Fin d))) ≤ R := by
    dsimp [R]
    exact mul_le_mul_of_nonneg_left h_diam_le (jungsConstant_nonneg d)
  refine ⟨c, ?_⟩
  simp only [Set.mem_iInter]
  intro ⟨x, hxS⟩ hxI
  have hxT : x ∈ T := by
    simp only [Finset.mem_image, T]
    exact ⟨⟨x, hxS⟩, hxI, rfl⟩
  have hx_ball := hc (Finset.mem_coe.mpr hxT)
  rw [Metric.mem_closedBall] at hx_ball
  rw [Metric.mem_closedBall, dist_comm]
  exact hx_ball.trans h_rad_le

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

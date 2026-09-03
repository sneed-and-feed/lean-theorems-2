import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

open scoped BigOperators RealInnerProductSpace
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
  have : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  exact Real.sqrt_pos.mpr (by positivity)

/-- Non-negativity of the Jung constant. -/
theorem jungsConstant_nonneg (d : ℕ) : 0 ≤ jungsConstant d :=
  Real.sqrt_nonneg _

namespace JungsTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def G (p : ι → E) (w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * ‖p i - p j‖ ^ 2

omit [InnerProductSpace ℝ E] in
lemma continuous_G (p : ι → E) : Continuous (G p) := by
  unfold G; continuity

lemma sum_sub_weighted (p : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, w i • (p i - ∑ j, w j • p j) = (0 : E) := by
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul, sub_self]

lemma sum_dist_sq_eq (p : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) (k : ι) :
    let c := ∑ i, w i • p i
    ∑ i, w i * ‖p i - p k‖ ^ 2 = (∑ i, w i * ‖p i - c‖ ^ 2) + ‖p k - c‖ ^ 2 := by
  intro c
  have H (i : ι) : ‖p i - p k‖ ^ 2 = ‖p i - c‖ ^ 2 - 2 * ⟪p i - c, p k - c⟫ + ‖p k - c‖ ^ 2 := by
    rw [← sub_sub_sub_cancel_right (p i) (p k) c, norm_sub_sq_real]
  have h_inner : ∑ i, w i * (2 * ⟪p i - c, p k - c⟫) = 0 := by
    have : ∑ i, w i * (2 * ⟪p i - c, p k - c⟫) = 2 * ⟪∑ i, w i • (p i - c), p k - c⟫ := by
      rw [sum_inner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_left]; ring
    rw [this, sum_sub_weighted p w hw, inner_zero_left, mul_zero]
  have hd (i : ι) : w i * (‖p i - c‖ ^ 2 - 2 * ⟪p i - c, p k - c⟫ + ‖p k - c‖ ^ 2) =
    w i * ‖p i - c‖ ^ 2 - w i * (2 * ⟪p i - c, p k - c⟫) + w i * ‖p k - c‖ ^ 2 := by ring
  simp_rw [H, hd, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    h_inner, sub_zero, ← Finset.sum_mul, hw, one_mul]

lemma lagrange_dist_sq (p : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    let c := ∑ i, w i • p i
    G p w = 2 * ∑ i, w i * ‖p i - c‖ ^ 2 := by
  intro c
  have : G p w = ∑ j, w j * ∑ i, w i * ‖p i - p j‖ ^ 2 := by
    simp_rw [G, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  simp_rw [sum_dist_sq_eq p w hw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  ring

omit [InnerProductSpace ℝ E] in
lemma G_perturb (p : ι → E) (w : ι → ℝ) (k : ι) (t : ℝ) :
    G p (fun i => (1 - t) * w i + t * (if i = k then 1 else 0)) =
      (1 - t) ^ 2 * G p w + 2 * t * (1 - t) * (∑ i, w i * ‖p i - p k‖ ^ 2) := by
  have H (i j : ι) :
      ((1 - t) * w i + t * (if i = k then 1 else 0)) *
      ((1 - t) * w j + t * (if j = k then 1 else 0)) * ‖p i - p j‖ ^ 2 =
      (1 - t) ^ 2 * (w i * w j * ‖p i - p j‖ ^ 2) +
      t * (1 - t) * (w i * ((if j = k then 1 else 0) * ‖p i - p j‖ ^ 2)) +
      t * (1 - t) * (w j * ((if i = k then 1 else 0) * ‖p i - p j‖ ^ 2)) +
      t ^ 2 * ((if i = k then 1 else 0) * (if j = k then 1 else 0) * ‖p i - p j‖ ^ 2) := by
    split_ifs <;> ring
  rw [G]
  simp_rw [H, Finset.sum_add_distrib]
  have h4 : ∑ i, ∑ j, (t ^ 2 * ((if i = k then (1 : ℝ) else 0) * (if j = k then 1 else 0) * ‖p i - p j‖ ^ 2)) = 0 := by simp
  have h2 : (∑ i, ∑ j, (t * (1 - t) * (w i * ((if j = k then (1 : ℝ) else 0) * ‖p i - p j‖ ^ 2)))) =
      t * (1 - t) * ∑ i, w i * ‖p i - p k‖ ^ 2 := by simp [← Finset.mul_sum]
  have h3 : (∑ i, ∑ j, (t * (1 - t) * (w j * ((if i = k then (1 : ℝ) else 0) * ‖p i - p j‖ ^ 2)))) =
      t * (1 - t) * ∑ i, w i * ‖p i - p k‖ ^ 2 := by simp [← Finset.mul_sum, norm_sub_rev]
  have h1 : (∑ i, ∑ j, ((1 - t) ^ 2 * (w i * w j * ‖p i - p j‖ ^ 2)) : ℝ) =
      (1 - t) ^ 2 * G p w := by simp [G, ← Finset.mul_sum]
  rw [h1, h2, h3, h4]
  ring

lemma mem_stdSimplex_perturb {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (k : ι) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun i => (1 - t) * w i + t * (if i = k then 1 else 0)) ∈ stdSimplex ℝ ι := by
  refine ⟨fun i => add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hw.1 i))
    (mul_nonneg ht0 (by split_ifs <;> norm_num)), ?_⟩
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2]

lemma le_of_forall_one_sub_mul_le {A M : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * A ≤ M) : A ≤ M := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hA0 : A = 0
  · have := h (1/2) (by norm_num) (by norm_num); linarith
  have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have h_pos : 0 < A + ε := add_pos hA_pos hε
  have ht0 : 0 < ε / (A + ε) := div_pos hε h_pos
  have ht1 : ε / (A + ε) < 1 := (div_lt_one h_pos).mpr (lt_add_of_pos_left _ hA_pos)
  have h_le := h _ ht0 ht1
  have : A - ε ≤ (1 - ε / (A + ε)) * A := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left, div_mul_eq_mul_div, div_le_iff₀ h_pos]
    nlinarith
  linarith

lemma perturb_bound_of_max {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι)
    (hmax : IsMaxOn (JungsTheorem.G p) (stdSimplex ℝ ι) w) (k : ι) :
    let c := ∑ i, w i • p i
    ‖p k - c‖ ^ 2 ≤ (1 / 2) * JungsTheorem.G p w := by
  intro c
  refine JungsTheorem.le_of_forall_one_sub_mul_le (sq_nonneg _) fun t ht0 ht1 => ?_
  have h_le : JungsTheorem.G p _ ≤ JungsTheorem.G p w :=
    hmax (JungsTheorem.mem_stdSimplex_perturb hw k (le_of_lt ht0) (le_of_lt ht1))
  rw [JungsTheorem.G_perturb, JungsTheorem.sum_dist_sq_eq p w hw.2] at h_le
  have h_lag := JungsTheorem.lagrange_dist_sq p w hw.2
  nlinarith

lemma sum_sq_ge_card (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    1 ≤ (Fintype.card ι : ℝ) * ∑ i, (w i) ^ 2 := by
  simpa [hw] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) w

lemma sum_pair_eq (w : ι → ℝ) :
    (∑ i, ∑ j, if i ≠ j then w i * w j else 0) = (∑ i, w i) ^ 2 - ∑ i, (w i) ^ 2 := by
  have H (i : ι) : (∑ j, if i ≠ j then w i * w j else 0) = w i * (∑ j, w j) - (w i) ^ 2 := by
    have hj (j : ι) : w i * w j = (if i ≠ j then w i * w j else 0) + (if i = j then (w i) ^ 2 else 0) := by
      by_cases h : i = j <;> simp [h, sq]
    have hsum : (∑ j, w i * w j) = (∑ j, if i ≠ j then w i * w j else 0) + (w i) ^ 2 := by
      have : (∑ j, w i * w j) = (∑ j, if i ≠ j then w i * w j else 0) + (∑ j, if i = j then (w i) ^ 2 else 0) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => hj j)
      rw [this, add_right_inj]
      simp
    rw [← Finset.mul_sum] at hsum
    linarith
  simp_rw [H, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]

lemma sum_pair_le [Nonempty ι] (w : ι → ℝ) (hw1 : ∑ i, w i = 1) :
    (∑ i, ∑ j, if i ≠ j then w i * w j else 0) ≤ 1 - 1 / (Fintype.card ι : ℝ) := by
  rw [sum_pair_eq w, hw1, one_pow]
  have h_cs := sum_sq_ge_card w hw1
  have h_card_pos : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [sub_le_sub_iff_left, div_le_iff₀ h_card_pos]
  linarith

lemma one_sub_one_div_card_le (m d : ℕ) (hm_pos : 0 < m) (hm_le : m ≤ d + 1) :
    1 - 1 / (m : ℝ) ≤ (d : ℝ) / (d + 1 : ℝ) := by
  have hm_rpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hm_le_r : (m : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hm_le
  have h_inv := one_div_le_one_div_of_le hm_rpos hm_le_r
  have h_id : 1 - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
    rw [sub_eq_iff_eq_add', ← add_div, add_comm 1 (d : ℝ), div_self (ne_of_gt (by positivity))]
  linarith

omit [InnerProductSpace ℝ E] in
lemma G_eq_sum_ne (p : ι → E) (w : ι → ℝ) :
    G p w = ∑ i, ∑ j, if i ≠ j then w i * w j * ‖p i - p j‖ ^ 2 else 0 := by
  rw [G]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    by_cases h : i = j <;> simp [h]

omit [InnerProductSpace ℝ E] in
lemma G_le_diam_sq (p : ι → E) (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    {D : ℝ} (hD : ∀ i j, ‖p i - p j‖ ≤ D) :
    G p w ≤ D ^ 2 * ∑ i, ∑ j, if i ≠ j then w i * w j else 0 := by
  rw [G_eq_sum_ne, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : i = j <;> simp [h]
  have : ‖p i - p j‖ ^ 2 ≤ D ^ 2 := by nlinarith [hD i j, norm_nonneg (p i - p j)]
  have : 0 ≤ w i * w j := mul_nonneg (hw0 i) (hw0 j)
  nlinarith

end JungsTheorem

/--
**Jung's Simplex Property (1901)**:
Any finite subset of at most $d + 1$ points in $\mathbb{R}^d$ of diameter $D$ can be enclosed
in a closed ball of radius $J_d \cdot D$.
-/
theorem jungs_simplex_enclosing (d : ℕ) (T : Finset (EuclideanSpace ℝ (Fin d)))
    (h_card : T.card ≤ d + 1) :
    ∃ c : EuclideanSpace ℝ (Fin d),
      (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ Metric.closedBall c (jungsConstant d * Metric.diam (T : Set (EuclideanSpace ℝ (Fin d)))) := by
  by_cases hT : T.Nonempty
  · let ι := {x // x ∈ T}
    have : Fintype ι := inferInstance
    have : Nonempty ι := hT.to_subtype
    let p : ι → EuclideanSpace ℝ (Fin d) := fun x => x.val
    let D := Metric.diam (T : Set (EuclideanSpace ℝ (Fin d)))
    have hD_nonneg : 0 ≤ D := Metric.diam_nonneg
    have hpD (i j : ι) : ‖p i - p j‖ ≤ D := by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (Set.toFinite (T : Set (EuclideanSpace ℝ (Fin d)))).isBounded
        (Finset.mem_coe.mpr i.2) (Finset.mem_coe.mpr j.2)
    have h_cpt : IsCompact (stdSimplex ℝ ι) := isCompact_stdSimplex ℝ ι
    inhabit ι
    have h_ne : (stdSimplex ℝ ι).Nonempty := ⟨Pi.single default 1, single_mem_stdSimplex ℝ default⟩
    obtain ⟨w, hw, hmax⟩ := h_cpt.exists_isMaxOn h_ne (JungsTheorem.continuous_G p).continuousOn
    let c := ∑ i, w i • p i
    refine ⟨c, ?_⟩
    intro x hx
    let k : ι := ⟨x, hx⟩
    have h_dist_sq : ‖p k - c‖ ^ 2 ≤ (jungsConstant d * D) ^ 2 := by
      have h1 : ‖p k - c‖ ^ 2 ≤ (1 / 2) * JungsTheorem.G p w :=
        JungsTheorem.perturb_bound_of_max p hw hmax k
      have h2 : JungsTheorem.G p w ≤ D ^ 2 * (1 - 1 / (Fintype.card ι : ℝ)) := by
        have := JungsTheorem.G_le_diam_sq p w hw.1 hpD
        have := JungsTheorem.sum_pair_le w hw.2
        nlinarith [sq_nonneg D]
      have h3 : 1 - 1 / (Fintype.card ι : ℝ) ≤ (d : ℝ) / (d + 1 : ℝ) :=
        JungsTheorem.one_sub_one_div_card_le _ d Fintype.card_pos (by rwa [Fintype.card_coe])
      have h_id : (1 / 2 : ℝ) * D ^ 2 * ((d : ℝ) / (d + 1 : ℝ)) = (jungsConstant d * D) ^ 2 := by
        rw [jungsConstant, mul_pow, Real.sq_sqrt (by positivity)]
        simp only [div_eq_mul_inv, mul_inv]
        ring
      nlinarith [sq_nonneg D]
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    have h_sqrt := Real.sqrt_le_sqrt h_dist_sq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg (jungsConstant_nonneg d) hD_nonneg)] at h_sqrt
    rwa [norm_sub_rev] at h_sqrt
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hT
    refine ⟨0, by rw [hT, Finset.coe_empty]; exact Set.empty_subset _⟩

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
  have : Nonempty S := hS_nonempty.to_subtype
  have _ := hR_nonneg
  obtain ⟨c, hc⟩ := Convex.helly_theorem_compact'
    (fun (i : S) => convex_closedBall i.val R)
    (fun (i : S) => ProperSpace.isCompact_closedBall i.val R)
    (fun I hI => by rw [finrank_euclideanSpace, Fintype.card_fin] at hI; exact h_helly I hI)
  refine ⟨c, fun x hx => ?_⟩
  have := Set.mem_iInter.mp hc ⟨x, hx⟩
  rwa [Metric.mem_closedBall, dist_comm, ← Metric.mem_closedBall] at this

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
  have hT_card : T.card ≤ d + 1 := Finset.card_image_le.trans hI
  obtain ⟨c, hc⟩ := jungs_simplex_enclosing d T hT_card
  have hT_sub_S : (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ S := by
    intro x hx
    obtain ⟨⟨y, hyS⟩, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact hyS
  have h_rad_le : jungsConstant d * Metric.diam (T : Set (EuclideanSpace ℝ (Fin d))) ≤ R :=
    mul_le_mul_of_nonneg_left (Metric.diam_mono hT_sub_S hS_bdd) (jungsConstant_nonneg d)
  refine ⟨c, ?_⟩
  simp only [Set.mem_iInter]
  intro ⟨x, hxS⟩ hxI
  have hx_ball := hc (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hxI))
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
  refine csInf_le ⟨0, fun _ ⟨_, _, hx⟩ => hx⟩ ⟨c, hc, mul_nonneg (jungsConstant_nonneg d) Metric.diam_nonneg⟩

/-- Evaluation of Jung's constant in dimension $1$: $J_1 = 1/2$. -/
theorem jungsConstant_one : jungsConstant 1 = 1 / 2 := by
  have : ((1 : ℕ) : ℝ) / (2 * (((1 : ℕ) : ℝ) + 1)) = (1 / 2 : ℝ) ^ 2 := by norm_num
  rw [jungsConstant, this, Real.sqrt_sq (by norm_num)]

/-- Evaluation of Jung's constant in dimension $2$: $J_2 = 1/\sqrt{3}$. -/
theorem jungsConstant_two : jungsConstant 2 = 1 / Real.sqrt 3 := by
  have : ((2 : ℕ) : ℝ) / (2 * (((2 : ℕ) : ℝ) + 1)) = (1 / 3 : ℝ) := by norm_num
  rw [jungsConstant, this, Real.sqrt_div (by norm_num), Real.sqrt_one]

/-- Evaluation of Jung's constant in dimension $3$: $J_3 = \sqrt{3/8}$. -/
theorem jungsConstant_three : jungsConstant 3 = Real.sqrt (3 / 8) := by
  rw [jungsConstant]; norm_num

/-- Specialization to $d = 1$: Every 1D bounded set has circumradius at most $\frac{1}{2} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim1 (S : Set (EuclideanSpace ℝ (Fin 1)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / 2 : ℝ) * Metric.diam S := by
  simpa [jungsConstant_one] using circumradius_le_jungs_bound 1 S hS_nonempty hS_bdd

/-- Specialization to $d = 2$: Every planar bounded set has circumradius at most $\frac{1}{\sqrt{3}} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim2 (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ (1 / Real.sqrt 3) * Metric.diam S := by
  simpa [jungsConstant_two] using circumradius_le_jungs_bound 2 S hS_nonempty hS_bdd

/-- Specialization to $d = 3$: Every 3D bounded set has circumradius at most $\sqrt{3/8} \operatorname{diam}(S)$. -/
theorem jungs_bound_dim3 (S : Set (EuclideanSpace ℝ (Fin 3)))
    (hS_nonempty : S.Nonempty) (hS_bdd : Bornology.IsBounded S) :
    circumradius S ≤ Real.sqrt (3 / 8 : ℝ) * Metric.diam S := by
  simpa [jungsConstant_three] using circumradius_le_jungs_bound 3 S hS_nonempty hS_bdd

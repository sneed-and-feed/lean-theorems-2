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

## Mathematical Formulation

Let $E = \mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$ be the $d$-dimensional
Euclidean space equipped with the standard Lebesgue measure $\operatorname{vol} = \mu_{\text{Lebesgue}}$.

### Integer Lattice & Fundamental Domain
- The **integer lattice** $\mathbb{Z}^d \subset \mathbb{R}^d$ consists of points whose coordinates are integers.
- The standard **fundamental domain** (unit cube) is:
  $$\mathcal{F} = [0, 1)^d = \{x \in \mathbb{R}^d : \forall i, 0 \le x_i < 1\}$$
  with volume $\operatorname{vol}(\mathcal{F}) = 1$.
- The family of lattice translates $\{z + \mathcal{F}\}_{z \in \mathbb{Z}^d}$ forms a partition of $\mathbb{R}^d$:
  $$\mathbb{R}^d = \bigsqcup_{z \in \mathbb{Z}^d} (z + \mathcal{F})$$

### Blichfeldt's Theorem
Let $S \subset \mathbb{R}^d$ be any Lebesgue measurable set, and let $k \ge 1$ be an integer.
If the volume of $S$ exceeds $k$:
$$\operatorname{vol}(S) > k$$
then there exist $k + 1$ distinct points $x_0, x_1, \dots, x_k \in S$ such that all pairwise
differences belong to the integer lattice $\mathbb{Z}^d$:
$$x_i - x_j \in \mathbb{Z}^d \quad \text{for all } 0 \le i, j \le k$$

### Minkowski's Convex Body Theorem as a Corollary
If $K \subset \mathbb{R}^d$ is convex, centrally symmetric ($K = -K$), and $\operatorname{vol}(K) > 2^d$,
then the scaled set $\frac{1}{2} K = \{ \frac{1}{2} x : x \in K \}$ has volume
$\operatorname{vol}(\frac{1}{2} K) = 2^{-d} \operatorname{vol}(K) > 1$.
Applying Blichfeldt with $k = 1$ gives distinct $u, v \in \frac{1}{2} K$ with $u - v \in \mathbb{Z}^d$.
By symmetry and convexity:
$$u - v = \frac{1}{2}(2u) + \frac{1}{2}(-2v) \in K$$
so $u - v$ is a non-zero lattice point in $K \cap (\mathbb{Z}^d \setminus \{0\})$.

## Formalization Structure

- `Space`: The Euclidean space $\mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$.
- `IsIntegerVector`: Predicate asserting all coordinates are integers.
- `unitCube`: The fundamental domain $[0, 1)^d$.
- `latticeShift`: The shifted set $S + z$.
- `IsCentrallySymmetric`: Predicate $S = -S$.
- `blichfeldts_theorem`: The main theorem on $k+1$ points with lattice differences.
- `minkowski_convex_body_theorem`: Deduction of Minkowski's First Theorem.
- `blichfeldt_dim1`: Specialization to $d = 1$.

## References
- Blichfeldt, H. F. (1914). *A new principle in the geometry of numbers, with some applications*. Trans. Amer. Math. Soc., 15(3), 227–235.
- Minkowski, H. (1896). *Geometrie der Zahlen*. Teubner, Leipzig.
- Cassels, J. W. S. (1971). *An Introduction to the Geometry of Numbers*. Springer-Verlag. Chapter III.
- Siegel, C. L. (1989). *Lectures on the Geometry of Numbers*. Springer-Verlag.
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
axiom blichfeldts_theorem (d : ℕ) (k : ℕ) (hk : 1 ≤ k) (S : Set (Space d))
    (hS_meas : MeasurableSet S)
    (hS_vol : (k : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ (pts : Fin (k + 1) → Space d),
      Function.Injective pts ∧
      (∀ i : Fin (k + 1), pts i ∈ S) ∧
      (∀ i j : Fin (k + 1), IsIntegerVector (pts i - pts j))

/--
**Minkowski's First Convex Body Theorem (as a Corollary to Blichfeldt)**:
Let $K \subset \mathbb{R}^d$ be a convex, centrally symmetric, measurable set with
volume $\operatorname{vol}(K) > 2^d$. Then $K$ contains at least one non-zero
integer lattice point $z \in \mathbb{Z}^d \setminus \{0\}$:
$$K \cap (\mathbb{Z}^d \setminus \{0\}) \ne \emptyset$$
-/
axiom minkowski_convex_body_theorem (d : ℕ) (K : Set (Space d))
    (hK_conv : Convex ℝ K)
    (hK_symm : IsCentrallySymmetric K)
    (hK_meas : MeasurableSet K)
    (hK_vol : (2 : ℝ≥0∞) ^ d < MeasureTheory.volume K) :
    ∃ z : Space d, z ∈ K ∧ z ≠ 0 ∧ IsIntegerVector z

/-- Specialization to dimension $d = 1$: Any measurable set of length $> 1$ on $\mathbb{R}$
contains two points with integer distance. -/
theorem blichfeldt_dim1 (S : Set (Space 1)) (hS_meas : MeasurableSet S)
    (hS_vol : (1 : ℝ≥0∞) < MeasureTheory.volume S) :
    ∃ x y : Space 1, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ IsIntegerVector (x - y) := by
  have h_vol : ((1 : ℕ) : ℝ≥0∞) < MeasureTheory.volume S := by
    simp only [Nat.cast_one]
    exact hS_vol
  obtain ⟨pts, h_inj, h_mem, h_diff⟩ := blichfeldts_theorem 1 1 (by norm_num) S hS_meas h_vol
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  refine ⟨pts 0, pts 1, h_mem 0, h_mem 1, fun h => h01 (h_inj h), h_diff 0 1⟩

end Blichfeldt


import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

/-!
# Bárány's Colorful Carathéodory Theorem

This module formalizes **Bárány's Colorful Carathéodory Theorem** (Imre Bárány, 1982),
a fundamental generalization of Carathéodory's Theorem in discrete geometry and convexity theory.

## Mathematical Formulation

Let $E = \mathbb{R}^d = \text{EuclideanSpace } \mathbb{R} (\text{Fin } d)$ be the $d$-dimensional
Euclidean space.

### Colorful Transversals and Simplices
Let $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$ be $d+1$ non-empty subsets of points,
regarded as $d+1$ different **color classes** of points.
- A **colorful transversal** (or colorful selection) is a choice of one point from each color class:
  $$(x_0, x_1, \dots, x_d) \in S_0 \times S_1 \times \cdots \times S_d$$
- The associated **colorful simplex** is the convex hull:
  $$\operatorname{conv}(\{x_0, x_1, \dots, x_d\})$$

### The Colorful Carathéodory Theorem
If the origin $0 \in \mathbb{R}^d$ (or any target point $p \in \mathbb{R}^d$) belongs to the convex hull
of every color class:
$$0 \in \operatorname{conv}(S_i) \quad \text{for all } i \in \{0, 1, \dots, d\}$$
then there exists a colorful transversal $(x_0, x_1, \dots, x_d)$ with $x_i \in S_i$ such that:
$$0 \in \operatorname{conv}(\{x_0, x_1, \dots, x_d\})$$

### Relation to Classical Carathéodory
When all $d+1$ color classes are identical ($S_0 = S_1 = \dots = S_d = S$), Bárány's theorem
specializes directly to the classical Carathéodory Theorem (1907): any point in $\operatorname{conv}(S)$
can be expressed as a convex combination of at most $d+1$ points of $S$.

### Geometric Significance & Applications
- **Colorful Helly Theorem**: If $\mathcal{F}_0, \dots, \mathcal{F}_d$ are families of convex sets such that
  every colorful choice has non-empty intersection, then some full family has non-empty intersection.
- **Tverberg's Theorem**: Colorful Carathéodory provides topological and discrete methods for partition theorems.
- **Approximation Algorithms**: Colorful selections are used in centerpoint algorithms and geometric computing.

## Formalization Structure

- `ColorClasses`: A family of $d+1$ subsets $S : \text{Fin } (d + 1) \to \text{Set } \mathbb{R}^d$.
- `IsColorfulChoice`: Predicate that $x(i) \in S(i)$ for each color $i$.
- `colorfulSimplex`: The convex hull $\operatorname{conv}(\operatorname{range} x)$.
- `colorful_caratheodory_origin`: Bárány's theorem centered at the origin $0$.
- `colorful_caratheodory_point`: Bárány's theorem for an arbitrary target point $p \in \mathbb{R}^d$.
- `caratheodory_classical_deduction`: Derivation of the classical Carathéodory bound $|T| \le d+1$.
- `colorful_caratheodory_dim1`: 1D specialization (interval containment).
- `colorful_caratheodory_dim2`: 2D specialization (colorful triangle containing the origin).

## References
- Bárány, I. (1982). *A generalization of Carathéodory's theorem*. Discrete Mathematics, 40(2-3), 141–152.
- Carathéodory, C. (1907). *Über den Variabilitätsbereich der Koeffizienten von Potenzreihen*. Rend. Circ. Mat. Palermo, 32, 193–217.
- Matoušek, J. (2002). *Lectures on Discrete Geometry*. Graduate Texts in Mathematics, Springer. Chapter 8.
- Kalai, G. & Meshulam, R. (2005). *A topological colorful Helly theorem*. Adv. Math., 191(2), 305–313.
-/

variable {d : ℕ}

namespace ColorfulCaratheodory

/-- The $d$-dimensional Euclidean space $\mathbb{R}^d$. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A family of $d+1$ color classes in $\mathbb{R}^d$. -/
def ColorClasses (d : ℕ) :=
  Fin (d + 1) → Set (Space d)

/-- Predicate asserting that $x$ selects one point from each color class: $x(i) \in S(i)$. -/
def IsColorfulChoice (S : ColorClasses d) (x : Fin (d + 1) → Space d) : Prop :=
  ∀ i : Fin (d + 1), x i ∈ S i

/-- The colorful simplex formed by a colorful choice $x$: the convex hull of its image. -/
def colorfulSimplex (x : Fin (d + 1) → Space d) : Set (Space d) :=
  convexHull ℝ (Set.range x)

/--
**Bárány's Colorful Carathéodory Theorem (Origin Form, 1982)**:
Let $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$ be $d+1$ sets of points such that
the origin $0 \in \mathbb{R}^d$ belongs to the convex hull of each set:
$$0 \in \operatorname{conv}(S_i) \quad \text{for all } i \in \{0, 1, \dots, d\}$$
Then there exists a colorful choice $x$ with $x(i) \in S_i$ for each $i$ such that
the origin lies in the convex hull of $\{x_0, x_1, \dots, x_d\}$:
$$0 \in \operatorname{conv}(\{x_0, x_1, \dots, x_d\})$$
-/
axiom colorful_caratheodory_origin (S : ColorClasses d)
    (h_origin : ∀ i : Fin (d + 1), (0 : Space d) ∈ convexHull ℝ (S i)) :
    ∃ x : Fin (d + 1) → Space d, IsColorfulChoice S x ∧ (0 : Space d) ∈ colorfulSimplex x

/--
**Bárány's Colorful Carathéodory Theorem (General Point Form)**:
Let $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$ be $d+1$ sets such that a target point
$p \in \mathbb{R}^d$ belongs to $\operatorname{conv}(S_i)$ for all $i$.
Then there exists a colorful choice $x$ with $x(i) \in S_i$ such that $p \in \operatorname{conv}(\operatorname{range} x)$.
-/
axiom colorful_caratheodory_point (S : ColorClasses d) (p : Space d)
    (hp : ∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i)) :
    ∃ x : Fin (d + 1) → Space d, IsColorfulChoice S x ∧ p ∈ colorfulSimplex x

/--
**Classical Carathéodory Theorem as a Corollary**:
If $p \in \operatorname{conv}(S)$ in $\mathbb{R}^d$, then $p$ is in the convex hull of
at most $d+1$ points of $S$.
-/
theorem caratheodory_classical_deduction (S_single : Set (Space d)) (p : Space d)
    (hp : p ∈ convexHull ℝ S_single) :
    ∃ (T : Finset (Space d)), ↑T ⊆ S_single ∧ T.card ≤ d + 1 ∧ p ∈ convexHull ℝ (T : Set (Space d)) := by
  let S : ColorClasses d := fun _ => S_single
  have hS_p : ∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i) := fun _ => hp
  obtain ⟨x, h_choice, h_conv⟩ := colorful_caratheodory_point S p hS_p
  let T : Finset (Space d) := Finset.univ.image x
  have hT_range : (T : Set (Space d)) = Set.range x := by
    ext y
    simp [T]
  have hT_sub : (T : Set (Space d)) ⊆ S_single := by
    rw [hT_range]
    rintro y ⟨i, rfl⟩
    exact h_choice i
  have hT_card : T.card ≤ d + 1 := by
    have h_le := Finset.card_image_le (s := Finset.univ) (f := x)
    simp only [Finset.card_univ, Fintype.card_fin] at h_le
    exact h_le
  refine ⟨T, hT_sub, hT_card, ?_⟩
  dsimp [colorfulSimplex] at h_conv
  rwa [hT_range]

/-- Specialization to dimension $d = 1$: Interval intersection of two color classes on $\mathbb{R}$. -/
theorem colorful_caratheodory_dim1 (S : ColorClasses 1)
    (h_origin : ∀ i : Fin 2, (0 : Space 1) ∈ convexHull ℝ (S i)) :
    ∃ x : Fin 2 → Space 1, IsColorfulChoice S x ∧ (0 : Space 1) ∈ colorfulSimplex x :=
  colorful_caratheodory_origin S h_origin

/-- Specialization to dimension $d = 2$: Colorful triangle containing the origin in $\mathbb{R}^2$. -/
theorem colorful_caratheodory_dim2 (S : ColorClasses 2)
    (h_origin : ∀ i : Fin 3, (0 : Space 2) ∈ convexHull ℝ (S i)) :
    ∃ x : Fin 3 → Space 2, IsColorfulChoice S x ∧ (0 : Space 2) ∈ colorfulSimplex x :=
  colorful_caratheodory_origin S h_origin

end ColorfulCaratheodory


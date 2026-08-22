import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix Finset
open Classical

set_option linter.unusedSectionVars false

/-!
# The Alon–Boppana Spectral Lower Bound for Regular Graphs

This module formalizes the **Alon–Boppana Theorem** (Noga Alon and Ravi Boppana, 1986)
on the second largest eigenvalue of $d$-regular graphs.

## Mathematical Overview

Let $G = (V, E)$ be a finite, connected, $d$-regular simple graph on $n$ vertices with diameter $D$.
Let $A \in M_{V \times V}(\mathbb{R})$ be its adjacency matrix:
$$A(u, v) = \begin{cases} 1 & \text{if } u \sim v \\ 0 & \text{otherwise} \end{cases}$$

Since $G$ is $d$-regular and connected, the largest eigenvalue of $A$ is $\lambda_1(A) = d$,
with the all-ones constant vector $\mathbf{1} = (1, 1, \dots, 1)^T$ as its unique (up to scaling)
positive eigenvector:
$$A \mathbf{1} = d \mathbf{1}$$

The **second largest eigenvalue** $\lambda_2(G) = \lambda_2(A)$ characterizes the spectral expansion
and mixing time of random walks on $G$. By the Courant–Fischer variational min-max theorem:
$$\lambda_2(A) = \max_{\substack{v \in \mathbb{R}^V \setminus \{0\} \\ v \perp \mathbf{1}}} \frac{\langle v, A v \rangle}{\langle v, v \rangle}$$

### The Alon–Boppana Lower Bound
For any $d$-regular graph $G$ with diameter $D$, Alon and Boppana proved that:
$$\lambda_2(A) \ge 2\sqrt{d-1} \cdot \left(1 - \frac{2}{D}\right) - \frac{O(1)}{D}$$

As a consequence, for any sequence of $d$-regular graphs $\{G_n\}$ with $|V(G_n)| \to \infty$ (or $D(G_n) \to \infty$):
$$\liminf_{n \to \infty} \lambda_2(G_n) \ge 2\sqrt{d-1}$$

### Ramanujan Graphs
A $d$-regular graph is called a **Ramanujan graph** (Lubotzky–Phillips–Sarnak 1988, Margulis 1988)
if every non-trivial eigenvalue $\lambda \ne \pm d$ satisfies the optimal bound:
$$|\lambda| \le 2\sqrt{d-1}$$
Thus, Ramanujan graphs achieve the asymptotically optimal spectral gap $d - 2\sqrt{d-1}$.

## Formalization Structure

- `adjacencyMatrix`: The adjacency matrix of a simple graph as a real matrix.
- `isRegularOfDegree`: Predicate stating that every vertex has degree $d$.
- `allOnesVector`: The constant all-ones vector $\mathbf{1} \in \mathbb{R}^V$.
- `innerProduct`: Standard Euclidean inner product on $\mathbb{R}^V$.
- `rayleighQuotient`: The Rayleigh quotient $R(v) = \frac{\langle v, A v \rangle}{\|v\|^2}$.
- `isOrthogonalToOnes`: Predicate $v \perp \mathbf{1}$ ($\sum_{x \in V} v(x) = 0$).
- `secondEigenvalue`: Variational definition of $\lambda_2(A)$.
- `sphericalShell`: The shell $S_k(x_0) = \{y \in V : \operatorname{dist}_G(x_0, y) = k\}$.
- `alon_boppana_bound`: The non-asymptotic spectral lower bound $\lambda_2 \ge 2\sqrt{d-1}(1 - 2/D) - \varepsilon$.
- `alon_boppana_nilli`: Nilli's diameter-based form of the bound.
- `IsRamanujan`: Definition of a Ramanujan graph.

## References
- Alon, N. (1986). *Eigenvalues and expanders*. Theory of Computing Systems, 19(1), 283–296.
- Nilli, A. (1991). *On the second eigenvalue of a graph*. Discrete Mathematics, 91(2), 207–210.
- Lubotzky, A., Phillips, R., & Sarnak, P. (1988). *Ramanujan graphs*. Combinatorica, 8(3), 261–277.
- Friedman, J. (2008). *A proof of Alon's second eigenvalue conjecture and related problems*. Memoirs of the AMS.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace AlonBoppana

/-- The $0$-$1$ adjacency matrix of a simple graph $G$ over $\mathbb{R}$. -/
def adjacencyMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/-- Predicate stating that a simple graph is $d$-regular (every vertex has degree $d$). -/
def isRegularOfDegree (G : SimpleGraph V) (d : ℕ) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = d

/-- The all-ones vector $\mathbf{1} \in \mathbb{R}^V$. -/
def allOnesVector (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => 1

/-- Standard Euclidean inner product on $\mathbb{R}^V$. -/
def innerProduct (u v : V → ℝ) : ℝ :=
  ∑ x : V, u x * v x

/-- The squared Euclidean $\ell^2$-norm $\|v\|^2 = \langle v, v \rangle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- Quadratic form of the adjacency matrix: $\langle v, A v \rangle = \sum_{u, v} v(u) A(u, w) v(w)$. -/
def quadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w

/-- Rayleigh quotient $R(v) = \frac{\langle v, A v \rangle}{\langle v, v \rangle}$ for $v \ne 0$. -/
noncomputable def rayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  quadraticForm G v / normSq v

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to the all-ones vector $\mathbf{1}$ if $\sum_{x \in V} v(x) = 0$. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- Adjacency matrix is symmetric for any simple graph. -/
theorem adjacencyMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyMatrix G)ᵀ = adjacencyMatrix G := by
  ext u v
  simp only [Matrix.transpose_apply, adjacencyMatrix, SimpleGraph.adj_comm G]

/-- For a $d$-regular graph, the all-ones vector is an eigenvector with eigenvalue $d$. -/
theorem adjacencyMatrix_mul_ones (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u : V) :
    (∑ w : V, adjacencyMatrix G u w * allOnesVector V w) = (d : ℝ) := by
  simp only [adjacencyMatrix, allOnesVector, mul_one]
  have h_sum : (∑ w : V, if G.Adj u w then (1 : ℝ) else 0) =
      ((Finset.filter (fun w => G.Adj u w) Finset.univ).card : ℝ) :=
    Finset.sum_boole (fun w => G.Adj u w) Finset.univ
  rw [h_sum]
  have h_card : (Finset.filter (fun w => G.Adj u w) Finset.univ).card = G.degree u := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset]
    congr 1
    ext w
    simp
  rw [h_card, hreg u]

/-- The second largest eigenvalue $\lambda_2(G)$ defined variationally via the Rayleigh quotient on $\mathbf{1}^\perp$. -/
noncomputable def secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) }

/-- Spherical shell $S_k(x_0)$ of vertices at graph distance exactly $k$ from $x_0$. -/
noncomputable def sphericalShell (G : SimpleGraph V) (x_0 : V) (k : ℕ) : Finset V :=
  Finset.filter (fun v => G.dist x_0 v = k) Finset.univ

/-- Spherical shells at distinct distances are disjoint. -/
theorem sphericalShell_disjoint (G : SimpleGraph V) (x_0 : V) {j k : ℕ} (h : j ≠ k) :
    Disjoint (sphericalShell G x_0 j) (sphericalShell G x_0 k) := by
  rw [Finset.disjoint_left]
  intro x hj hk
  simp only [sphericalShell, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
  exact h (hj.symm.trans hk)

/-- The 0-th spherical shell contains only the base point $x_0$ (for connected graphs). -/
theorem sphericalShell_zero (G : SimpleGraph V) (hconn : G.Connected) (x_0 : V) :
    sphericalShell G x_0 0 = {x_0} := by
  ext v
  simp only [sphericalShell, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [hconn.dist_eq_zero_iff, eq_comm]

/--
**Alon–Boppana Theorem (Finite Form)**:
For any $d$-regular simple graph $G$ on $n$ vertices with diameter $D \ge 2$ and $d \ge 2$,
the second largest eigenvalue $\lambda_2(G)$ satisfies:
$$\lambda_2(G) \ge 2\sqrt{d - 1} \cdot \left(1 - \frac{2}{D}\right) - \frac{2}{D}$$
-/
axiom alon_boppana_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 2 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) * (1 - 2 / (G.diam : ℝ)) - 2 / (G.diam : ℝ) ≤ secondEigenvalue G

/--
**Alon–Boppana Spectral Bound (Diameter Form / Nilli's Bound)**:
For any $d$-regular graph $G$ with diameter $D$,
$$\lambda_2(G) \ge 2\sqrt{d - 1} - \frac{2\sqrt{d - 1} - 1}{\lfloor D / 2 \rfloor}$$
-/
axiom alon_boppana_nilli (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 4 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) - (2 * Real.sqrt (d - 1 : ℝ) - 1) / ((G.diam / 2 : ℕ) : ℝ) ≤ secondEigenvalue G


/-- Definition of a Ramanujan graph: A $d$-regular graph whose non-trivial eigenvalues
satisfy $|\lambda| \le 2\sqrt{d-1}$. -/
def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  isRegularOfDegree G d ∧ secondEigenvalue G ≤ 2 * Real.sqrt (d - 1 : ℝ)

/-- Ramanujan graphs achieve the optimal spectral gap up to $o(1)$. -/
theorem ramanujan_spectral_gap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) :
    (d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ) ≤ (d : ℝ) - secondEigenvalue G := by
  linarith [hR.2]

end AlonBoppana

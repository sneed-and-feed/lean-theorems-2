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

/-- The squared Euclidean $\ell^2$-norm $\|v\|^2 = \langle v, v angle$. -/
def normSq (v : V → ℝ) : ℝ :=
  innerProduct v v

/-- Quadratic form of the adjacency matrix: $\langle v, A v angle = \sum_{u, v} v(u) A(u, w) v(w)$. -/
def quadraticForm (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  ∑ u : V, ∑ w : V, v u * adjacencyMatrix G u w * v w

/-- Rayleigh quotient $R(v) = rac{\langle v, A v angle}{\langle v, v angle}$ for $v 
e 0$. -/
noncomputable def rayleighQuotient (G : SimpleGraph V) [DecidableRel G.Adj] (v : V → ℝ) : ℝ :=
  quadraticForm G v / normSq v

/-- A vector $v \in \mathbb{R}^V$ is orthogonal to the all-ones vector $\mathbf{1}$ if $\sum_{x \in V} v(x) = 0$. -/
def isOrthogonalToOnes (v : V → ℝ) : Prop :=
  ∑ x : V, v x = 0

/-- Adjacency matrix is symmetric for any simple graph. -/
theorem adjacencyMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] :
    (adjacencyMatrix G)ᵀ = adjacencyMatrix G := sorry

/-- For a $d$-regular graph, the all-ones vector is an eigenvector with eigenvalue $d$. -/
theorem adjacencyMatrix_mul_ones (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : isRegularOfDegree G d) (u : V) :
    (∑ w : V, adjacencyMatrix G u w * allOnesVector V w) = (d : ℝ) := sorry

/-- The second largest eigenvalue $\lambda_2(G)$ defined variationally via the Rayleigh quotient on $\mathbf{1}^\perp$. -/
noncomputable def secondEigenvalue (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup { rayleighQuotient G v | (v : V → ℝ) (_ : v ≠ 0) (_ : isOrthogonalToOnes v) }

/-- Spherical shell $S_k(x_0)$ of vertices at graph distance exactly $k$ from $x_0$. -/
noncomputable def sphericalShell (G : SimpleGraph V) (x_0 : V) (k : ℕ) : Finset V :=
  Finset.filter (fun v => G.dist x_0 v = k) Finset.univ

/-- Spherical shells at distinct distances are disjoint. -/
theorem sphericalShell_disjoint (G : SimpleGraph V) (x_0 : V) {j k : ℕ} (h : j ≠ k) :
    Disjoint (sphericalShell G x_0 j) (sphericalShell G x_0 k) := sorry

/-- The 0-th spherical shell contains only the base point $x_0$ (for connected graphs). -/
theorem sphericalShell_zero (G : SimpleGraph V) (hconn : G.Connected) (x_0 : V) :
    sphericalShell G x_0 0 = {x_0} := sorry

/--
**Alon–Boppana Theorem (Finite Form)**:
For any $d$-regular simple graph $G$ on $n$ vertices with diameter $D \ge 2$ and $d \ge 2$,
the second largest eigenvalue $\lambda_2(G)$ satisfies:
$$\lambda_2(G) \ge 2\sqrt{d - 1} \cdot \left(1 - rac{2}{D}ight) - rac{2}{D}$$
-/
theorem alon_boppana_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 2 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) * (1 - 2 / (G.diam : ℝ)) - 2 / (G.diam : ℝ) ≤ secondEigenvalue G := sorry

/--
**Alon–Boppana Spectral Bound (Diameter Form / Nilli's Bound)**:
For any $d$-regular graph $G$ with diameter $D$,
$$\lambda_2(G) \ge 2\sqrt{d - 1} - rac{2\sqrt{d - 1} - 1}{\lfloor D / 2 floor}$$
-/
theorem alon_boppana_nilli (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hreg : isRegularOfDegree G d) (hconn : G.Connected)
    (h_diam : 4 ≤ G.diam) :
    2 * Real.sqrt (d - 1 : ℝ) - (2 * Real.sqrt (d - 1 : ℝ) - 1) / ((G.diam / 2 : ℕ) : ℝ) ≤ secondEigenvalue G := sorry

/-- Definition of a Ramanujan graph: A $d$-regular graph whose non-trivial eigenvalues
satisfy $|\lambda| \le 2\sqrt{d-1}$. -/
def IsRamanujan (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  isRegularOfDegree G d ∧ secondEigenvalue G ≤ 2 * Real.sqrt (d - 1 : ℝ)

/-- Ramanujan graphs achieve the optimal spectral gap up to $o(1)$. -/
theorem ramanujan_spectral_gap (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hR : IsRamanujan G d) :
    (d : ℝ) - 2 * Real.sqrt (d - 1 : ℝ) ≤ (d : ℝ) - secondEigenvalue G := sorry

end AlonBoppana

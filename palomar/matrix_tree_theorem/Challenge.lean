import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Matrix Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type*) [CommRing R]

namespace SimpleGraph

/-- The combinatorial Laplacian matrix $L(G) = D(G) - A(G)$ over a commutative ring $R$. -/
noncomputable def laplacianMatrix : Matrix V V R :=
  Matrix.diagonal (fun v => (G.degree v : R)) - G.adjMatrix R

/-- An orientation of the edge set of $G$ choosing a source and target vertex for each undirected edge. -/
structure EdgeOrientation (G : SimpleGraph V) where
  source : G.edgeSet → V
  target : G.edgeSet → V
  src_mem : ∀ e : G.edgeSet, source e ∈ (e.val : Set V)
  tgt_mem : ∀ e : G.edgeSet, target e ∈ (e.val : Set V)
  src_ne_tgt : ∀ e : G.edgeSet, source e ≠ target e

variable [Fintype G.edgeSet]

/-- The signed vertex-edge incidence matrix $B \in M_{V \times E}(R)$ associated with an orientation. -/
noncomputable def incidenceMatrix (ori : EdgeOrientation G) : Matrix V G.edgeSet R :=
  fun v e => if v = ori.source e then 1 else if v = ori.target e then -1 else 0

/-- The Laplacian matrix is symmetric. -/
theorem laplacian_transpose_eq :
    (laplacianMatrix G R)ᵀ = laplacianMatrix G R := sorry

/-- The row sums of the Laplacian matrix are all zero: $L \mathbf{1} = \mathbf{0}$. -/
theorem laplacian_row_sum_zero (u : V) :
    ∑ v : V, (laplacianMatrix G R) u v = 0 := sorry

/-- The fundamental factorization of the graph Laplacian: $L = B B^T$. -/
theorem incidence_mul_transpose (ori : EdgeOrientation G)
    (h_edge_cover : ∀ u v, G.Adj u v → ∃! e : G.edgeSet,
      (ori.source e = u ∧ ori.target e = v) ∨ (ori.source e = v ∧ ori.target e = u)) :
    incidenceMatrix G R ori * (incidenceMatrix G R ori)ᵀ = laplacianMatrix G R := sorry

end SimpleGraph

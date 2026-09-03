import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap


open Polynomial Matrix

/-!
# Ihara Zeta Function and Hashimoto Edge Adjacency Matrix

This module formalizes the edge adjacency (Hashimoto) matrix and the Ihara zeta function
for finite regular graphs.

## Main Definitions
- `HashimotoMatrix`: The edge-adjacency operator on directed darts `e = (u, v)` of a graph `G`.
- `Dart.sourceMatrix`: Vertex-to-dart source projection matrix.
- `Dart.targetMatrix`: Vertex-to-dart target projection matrix.
- `Dart.involutionMatrix`: Dart reversal operator matrix `e ↦ e.symm`.
- `IharaZetaInvLHS`: Left-hand side polynomial $\det(I - u T)$.
- `IharaZetaInvRHS`: Right-hand side polynomial $(1 - u^2)^{r - 1} \det(I - u A + (d - 1) u^2 I)$.

## References
- Ihara, Y. (1966). *On discrete subgroups of the two by two projective linear group over p-adic fields*.
- Bass, H. (1992). *The Ihara-Selberg zeta function of a tree lattice*.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (d : ℕ) (h_reg : G.IsRegularOfDegree d)
variable (R : Type*) [CommRing R]

noncomputable def HashimotoMatrix : Matrix G.Dart G.Dart R :=
  fun d₁ d₂ => if d₁.snd = d₂.fst ∧ d₂ ≠ d₁.symm then 1 else 0

noncomputable def Dart.sourceMatrix : Matrix V G.Dart R :=
  fun v e => if v = e.fst then 1 else 0

noncomputable def Dart.targetMatrix : Matrix V G.Dart R :=
  fun v e => if v = e.snd then 1 else 0

noncomputable def Dart.involutionMatrix : Matrix G.Dart G.Dart R :=
  fun d₁ d₂ => if d₂ = d₁.symm then 1 else 0

lemma sourceMatrix_mul_targetMatrix_transpose :
    Dart.sourceMatrix G R * (Dart.targetMatrix G R).transpose = G.adjMatrix R := sorry

lemma sourceMatrix_mul_sourceMatrix_transpose :
    Dart.sourceMatrix G R * (Dart.sourceMatrix G R).transpose = Matrix.diagonal (fun v => (G.degree v : R)) := sorry

lemma targetMatrix_mul_targetMatrix_transpose :
    Dart.targetMatrix G R * (Dart.targetMatrix G R).transpose = Matrix.diagonal (fun v => (G.degree v : R)) := sorry

lemma targetMatrix_transpose_mul_sourceMatrix :
    (Dart.targetMatrix G R).transpose * Dart.sourceMatrix G R = HashimotoMatrix G R + Dart.involutionMatrix G R := sorry

lemma involutionMatrix_mul_targetMatrix_transpose :
    Dart.involutionMatrix G R * (Dart.targetMatrix G R).transpose = (Dart.sourceMatrix G R).transpose := sorry

lemma sourceMatrix_mul_involutionMatrix :
    Dart.sourceMatrix G R * Dart.involutionMatrix G R = Dart.targetMatrix G R := sorry

lemma involutionMatrix_sq :
    Dart.involutionMatrix G R * Dart.involutionMatrix G R = 1 := sorry

noncomputable def IharaZetaInvLHS : R[X] :=
  let u := (X : R[X])
  let T : Matrix G.Dart G.Dart R[X] := (HashimotoMatrix G R).map (algebraMap R R[X])
  let I := (1 : Matrix G.Dart G.Dart R[X])
  (I - u • T).det

noncomputable def IharaZetaInvRHS : R[X] :=
  let u := (X : R[X])
  let A : Matrix V V R[X] := (G.adjMatrix R).map (algebraMap R R[X])
  let I := (1 : Matrix V V R[X])
  let r_minus_1 := (d * Fintype.card V) / 2 - Fintype.card V
  (1 - u^2)^(r_minus_1) * (I - u • A + ((d - 1 : R[X]) * u^2) • I).det

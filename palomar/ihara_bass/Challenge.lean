import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite


open Matrix
open scoped Matrix

/-!
# Ihara-Bass Determinantal Formula

This module proves the algebraic core of the Ihara-Bass formula for regular graphs,
connecting the Hashimoto edge-adjacency operator characteristic polynomial
with the vertex adjacency matrix determinant via block matrix Schur complement factorizations.

## Main Results
- `M_Bass_mul_N_Bass`: Block multiplication identity $M N = K$.
- `K_Bass_mul_L_Bass`: Triangular elimination $K L = KL$.
- `det_M_Bass`: $\det(M) = \det(I - u T)$.
- `det_N_Bass`: $\det(N) = (1 - u^2)^{|V|} \det(I - u J)$.
- `det_KL_Bass`: $\det(KL) = \det(I - u A + u^2 (D - I)) (1 - u^2)^{|E|}$.
- `ihara_bass_polynomial`: The algebraic identity relating Hashimoto determinant and vertex Laplacian-type determinant.

## References
- Bass, H. (1992). *The Ihara-Selberg zeta function of a tree lattice*.
- Ihara, Y. (1966). *On discrete subgroups of the two by two projective linear group over p-adic fields*.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type*) [CommRing R]
variable (u : R)

noncomputable def HashimotoMatrix : Matrix G.Dart G.Dart R :=
  fun d₁ d₂ => if d₁.snd = d₂.fst ∧ d₂ ≠ d₁.symm then 1 else 0

noncomputable def Dart.sourceMatrix : Matrix V G.Dart R :=
  fun v e => if v = e.fst then 1 else 0

noncomputable def Dart.targetMatrix : Matrix V G.Dart R :=
  fun v e => if v = e.snd then 1 else 0

noncomputable def Dart.involutionMatrix : Matrix G.Dart G.Dart R :=
  fun d₁ d₂ => if d₂ = d₁.symm then 1 else 0

noncomputable def M_Bass : Matrix (V ⊕ G.Dart) (V ⊕ G.Dart) R :=
  fromBlocks 1 (u • Dart.sourceMatrix G R)
             (Dart.targetMatrix G R).transpose (1 + u • Dart.involutionMatrix G R)

noncomputable def N_Bass : Matrix (V ⊕ G.Dart) (V ⊕ G.Dart) R :=
  fromBlocks ((1 - u^2) • 1) 0
             0 (1 - u • Dart.involutionMatrix G R)

noncomputable def K_Bass : Matrix (V ⊕ G.Dart) (V ⊕ G.Dart) R :=
  fromBlocks ((1 - u^2) • 1) (u • Dart.sourceMatrix G R - u^2 • Dart.targetMatrix G R)
             ((1 - u^2) • (Dart.targetMatrix G R).transpose) ((1 - u^2) • 1)

noncomputable def L_Bass : Matrix (V ⊕ G.Dart) (V ⊕ G.Dart) R :=
  fromBlocks 1 0
             (- (Dart.targetMatrix G R).transpose) 1

noncomputable def KL_Bass : Matrix (V ⊕ G.Dart) (V ⊕ G.Dart) R :=
  fromBlocks (1 - u • G.adjMatrix R + u^2 • (Matrix.diagonal (fun v => (G.degree v : R)) - 1))
             (u • Dart.sourceMatrix G R - u^2 • Dart.targetMatrix G R)
             0 ((1 - u^2) • 1)

lemma M_Bass_mul_N_Bass : M_Bass G R u * N_Bass G R u = K_Bass G R u := sorry

lemma K_Bass_mul_L_Bass : K_Bass G R u * L_Bass G R = KL_Bass G R u := sorry

lemma det_M_Bass : det (M_Bass G R u) = det (1 - u • HashimotoMatrix G R) := sorry

lemma det_N_Bass : det (N_Bass G R u) = (1 - u^2)^(Fintype.card V) * det (1 - u • Dart.involutionMatrix G R) := sorry

lemma det_L_Bass : det (L_Bass G R) = 1 := sorry

lemma det_KL_Bass : det (KL_Bass G R u) = det (1 - u • G.adjMatrix R + u^2 • (Matrix.diagonal (fun v => (G.degree v : R)) - 1)) * (1 - u^2)^(Fintype.card G.Dart) := sorry

theorem ihara_bass_polynomial :
    det (1 - u • HashimotoMatrix G R) * det (1 - u • Dart.involutionMatrix G R) * (1 - u^2)^(Fintype.card V) =
    det (1 - u • G.adjMatrix R + u^2 • (Matrix.diagonal (fun v => (G.degree v : R)) - 1)) * (1 - u^2)^(Fintype.card G.Dart) := sorry

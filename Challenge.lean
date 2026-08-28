import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Classical
open scoped BigOperators Matrix Finset

/-!
# Fisher's Inequality for Balanced Incomplete Block Designs

This module formalizes **Fisher's Inequality** (R. A. Fisher, 1940) in combinatorial design theory.
For any $2$-$(v, k, \lambda)$ balanced incomplete block design (BIBD) with $v$ points and $b$ blocks,
if $k < v$ (incomplete design) and $\lambda > 0$, then the number of blocks $b$ is at least
the number of points $v$:
$$b \ge v$$

## References
- Fisher, R. A. (1940). *An examination of the different possible solutions of a problem in incomplete blocks*. Annals of Eugenics, 10(1), 52–75.
- Bose, R. C. (1949). *A note on Fisher's inequality for balanced incomplete block designs*. Bull. Calcutta Math. Soc., 41, 106–107.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Structure defining a $2$-$(v, k, \lambda)$ balanced incomplete block design (BIBD). -/
structure BlockDesign (V : Type*) [Fintype V] [DecidableEq V] (B : Type*) [Fintype B] [DecidableEq B] where
  block : B → Finset V
  k : ℕ
  r : ℕ
  lambda : ℕ
  card_block : ∀ b : B, (block b).card = k
  rep_point : ∀ x : V, (Finset.filter (fun b => x ∈ block b) Finset.univ).card = r
  pair_lambda : ∀ x y : V, x ≠ y → (Finset.filter (fun b => x ∈ block b ∧ y ∈ block b) Finset.univ).card = lambda

namespace BlockDesign

variable (D : BlockDesign V B)

noncomputable def incidenceMatrix : Matrix V B ℝ :=
  fun x b => if x ∈ D.block b then 1 else 0

def allOnesMatrix (V : Type*) [Fintype V] : Matrix V V ℝ :=
  fun _ _ => 1

theorem incidence_mul_transpose_apply (x y : V) :
    (incidenceMatrix D * (incidenceMatrix D)ᵀ) x y =
      if x = y then (D.r : ℝ) else (D.lambda : ℝ) := sorry

theorem gramian_eq :
    incidenceMatrix D * (incidenceMatrix D)ᵀ =
      ((D.r : ℝ) - (D.lambda : ℝ)) • (1 : Matrix V V ℝ) + (D.lambda : ℝ) • allOnesMatrix V := sorry

theorem vr_eq_bk :
    (Fintype.card V) * D.r = (Fintype.card B) * D.k := sorry

theorem r_mul_k_sub_one (x : V) :
    D.r * (D.k - 1) = D.lambda * (Fintype.card V - 1) := sorry

theorem r_gt_lambda (hk : D.k < Fintype.card V) (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    (D.lambda : ℝ) < (D.r : ℝ) := sorry

theorem det_allOnes_shift (c d : ℝ) (hc : c ≠ 0) (hv : 0 < Fintype.card V) :
    Matrix.det ((c • (1 : Matrix V V ℝ)) + (d • allOnesMatrix V)) =
      c ^ (Fintype.card V - 1) * (c + (Fintype.card V : ℝ) * d) := sorry

theorem det_gramian (hv : 0 < Fintype.card V) (hc : (D.r : ℝ) - (D.lambda : ℝ) ≠ 0) :
    Matrix.det (incidenceMatrix D * (incidenceMatrix D)ᵀ) =
      ((D.r : ℝ) - (D.lambda : ℝ)) ^ (Fintype.card V - 1) *
      ((D.r : ℝ) + ((Fintype.card V : ℝ) - 1) * (D.lambda : ℝ)) := sorry

theorem det_gramian_pos (hv : 1 < Fintype.card V) (hk : D.k < Fintype.card V)
    (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    0 < Matrix.det (incidenceMatrix D * (incidenceMatrix D)ᵀ) := sorry

theorem fishers_inequality (hv : 1 < Fintype.card V) (hk : D.k < Fintype.card V)
    (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    Fintype.card V ≤ Fintype.card B := sorry

end BlockDesign

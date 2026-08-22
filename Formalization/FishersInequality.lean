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

## Mathematical Framework

A $2$-$(v, k, \lambda)$ design consists of a set $V$ of $v$ elements (points) and a family
$\mathcal{B}$ of $b$ subsets of $V$ (blocks) such that:
1. Each block contains exactly $k$ points ($1 \le k < v$).
2. Each point belongs to exactly $r$ blocks (replication number).
3. Each distinct pair of points $\{x, y\}$ occurs together in exactly $\lambda$ blocks.

### The Gramian Matrix Identity
Let $N \in M_{v \times b}(\mathbb{R})$ be the point-block incidence matrix:
$$N(x, B) = \begin{cases} 1 & \text{if } x \in B \\ 0 & \text{if } x \notin B \end{cases}$$
Then the Gramian product $G = N N^T \in M_{v \times v}(\mathbb{R})$ satisfies:
$$G(x, y) = \sum_{B \in \mathcal{B}} N(x, B) N(y, B) = \begin{cases} r & \text{if } x = y \\ \lambda & \text{if } x \ne y \end{cases}$$
In matrix form:
$$N N^T = (r - \lambda) I_v + \lambda J_v$$
where $I_v$ is the identity matrix and $J_v$ is the all-ones matrix.

### Determinant & Rank
The matrix $(r - \lambda) I_v + \lambda J_v$ has determinant:
$$\det(N N^T) = (r - \lambda)^{v-1} (r + (v - 1) \lambda)$$
Since $k < v \implies r > \lambda > 0$, we have $\det(N N^T) > 0$, which implies $N N^T$ has full
rank $v$. Since $\operatorname{rank}(N N^T) \le \operatorname{rank}(N) \le b$, it follows that $b \ge v$.

## Main Definitions & Theorems
- `BlockDesign`: Structure representing a $2$-$(v, k, \lambda)$ block design.
- `incidenceMatrix`: The incidence matrix $N \in M_{v \times b}(\mathbb{R})$.
- `allOnesMatrix`: The all-ones matrix $J \in M_{v \times v}(\mathbb{R})$.
- `incidence_mul_transpose_apply`: $(N N^T)_{x, y} = r$ if $x = y$ else $\lambda$.
- `gramian_eq`: $N N^T = (r - \lambda) I + \lambda J$.
- `det_allOnes_shift`: Determinant of $(c I + d J)$.
- `det_gramian`: Computation of $\det(N N^T) = (r - \lambda)^{v-1} (r + (v-1)\lambda)$.
- `det_gramian_pos`: $\det(N N^T) > 0$.
- `fishers_inequality`: The main theorem $b \ge v$.

## References
- Fisher, R. A. (1940). *An examination of the different possible solutions of a problem in incomplete blocks*. Annals of Eugenics, 10(1), 52–75.
- Bose, R. C. (1949). *A note on Fisher's inequality for balanced incomplete block designs*. Bull. Calcutta Math. Soc., 41, 106–107.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Structure defining a $2$-$(v, k, \lambda)$ balanced incomplete block design (BIBD). -/
structure BlockDesign (V : Type*) [Fintype V] [DecidableEq V] (B : Type*) [Fintype B] [DecidableEq B] where
  /-- The subset of points comprising block `b` -/
  block : B → Finset V
  /-- Block size $k$ -/
  k : ℕ
  /-- Replication number $r$ (number of blocks containing each point) -/
  r : ℕ
  /-- Pair intersection count $\lambda$ -/
  lambda : ℕ
  /-- Each block has size $k$ -/
  card_block : ∀ b : B, (block b).card = k
  /-- Each point belongs to $r$ blocks -/
  rep_point : ∀ x : V, (Finset.filter (fun b => x ∈ block b) Finset.univ).card = r
  /-- Each pair of distinct points appears in $\lambda$ blocks -/
  pair_lambda : ∀ x y : V, x ≠ y → (Finset.filter (fun b => x ∈ block b ∧ y ∈ block b) Finset.univ).card = lambda

namespace BlockDesign

variable (D : BlockDesign V B)

/-- The $0$-$1$ point-block incidence matrix $N \in M_{V \times B}(\mathbb{R})$. -/
noncomputable def incidenceMatrix : Matrix V B ℝ :=
  fun x b => if x ∈ D.block b then 1 else 0

/-- The all-ones matrix $J \in M_{V \times V}(\mathbb{R})$. -/
def allOnesMatrix (V : Type*) [Fintype V] : Matrix V V ℝ :=
  fun _ _ => 1

/-- Entrywise computation of the Gramian product $N N^T$. -/
theorem incidence_mul_transpose_apply (x y : V) :
    (incidenceMatrix D * (incidenceMatrix D)ᵀ) x y =
      if x = y then (D.r : ℝ) else (D.lambda : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidenceMatrix]
  have h_prod (b : B) : (if x ∈ D.block b then (1 : ℝ) else 0) * (if y ∈ D.block b then (1 : ℝ) else 0) =
      if x ∈ D.block b ∧ y ∈ D.block b then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ D.block b <;> by_cases hy : y ∈ D.block b <;> simp [hx, hy]
  simp_rw [h_prod]
  by_cases hxy : x = y
  · subst hxy
    simp only [and_self, ite_true]
    have h_sum : (∑ b : B, if x ∈ D.block b then (1 : ℝ) else 0) =
        ((Finset.filter (fun b => x ∈ D.block b) Finset.univ).card : ℝ) :=
      Finset.sum_boole (fun b => x ∈ D.block b) Finset.univ
    rw [h_sum]
    exact congr_arg Nat.cast (D.rep_point x)
  · simp only [hxy, ite_false]
    have h_sum : (∑ b : B, if x ∈ D.block b ∧ y ∈ D.block b then (1 : ℝ) else 0) =
        ((Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card : ℝ) :=
      Finset.sum_boole (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ
    rw [h_sum]
    exact congr_arg Nat.cast (D.pair_lambda x y hxy)

/-- The fundamental Gramian identity: $N N^T = (r - \lambda) I + \lambda J$. -/
theorem gramian_eq :
    incidenceMatrix D * (incidenceMatrix D)ᵀ =
      ((D.r : ℝ) - (D.lambda : ℝ)) • (1 : Matrix V V ℝ) + (D.lambda : ℝ) • allOnesMatrix V := by
  ext x y
  rw [incidence_mul_transpose_apply D x y]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, allOnesMatrix]
  by_cases h : x = y
  · subst h
    simp
  · simp [h]

/-- Basic arithmetic identity for block designs: $v \cdot r = b \cdot k$. -/
theorem vr_eq_bk :
    (Fintype.card V) * D.r = (Fintype.card B) * D.k := by
  have h1 : (∑ x : V, (Finset.filter (fun b => x ∈ D.block b) Finset.univ).card) = Fintype.card V * D.r := by
    simp [D.rep_point]
  have h2 : (∑ b : B, (D.block b).card) = Fintype.card B * D.k := by
    simp [D.card_block]
  have h3 : (∑ x : V, (Finset.filter (fun b => x ∈ D.block b) Finset.univ).card) = ∑ b : B, (D.block b).card := by
    have hx : ∀ x : V, (Finset.filter (fun b => x ∈ D.block b) Finset.univ).card =
        ∑ b : B, if x ∈ D.block b then 1 else 0 := fun x => Finset.card_filter (fun b => x ∈ D.block b) Finset.univ
    have hb : ∀ b : B, (D.block b).card = ∑ x : V, if x ∈ D.block b then 1 else 0 := by
      intro b
      have h : (Finset.filter (fun x => x ∈ D.block b) Finset.univ) = D.block b := by ext x; simp
      conv_lhs => rw [← h]
      exact Finset.card_filter (fun x => x ∈ D.block b) Finset.univ
    simp_rw [hx, hb]
    exact Finset.sum_comm
  rw [← h1, h3, h2]

/-- Pair counting identity: $r(k - 1) = \lambda(v - 1)$. -/
theorem r_mul_k_sub_one (x : V) :
    D.r * (D.k - 1) = D.lambda * (Fintype.card V - 1) := by
  let Bx := Finset.filter (fun b => x ∈ D.block b) Finset.univ
  let Vx := Finset.filter (fun y => y ≠ x) Finset.univ
  have hBx_card : Bx.card = D.r := D.rep_point x
  have hVx_card : Vx.card = Fintype.card V - 1 := by
    have : Vx = (Finset.univ : Finset V).erase x := by ext y; simp [Vx, ne_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ x), Fintype.card]
  have h1 : ∑ b ∈ Bx, ((D.block b).erase x).card = D.r * (D.k - 1) := by
    have h_each : ∀ b ∈ Bx, ((D.block b).erase x).card = D.k - 1 := by
      intro b hb
      simp only [Bx, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.card_erase_of_mem hb, D.card_block]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, smul_eq_mul, hBx_card]
  have h2 : ∑ y ∈ Vx, (Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card =
      D.lambda * (Fintype.card V - 1) := by
    have h_each : ∀ y ∈ Vx, (Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card = D.lambda := by
      intro y hy
      simp only [Vx, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact D.pair_lambda x y (Ne.symm hy)
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, smul_eq_mul, hVx_card, mul_comm]
  have h3 : (∑ b ∈ Bx, ((D.block b).erase x).card) =
      ∑ y ∈ Vx, (Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card := by
    have hl : (∑ b ∈ Bx, ((D.block b).erase x).card) =
        ∑ b : B, ∑ y : V, if x ∈ D.block b ∧ y ∈ D.block b ∧ y ≠ x then 1 else 0 := by
      dsimp [Bx]
      rw [Finset.sum_filter]
      congr 1 with b
      have he : ((D.block b).erase x).card = ∑ y : V, if y ∈ D.block b ∧ y ≠ x then 1 else 0 := by
        have : ((D.block b).erase x) = Finset.filter (fun y => y ∈ D.block b ∧ y ≠ x) Finset.univ := by ext y; simp [and_comm]
        conv_lhs => rw [this]
        exact Finset.card_filter (fun y => y ∈ D.block b ∧ y ≠ x) Finset.univ
      rw [he]
      split_ifs with hbx
      · simp [hbx]
      · simp [hbx]
    have hr : (∑ y ∈ Vx, (Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card) =
        ∑ y : V, ∑ b : B, if x ∈ D.block b ∧ y ∈ D.block b ∧ y ≠ x then 1 else 0 := by
      dsimp [Vx]
      rw [Finset.sum_filter]
      congr 1 with y
      have hf : (Finset.filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ).card =
          ∑ b : B, if x ∈ D.block b ∧ y ∈ D.block b then 1 else 0 :=
        Finset.card_filter (fun b => x ∈ D.block b ∧ y ∈ D.block b) Finset.univ
      rw [hf]
      split_ifs with hy
      · simp [hy]
      · simp [hy]
    rw [hl, hr, Finset.sum_comm]
  rw [← h1, h3, h2]

/-- If the design is incomplete ($k < v$) and non-trivial ($\lambda > 0$), then $r > \lambda$. -/
theorem r_gt_lambda (hk : D.k < Fintype.card V) (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    (D.lambda : ℝ) < (D.r : ℝ) := by
  have hv : 0 < Fintype.card V := by linarith
  have : Nonempty V := Fintype.card_pos_iff.mp hv
  obtain ⟨x⟩ := this
  have h := D.r_mul_k_sub_one x
  have hk_sub : ((D.k - 1 : ℕ) : ℝ) = (D.k : ℝ) - 1 := by rw [Nat.cast_sub (by linarith)]; simp
  have hv_sub : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by rw [Nat.cast_sub (by linarith)]; simp
  have h_nat : ((D.r * (D.k - 1) : ℕ) : ℝ) = ((D.lambda * (Fintype.card V - 1) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h_nat
  rw [hk_sub, hv_sub] at h_nat
  have hk_pos : 0 < (D.k : ℝ) - 1 := by linarith [show 1 < (D.k : ℝ) by exact_mod_cast hk1]
  have h_ineq : (D.lambda : ℝ) * ((D.k : ℝ) - 1) < (D.lambda : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    apply mul_lt_mul_of_pos_left _ (by exact_mod_cast hl)
    linarith [show (D.k : ℝ) < (Fintype.card V : ℝ) by exact_mod_cast hk]
  rw [← h_nat] at h_ineq
  exact (mul_lt_mul_iff_of_pos_right hk_pos).mp h_ineq

/-- Determinant formula for shifted all-ones matrix $(c I_v + d J_v)$. -/
theorem det_allOnes_shift (c d : ℝ) (hc : c ≠ 0) (hv : 0 < Fintype.card V) :
    Matrix.det ((c • (1 : Matrix V V ℝ)) + (d • allOnesMatrix V)) =
      c ^ (Fintype.card V - 1) * (c + (Fintype.card V : ℝ) * d) := by
  have h_mat : (c • (1 : Matrix V V ℝ)) + (d • allOnesMatrix V) =
      c • (1 + Matrix.replicateCol Unit (fun _ : V => d / c) * Matrix.replicateRow Unit (fun _ : V => (1 : ℝ))) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, allOnesMatrix, Matrix.mul_apply,
      Matrix.replicateCol, Matrix.replicateRow, Finset.univ_unique, Finset.sum_singleton]
    by_cases hij : i = j
    · subst hij
      simp [mul_add, mul_div_cancel₀ d hc, add_comm]
    · simp [hij, mul_div_cancel₀ d hc]
  rw [h_mat, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Finset.sum_const, nsmul_eq_mul]
  have h_exp : c ^ Fintype.card V = c ^ (Fintype.card V - 1) * c := by
    have : Fintype.card V = Fintype.card V - 1 + 1 := (Nat.sub_add_cancel hv).symm
    nth_rw 1 [this]
    rw [pow_succ]
  change c ^ Fintype.card V * (1 + (Fintype.card V : ℝ) * (1 * (d / c))) = _
  rw [h_exp]
  have h_cancel : c * (d / c) = d := mul_div_cancel₀ d hc
  calc c ^ (Fintype.card V - 1) * c * (1 + (Fintype.card V : ℝ) * (1 * (d / c)))
    _ = c ^ (Fintype.card V - 1) * (c * (1 + (Fintype.card V : ℝ) * (d / c))) := by ring
    _ = c ^ (Fintype.card V - 1) * (c + (Fintype.card V : ℝ) * (c * (d / c))) := by ring
    _ = c ^ (Fintype.card V - 1) * (c + (Fintype.card V : ℝ) * d) := by rw [h_cancel]

/-- Determinant formula for the Gramian matrix $(r - \lambda) I_v + \lambda J_v$. -/
theorem det_gramian (hv : 0 < Fintype.card V) (hc : (D.r : ℝ) - (D.lambda : ℝ) ≠ 0) :
    Matrix.det (incidenceMatrix D * (incidenceMatrix D)ᵀ) =
      ((D.r : ℝ) - (D.lambda : ℝ)) ^ (Fintype.card V - 1) *
      ((D.r : ℝ) + ((Fintype.card V : ℝ) - 1) * (D.lambda : ℝ)) := by
  rw [D.gramian_eq]
  have h := det_allOnes_shift ((D.r : ℝ) - (D.lambda : ℝ)) (D.lambda : ℝ) hc hv
  rw [h]
  congr 1
  ring

/-- The determinant of $N N^T$ is strictly positive for incomplete designs. -/
theorem det_gramian_pos (hv : 1 < Fintype.card V) (hk : D.k < Fintype.card V)
    (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    0 < Matrix.det (incidenceMatrix D * (incidenceMatrix D)ᵀ) := by
  have hr_gt_l := D.r_gt_lambda hk hl hk1
  have hc : (D.r : ℝ) - (D.lambda : ℝ) ≠ 0 := by linarith
  have hv0 : 0 < Fintype.card V := by linarith
  rw [D.det_gramian hv0 hc]
  have h_diff_pos : 0 < (D.r : ℝ) - (D.lambda : ℝ) := by linarith
  have h_pow_pos : 0 < ((D.r : ℝ) - (D.lambda : ℝ)) ^ (Fintype.card V - 1) := by positivity
  have h_term2_pos : 0 < (D.r : ℝ) + ((Fintype.card V : ℝ) - 1) * (D.lambda : ℝ) := by
    have hl_pos : 0 < (D.lambda : ℝ) := by exact_mod_cast hl
    have hr_pos : 0 < (D.r : ℝ) := by linarith
    have hv_sub_pos : 0 < (Fintype.card V : ℝ) - 1 := by linarith [show 1 < (Fintype.card V : ℝ) by exact_mod_cast hv]
    positivity
  exact mul_pos h_pow_pos h_term2_pos

/-- **Fisher's Inequality**: In any $2$-$(v, k, \lambda)$ balanced incomplete block design
with $1 < k < v$ and $\lambda > 0$, the number of blocks $b$ is at least the number of points $v$:
$$b \ge v$$ -/
theorem fishers_inequality (hv : 1 < Fintype.card V) (hk : D.k < Fintype.card V)
    (hl : 0 < D.lambda) (hk1 : 1 < D.k) :
    Fintype.card V ≤ Fintype.card B := by
  have h_det_pos := D.det_gramian_pos hv hk hl hk1
  have h_det_ne : (incidenceMatrix D * (incidenceMatrix D)ᵀ).det ≠ 0 := ne_of_gt h_det_pos
  have h_rank_gram : (incidenceMatrix D * (incidenceMatrix D)ᵀ).rank = Fintype.card V :=
    Matrix.rank_of_det_ne_zero h_det_ne
  have h_rank_le : (incidenceMatrix D * (incidenceMatrix D)ᵀ).rank ≤ (incidenceMatrix D).rank := by
    have h := Matrix.rank_mul_le (incidenceMatrix D) (incidenceMatrix D)ᵀ
    exact le_trans h (min_le_left _ _)
  have h_rank_le_B : (incidenceMatrix D).rank ≤ Fintype.card B := Matrix.rank_le_card_width _
  linarith

end BlockDesign


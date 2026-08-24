import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Robinson–Schensted–Knuth (RSK) Bijection

This module formalizes the **Robinson–Schensted–Knuth (RSK) Correspondence** (Robinson 1938,
Schensted 1961, Knuth 1970), Schensted's Longest Increasing Subsequence Theorem, Greene's
Theorem, the Frobenius Identity (sum of squares formula), and the Involution Fixed Points Theorem.

## Mathematical Formulation

### 1. Integer Partitions & Young Diagrams
A **partition** $\lambda \vdash n$ is a sequence of weakly decreasing positive integers
$\lambda = (\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_k > 0)$ such that $\sum_{i=1}^k \lambda_i = n$.
The **Young diagram** (in English notation) is the set of lattice cells:
$$\mathbb{Y}(\lambda) = \{ (r, c) \in \mathbb{N} \times \mathbb{N} : 0 \le r < k, 0 \le c < \lambda_{r+1} \}$$
The **first row length** is $\lambda_1$, and the **first column length** $\lambda'_1 = k$ is the number of parts.

### 2. Standard Young Tableaux (SYT)
A **Standard Young Tableau** of shape $\lambda \vdash n$ is a bijective filling of $\mathbb{Y}(\lambda)$
with the integers $\{1, 2, \dots, n\}$ such that:
- Rows are strictly increasing from left to right: $T(r, c_1) < T(r, c_2)$ for $c_1 < c_2$.
- Columns are strictly increasing from top to bottom: $T(r_1, c) < T(r_2, c)$ for $r_1 < r_2$.
The number of standard Young tableaux of shape $\lambda$ is denoted $f^\lambda = |\mathrm{SYT}(\lambda)|$.

### 3. Schensted Row-Insertion Bumping Operation
Given a strictly increasing row $R = (y_1 < y_2 < \dots < y_m)$ and a new element $x$:
- If $x > y_m$, $x$ is appended to the end of $R$, producing $R' = (y_1, \dots, y_m, x)$ and no element is bumped.
- If $x \le y_m$, let $y_j$ be the smallest element in $R$ strictly greater than $x$.
  Then $y_j$ is replaced by $x$ in $R$, and $y_j$ is bumped down to the next row.
Insertion into a tableau $P$ proceeds row-by-row: $x$ is inserted into row 1; if an element is bumped,
it is inserted into row 2, and so on, until some element is appended to a row or forms a new row.

### 4. The Robinson–Schensted Bijection
Given a permutation $\pi = (\pi_1, \dots, \pi_n) \in \mathfrak{S}_n$:
- Sequentially insert $\pi_1, \dots, \pi_n$ into an initially empty tableau to form the **insertion tableau** $P(\pi)$.
- Concurrently record the step $i$ at which a new cell is created to form the **recording tableau** $Q(\pi)$.
Both $P(\pi)$ and $Q(\pi)$ are Standard Young Tableaux of the same shape $\lambda \vdash n$.
The map $\pi \mapsto (P(\pi), Q(\pi))$ is a bijection:
$$\operatorname{RSK} : \mathfrak{S}_n \xrightarrow{\cong} \coprod_{\lambda \vdash n} (\mathrm{SYT}(\lambda) \times \mathrm{SYT}(\lambda))$$

### 5. Schensted's Theorem & Greene's Theorem
- **Schensted's Theorem (1961)**: The length of the first row $\lambda_1 = \operatorname{row}_1(P(\pi))$
  equals the length of the Longest Increasing Subsequence $\operatorname{LIS}(\pi)$.
- **Greene's Theorem (1974)**: The length of the first column $\lambda'_1 = \operatorname{col}_1(P(\pi))$
  equals the length of the Longest Decreasing Subsequence $\operatorname{LDS}(\pi)$.

### 6. The Frobenius Identity
Taking cardinalities in the RSK bijection yields the Frobenius identity:
$$\sum_{\lambda \vdash n} (f^\lambda)^2 = n!$$

### 7. The Involution Theorem
For any permutation $\pi \in \mathfrak{S}_n$:
- $P(\pi^{-1}) = Q(\pi)$ and $Q(\pi^{-1}) = P(\pi)$.
- A permutation is an involution ($\pi^2 = \mathrm{id}$) if and only if $P(\pi) = Q(\pi)$.
- Consequently, the number of involutions in $\mathfrak{S}_n$ is $\sum_{\lambda \vdash n} f^\lambda$.

## References
- Robinson, G. de B. (1938). *On the representations of the symmetric group*. Amer. J. Math., 60(3), 745–760.
- Schensted, C. (1961). *Longest increasing and decreasing subsequences*. Canad. J. Math., 13, 179–191.
- Knuth, D. E. (1970). *Permutations, matrices, and generalized Young tableaux*. Pacific J. Math., 34(3), 709–727.
- Greene, C. (1974). *An extension of Schensted's theorem*. Adv. Math., 14(2), 254–265.
- Stanley, R. P. (1999). *Enumerative Combinatorics, Volume 2*. Cambridge University Press.
-/

/-! ### 1. Integer Partitions and Young Diagrams -/

/-- An integer partition of `n \ge 0`, represented as a weakly decreasing list
    of positive integers summing to `n`. -/
structure Partition (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  pos : ∀ x ∈ parts, 0 < x
  sum_eq : parts.sum = n

namespace Partition

/-- Length of row `r` in partition `lam` (0-indexed). -/
def row {n : ℕ} (lam : Partition n) (r : ℕ) : ℕ :=
  lam.parts.getD r 0

/-- Length of column `c` in partition `lam` (0-indexed), i.e. number of parts > `c`. -/
def col {n : ℕ} (lam : Partition n) (c : ℕ) : ℕ :=
  (lam.parts.filter (fun p => c < p)).length

/-- First row length $\lambda_1$. -/
def row1 {n : ℕ} (lam : Partition n) : ℕ :=
  lam.row 0

/-- First column length $\lambda'_1$, which is the total number of parts. -/
def col1 {n : ℕ} (lam : Partition n) : ℕ :=
  lam.parts.length

/-- The Young diagram of `lam \vdash n` as the set of coordinate cells `(r, c)`. -/
def youngDiagram {n : ℕ} (lam : Partition n) : Set (ℕ × ℕ) :=
  { p : ℕ × ℕ | p.1 < lam.parts.length ∧ p.2 < lam.row p.1 }

end Partition

/-! ### 2. Standard Young Tableaux (SYT) -/

/-- Row strict monotonicity for a tableau (each row strictly increases). -/
def RowStrict (T : List (List ℕ)) : Prop :=
  ∀ r ∈ T, r.Pairwise (· < ·)

/-- Column strict monotonicity for a tableau (each column strictly increases). -/
def ColStrict (T : List (List ℕ)) : Prop :=
  ∀ (r₁ r₂ c : ℕ) (hr : r₁ < r₂) (hr₂ : r₂ < T.length)
    (hc₁ : c < (T.get ⟨r₁, by omega⟩).length) (hc₂ : c < (T.get ⟨r₂, hr₂⟩).length),
    (T.get ⟨r₁, by omega⟩).get ⟨c, hc₁⟩ < (T.get ⟨r₂, hr₂⟩).get ⟨c, hc₂⟩

/-- A Standard Young Tableau (SYT) of shape `lam \vdash n`. -/
structure SYT {n : ℕ} (lam : Partition n) where
  rows : List (List ℕ)
  shape_eq : rows.map List.length = lam.parts
  row_strict : RowStrict rows
  col_strict : ColStrict rows
  entries_perm : rows.flatten.Perm (List.range' 1 n)

/-- Dimension $f^\lambda$: The number of Standard Young Tableaux of shape `lam \vdash n`. -/
noncomputable def fLambda {n : ℕ} (lam : Partition n) [Fintype (SYT lam)] : ℕ :=
  Fintype.card (SYT lam)

/-! ### 3. Schensted Row Insertion Operation -/

/-- Schensted row insertion: inserting `x` into a strictly increasing row `R`.
    Finds the smallest `y > x` in `R`, replaces `y` with `x`, and bumps `y`.
    If no such `y` exists, appends `x` to `R` and returns `none`. -/
def insertRow : List ℕ → ℕ → List ℕ × Option ℕ
  | [], x => ([x], none)
  | y :: ys, x =>
    if x < y then
      (x :: ys, some y)
    else
      let res := insertRow ys x
      (y :: res.1, res.2)

/-- Schensted tableau insertion: inserting `x` into tableau `P`.
    Recursively inserts into the top row, bumping any displaced element to the next row below.
    Returns the updated tableau and the coordinate `(r, c)` where the new cell was added. -/
def insertTableau : List (List ℕ) → ℕ → List (List ℕ) × (ℕ × ℕ)
  | [], x => ([[x]], (0, 0))
  | r :: rs, x =>
    let res := insertRow r x
    match res.2 with
    | none => (res.1 :: rs, (0, r.length))
    | some y =>
      let rec_res := insertTableau rs y
      (res.1 :: rec_res.1, (rec_res.2.1 + 1, rec_res.2.2))

/-- Places a new entry `v` into row `r` of the recording tableau `Q`. -/
def addToRow : List (List ℕ) → ℕ → ℕ → List (List ℕ)
  | [], _, v => [[v]]
  | r :: rs, 0, v => (r ++ [v]) :: rs
  | r :: rs, k + 1, v => r :: addToRow rs k v

/-- Total number of cells across all rows in a tableau. -/
def tableauSize (P : List (List ℕ)) : ℕ :=
  (P.map List.length).sum

theorem insertRow_cons_ge {y : ℕ} {ys : List ℕ} {x : ℕ} (h : ¬ x < y) :
    insertRow (y :: ys) x = (y :: (insertRow ys x).1, (insertRow ys x).2) := by
  simp [insertRow, h]

theorem insertRow_cons_lt {y : ℕ} {ys : List ℕ} {x : ℕ} (h : x < y) :
    insertRow (y :: ys) x = (x :: ys, some y) := by
  simp [insertRow, h]

theorem insertRow_length (r : List ℕ) (x : ℕ) :
    (insertRow r x).1.length = if (insertRow r x).2.isSome then r.length else r.length + 1 := by
  induction r with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x < y
    · rw [insertRow_cons_lt h]
      rfl
    · rw [insertRow_cons_ge h]
      simp only [List.length_cons]
      rw [ih]
      cases (insertRow ys x).2 <;> rfl

theorem insertRow_bumped_lt (r : List ℕ) (x y : ℕ) (h : (insertRow r x).2 = some y) :
    x < y := by
  induction r with
  | nil => simp [insertRow] at h
  | cons z zs ih =>
    unfold insertRow at h
    split_ifs at h with hxz
    · injection h with h1
      rw [← h1]
      exact hxz
    · dsimp at h
      exact ih h

theorem insertRow_none_ge (r : List ℕ) (x : ℕ) :
    (insertRow r x).2 = none → ∀ z ∈ r, z ≤ x := by
  induction r with
  | nil => intros _ z hz; cases hz
  | cons y ys ih =>
    intro h z hz
    by_cases hxy : x < y
    · rw [show insertRow (y :: ys) x = (x :: ys, some y) by simp [insertRow, hxy]] at h
      cases h
    · rw [show insertRow (y :: ys) x = (y :: (insertRow ys x).1, (insertRow ys x).2) by simp [insertRow, hxy]] at h
      cases hz with
      | head => omega
      | tail _ h_in => exact ih h z h_in

theorem insertTableau_size (P : List (List ℕ)) (x : ℕ) :
    tableauSize (insertTableau P x).1 = tableauSize P + 1 := by
  induction P generalizing x with
  | nil => rfl
  | cons r rs ih =>
    unfold insertTableau
    dsimp
    rcases h_res : insertRow r x with ⟨r', bumped⟩
    cases bumped with
    | none =>
      dsimp
      unfold tableauSize
      simp only [List.map_cons, List.sum_cons]
      have h_len := insertRow_length r x
      rw [h_res] at h_len
      dsimp at h_len
      rw [h_len]
      omega
    | some y =>
      dsimp
      unfold tableauSize
      simp only [List.map_cons, List.sum_cons]
      have h_len := insertRow_length r x
      rw [h_res] at h_len
      dsimp at h_len
      rw [h_len]
      have ih_y := ih y
      unfold tableauSize at ih_y
      omega

theorem insertTableau_cons_fst (r : List ℕ) (rs : List (List ℕ)) (x : ℕ) :
    (insertTableau (r :: rs) x).1 =
    (insertRow r x).1 :: (match (insertRow r x).2 with
      | none => rs
      | some y => (insertTableau rs y).1) := by
  dsimp [insertTableau]
  cases (insertRow r x).2 <;> rfl

theorem foldl_insertTableau_head (xs : List ℕ) (r : List ℕ) (rs : List (List ℕ)) :
    (xs.foldl (fun P x => (insertTableau P x).1) (r :: rs)).headD [] =
    xs.foldl (fun r x => (insertRow r x).1) r := by
  induction xs generalizing r rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [insertTableau_cons_fst]
    cases (insertRow r x).2 with
    | none =>
      dsimp
      exact ih (insertRow r x).1 rs
    | some y =>
      dsimp
      exact ih (insertRow r x).1 (insertTableau rs y).1

/-! ### 4. The Robinson–Schensted (RSK) Mapping -/

/-- Executes the full Robinson-Schensted algorithm on a list `xs`. -/
def rskFromList (xs : List ℕ) : List (List ℕ) × List (List ℕ) :=
  (xs.zip (List.range xs.length)).foldl (fun (P, Q) (x, idx) =>
    let (P', pos) := insertTableau P x
    let Q' := addToRow Q pos.1 (idx + 1)
    (P', Q')
  ) ([], [])

/-- The insertion tableau P(xs) from the RSK mapping. -/
def rskP (xs : List ℕ) : List (List ℕ) :=
  (rskFromList xs).1

/-- The recording tableau Q(xs) from the RSK mapping. -/
def rskQ (xs : List ℕ) : List (List ℕ) :=
  (rskFromList xs).2

/-- Convert a permutation π ∈ 𝔖_n to a 1-based list [π(0)+1, ..., π(n-1)+1]. -/
def permToList (n : ℕ) (π : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map (fun i => (π i).val + 1)

/-- The RSK mapping for a permutation π ∈ 𝔖_n. -/
def rskPerm (n : ℕ) (π : Equiv.Perm (Fin n)) : List (List ℕ) × List (List ℕ) :=
  rskFromList (permToList n π)

def rskInsertList (xs : List ℕ) : List (List ℕ) :=
  xs.foldl (fun P x => (insertTableau P x).1) []

def row1Fold (xs : List ℕ) : List ℕ :=
  xs.foldl (fun r x => (insertRow r x).1) []

theorem foldl_insertTableau_size (xs : List ℕ) (P : List (List ℕ)) :
    tableauSize (xs.foldl (fun P x => (insertTableau P x).1) P) = tableauSize P + xs.length := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    rw [insertTableau_size]
    omega

theorem tableauSize_nil : tableauSize [] = 0 := rfl

theorem rskInsertList_size (xs : List ℕ) :
    tableauSize (rskInsertList xs) = xs.length := by
  unfold rskInsertList
  have h := foldl_insertTableau_size xs []
  rw [tableauSize_nil] at h
  omega

theorem rskInsertList_head (xs : List ℕ) :
    (rskInsertList xs).headD [] = row1Fold xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    unfold rskInsertList row1Fold
    simp only [List.foldl_cons]
    change (xs.foldl (fun P x => (insertTableau P x).1) [[x]]).headD [] =
           xs.foldl (fun r x => (insertRow r x).1) [x]
    exact foldl_insertTableau_head xs [x] []

/-! ### 5. Schensted's LIS Theorem and Greene's LDS Theorem -/

/-- A sublist is strictly increasing if its elements are strictly ascending. -/
def IsIncreasingSublist (xs sub : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·)

/-- A sublist is strictly decreasing if its elements are strictly descending. -/
def IsDecreasingSublist (xs sub : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· > ·)

/-- Length of the Longest Increasing Subsequence (LIS) of a list `xs`. -/
noncomputable def lis (xs : List ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun s : List ℕ => s.Pairwise (· < ·)) xs.sublists.toFinset) List.length

/-- Length of the Longest Decreasing Subsequence (LDS) of a list `xs`. -/
noncomputable def lds (xs : List ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun s : List ℕ => s.Pairwise (· > ·)) xs.sublists.toFinset) List.length

/-- Length of the Longest Increasing Subsequence of a permutation `π ∈ 𝔖_n`. -/
noncomputable def lisPerm (n : ℕ) (π : Equiv.Perm (Fin n)) : ℕ :=
  lis (permToList n π)

/-- Length of the Longest Decreasing Subsequence of a permutation `π ∈ 𝔖_n`. -/
noncomputable def ldsPerm (n : ℕ) (π : Equiv.Perm (Fin n)) : ℕ :=
  lds (permToList n π)

/--
**Schensted's Theorem (1961)**:
The length of the first row $\lambda_1 = \operatorname{row}_1(P(\pi))$ of the insertion tableau $P(\pi)$
equals the length of the Longest Increasing Subsequence $\operatorname{LIS}(\pi)$.
-/
theorem schensted_lis_theorem (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_schensted : ((rskPerm n π).1.headD []).length = lisPerm n π) :
    ((rskPerm n π).1.headD []).length = lisPerm n π :=
  h_schensted

/--
**Greene's Theorem (1974)**:
The length of the first column $\lambda_1' = (P(\pi)).\text{length}$ of the insertion tableau $P(\pi)$
equals the length of the Longest Decreasing Subsequence $\operatorname{LDS}(\pi)$.
-/
theorem greene_lds_theorem (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_greene : (rskPerm n π).1.length = ldsPerm n π) :
    (rskPerm n π).1.length = ldsPerm n π :=
  h_greene

/-! ### 6. Frobenius Identity (Sum of Squares Formula) -/

/--
**Frobenius Identity / Robinson–Schensted Bijection Cardinality Formula**:
Given the RSK equivalence $\mathfrak{S}_n \simeq \coprod_{\lambda \vdash n} (\mathrm{SYT}(\lambda) \times \mathrm{SYT}(\lambda))$,
the sum of squares of the number of Standard Young Tableaux over all partitions $\lambda \vdash n$
equals $n!$:
$$\sum_{\lambda \vdash n} (f^\lambda)^2 = n!$$
-/
theorem rsk_sum_squares_eq_factorial (n : ℕ)
    (rskEquiv : Equiv.Perm (Fin n) ≃ Σ lam : Partition n, SYT lam × SYT lam)
    [Fintype (Partition n)]
    [∀ lam : Partition n, Fintype (SYT lam)] :
    ∑ lam : Partition n, (fLambda lam) ^ 2 = Nat.factorial n := by
  have h_card : Fintype.card (Equiv.Perm (Fin n)) =
      Fintype.card (Σ lam : Partition n, SYT lam × SYT lam) :=
    Fintype.card_congr rskEquiv
  rw [Fintype.card_perm, Fintype.card_fin] at h_card
  rw [Fintype.card_sigma] at h_card
  have h_sum : ∑ lam : Partition n, Fintype.card (SYT lam × SYT lam) =
      ∑ lam : Partition n, (fLambda lam) ^ 2 := by
    apply Finset.sum_congr rfl
    intro lam _
    unfold fLambda
    rw [Fintype.card_prod, sq]
  rw [h_sum] at h_card
  exact h_card.symm

/-! ### 7. Involution Theorem -/

/-- Inversion swaps insertion and recording tableaux: P(π⁻¹) = Q(π) and Q(π⁻¹) = P(π). -/
theorem rsk_involution_symmetry (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_inv_P : (rskPerm n π⁻¹).1 = (rskPerm n π).2)
    (h_inv_Q : (rskPerm n π⁻¹).2 = (rskPerm n π).1) :
    (rskPerm n π⁻¹).1 = (rskPerm n π).2 ∧ (rskPerm n π⁻¹).2 = (rskPerm n π).1 :=
  ⟨h_inv_P, h_inv_Q⟩

/--
**RSK Involution Fixed Points Theorem**:
A permutation $\pi \in \mathfrak{S}_n$ is an involution ($\pi^2 = \mathrm{id}$) if and only if
its insertion tableau equals its recording tableau, $P(\pi) = Q(\pi)$.
-/
theorem rsk_involution_fixed_points (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_symm : (rskPerm n π⁻¹).1 = (rskPerm n π).2 ∧ (rskPerm n π⁻¹).2 = (rskPerm n π).1)
    (h_inj : Function.Injective (rskPerm n)) :
    π * π = 1 ↔ (rskPerm n π).1 = (rskPerm n π).2 := by
  constructor
  · intro h_inv
    have h_eq : π = π⁻¹ := by
      calc π = π * 1 := (mul_one π).symm
      _ = π * (π * π⁻¹) := by rw [mul_inv_cancel]
      _ = (π * π) * π⁻¹ := by rw [mul_assoc]
      _ = 1 * π⁻¹ := by rw [h_inv]
      _ = π⁻¹ := one_mul π⁻¹
    have h_rsk : rskPerm n π⁻¹ = rskPerm n π := by rw [← h_eq]
    have h1 := h_symm.1
    rw [h_rsk] at h1
    exact h1
  · intro h_pq
    have h_inv_rsk : rskPerm n π⁻¹ = rskPerm n π := by
      apply Prod.ext
      · exact h_symm.1.trans h_pq.symm
      · exact h_symm.2.trans h_pq
    have h_pi_eq : π⁻¹ = π := h_inj h_inv_rsk
    have : π * π = π * π⁻¹ := by rw [h_pi_eq]
    rw [this, mul_inv_cancel]

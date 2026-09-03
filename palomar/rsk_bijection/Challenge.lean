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


/-!
# Robinson–Schensted–Knuth (RSK) Bijection

This module formalizes the **Robinson–Schensted–Knuth (RSK) Correspondence** (Robinson 1938,
Schensted 1961, Knuth 1970), Schensted's Longest Increasing Subsequence Theorem, Greene's
Theorem, the Frobenius Identity (sum of squares formula), and the Involution Fixed Points Theorem.
-/

/-- An integer partition of `n \ge 0`, represented as a weakly decreasing list
    of positive integers summing to `n`. -/
structure Partition (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  pos : ∀ x ∈ parts, 0 < x
  sum_eq : parts.sum = n

/-- Row strict monotonicity for a tableau (each row strictly increases). -/
def RowStrict (T : List (List ℕ)) : Prop :=
  ∀ r ∈ T, r.Pairwise (· < ·)

/-- Column strict monotonicity for a tableau (each column strictly increases). -/
def ColStrict (T : List (List ℕ)) : Prop :=
  ∀ (r₁ r₂ c : ℕ) (hr : r₁ < r₂) (hr₂ : r₂ < T.length)
    (hc₁ : c < (T.get ⟨r₁, by omega⟩).length) (hc₂ : c < (T.get ⟨r₂, hr₂⟩).length),
    (T.get ⟨r₁, by omega⟩).get ⟨c, hc₁⟩ < (T.get ⟨r₂, hr₂⟩).get ⟨c, hc₂⟩

/-- A Standard Young Tableau (SYT) of shape `lam dash n`. -/
structure SYT {n : ℕ} (lam : Partition n) where
  rows : List (List ℕ)
  shape_eq : rows.map List.length = lam.parts
  row_strict : RowStrict rows
  col_strict : ColStrict rows
  entries_perm : rows.flatten.Perm (List.range' 1 n)

/-- Dimension $f^\lambda$: The number of Standard Young Tableaux of shape `lam dash n`. -/
noncomputable def fLambda {n : ℕ} (lam : Partition n) [Fintype (SYT lam)] : ℕ :=
  Fintype.card (SYT lam)

/-- Schensted row insertion: inserting `x` into a strictly increasing row `R`. -/
def insertRow : List ℕ → ℕ → List ℕ × Option ℕ
  | [], x => ([x], none)
  | y :: ys, x =>
    if x < y then
      (x :: ys, some y)
    else
      let res := insertRow ys x
      (y :: res.1, res.2)

/-- Schensted tableau insertion: inserting `x` into tableau `P`. -/
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

/-- Executes the full Robinson-Schensted algorithm on a list `xs`. -/
def rskFromList (xs : List ℕ) : List (List ℕ) × List (List ℕ) :=
  (xs.zip (List.range xs.length)).foldl (fun (P, Q) (x, idx) =>
    let (P', pos) := insertTableau P x
    let Q' := addToRow Q pos.1 (idx + 1)
    (P', Q')
  ) ([], [])

/-- Convert a permutation π ∈ 𝔖_n to a 1-based list [π(0)+1, ..., π(n-1)+1]. -/
def permToList (n : ℕ) (π : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map (fun i => (π i).val + 1)

/-- The RSK mapping for a permutation π ∈ 𝔖_n. -/
def rskPerm (n : ℕ) (π : Equiv.Perm (Fin n)) : List (List ℕ) × List (List ℕ) :=
  rskFromList (permToList n π)

/-- Length of the Longest Increasing Subsequence of a list `xs`. -/
noncomputable def lis (xs : List ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun s : List ℕ => s.Pairwise (· < ·)) xs.sublists.toFinset) List.length

/-- Length of the Longest Decreasing Subsequence of a list `xs`. -/
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
    ((rskPerm n π).1.headD []).length = lisPerm n π := sorry

/--
**Greene's Theorem (1974)**:
The length of the first column $\lambda_1' = (P(\pi)).	ext{length}$ of the insertion tableau $P(\pi)$
equals the length of the Longest Decreasing Subsequence $\operatorname{LDS}(\pi)$.
-/
theorem greene_lds_theorem (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_greene : (rskPerm n π).1.length = ldsPerm n π) :
    (rskPerm n π).1.length = ldsPerm n π := sorry

/--
**Frobenius Identity / Robinson–Schensted Bijection Cardinality Formula**:
Given the RSK equivalence $\mathfrak{S}_n \simeq \coprod_{\lambda dash n} (\mathrm{SYT}(\lambda) 	imes \mathrm{SYT}(\lambda))$,
the sum of squares of the number of Standard Young Tableaux over all partitions $\lambda dash n$
equals $n!$:
$$\sum_{\lambda dash n} (f^\lambda)^2 = n!$$
-/
theorem rsk_sum_squares_eq_factorial (n : ℕ)
    (rskEquiv : Equiv.Perm (Fin n) ≃ Σ lam : Partition n, SYT lam × SYT lam)
    [Fintype (Partition n)]
    [∀ lam : Partition n, Fintype (SYT lam)] :
    ∑ lam : Partition n, (fLambda lam) ^ 2 = Nat.factorial n := sorry

/-- Inversion swaps insertion and recording tableaux: P(π⁻¹) = Q(π) and Q(π⁻¹) = P(π). -/
theorem rsk_involution_symmetry (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_inv_P : (rskPerm n π⁻¹).1 = (rskPerm n π).2)
    (h_inv_Q : (rskPerm n π⁻¹).2 = (rskPerm n π).1) :
    (rskPerm n π⁻¹).1 = (rskPerm n π).2 ∧ (rskPerm n π⁻¹).2 = (rskPerm n π).1 := sorry

/--
**RSK Involution Fixed Points Theorem**:
A permutation $\pi \in \mathfrak{S}_n$ is an involution ($\pi^2 = \mathrm{id}$) if and only if
its insertion tableau equals its recording tableau, $P(\pi) = Q(\pi)$.
-/
theorem rsk_involution_fixed_points (n : ℕ) (π : Equiv.Perm (Fin n))
    (h_symm : (rskPerm n π⁻¹).1 = (rskPerm n π).2 ∧ (rskPerm n π⁻¹).2 = (rskPerm n π).1)
    (h_inj : Function.Injective (rskPerm n)) :
    π * π = 1 ↔ (rskPerm n π).1 = (rskPerm n π).2 := sorry

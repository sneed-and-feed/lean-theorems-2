import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators Matrix
open Classical

namespace BirkhoffVonNeumann

variable {n : ℕ}

/-- A square real matrix $M$ of size $n 	imes n$ is **doubly stochastic** if all its entries
are non-negative and all its row sums and column sums equal $1$. -/
def IsDoublyStochastic (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)

/-- The permutation matrix $P_\sigma$ associated to a permutation $\sigma \in S_n$.
$(P_\sigma)_{i,j} = 1$ if $j = \sigma(i)$ and $0$ otherwise. -/
def permutationMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j = σ i then 1 else 0

/-- The set of all $n 	imes n$ doubly stochastic matrices. -/
def doublyStochasticSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { M | IsDoublyStochastic M }

/-- The set of all $n 	imes n$ permutation matrices. -/
def permutationMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { permutationMatrix σ | σ : Equiv.Perm (Fin n) }

/-- Every permutation matrix is doubly stochastic. -/
theorem permutationMatrix_isDoublyStochastic (σ : Equiv.Perm (Fin n)) :
    IsDoublyStochastic (permutationMatrix σ) := sorry

/-- The set of doubly stochastic matrices is convex. -/
theorem convex_doublyStochastic (n : ℕ) : Convex ℝ (doublyStochasticSet n) := sorry

/-- Hall's marriage condition holds for the row supports of any doubly stochastic matrix. -/
theorem hall_condition_doublyStochastic (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (S : Finset (Fin n)) :
    S.card ≤ (S.biUnion (fun i => Finset.filter (fun j => 0 < M i j) Finset.univ)).card := sorry

/-- Every doubly stochastic matrix admits a permutation $\sigma \in S_n$ such that
$M_{i, \sigma(i)} > 0$ for all $i$ (positive diagonal / Hall-König support matching). -/
theorem exists_perm_positive_entries (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < M i (σ i) := sorry

/--
**Birkhoff–von Neumann Theorem (1946/1953)**:
Every doubly stochastic matrix is in the convex hull of permutation matrices.
$$\mathcal{D}_n = \operatorname{Conv}(\mathcal{P}_n)$$
-/
theorem birkhoff_von_neumann_convex_hull (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    M ∈ convexHull ℝ (permutationMatrices n) := sorry

/-- A matrix is doubly stochastic if and only if it belongs to the convex hull of permutation matrices. -/
theorem birkhoff_von_neumann_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ convexHull ℝ (permutationMatrices n) ↔ IsDoublyStochastic M := sorry

/--
**Birkhoff–von Neumann Theorem (Explicit Convex Combination Form)**:
Every doubly stochastic matrix is an explicit convex combination of permutation matrices:
$$M = \sum_{\sigma \in S_n} c_\sigma P_\sigma, \quad c_\sigma \ge 0, \quad \sum_\sigma c_\sigma = 1$$
-/
theorem birkhoff_von_neumann_convex_combination (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    ∃ (c : Equiv.Perm (Fin n) → ℝ), (∀ σ, 0 ≤ c σ) ∧ (∑ σ, c σ = 1) ∧
      M = ∑ σ, c σ • permutationMatrix σ := sorry

/-- The extreme points of the doubly stochastic polytope $\mathcal{D}_n$ are exactly the permutation matrices. -/
theorem extremePoints_doublyStochasticSet (n : ℕ) :
    Set.extremePoints ℝ (doublyStochasticSet n) = permutationMatrices n := sorry

/-- The support of a permutation matrix has cardinality exactly $n$. -/
theorem permutationMatrix_card_matrixSupp (σ : Equiv.Perm (Fin n)) :
    (Finset.filter (fun p : Fin n × Fin n => 0 < permutationMatrix σ p.1 p.2) Finset.univ).card = n := sorry

/-- Any $n 	imes n$ doubly stochastic matrix has at least $n$ positive entries. -/
theorem card_matrixSupp_ge_n (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    n ≤ (Finset.filter (fun p : Fin n × Fin n => 0 < M p.1 p.2) Finset.univ).card := sorry

/-- The support of any $n 	imes n$ matrix is bounded above by $n^2$. -/
theorem matrixSupp_card_le_sq (M : Matrix (Fin n) (Fin n) ℝ) :
    (Finset.filter (fun p : Fin n × Fin n => 0 < M p.1 p.2) Finset.univ).card ≤ n * n := sorry

/-- A doubly stochastic matrix has all entries in $\{0, 1\}$ if and only if it is a permutation matrix. -/
theorem isDoublyStochastic_and_entries_zero_one_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    (IsDoublyStochastic M ∧ ∀ i j, M i j = 0 ∨ M i j = 1) ↔ M ∈ permutationMatrices n := sorry

end BirkhoffVonNeumann

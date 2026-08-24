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
import Formalization.KonigMatching

open scoped BigOperators Matrix
open Classical

/-!
# Birkhoff–von Neumann Theorem on Doubly Stochastic Matrices

This module formalizes the **Birkhoff–von Neumann Theorem** (Garrett Birkhoff, 1946; John von Neumann, 1953),
a cornerstone theorem in convex geometry, polyhedral combinatorics, and matrix theory establishing that the
polytope $\mathcal{D}_n$ of $n \times n$ doubly stochastic matrices is the convex hull of the set $\mathcal{P}_n$
of $n \times n$ permutation matrices:
$$\mathcal{D}_n = \operatorname{Conv}(\mathcal{P}_n)$$
Moreover, the extreme points of $\mathcal{D}_n$ are precisely the permutation matrices $\mathcal{P}_n$:
$$\operatorname{Ext}(\mathcal{D}_n) = \mathcal{P}_n$$

## Mathematical Framework

### Doubly Stochastic Matrices
An $n \times n$ real matrix $M$ is **doubly stochastic** if:
1. **Non-negativity**: $M_{i,j} \ge 0$ for all $i, j \in \{1,\dots,n\}$.
2. **Row stochasticity**: $\sum_{j=1}^n M_{i,j} = 1$ for every row $i$.
3. **Column stochasticity**: $\sum_{i=1}^n M_{i,j} = 1$ for every column $j$.

### Permutation Matrices
For each permutation $\sigma \in S_n$, the **permutation matrix** $P_\sigma$ is defined by:
$$(P_\sigma)_{i,j} = \begin{cases} 1 & \text{if } j = \sigma(i) \\ 0 & \text{otherwise} \end{cases}$$
Every permutation matrix is doubly stochastic.

### Support Matching & Hall's Marriage Theorem
By applying Hall's Marriage Theorem to the bipartite graph with edges $(i, j)$ where $M_{i,j} > 0$,
any doubly stochastic matrix $M$ admits a permutation $\sigma \in S_n$ such that:
$$M_{i, \sigma(i)} > 0 \quad \text{for all } i \in \{1,\dots,n\}$$
This positive diagonal extraction is the key combinatorial engine enabling the inductive reduction.

### Birkhoff Reduction Step
Given a doubly stochastic matrix $M$ and a positive support permutation $\sigma$, let:
$$\theta = \min_{1 \le i \le n} M_{i, \sigma(i)} > 0$$
- If $\theta = 1$, then $M = P_\sigma$.
- If $\theta < 1$, the matrix:
  $$M' = \frac{1}{1 - \theta}(M - \theta P_\sigma)$$
  is again doubly stochastic, satisfies $M = (1 - \theta) M' + \theta P_\sigma$, and has strictly fewer
  positive entries: $|\operatorname{supp}(M')| < |\operatorname{supp}(M)|$.
By well-founded induction on the support size $|\operatorname{supp}(M)|$, $M$ is a convex combination
of permutation matrices.

## Main Theorems Formalized

- `IsDoublyStochastic`: Predicate defining doubly stochastic matrices.
- `permutationMatrix`: Definition of $P_\sigma$ for $\sigma \in S_n$.
- `permutationMatrix_isDoublyStochastic`: Permutation matrices are doubly stochastic.
- `convex_doublyStochastic`: The set $\mathcal{D}_n$ is convex.
- `hall_condition_doublyStochastic`: Hall's marriage condition holds for row supports.
- `exists_perm_positive_entries`: Existence of positive diagonal permutation $\sigma \in S_n$.
- `birkhoff_von_neumann_convex_hull`: $M \in \operatorname{Conv}(\mathcal{P}_n)$ for any $M \in \mathcal{D}_n$.
- `birkhoff_von_neumann_iff`: Characterization $\mathcal{D}_n = \operatorname{Conv}(\mathcal{P}_n)$.
- `birkhoff_von_neumann_convex_combination`: Explicit constructive decomposition $M = \sum_\sigma c_\sigma P_\sigma$.
- `extremePoints_doublyStochasticSet`: Characterization $\operatorname{Ext}(\mathcal{D}_n) = \mathcal{P}_n$.
- `permutationMatrix_card_matrixSupp`: $|\operatorname{supp}(P_\sigma)| = n$.
- `card_matrixSupp_ge_n`: Support size lower bound $|\operatorname{supp}(M)| \ge n$.
- `matrixSupp_card_le_sq`: Support size upper bound $|\operatorname{supp}(M)| \le n^2$.
- `isDoublyStochastic_and_entries_zero_one_iff`: $0$-$1$ doubly stochastic matrices are permutation matrices.

## References
- Birkhoff, G. (1946). *Tres observaciones sobre el algebra lineal*. Universidad Nacional de Tucumán
  Revista, Serie A, 5, 147–151.
- von Neumann, J. (1953). *A certain zero-sum two-person game equivalent to the optimal assignment problem*.
  Contributions to the Theory of Games, 2, 5–12.
- Hall, P. (1935). *On Representatives of Subsets*. J. London Math. Soc., 10(1), 26–30.
- Schrijver, A. (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
-/

namespace BirkhoffVonNeumann

variable {n : ℕ}

/-- A square real matrix $M$ of size $n \times n$ is **doubly stochastic** if all its entries
are non-negative and all its row sums and column sums equal $1$. -/
def IsDoublyStochastic (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)

/-- The permutation matrix $P_\sigma$ associated to a permutation $\sigma \in S_n$.
$(P_\sigma)_{i,j} = 1$ if $j = \sigma(i)$ and $0$ otherwise. -/
def permutationMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j = σ i then 1 else 0

/-- The set of all $n \times n$ doubly stochastic matrices. -/
def doublyStochasticSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { M | IsDoublyStochastic M }

/-- The set of all $n \times n$ permutation matrices. -/
def permutationMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { permutationMatrix σ | σ : Equiv.Perm (Fin n) }

lemma permutationMatrix_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutationMatrix σ i j = if j = σ i then 1 else 0 :=
  rfl

lemma permutationMatrix_nonneg (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    0 ≤ permutationMatrix σ i j := by
  dsimp [permutationMatrix]; split_ifs <;> positivity

lemma permutationMatrix_row_sum (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∑ j, permutationMatrix σ i j = 1 := by
  simp [permutationMatrix, Finset.sum_ite_eq']

lemma permutationMatrix_col_sum (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    ∑ i, permutationMatrix σ i j = 1 := by
  simp [permutationMatrix, eq_comm (a := j), ← σ.eq_symm_apply]

/-- Every permutation matrix is doubly stochastic. -/
theorem permutationMatrix_isDoublyStochastic (σ : Equiv.Perm (Fin n)) :
    IsDoublyStochastic (permutationMatrix σ) :=
  ⟨permutationMatrix_nonneg σ, permutationMatrix_row_sum σ, permutationMatrix_col_sum σ⟩

theorem permutationMatrices_subset_doublyStochastic (n : ℕ) :
    permutationMatrices n ⊆ doublyStochasticSet n := by
  rintro M ⟨σ, rfl⟩
  exact permutationMatrix_isDoublyStochastic σ

/-- The set of doubly stochastic matrices is convex. -/
theorem convex_doublyStochastic (n : ℕ) : Convex ℝ (doublyStochasticSet n) := by
  intro A hA B hB a b ha hb hab
  dsimp [doublyStochasticSet, IsDoublyStochastic] at hA hB ⊢
  refine ⟨fun i j => add_nonneg (mul_nonneg ha (hA.1 i j)) (mul_nonneg hb (hB.1 i j)),
    fun i => by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hA.2.1 i, hB.2.1 i, hab],
    fun j => by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hA.2.2 j, hB.2.2 j, hab]⟩

/-- The convex hull of permutation matrices is contained in the set of doubly stochastic matrices. -/
theorem convexHull_permutationMatrices_subset (n : ℕ) :
    convexHull ℝ (permutationMatrices n) ⊆ doublyStochasticSet n :=
  convexHull_min (permutationMatrices_subset_doublyStochastic n) (convex_doublyStochastic n)

/-! ### Support and Hall's Marriage Theorem (Positive Diagonal) -/

/-- The row support of row $i$: column indices $j$ where $M_{i,j} > 0$. -/
noncomputable def rowSupp (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.filter (fun j => 0 < M i j) Finset.univ

/-- The matrix support: pairs $(i, j)$ where $M_{i,j} > 0$. -/
noncomputable def matrixSupp (M : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => 0 < M p.1 p.2) Finset.univ

/-- Hall's marriage condition holds for the row supports of any doubly stochastic matrix. -/
theorem hall_condition_doublyStochastic (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (S : Finset (Fin n)) :
    S.card ≤ (S.biUnion (rowSupp M)).card := by
  let T := S.biUnion (rowSupp M)
  have h_zero : ∀ i ∈ S, ∀ j ∉ T, M i j = 0 := fun i hi j hj =>
    le_antisymm (not_lt.mp fun h => hj (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩)) (hM.1 i j)
  have h_row : ∀ i ∈ S, ∑ j ∈ T, M i j = 1 := fun i hi =>
    (Finset.sum_subset (Finset.subset_univ T) (fun j _ hj => h_zero i hi j hj)).trans (hM.2.1 i)
  have h_le : (S.card : ℝ) ≤ (T.card : ℝ) := calc
    (S.card : ℝ) = ∑ i ∈ S, ∑ j ∈ T, M i j := by
      have : (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
      rw [this]; exact Finset.sum_congr rfl (fun i hi => (h_row i hi).symm)
    _ = ∑ j ∈ T, ∑ i ∈ S, M i j := Finset.sum_comm
    _ ≤ ∑ j ∈ T, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
      (Finset.sum_le_univ_sum_of_nonneg (fun i => hM.1 i j)).trans_eq (hM.2.2 j)
    _ = T.card := by simp
  exact Nat.cast_le.mp h_le

/-- Every doubly stochastic matrix admits a permutation $\sigma \in S_n$ such that
$M_{i, \sigma(i)} > 0$ for all $i$ (positive diagonal / Hall-König support matching). -/
theorem exists_perm_positive_entries (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < M i (σ i) := by
  obtain ⟨f, hf_inj, hf_supp⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (rowSupp M)).mp (hall_condition_doublyStochastic M hM)
  exact ⟨Equiv.ofBijective f ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩,
    fun i => (Finset.mem_filter.mp (hf_supp i)).2⟩

lemma eq_permutationMatrix_of_diag_one (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (σ : Equiv.Perm (Fin n)) (h_diag : ∀ i, M i (σ i) = 1) :
    M = permutationMatrix σ := by
  ext i j
  dsimp [permutationMatrix]
  split_ifs with hj
  · rw [hj, h_diag]
  · have h_erase : ∑ k ∈ Finset.univ.erase (σ i), M i k = 0 := by
      linarith [Finset.add_sum_erase Finset.univ (fun k => M i k) (Finset.mem_univ (σ i)), hM.2.1 i, h_diag i]
    exact Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hM.1 i k) |>.mp h_erase j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

/-! ### Reduced Matrix Construction for Birkhoff Induction -/

/-- Reduced matrix $M' = \frac{1}{1 - \theta}(M - \theta P_\sigma)$. -/
noncomputable def reducedMatrix (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (θ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (M i j - θ * permutationMatrix σ i j) / (1 - θ)

lemma reducedMatrix_apply (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (θ : ℝ) (i j : Fin n) :
    reducedMatrix M σ θ i j = (M i j - θ * permutationMatrix σ i j) / (1 - θ) :=
  rfl

lemma isDoublyStochastic_reducedMatrix (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (σ : Equiv.Perm (Fin n)) (θ : ℝ) (_hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (hθ_le : ∀ i, θ ≤ M i (σ i)) :
    IsDoublyStochastic (reducedMatrix M σ θ) := by
  have h1_ne : 1 - θ ≠ 0 := by linarith
  refine ⟨fun i j => by
      dsimp [reducedMatrix, permutationMatrix]; split_ifs with hj
      · subst hj; exact div_nonneg (by linarith [hθ_le i]) (by linarith)
      · exact div_nonneg (by linarith [hM.1 i j]) (by linarith),
    fun i => by simp_rw [reducedMatrix_apply, div_eq_mul_inv]; rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hM.2.1 i, permutationMatrix_row_sum]; simp [mul_inv_cancel₀ h1_ne],
    fun j => by simp_rw [reducedMatrix_apply, div_eq_mul_inv]; rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hM.2.2 j, permutationMatrix_col_sum]; simp [mul_inv_cancel₀ h1_ne]⟩

lemma convex_combination_reducedMatrix (M : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (θ : ℝ) (hθ_lt : θ < 1) :
    (1 - θ) • reducedMatrix M σ θ + θ • permutationMatrix σ = M := by
  ext i j; dsimp [reducedMatrix]; rw [mul_div_cancel₀ _ (by linarith)]; ring

lemma matrixSupp_reducedMatrix_subset (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (θ : ℝ)
    (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1) :
    matrixSupp (reducedMatrix M σ θ) ⊆ matrixSupp M := by
  intro ⟨i, j⟩ hp
  simp only [matrixSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  dsimp [reducedMatrix, permutationMatrix] at hp
  have h1 : 0 < 1 - θ := by linarith
  have h_pos := (div_pos_iff_of_pos_right h1).mp hp
  split_ifs at h_pos <;> linarith

lemma not_mem_matrixSupp_reducedMatrix_min (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (i₀ : Fin n) :
    (i₀, σ i₀) ∉ matrixSupp (reducedMatrix M σ (M i₀ (σ i₀))) := by
  simp [matrixSupp, reducedMatrix, permutationMatrix]

lemma card_matrixSupp_reducedMatrix_lt (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (i₀ : Fin n) (h_pos : 0 < M i₀ (σ i₀)) (hθ_lt : M i₀ (σ i₀) < 1) :
    (matrixSupp (reducedMatrix M σ (M i₀ (σ i₀)))).card < (matrixSupp M).card := by
  have h_sub := matrixSupp_reducedMatrix_subset M σ (M i₀ (σ i₀)) (le_of_lt h_pos) hθ_lt
  have h_not := not_mem_matrixSupp_reducedMatrix_min M σ i₀
  have h_in : (i₀, σ i₀) ∈ matrixSupp M := by simpa [matrixSupp] using h_pos
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun heq => h_not (heq ▸ h_in)⟩)

lemma entry_le_one_of_isDoublyStochastic (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (i j : Fin n) : M i j ≤ 1 :=
  (Finset.single_le_sum (fun k _ => hM.1 i k) (Finset.mem_univ j)).trans_eq (hM.2.1 i)

lemma birkhoff_induction (k : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M)
    (hk : (matrixSupp M).card ≤ k) :
    M ∈ convexHull ℝ (permutationMatrices n) := by
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    obtain ⟨σ, hσ_pos⟩ := exists_perm_positive_entries M hM
    cases isEmpty_or_nonempty (Fin n) with
    | inl _ => exact Subsingleton.elim M (permutationMatrix 1) ▸ subset_convexHull ℝ _ ⟨1, rfl⟩
    | inr _ =>
      obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ (fun i => M i (σ i)) Finset.univ_nonempty
      let θ := M i₀ (σ i₀)
      rcases eq_or_lt_of_le (entry_le_one_of_isDoublyStochastic M hM i₀ (σ i₀)) with (hθ_eq_one | hθ_lt_one)
      · have h_all_one : ∀ i, M i (σ i) = 1 := fun i =>
          le_antisymm (entry_le_one_of_isDoublyStochastic M hM i (σ i)) (hθ_eq_one ▸ hi₀_min i (Finset.mem_univ i))
        rw [eq_permutationMatrix_of_diag_one M hM σ h_all_one]
        exact subset_convexHull ℝ _ ⟨σ, rfl⟩
      · let M' := reducedMatrix M σ θ
        have hM'_ds := isDoublyStochastic_reducedMatrix M hM σ θ (hσ_pos i₀) hθ_lt_one (fun i => hi₀_min i (Finset.mem_univ i))
        have hM'_hull := ih (matrixSupp M').card ((card_matrixSupp_reducedMatrix_lt M σ i₀ (hσ_pos i₀) hθ_lt_one).trans_le hk) M' hM'_ds le_rfl
        rw [← convex_combination_reducedMatrix M σ θ hθ_lt_one]
        exact convex_convexHull ℝ _ hM'_hull (subset_convexHull ℝ _ ⟨σ, rfl⟩) (by linarith) (by linarith [hσ_pos i₀]) (by ring)

/--
**Birkhoff–von Neumann Theorem (1946/1953)**:
Every doubly stochastic matrix is in the convex hull of permutation matrices.
$$\mathcal{D}_n = \operatorname{Conv}(\mathcal{P}_n)$$
-/
theorem birkhoff_von_neumann_convex_hull (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    M ∈ convexHull ℝ (permutationMatrices n) :=
  birkhoff_induction (matrixSupp M).card M hM le_rfl

/-- A matrix is doubly stochastic if and only if it belongs to the convex hull of permutation matrices. -/
theorem birkhoff_von_neumann_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ convexHull ℝ (permutationMatrices n) ↔ IsDoublyStochastic M :=
  ⟨fun h => convexHull_permutationMatrices_subset n h, birkhoff_von_neumann_convex_hull M⟩

/-! ### Explicit Convex Combination Decomposition -/

lemma exists_convex_combination_induction (k : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) (hk : (matrixSupp M).card ≤ k) :
    ∃ (c : Equiv.Perm (Fin n) → ℝ), (∀ σ, 0 ≤ c σ) ∧ (∑ σ, c σ = 1) ∧
      M = ∑ σ, c σ • permutationMatrix σ := by
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    obtain ⟨σ₀, hσ₀_pos⟩ := exists_perm_positive_entries M hM
    cases isEmpty_or_nonempty (Fin n) with
    | inl _ =>
      have : Subsingleton (Matrix (Fin n) (Fin n) ℝ) := inferInstance
      exact ⟨fun _ => 1, fun _ => by positivity, by simp, Subsingleton.elim M _⟩
    | inr _ =>
      obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ (fun i => M i (σ₀ i)) Finset.univ_nonempty
      let θ := M i₀ (σ₀ i₀)
      rcases eq_or_lt_of_le (entry_le_one_of_isDoublyStochastic M hM i₀ (σ₀ i₀)) with (hθ_eq_one | hθ_lt_one)
      · have h_all_one : ∀ i, M i (σ₀ i) = 1 := fun i =>
          le_antisymm (entry_le_one_of_isDoublyStochastic M hM i (σ₀ i)) (hθ_eq_one ▸ hi₀_min i (Finset.mem_univ i))
        have hM_eq := eq_permutationMatrix_of_diag_one M hM σ₀ h_all_one
        refine ⟨fun σ => if σ = σ₀ then 1 else 0, fun σ => by dsimp; split_ifs <;> positivity, by simp, ?_⟩
        simp [hM_eq, ite_smul]
      · let M' := reducedMatrix M σ₀ θ
        have hM'_ds := isDoublyStochastic_reducedMatrix M hM σ₀ θ (hσ₀_pos i₀) hθ_lt_one (fun i => hi₀_min i (Finset.mem_univ i))
        obtain ⟨c', hc'_nonneg, hc'_sum, hc'_decomp⟩ :=
          ih (matrixSupp M').card ((card_matrixSupp_reducedMatrix_lt M σ₀ i₀ (hσ₀_pos i₀) hθ_lt_one).trans_le hk) M' hM'_ds le_rfl
        refine ⟨fun σ => (1 - θ) * c' σ + if σ = σ₀ then θ else 0,
          fun σ => by dsimp; split_ifs <;> nlinarith [hc'_nonneg σ, hσ₀_pos i₀],
          by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hc'_sum],
          ?_⟩
        have h_comb : M = (1 - θ) • M' + θ • permutationMatrix σ₀ :=
          (convex_combination_reducedMatrix M σ₀ θ hθ_lt_one).symm
        rw [h_comb, hc'_decomp, Finset.smul_sum]
        simp_rw [add_smul, mul_smul, ite_smul, zero_smul]
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

/--
**Birkhoff–von Neumann Theorem (Explicit Convex Combination Form)**:
Every doubly stochastic matrix is an explicit convex combination of permutation matrices:
$$M = \sum_{\sigma \in S_n} c_\sigma P_\sigma, \quad c_\sigma \ge 0, \quad \sum_\sigma c_\sigma = 1$$
-/
theorem birkhoff_von_neumann_convex_combination (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsDoublyStochastic M) :
    ∃ (c : Equiv.Perm (Fin n) → ℝ), (∀ σ, 0 ≤ c σ) ∧ (∑ σ, c σ = 1) ∧
      M = ∑ σ, c σ • permutationMatrix σ :=
  exists_convex_combination_induction (matrixSupp M).card M hM le_rfl

/-! ### Extreme Points of the Doubly Stochastic Polytope -/

/-- Every permutation matrix is an extreme point of the doubly stochastic polytope $\mathcal{D}_n$. -/
theorem permutationMatrix_mem_extremePoints (σ : Equiv.Perm (Fin n)) :
    permutationMatrix σ ∈ Set.extremePoints ℝ (doublyStochasticSet n) := by
  refine ⟨permutationMatrix_isDoublyStochastic σ, fun A hA B hB ⟨a, b, ha_pos, hb_pos, hab, h_seg⟩ => ?_⟩
  exact eq_permutationMatrix_of_diag_one A hA σ fun i => by
    have h_pt : a * A i (σ i) + b * B i (σ i) = 1 := by
      have := congr_fun (congr_fun h_seg i) (σ i)
      simpa [permutationMatrix] using this
    have hA1 := entry_le_one_of_isDoublyStochastic A hA i (σ i)
    have hB1 := entry_le_one_of_isDoublyStochastic B hB i (σ i)
    nlinarith

/-- The extreme points of the doubly stochastic polytope $\mathcal{D}_n$ are exactly the permutation matrices. -/
theorem extremePoints_doublyStochasticSet (n : ℕ) :
    Set.extremePoints ℝ (doublyStochasticSet n) = permutationMatrices n := by
  ext M
  refine ⟨fun ⟨hM_ds, hM_ext_prop⟩ => ?_, fun ⟨σ, hσ⟩ => hσ ▸ permutationMatrix_mem_extremePoints σ⟩
  cases isEmpty_or_nonempty (Fin n) with
  | inl _ => exact ⟨1, (Subsingleton.elim M _).symm⟩
  | inr _ =>
    obtain ⟨σ, hσ_pos⟩ := exists_perm_positive_entries M hM_ds
    obtain ⟨i₀, _, hi₀_min⟩ := Finset.exists_min_image Finset.univ (fun i => M i (σ i)) Finset.univ_nonempty
    let θ := M i₀ (σ i₀)
    rcases eq_or_lt_of_le (entry_le_one_of_isDoublyStochastic M hM_ds i₀ (σ i₀)) with (hθ_eq_one | hθ_lt_one)
    · have h_all_one : ∀ i, M i (σ i) = 1 := fun i =>
        le_antisymm (entry_le_one_of_isDoublyStochastic M hM_ds i (σ i)) (hθ_eq_one ▸ hi₀_min i (Finset.mem_univ i))
      exact ⟨σ, (eq_permutationMatrix_of_diag_one M hM_ds σ h_all_one).symm⟩
    · let M' := reducedMatrix M σ θ
      have hM'_ds := isDoublyStochastic_reducedMatrix M hM_ds σ θ (hσ_pos i₀) hθ_lt_one (fun i => hi₀_min i (Finset.mem_univ i))
      have h_seg : M ∈ openSegment ℝ M' (permutationMatrix σ) :=
        ⟨1 - θ, θ, by linarith, hσ_pos i₀, by ring, convex_combination_reducedMatrix M σ θ hθ_lt_one⟩
      have hM'_eq := hM_ext_prop hM'_ds (permutationMatrix_isDoublyStochastic σ) h_seg
      have hM'_zero : (reducedMatrix M σ θ) i₀ (σ i₀) = 0 := by
        dsimp [reducedMatrix, permutationMatrix, θ]; simp
      have h_pt := congr_fun (congr_fun hM'_eq i₀) (σ i₀)
      linarith [hσ_pos i₀]

/-! ### Combinatorial Corollaries and Support Bounds -/

lemma matrixSupp_permutationMatrix (σ : Equiv.Perm (Fin n)) :
    matrixSupp (permutationMatrix σ) = (Finset.univ : Finset (Fin n)).image (fun i => (i, σ i)) := by
  ext ⟨i, j⟩
  simp only [matrixSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [permutationMatrix_apply]
  constructor
  · intro h; split_ifs at h with hj
    · exact ⟨i, Prod.ext rfl hj.symm⟩
    · linarith
  · rintro ⟨a, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    simp

/-- The support of a permutation matrix has cardinality exactly $n$. -/
theorem permutationMatrix_card_matrixSupp (σ : Equiv.Perm (Fin n)) :
    (matrixSupp (permutationMatrix σ)).card = n := by
  rw [matrixSupp_permutationMatrix, Finset.card_image_of_injective _ (fun x y h => congr_arg Prod.fst h)]
  simp

/-- Any $n \times n$ doubly stochastic matrix has at least $n$ positive entries. -/
theorem card_matrixSupp_ge_n (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsDoublyStochastic M) :
    n ≤ (matrixSupp M).card := by
  obtain ⟨σ, hσ_pos⟩ := exists_perm_positive_entries M hM
  have hS : (Finset.univ : Finset (Fin n)).image (fun i => (i, σ i)) ⊆ matrixSupp M := by
    rintro ⟨i, j⟩ hp
    obtain ⟨a, _, heq⟩ := Finset.mem_image.mp hp
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    simpa [matrixSupp] using hσ_pos a
  have h_card : ((Finset.univ : Finset (Fin n)).image (fun i => (i, σ i))).card = n := by
    rw [Finset.card_image_of_injective _ (fun x y h => congr_arg Prod.fst h)]
    simp
  have : ((Finset.univ : Finset (Fin n)).image (fun i => (i, σ i))).card ≤ (matrixSupp M).card :=
    Finset.card_le_card hS
  omega

/-- The support of any $n \times n$ matrix is bounded above by $n^2$. -/
theorem matrixSupp_card_le_sq (M : Matrix (Fin n) (Fin n) ℝ) :
    (matrixSupp M).card ≤ n * n := by
  simpa using Finset.card_le_univ (matrixSupp M)

/-- A doubly stochastic matrix has all entries in $\{0, 1\}$ if and only if it is a permutation matrix. -/
theorem isDoublyStochastic_and_entries_zero_one_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    (IsDoublyStochastic M ∧ ∀ i j, M i j = 0 ∨ M i j = 1) ↔ M ∈ permutationMatrices n := by
  refine ⟨fun ⟨hM, h01⟩ => ?_, fun ⟨σ, hσ⟩ => hσ ▸ ⟨permutationMatrix_isDoublyStochastic σ, fun i j => by
    dsimp [permutationMatrix]; split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]⟩⟩
  obtain ⟨σ, hσ_pos⟩ := exists_perm_positive_entries M hM
  have h_diag : ∀ i, M i (σ i) = 1 := fun i => (h01 i (σ i)).resolve_left (ne_of_gt (hσ_pos i))
  exact ⟨σ, (eq_permutationMatrix_of_diag_one M hM σ h_diag).symm⟩

end BirkhoffVonNeumann

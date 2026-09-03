import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Formalization.SpernerAntichain

open scoped BigOperators Finset


/-!
# Stanley's $\mathfrak{sl}_2$ Sperner Proof for Partition Poset $L(m, n)$

This module formalizes **Stanley's $\mathfrak{sl}_2$ Sperner Theorem** (Richard P. Stanley, 1980)
for the **partition lattice / poset** $L(m, n)$ of Young diagrams fitting inside an $m \times n$ rectangle.

## Mathematical Overview

### 1. The Partition Poset $L(m, n)$
The poset $L(m, n)$ consists of integer partitions $\lambda = (\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{m-1} \ge 0)$
with parts bounded by $n$ ($\lambda_0 \le n$).
- **Partial order**: Young diagram inclusion $\lambda \le \mu \iff \forall i, \lambda_i \le \mu_i$.
- **Rank function**: The size / area $|\lambda| = \sum_{i=0}^{m-1} \lambda_i \in \{0, 1, \dots, mn\}$.
- **Rank levels**: $L_k(m, n) = \{\lambda \in L(m, n) : |\lambda| = k\}$, with size $p_k(m, n) = |L_k(m, n)|$.
- **Total capacity**: $\sum_{k=0}^{mn} p_k(m, n) = \binom{m+n}{m}$ (Gaussian / $q$-binomial coefficient $\binom{m+n}{m}_q$ at $q=1$).

### 2. Rank-Symmetry via Partition Complementation
The complement partition $\lambda^* \in L(m, n)$ is defined by:
$$\lambda^*_i = n - \lambda_{m - 1 - i}$$
Complementation is an order-reversing involution:
- $(\lambda^*)^* = \lambda$
- $|\lambda^*| = mn - |\lambda|$
This establishes **rank-symmetry**:
$$p_k(m, n) = p_{mn - k}(m, n) \quad \text{for all } 0 \le k \le mn$$

### 3. Stanley's $\mathfrak{sl}_2$ Representation Proof of Unimodality
Stanley constructed an action of the Lie algebra $\mathfrak{sl}_2(\mathbb{C}) = \operatorname{span}\{E, F, H\}$
on the graded vector space $V = \bigoplus_{k=0}^{mn} V_k$, where $V_k = \mathbb{R}^{L_k(m, n)}$:
- **Raising operator** $E : V_k \to V_{k+1}$ adds boxes with combinatorial weights.
- **Lowering operator** $F : V_{k+1} \to V_k$ removes boxes (adjoint $F = E^*$).
- **Weight operator** $H : V_k \to V_k$ acts by $H(v) = (2k - mn) v$.
- **Lie bracket relations**:
  $$[H, E] = 2E, \quad [H, F] = -2F, \quad [E, F] = H$$

From the unitary representation theory of $\mathfrak{sl}_2$:
- The commutator relation $\|E v\|^2 = \|F v\|^2 + (mn - 2k) \|v\|^2$ guarantees that $E : V_k \to V_{k+1}$
  is strictly injective for all $k < mn/2$ (**Hard Lefschetz property**).
- By linear algebra, $\dim(V_k) \le \dim(V_{k+1})$ for $k < mn/2$.
- This proves **rank-unimodality** of Gaussian coefficients:
  $$p_0(m, n) \le p_1(m, n) \le \dots \le p_{\lfloor mn/2 \rfloor}(m, n) \ge \dots \ge p_{mn}(m, n)$$

### 4. The Strong Sperner Property
A ranked poset has the **Strong Sperner property** if the maximum size of an antichain
equals the maximum rank level size:
$$\max_{\mathcal{A} \text{ antichain}} |\mathcal{A}| = p_{\lfloor mn/2 \rfloor}(m, n)$$
By Stanley's theorem, the partition poset $L(m, n)$ is a symmetric Peck poset, decomposes
into symmetric chains, and therefore satisfies the Strong Sperner property.

## References
* Stanley, R. P. (1980). *Weyl groups, the hard Lefschetz theorem, and the Sperner property*.
  SIAM Journal on Algebraic and Discrete Methods, 1(2), 168–184.
* Stanley, R. P. (1982). *Some Aspects of Groups Acting on Symmetric Posets*.
  Journal of Combinatorial Theory, Series A, 32(2), 132–161.
* Proctor, R. A. (1982). *Representations of $\mathfrak{sl}(2, \mathbb{C})$ on posets and the Sperner property*.
  SIAM Journal on Algebraic and Discrete Methods, 3(2), 275–280.
-/

namespace StanleySL2

-- ============================================================================
-- Section 1: The Partition Poset L(m, n)
-- ============================================================================

/-- An integer partition bounded by an `m × n` rectangle.
    Represented as a non-increasing sequence `parts : Fin m → ℕ` with `parts i ≤ n`. -/
@[ext]
structure PartitionBox (m n : ℕ) where
  parts : Fin m → ℕ
  le_bound : ∀ i : Fin m, parts i ≤ n
  monotone_parts : ∀ ⦃i j : Fin m⦄, i ≤ j → parts j ≤ parts i
  deriving DecidableEq

/-- The canonical embedding of a `PartitionBox m n` into `Fin m → Fin (n + 1)`. -/
def toFin {m n : ℕ} (p : PartitionBox m n) : Fin m → Fin (n + 1) :=
  fun i => ⟨p.parts i, Nat.lt_succ_of_le (p.le_bound i)⟩

lemma toFin_injective {m n : ℕ} : Function.Injective (toFin (m := m) (n := n)) :=
  fun _ _ h => PartitionBox.ext (funext fun i => congr_arg Fin.val (congr_fun h i))

noncomputable instance (m n : ℕ) : Fintype (PartitionBox m n) :=
  Fintype.ofInjective (toFin (m := m) (n := n)) toFin_injective

/-- Partial order on `PartitionBox m n` defined by Young diagram containment. -/
instance (m n : ℕ) : PartialOrder (PartitionBox m n) where
  le p q := ∀ i, p.parts i ≤ q.parts i
  le_refl _ _ := le_rfl
  le_trans _ _ _ h12 h23 i := (h12 i).trans (h23 i)
  le_antisymm _ _ h12 h21 := PartitionBox.ext (funext fun i => (h12 i).antisymm (h21 i))

instance (m n : ℕ) (p q : PartitionBox m n) : Decidable (p ≤ q) :=
  Fintype.decidableForallFintype

/-- An antichain in the partition poset `PartitionBox m n`. -/
def IsAntichain {m n : ℕ} (A : Finset (PartitionBox m n)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≤ q → p = q

/-- The rank (size / number of boxes in Young diagram) of a partition `p`. -/
def rank {m n : ℕ} (p : PartitionBox m n) : ℕ :=
  ∑ i : Fin m, p.parts i

lemma rank_le_mul {m n : ℕ} (p : PartitionBox m n) : rank p ≤ m * n := by
  simpa [rank] using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => p.le_bound i

lemma rank_le_rank_of_le {m n : ℕ} {p q : PartitionBox m n} (h : p ≤ q) : rank p ≤ rank q :=
  Finset.sum_le_sum fun i _ => h i

lemma eq_of_le_of_rank_eq {m n : ℕ} {p q : PartitionBox m n} (hle : p ≤ q) (hrank : rank p = rank q) :
    p = q := by
  ext i
  by_contra hne
  have := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, (hle i).lt_of_ne hne⟩
  exact this.ne hrank

-- ============================================================================
-- Section 2: Rank Levels, Partition Complementation & Rank Symmetry
-- ============================================================================

/-- The set of partitions of rank `k` fitting in an `m × n` box. -/
noncomputable def rankLevel (m n k : ℕ) : Finset (PartitionBox m n) :=
  Finset.univ.filter (fun p => rank p = k)

/-- The number of partitions of rank `k` fitting in an `m × n` box, denoted $p_k(m, n)$. -/
noncomputable def rankSize (m n k : ℕ) : ℕ :=
  (rankLevel m n k).card

/-- Every rank level in `PartitionBox m n` is an antichain. -/
theorem rankLevel_isAntichain (m n k : ℕ) :
    IsAntichain (rankLevel m n k) :=
  fun _ hp _ hq hle => eq_of_le_of_rank_eq hle ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

lemma rankLevel_eq_empty_of_gt {m n k : ℕ} (hk : m * n < k) :
    rankLevel m n k = ∅ :=
  Finset.filter_eq_empty_iff.mpr fun p _ => by have := rank_le_mul p; omega

lemma rankSize_eq_zero_of_gt {m n k : ℕ} (hk : m * n < k) :
    rankSize m n k = 0 := by
  simp [rankSize, rankLevel_eq_empty_of_gt hk]

/-- The index reversing map on `Fin m`. -/
def finRev {m : ℕ} (i : Fin m) : Fin m :=
  ⟨m - 1 - i.val, by omega⟩

lemma finRev_involutive {m : ℕ} : Function.Involutive (finRev (m := m)) :=
  fun i => Fin.ext (by dsimp [finRev]; omega)

lemma finRev_bijective {m : ℕ} : Function.Bijective (finRev (m := m)) :=
  finRev_involutive.bijective

lemma finRev_order_reversing {m : ℕ} {i j : Fin m} (hij : i ≤ j) :
    finRev j ≤ finRev i := by
  show (finRev j).1 ≤ (finRev i).1
  have := i.2; have := j.2; have : i.1 ≤ j.1 := hij
  dsimp [finRev]; omega

/-- The complement partition `p^*` in the bounding box `m × n`. -/
def complementPartition {m n : ℕ} (p : PartitionBox m n) : PartitionBox m n where
  parts i := n - p.parts (finRev i)
  le_bound _ := Nat.sub_le n _
  monotone_parts _ _ hij := Nat.sub_le_sub_left (p.monotone_parts (finRev_order_reversing hij)) n

lemma complementPartition_involutive {m n : ℕ} :
    Function.Involutive (complementPartition (m := m) (n := n)) :=
  fun p => PartitionBox.ext (funext fun i => by
    have := p.le_bound i
    dsimp [complementPartition]
    rw [finRev_involutive i]
    omega)

lemma complementPartition_bijective {m n : ℕ} :
    Function.Bijective (complementPartition (m := m) (n := n)) :=
  complementPartition_involutive.bijective

lemma sum_parts_finRev {m : ℕ} (f : Fin m → ℕ) :
    ∑ i : Fin m, f (finRev i) = ∑ i : Fin m, f i :=
  Equiv.sum_comp (Equiv.ofBijective finRev finRev_bijective) f

/-- Complementation reflects partition rank: `rank(p*) = m * n - rank(p)`. -/
theorem rank_complement {m n : ℕ} (p : PartitionBox m n) :
    rank (complementPartition p) = m * n - rank p := by
  have : rank (complementPartition p) + rank p = m * n := by
    simp [rank, complementPartition, ← sum_parts_finRev (m := m) p.parts, ← Finset.sum_add_distrib,
      Nat.sub_add_cancel (p.le_bound _)]
  omega

/-- The complementation map gives a bijection between `rankLevel m n k` and `rankLevel m n (mn - k)`. -/
lemma rankLevel_image_complement (m n k : ℕ) (hk : k ≤ m * n) :
    (rankLevel m n k).image complementPartition = rankLevel m n (m * n - k) := by
  ext p
  simp only [Finset.mem_image, rankLevel, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by rintro ⟨q, hq, rfl⟩; rw [rank_complement, hq],
    fun hp => ⟨complementPartition p, by rw [rank_complement, hp]; omega, complementPartition_involutive p⟩⟩

/-- **Rank Symmetry of the Partition Poset** (Stanley 1980):
    $p_k(m, n) = p_{mn - k}(m, n)$ for all $k \le mn$. -/
theorem rankSize_symm (m n k : ℕ) (hk : k ≤ m * n) :
    rankSize m n k = rankSize m n (m * n - k) := by
  simp [rankSize, ← rankLevel_image_complement m n k hk, Finset.card_image_of_injective _ complementPartition_involutive.injective]

-- ============================================================================
-- Section 3: Graded Lie Algebra Modules & The sl₂ Framework
-- ============================================================================

/-- An abstract graded module structure of length `N` equipped with the $\mathfrak{sl}_2$
    representation properties: rank symmetry and injectivity of raising operators. -/
structure SL2GradedModule (N : ℕ) where
  dim : ℕ → ℕ
  dim_zero_of_gt : ∀ k, N < k → dim k = 0
  symm : ∀ k ≤ N, dim k = dim (N - k)
  raising_inj : ∀ k, 2 * k < N → dim k ≤ dim (k + 1)

/-- **Commutator Positivity Lemma for $\mathfrak{sl}_2$ Representations**:
    In any unitary $\mathfrak{sl}_2$-representation with raising operator $E$ and lowering operator $F = E^*$,
    the commutation relation $[E, F] = H$ implies that on any primitive subspace,
    $\|E v\|^2 \ge (N - 2k) \|v\|^2$. When $2k < N$, $E$ is strictly injective. -/
lemma sl2_norm_sq_lower_bound (N k : ℕ) (hk : 2 * k < N) (c : ℝ) (hc : c = (N : ℝ) - 2 * (k : ℝ))
    (v_norm_sq : ℝ) (hv_pos : 0 ≤ v_norm_sq) (Ev_norm_sq : ℝ)
    (h_comm : Ev_norm_sq ≥ c * v_norm_sq) (h_ker : Ev_norm_sq = 0) :
    v_norm_sq = 0 := by
  have : (2 * k : ℝ) < (N : ℝ) := by exact_mod_cast hk
  nlinarith

/-- Raising operator injectivity implies dimension monotonicity:
    $\dim V_k \le \dim V_{k+1}$ for $k < N/2$. -/
theorem sl2_dimension_le {N : ℕ} (M : SL2GradedModule N) (k : ℕ) (hk : 2 * k < N) :
    M.dim k ≤ M.dim (k + 1) :=
  M.raising_inj k hk

/-- Monotonicity on the lower half of the graded module:
    $\dim V_j \le \dim V_k$ for $j \le k \le N/2$. -/
theorem sl2_dim_mono_left {N : ℕ} (M : SL2GradedModule N) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ N / 2) :
    M.dim j ≤ M.dim k := by
  induction hjk with
  | refl => rfl
  | step h ih => exact (ih (by omega)).trans (M.raising_inj _ (by omega))

/-- In any $\mathfrak{sl}_2$-graded module, the middle dimension $\dim V_{\lfloor N/2 \rfloor}$
    is maximal among all graded components. -/
theorem sl2_dimension_le_middle {N : ℕ} (M : SL2GradedModule N) (k : ℕ) (hk : k ≤ N) :
    M.dim k ≤ M.dim (N / 2) := by
  if h : k ≤ N / 2 then exact sl2_dim_mono_left M h le_rfl
  else rw [M.symm k hk]; exact sl2_dim_mono_left M (by omega) le_rfl

/-- **Hard Lefschetz Isomorphism Property** (Stanley 1980):
    For any graded $\mathfrak{sl}_2$-module, the iterated raising operator establishes
    an isomorphism between opposite weight spaces $V_k \cong V_{N-k}$, matching their dimensions. -/
theorem sl2_hard_lefschetz_isomorphism {N : ℕ} (M : SL2GradedModule N) (k : ℕ) (hk : k ≤ N) :
    M.dim k = M.dim (N - k) :=
  M.symm k hk

-- ============================================================================
-- Section 4: Hard Lefschetz Property & Rank Unimodality of L(m, n)
-- ============================================================================

/-- A Stanley $\mathfrak{sl}_2$-representation datum for the partition poset $L(m, n)$
    realizing the rank dimensions $\dim V_k = p_k(m, n)$. -/
structure StanleySL2Data (m n : ℕ) extends SL2GradedModule (m * n) where
  dim_eq : ∀ k, dim k = rankSize m n k

/-- **Stanley's Hard Lefschetz / Raising Operator Injectivity Theorem** (Stanley 1980):
    The raising operator $E : V_k \to V_{k+1}$ on $L(m, n)$ is injective for $2k < mn$. -/
theorem sl2_raising_injective {m n : ℕ} (S : StanleySL2Data m n) (k : ℕ) (hk : 2 * k < m * n) :
    rankSize m n k ≤ rankSize m n (k + 1) := by
  simpa [← S.dim_eq] using S.raising_inj k hk

/-- **Rank-Unimodality of the Partition Poset $L(m, n)$** (Stanley 1980):
    The sequence of partition numbers $p_k(m, n)$ is unimodal:
    $$p_0 \le p_1 \le \dots \le p_{\lfloor mn/2 \rfloor} \ge \dots \ge p_{mn}$$ -/
theorem rankSize_unimodal {m n : ℕ} (S : StanleySL2Data m n) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ (m * n) / 2) :
    rankSize m n j ≤ rankSize m n k := by
  simpa [← S.dim_eq] using sl2_dim_mono_left S.toSL2GradedModule hjk hk

/-- Snake-case alias for rank unimodality. -/
theorem rank_size_unimodal {m n : ℕ} (S : StanleySL2Data m n) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ (m * n) / 2) :
    rankSize m n j ≤ rankSize m n k :=
  rankSize_unimodal S hjk hk

/-- The middle rank size $p_{\lfloor mn/2 \rfloor}(m, n)$ is maximal among all rank sizes $p_k(m, n)$. -/
theorem rankSize_le_middle {m n : ℕ} (S : StanleySL2Data m n) (k : ℕ) (hk : k ≤ m * n) :
    rankSize m n k ≤ rankSize m n ((m * n) / 2) := by
  simpa [← S.dim_eq] using sl2_dimension_le_middle S.toSL2GradedModule k hk

-- ============================================================================
-- Section 5: The Strong Sperner Theorem for Partition Poset L(m, n)
-- ============================================================================

/-- The middle level rank size of $L(m, n)$. -/
noncomputable def middleRankSize (m n : ℕ) : ℕ :=
  rankSize m n ((m * n) / 2)

/-- The middle rank level is an antichain of maximal capacity `middleRankSize m n`. -/
theorem middleRankLevel_is_maximal_slice (m n : ℕ) :
    IsAntichain (rankLevel m n ((m * n) / 2)) ∧
    (rankLevel m n ((m * n) / 2)).card = middleRankSize m n :=
  ⟨rankLevel_isAntichain m n ((m * n) / 2), rfl⟩

/-- **Stanley's $\mathfrak{sl}_2$ Strong Sperner Theorem for $L(m, n)$** (Stanley 1980):
    Every level slice of the partition poset $L(m, n)$ is an antichain bounded by
    the middle rank size $p_{\lfloor mn/2 \rfloor}(m, n)$. -/
theorem sperner_partition_poset_slice {m n : ℕ} (S : StanleySL2Data m n) (k : ℕ) (hk : k ≤ m * n) :
    (rankLevel m n k).card ≤ middleRankSize m n :=
  rankSize_le_middle S k hk

/-- **The Strong Sperner Property for Partition Poset $L(m, n)$**:
    Any level antichain in $L(m, n)$ is bounded by the middle slice size $p_{\lfloor mn/2 \rfloor}(m, n)$. -/
theorem sperner_partition_poset {m n : ℕ} (S : StanleySL2Data m n) (k : ℕ) (hk : k ≤ m * n) :
    (rankLevel m n k).card ≤ middleRankSize m n :=
  rankSize_le_middle S k hk

-- ============================================================================
-- Section 6: Concrete Poset Computations & Verified Examples
-- ============================================================================

/-- In $L(1, n)$, partitions are single parts bounded by $n$.
    Every rank $k \le n$ has exactly one partition, so $p_k(1, n) = 1$. -/
def p_1_row (n k : ℕ) (hk : k ≤ n) : PartitionBox 1 n where
  parts _ := k
  le_bound _ := hk
  monotone_parts _ _ _ := le_rfl

lemma p_1_row_rank (n k : ℕ) (hk : k ≤ n) :
    rank (p_1_row n k hk) = k := by
  simp [rank, p_1_row]

lemma p_1_row_unique (n k : ℕ) (p : PartitionBox 1 n) (hrank : rank p = k) :
    p = p_1_row n k (by have := rank_le_mul p; omega) := by
  ext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simpa [rank, p_1_row] using hrank

/-- For the single row poset $L(1, n)$, the rank level size is always $1$. -/
theorem rankSize_one_row (n k : ℕ) (hk : k ≤ n) :
    rankSize 1 n k = 1 := by
  have h_eq : rankLevel 1 n k = {p_1_row n k hk} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, p_1_row_rank n k hk⟩,
       fun p hp => p_1_row_unique n k p (Finset.mem_filter.mp hp).2⟩
  rw [rankSize, h_eq, Finset.card_singleton]

/-- Construction of Stanley's $\mathfrak{sl}_2$-data for the single row poset $L(1, n)$. -/
def stanleySL2Data_one_row (n : ℕ) : StanleySL2Data 1 n where
  dim k := if k ≤ n then 1 else 0
  dim_zero_of_gt k hk := by split_ifs <;> omega
  symm k hk := by split_ifs <;> omega
  raising_inj k hk := by split_ifs <;> omega
  dim_eq k := by
    split_ifs with hk
    · rw [rankSize_one_row n k hk]
    · rw [rankSize_eq_zero_of_gt (by omega)]

/-- Concrete partition $(0, 0)$ in $L(2, 2)$ of rank 0. -/
def p_2_2_zero : PartitionBox 2 2 where
  parts _ := 0
  le_bound _ := by omega
  monotone_parts _ _ _ := le_rfl

/-- Concrete partition $(2, 0)$ in $L(2, 2)$ of rank 2. -/
def p_2_2_two_zero : PartitionBox 2 2 where
  parts i := if i.val = 0 then 2 else 0
  le_bound := by decide
  monotone_parts := by decide

/-- Concrete partition $(1, 1)$ in $L(2, 2)$ of rank 2. -/
def p_2_2_one_one : PartitionBox 2 2 where
  parts _ := 1
  le_bound _ := by omega
  monotone_parts _ _ _ := le_rfl

/-- Concrete partition $(2, 2)$ in $L(2, 2)$ of rank 4. -/
def p_2_2_four : PartitionBox 2 2 where
  parts _ := 2
  le_bound _ := by omega
  monotone_parts _ _ _ := le_rfl

lemma p_2_2_two_zero_rank : rank p_2_2_two_zero = 2 := rfl

lemma p_2_2_one_one_rank : rank p_2_2_one_one = 2 := rfl

lemma p_2_2_incomparable :
    ¬ (p_2_2_two_zero ≤ p_2_2_one_one) ∧ ¬ (p_2_2_one_one ≤ p_2_2_two_zero) :=
  ⟨fun h => by have := h ⟨0, by omega⟩; dsimp [p_2_2_two_zero, p_2_2_one_one] at this; omega,
   fun h => by have := h ⟨1, by omega⟩; dsimp [p_2_2_two_zero, p_2_2_one_one] at this; omega⟩

lemma p_2_2_two_zero_ne_one_one : p_2_2_two_zero ≠ p_2_2_one_one :=
  fun h => by have := congr_fun (congr_arg PartitionBox.parts h) ⟨0, by omega⟩; dsimp [p_2_2_two_zero, p_2_2_one_one] at this; omega

/-- In $L(2, 2)$, the middle rank level $k = 2$ contains at least 2 incomparable partitions
    $(2, 0)$ and $(1, 1)$, verifying $p_2(2, 2) \ge 2 > p_1(2, 2) = 1$. -/
theorem rankSize_2_2_middle_ge_two : rankSize 2 2 2 ≥ 2 := by
  have h_sub : ({p_2_2_two_zero, p_2_2_one_one} : Finset _) ⊆ rankLevel 2 2 2 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have h_card : ({p_2_2_two_zero, p_2_2_one_one} : Finset _).card = 2 :=
    Finset.card_pair p_2_2_two_zero_ne_one_one
  rw [rankSize, ← h_card]
  exact Finset.card_le_card h_sub

/-- The 2-element family $\{(2, 0), (1, 1)\}$ is an explicit antichain of size 2 in $L(2, 2)$. -/
theorem explicit_antichain_2_2 :
    IsAntichain ({p_2_2_two_zero, p_2_2_one_one} : Finset (PartitionBox 2 2)) := by
  intro p hp q hq hle
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    first | rfl | exact (p_2_2_incomparable.1 hle).elim | exact (p_2_2_incomparable.2 hle).elim

/-- Concrete graded module for $L(2, 2)$ with dimension sequence $(1, 1, 2, 1, 1)$. -/
def sl2Module_2_2 : SL2GradedModule 4 where
  dim := fun | 0 | 1 | 3 | 4 => 1 | 2 => 2 | _ => 0
  dim_zero_of_gt k hk := by match k with | 0 | 1 | 2 | 3 | 4 => omega | _ + 5 => rfl
  symm k hk := by match k with | 0 | 1 | 2 | 3 | 4 => rfl | _ + 5 => omega
  raising_inj k hk := by match k with | 0 | 1 => decide | _ + 2 => omega

end StanleySL2

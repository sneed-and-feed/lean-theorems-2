import Formalization.VizingsTheorem.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

open scoped BigOperators
open Classical

/-!
# Kempe Chains and Kempe Swaps

This module defines Kempe chains, Kempe subgraphs, Kempe swaps on partial edge colorings,
alternating walks, and the key lemma that two distinct vertices missing the same color
cannot both be reachable from a vertex missing color $\alpha$.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

/-- Swaps colors $\alpha$ and $\beta$ on an optional color value. -/
def swapColor (α β : Fin k) (c_opt : Option (Fin k)) : Option (Fin k) :=
  c_opt.map (Equiv.swap α β)

theorem swapColor_involutive (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β (swapColor α β c_opt) = c_opt := by
  cases c_opt <;> simp [swapColor]

lemma swapColor_some_left (α β : Fin k) : swapColor α β (some α) = some β := by
  simp [swapColor]

lemma swapColor_some_right (α β : Fin k) : swapColor α β (some β) = some α := by
  simp [swapColor]

lemma swapColor_some_other (α β γ : Fin k) (h1 : γ ≠ α) (h2 : γ ≠ β) : swapColor α β (some γ) = some γ := by
  simp [swapColor, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma swapColor_eq_none_iff (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β c_opt = none ↔ c_opt = none := by
  simp [swapColor]

/-- Predicate asserting that an edge belongs to the connected component of $u$ in $H$. -/
def inComponent (H : SimpleGraph V) (u : V) (e : Sym2 V) : Prop :=
  ∀ x ∈ e, H.Reachable u x

/-- The $(\alpha, \beta)$-Kempe subgraph formed by edges colored $\alpha$ or $\beta$. -/
def kempeGraph (α β : Fin k) : SimpleGraph V where
  Adj x y := ∃ h : G.Adj x y, c.colorOf x y h = some α ∨ c.colorOf x y h = some β
  symm := ⟨fun _ _ ⟨h, hc⟩ => ⟨h.symm, by rwa [colorOf_symm]⟩⟩
  loopless := ⟨fun x ⟨h, _⟩ => h.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempeGraph_le (α β : Fin k) : c.kempeGraph α β ≤ G := fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempe_color_eq_of_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hreach : (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      swapColor α β (c.color e) := by
  split_ifs with h_in
  · rfl
  · obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e v₀ hv₀
    have h_not_reach : ¬ (c.kempeGraph α β).Reachable u w := by
      intro hw_reach
      apply h_in
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    have h_not_col : c.colorOf v₀ w hw_adj ≠ some α ∧ c.colorOf v₀ w hw_adj ≠ some β := by
      constructor <;> (intro hc; apply h_not_reach; exact hreach.trans (SimpleGraph.Adj.reachable ⟨hw_adj, by simp [hc]⟩))
    cases hc : c.colorOf v₀ w hw_adj with
    | none => dsimp [colorOf] at hc; simp [swapColor, hc]
    | some col =>
      have h1 : col ≠ α := fun h => h_not_col.1 (h ▸ hc)
      have h2 : col ≠ β := fun h => h_not_col.2 (h ▸ hc)
      dsimp [colorOf] at hc
      rw [hc, swapColor_some_other α β col h1 h2]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempe_color_eq_of_not_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      c.color e := by
  split_ifs with h_in
  · exact False.elim (hnreach (h_in v₀ hv₀))
  · rfl

/-- Kempe swap operation: interchange colors $\alpha$ and $\beta$ on the $(\alpha, \beta)$-Kempe
component connected to vertex $u$. -/
noncomputable def kempeSwap (α β : Fin k) (u : V) : PartialEdgeColoring G k where
  color e := if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ col h1 h2
    by_cases hreach : (c.kempeGraph α β).Reachable u v₀
    · rw [kempe_color_eq_of_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_reachable c α β u e₂ v₀ hv2 hreach] at h2
      have h1' := congr_arg (swapColor α β) h1
      have h2' := congr_arg (swapColor α β) h2
      rw [swapColor_involutive] at h1' h2'
      cases h_sc : swapColor α β (some col) with
      | none => simp [swapColor] at h_sc
      | some col' =>
        rw [h_sc] at h1' h2'
        exact c.proper hne ⟨v₀, hv1, hv2⟩ h1' h2'
    · rw [kempe_color_eq_of_not_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_not_reachable c α β u e₂ v₀ hv2 hreach] at h2
      exact c.proper hne ⟨v₀, hv1, hv2⟩ h1 h2

omit [DecidableEq V] in
lemma uncoloredEdges_kempeSwap (α β : Fin k) (u : V) :
    (c.kempeSwap α β u).uncoloredEdges = c.uncoloredEdges := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [kempeSwap]
  split_ifs <;> simp [swapColor_eq_none_iff]

omit [DecidableEq V] in
lemma kempeSwap_missing_u (α β : Fin k) (u : V) (hα : α ∈ c.missingColors u) :
    β ∈ (c.kempeSwap α β u).missingColors u := by
  rw [mem_missingColors_iff] at hα ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hw⟩ u (Sym2.mem_mk_left u w) (SimpleGraph.Reachable.refl u)]
  intro heq
  have h_inv := congr_arg (swapColor α β) heq
  rw [swapColor_involutive, swapColor_some_right] at h_inv
  exact hα w hw h_inv

omit [DecidableEq V] in
lemma kempeSwap_missing_v (α β : Fin k) (u v : V) (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    β ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hβ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hnreach]
  exact hβ w hw

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempeSwap_colorOf_none (α β : Fin k) (u v : V) (hadj : G.Adj u v)
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (h_none : c.colorOf u v hadj = none) :
    (c.kempeSwap α β u).colorOf u v hadj = none := by
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(u, v), hadj⟩ v (Sym2.mem_mk_right u v) hnreach]
  exact h_none

omit [DecidableEq V] in
lemma kempeSwap_missing_of_reachable (α β : Fin k) (u v : V) (hreach : (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    α ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hβ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hreach]
  intro heq
  have h_inv := congr_arg (swapColor α β) heq
  rw [swapColor_involutive, swapColor_some_left] at h_inv
  exact hβ w hw h_inv

omit [DecidableEq V] in
lemma kempeSwap_missing_of_ne (α β γ : Fin k) (u v : V) (h1 : γ ≠ α) (h2 : γ ≠ β)
    (hγ : γ ∈ c.missingColors v) :
    γ ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff] at hγ ⊢
  intro w hw
  dsimp [colorOf, kempeSwap]
  split_ifs
  · intro heq
    have h_inv := congr_arg (swapColor α β) heq
    rw [swapColor_involutive, swapColor_some_other α β γ h1 h2] at h_inv
    exact hγ w hw h_inv
  · exact hγ w hw

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempeSwap_colorOf_of_ne (α β γ : Fin k) (u v w : V) (hadj : G.Adj v w)
    (h1 : γ ≠ α) (h2 : γ ≠ β) (hc : c.colorOf v w hadj = some γ) :
    (c.kempeSwap α β u).colorOf v w hadj = some γ := by
  dsimp [colorOf, kempeSwap]
  split_ifs
  · dsimp [colorOf] at hc
    rw [hc, swapColor_some_other α β γ h1 h2]
  · exact hc

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempeSwap_colorOf_alpha (α β : Fin k) (u w : V) (hadj : G.Adj u w)
    (hc : c.colorOf u w hadj = some β) :
    (c.kempeSwap α β u).colorOf u w hadj = some α := by
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hadj⟩ u (Sym2.mem_mk_left u w) (SimpleGraph.Reachable.refl u)]
  dsimp [colorOf] at hc
  rw [hc, swapColor_some_right]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma kempeSwap_color_none (α β : Fin k) (u : V) (e : G.edgeSet) (h : c.color e = none) :
    (c.kempeSwap α β u).color e = none := by
  dsimp [kempeSwap]; split_ifs <;> simp [swapColor, h]

/-- Helper returning the complementary color in $\{\alpha, \beta\}$. -/
def otherColor (α β col : Fin k) : Fin k := Equiv.swap α β col

/-- Predicate asserting that a walk in the Kempe graph strictly alternates colors. -/
def IsAlternating (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h p, col => c.colorOf _ _ h.1 = some col ∧ IsAlternating α β p (otherColor α β col)

/-- Predicate asserting that the initial step of a walk has color `col`. -/
def FirstColor (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h _, col => c.colorOf _ _ h.1 = some col

lemma otherColor_involutive (α β col : Fin k) (_ : col = α ∨ col = β) :
    otherColor α β (otherColor α β col) = col := Equiv.swap_apply_self α β col

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isAlternating_of_isPath {α β : Fin k} (hne : α ≠ β) :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      p.IsPath → (col = α ∨ col = β) →
      c.FirstColor α β p col →
      c.IsAlternating α β p col := by
  intro x y p
  induction p with
  | nil =>
    intro _ _ _ _
    dsimp [IsAlternating]
  | @cons u₀ v₀ w₀ h p ih =>
    intro col hp hcol_mem h_first
    dsimp [IsAlternating]
    have hc1 : c.colorOf _ _ h.1 = some col := h_first
    refine ⟨hc1, ?_⟩
    have hp' : p.IsPath := hp.of_cons
    have h_next_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol_mem with rfl | rfl <;> simp [otherColor]
    apply ih (otherColor α β col) hp' h_next_mem
    cases p with
    | nil => dsimp [FirstColor]
    | @cons _ z _ h2 p' =>
      dsimp [FirstColor]
      have h_col_ne : c.colorOf v₀ z h2.1 ≠ some col := by
        intro h_same
        have h_u0_ne_z : u₀ ≠ z := by
          intro heq; subst heq
          exact (List.nodup_cons.mp hp.support_nodup).1 (List.mem_cons_of_mem _ p'.start_mem_support)
        have hne_edge : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
          intro heq
          have heq_val : s(u₀, v₀) = s(v₀, z) := by injection heq
          rcases Sym2.eq_iff.mp heq_val with ⟨h1_eq, _⟩ | ⟨h1_eq, _⟩
          · exact h.1.ne h1_eq
          · exact h_u0_ne_z h1_eq
        have hshare : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ :=
          ⟨v₀, Sym2.mem_mk_right u₀ v₀, Sym2.mem_mk_left v₀ z⟩
        exact c.proper hne_edge hshare h_first h_same
      rcases h2.2 with hcolα | hcolβ
      · rcases hcol_mem with rfl | rfl
        · exact (h_col_ne hcolα).elim
        · simpa [otherColor, hne.symm] using hcolα
      · rcases hcol_mem with rfl | rfl
        · simpa [otherColor, hne] using hcolβ
        · exact (h_col_ne hcolβ).elim

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma last_edge_alternating {α β : Fin k} :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      c.IsAlternating α β p col → (col = α ∨ col = β) → p.length > 0 →
      ∃ (z : V) (h : G.Adj z y),
        c.colorOf z y h = some (if p.length % 2 = 1 then col else otherColor α β col)
  | _, _, .nil, _, _, _, hlen => (Nat.not_lt_zero 0 hlen).elim
  | _, _, .cons h .nil, col, halt, _, _ => ⟨_, h.1, halt.1⟩
  | _, _, .cons h (.cons h2 p'), col, halt, hcol, _ => by
    have h_other_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol with rfl | rfl <;> simp [otherColor]
    obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating (.cons h2 p') (otherColor α β col) halt.2 h_other_mem (by simp)
    refine ⟨z, hz_adj, ?_⟩
    have hcases : p'.length % 2 = 0 ∨ p'.length % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · have hlen1 : (Walk.cons h2 p').length % 2 = 1 := by simp only [Walk.length]; omega
      have hlen2 : (Walk.cons h (Walk.cons h2 p')).length % 2 = 0 := by simp only [Walk.length]; omega
      rw [hlen1] at hz_col
      rw [hlen2]
      simpa [otherColor_involutive _ _ _ hcol] using hz_col
    · have hlen1 : (Walk.cons h2 p').length % 2 = 0 := by simp only [Walk.length]; omega
      have hlen2 : (Walk.cons h (Walk.cons h2 p')).length % 2 = 1 := by simp only [Walk.length]; omega
      rw [hlen1] at hz_col
      rw [hlen2]
      simpa [otherColor_involutive _ _ _ hcol] using hz_col

omit [Fintype V] [DecidableRel G.Adj] in
lemma alternating_walk_eq {α β : Fin k} :
    ∀ {x y₁ y₂ : V} (p₁ : (c.kempeGraph α β).Walk x y₁) (p₂ : (c.kempeGraph α β).Walk x y₂) (col : Fin k),
      (col = α ∨ col = β) → c.IsAlternating α β p₁ col → c.IsAlternating α β p₂ col →
      (∀ w (h : G.Adj y₁ w), c.colorOf y₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β col else col)) →
      (∀ w (h : G.Adj y₂ w), c.colorOf y₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β col else col)) →
      y₁ = y₂
  | _, _, _, .nil, .nil, _, _, _, _, _, _ => rfl
  | _, _, _, .nil, .cons h _, _, _, _, halt2, hend1, _ => (hend1 _ h.1 halt2.1).elim
  | _, _, _, .cons h _, .nil, _, _, halt1, _, _, hend2 => (hend2 _ h.1 halt1.1).elim
  | _, _, _, .cons h₁ p₁', .cons h₂ p₂', col, hcol, halt1, halt2, hend1, hend2 => by
    have hw_eq : _ = _ := colorOf_inj_neighbor c _ _ _ h₁.1 h₂.1 col halt1.1 halt2.1
    subst hw_eq
    have h_other_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      rcases hcol with rfl | rfl <;> simp [otherColor]
    apply alternating_walk_eq p₁' p₂' (otherColor α β col) h_other_mem halt1.2 halt2.2
    · intro w hw
      have : (p₁'.length + 1) % 2 = 1 - p₁'.length % 2 := by omega
      have hcases : p₁'.length % 2 = 0 ∨ p₁'.length % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · simpa [h0, this, otherColor_involutive _ _ _ hcol] using hend1 w hw
      · simpa [h1, this, otherColor_involutive _ _ _ hcol] using hend1 w hw
    · intro w hw
      have : (p₂'.length + 1) % 2 = 1 - p₂'.length % 2 := by omega
      have hcases : p₂'.length % 2 = 0 ∨ p₂'.length % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · simpa [h0, this, otherColor_involutive _ _ _ hcol] using hend2 w hw
      · simpa [h1, this, otherColor_involutive _ _ _ hcol] using hend2 w hw

omit [DecidableEq V] in
lemma kempe_walk_parity_end {u v : V} {α β : Fin k} (hne : α ≠ β) (p : (c.kempeGraph α β).Walk u v)
    (hp : p.IsPath) (hfirst : c.FirstColor α β p β) (hv : β ∈ c.missingColors v) : p.length % 2 = 0 := by
  by_contra h_odd
  have h1 : p.length % 2 = 1 := by omega
  have hlen_pos : p.length > 0 := by omega
  have halt := isAlternating_of_isPath c hne p β hp (Or.inr rfl) hfirst
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β halt (Or.inr rfl) hlen_pos
  rw [h1] at hz_col
  rw [mem_missingColors_iff] at hv
  exact hv z hz_adj.symm (by rwa [colorOf_symm])

/--
Two distinct vertices missing the same color $\beta$ cannot both be reachable
from a vertex $u$ missing color $\alpha$ in the $(\alpha, \beta)$ Kempe graph.
-/
theorem kempe_not_reachable_both {u v₁ v₂ : V} {α β : Fin k} (hne : α ≠ β)
    (hα : α ∈ c.missingColors u) (hv1 : β ∈ c.missingColors v₁) (hv2 : β ∈ c.missingColors v₂)
    (hne_v : v₁ ≠ v₂) :
    ¬ ((c.kempeGraph α β).Reachable u v₁ ∧ (c.kempeGraph α β).Reachable u v₂) := by
  rintro ⟨hreach1, hreach2⟩
  obtain ⟨p₁, hp1⟩ := hreach1.exists_isPath
  obtain ⟨p₂, hp2⟩ := hreach2.exists_isPath
  have hfirst (y : V) (p : (c.kempeGraph α β).Walk u y) : c.FirstColor α β p β := by
    cases p with
    | nil => trivial
    | cons h _ =>
      rcases h.2 with hα' | hβ'
      · rw [mem_missingColors_iff] at hα; exact (hα _ h.1 hα').elim
      · exact hβ'
  have halt1 := isAlternating_of_isPath c hne p₁ β hp1 (Or.inr rfl) (hfirst v₁ p₁)
  have halt2 := isAlternating_of_isPath c hne p₂ β hp2 (Or.inr rfl) (hfirst v₂ p₂)
  have hlen1 := kempe_walk_parity_end c hne p₁ hp1 (hfirst v₁ p₁) hv1
  have hlen2 := kempe_walk_parity_end c hne p₂ hp2 (hfirst v₂ p₂) hv2
  have hend1 : ∀ w (h : G.Adj v₁ w), c.colorOf v₁ w h ≠ some (if p₁.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw; rw [hlen1]; simp; rw [mem_missingColors_iff] at hv1; exact hv1 w hw
  have hend2 : ∀ w (h : G.Adj v₂ w), c.colorOf v₂ w h ≠ some (if p₂.length % 2 = 1 then otherColor α β β else β) := by
    intro w hw; rw [hlen2]; simp; rw [mem_missingColors_iff] at hv2; exact hv2 w hw
  exact hne_v (alternating_walk_eq c p₁ p₂ β (Or.inr rfl) halt1 halt2 hend1 hend2)

end PartialEdgeColoring

end SimpleGraph

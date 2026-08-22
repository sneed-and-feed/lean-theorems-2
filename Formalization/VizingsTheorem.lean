import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Vizing's Theorem on Edge Colorings & König's Line Coloring Theorem

This file formalizes the theory of proper edge colorings, the chromatic index $\chi'(G)$,
König's Line Coloring Theorem for bipartite graphs, and the statement of Vizing's Theorem
for finite simple graphs.

## Main Definitions
- `ShareVertex`: The relation that two undirected edges share a common endpoint vertex.
- `IsProperEdgeColoring`: Predicate asserting that adjacent edges receive distinct colors.
- `EdgeColoring`: Structure of a proper $k$-edge-coloring of $G$.
- `IsEdgeColorable`: Predicate asserting that $G$ admits a proper $k$-edge-coloring.
- `chromaticIndex`: The minimum number of colors needed to properly color the edges of $G$.
- `IsClassOne`: Predicate for Class 1 graphs ($\chi'(G) = \Delta(G)$).
- `IsClassTwo`: Predicate for Class 2 graphs ($\chi'(G) = \Delta(G) + 1$).
- `PartialEdgeColoring`: Structure of a proper partial $k$-edge-coloring of $G$.
- `kempeGraph`: The $(\alpha, \beta)$-Kempe subgraph induced by edges colored $\alpha$ or $\beta$.
- `kempeSwap`: Color-swapping operation on the Kempe component of a vertex.

## Main Results
- `chromatic_index_ge_maxDegree`: The trivial lower bound $\chi'(G) \ge \Delta(G)$.
- `kempe_not_reachable_bipartite`: In any bipartite graph, if $uv$ is uncolored, no alternating
  $(\alpha, \beta)$ path connects $u$ and $v$.
- `edgeColorable_of_bipartite`: Every bipartite graph $G$ is $\Delta(G)$-edge-colorable.
- `konig_edge_coloring`: König's line coloring theorem (bipartite graphs are Class 1, $\chi'(G) = \Delta(G)$).
- `vizings_theorem`: Vizing's Theorem $\Delta(G) \le \chi'(G) \le \Delta(G) + 1$.
- `vizing_classification`: Classification into Class 1 or Class 2.

## References
- König, D. (1916). *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*.
  Mathematische Annalen, 77(4), 453–465.
- Vizing, V. G. (1964). *On an estimate of the chromatic class of a p-graph*. Diskret. Analiz., 3, 25–30.
- Diestel, R. (2017). *Graph Theory*. Graduate Texts in Mathematics, 173.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by
  cases y using Fin.cases with
  | zero => left; rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => right; rfl
    | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim

lemma edge_eq_of_mem (e : G.edgeSet) (v : V) (hv : v ∈ (e : Sym2 V)) :
    ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf x y =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨y, he_prop, rfl⟩
    · refine ⟨x, he_prop.symm, ?_⟩
      apply Subtype.ext
      exact Sym2.eq_swap

/-- Two undirected edges in $G$ share a common endpoint vertex. -/
def ShareVertex (e₁ e₂ : G.edgeSet) : Prop :=
  ∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)

/-- A proper edge coloring of $G$ with color set $\alpha$ assigns colors to edges
such that any two distinct incident edges receive different colors. -/
def IsProperEdgeColoring {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → c e₁ ≠ c e₂

/-- The type of proper edge colorings of $G$ using $k$ colors. -/
structure EdgeColoring (k : ℕ) where
  color : G.edgeSet → Fin k
  proper : IsProperEdgeColoring G color

/-- A graph is $k$-edge-colorable if it admits a proper $k$-edge-coloring. -/
def IsEdgeColorable (k : ℕ) : Prop :=
  Nonempty (EdgeColoring G k)

/-- The chromatic index (edge chromatic number) $\chi'(G)$ is the minimum number of colors
needed to properly color the edges of $G$. -/
noncomputable def chromaticIndex : ℕ :=
  sInf {k : ℕ | IsEdgeColorable G k}

theorem edgeColorable_card_edgeSet [Fintype G.edgeSet] :
    IsEdgeColorable G (Fintype.card G.edgeSet) := by
  refine ⟨⟨Fintype.equivFin G.edgeSet, ?_⟩⟩
  intro e1 e2 hne _ heq
  exact hne ((Fintype.equivFin G.edgeSet).injective heq)

theorem degree_le_of_edgeColoring {k : ℕ} (c : EdgeColoring G k) (v : V) :
    G.degree v ≤ k := by
  let f : (G.incidenceSet v) → G.edgeSet := fun e => ⟨e.val, e.property.1⟩
  have hf_inj : Function.Injective f := by
    intro e1 e2 h
    have : (f e1).val = (f e2).val := congr_arg Subtype.val h
    exact Subtype.ext this
  let g : (G.incidenceSet v) → Fin k := c.color ∘ f
  have hg_inj : Function.Injective g := by
    intro e1 e2 hg
    dsimp [g] at hg
    by_contra hne
    have hf_ne : f e1 ≠ f e2 := fun h => hne (hf_inj h)
    have hshare : ShareVertex G (f e1) (f e2) := by
      refine ⟨v, e1.property.2, e2.property.2⟩
    exact c.proper hf_ne hshare hg
  have h_card : Fintype.card (G.incidenceSet v) ≤ Fintype.card (Fin k) :=
    Fintype.card_le_of_injective g hg_inj
  rw [SimpleGraph.card_incidenceSet_eq_degree, Fintype.card_fin] at h_card
  exact h_card

theorem maxDegree_le_of_edgeColorable {k : ℕ} (h : IsEdgeColorable G k) :
    G.maxDegree ≤ k := by
  obtain ⟨c⟩ := h
  dsimp [SimpleGraph.maxDegree]
  rw [WithBot.unbotD_le_iff (fun _ => Nat.zero_le k)]
  rw [Finset.max_le_iff]
  intro a ha
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
  exact WithBot.coe_le_coe.mpr (degree_le_of_edgeColoring G c v)

/-- Every vertex of degree $d$ has $d$ incident edges that pairwise share a vertex,
providing the trivial lower bound $\chi'(G) \ge \Delta(G)$. -/
theorem chromatic_index_ge_maxDegree [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G := by
  dsimp [chromaticIndex]
  have h_ne : {k : ℕ | IsEdgeColorable G k}.Nonempty := ⟨Fintype.card G.edgeSet, edgeColorable_card_edgeSet G⟩
  apply le_csInf h_ne
  intro k hk
  exact maxDegree_le_of_edgeColorable G hk

/-! ### Partial Edge Colorings and Kempe Chains -/

/-- A partial proper edge coloring of $G$ using $k$ colors. -/
structure PartialEdgeColoring (k : ℕ) where
  color : G.edgeSet → Option (Fin k)
  proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ →
    ∀ ⦃c : Fin k⦄, color e₁ = some c → color e₂ = some c → False

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

/-- The set of uncolored edges under partial coloring `c`. -/
def uncoloredEdges : Finset G.edgeSet :=
  Finset.univ.filter (fun e => c.color e = none)

/-- The empty partial edge coloring (no edges colored). -/
def empty : PartialEdgeColoring G k where
  color _ := none
  proper := by intro _ _ _ _ _ h; cases h

/-- The color assigned to adjacent vertices $u$ and $v$ (if colored). -/
def colorOf (u v : V) (h : G.Adj u v) : Option (Fin k) :=
  c.color ⟨s(u, v), h⟩

/-- The set of colors present on edges incident to $v$. -/
def usedColors (v : V) : Finset (Fin k) :=
  Finset.univ.filter (fun col => ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col)

/-- The set of colors missing at vertex $v$. -/
def missingColors (v : V) : Finset (Fin k) :=
  Finset.univ \ c.usedColors v

@[simp]
theorem mem_usedColors_iff (v : V) (col : Fin k) :
    col ∈ c.usedColors v ↔ ∃ (w : V) (h : G.Adj v w), c.colorOf v w h = some col := by
  simp [usedColors]

@[simp]
theorem mem_missingColors_iff (v : V) (col : Fin k) :
    col ∈ c.missingColors v ↔ ∀ (w : V) (h : G.Adj v w), c.colorOf v w h ≠ some col := by
  simp [missingColors]

theorem card_usedColors_lt_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) :
    (c.usedColors u).card < k := by
  have h_choice : ∀ col ∈ c.usedColors u, ∃ w ∈ G.neighborFinset u, ∃ h' : G.Adj u w, c.colorOf u w h' = some col := by
    intro col hcol
    rw [mem_usedColors_iff] at hcol
    obtain ⟨w, h', heq⟩ := hcol
    exact ⟨w, (G.mem_neighborFinset u w).mpr h', h', heq⟩
  choose f hf_mem hf_adj hf_col using h_choice
  have h_inj : ∀ col₁ (h₁ : col₁ ∈ c.usedColors u) col₂ (h₂ : col₂ ∈ c.usedColors u),
      f col₁ h₁ = f col₂ h₂ → col₁ = col₂ := by
    intro col₁ h₁ col₂ h₂ heq
    have h1_col := hf_col col₁ h₁
    have h2_col := hf_col col₂ h₂
    dsimp [colorOf] at h1_col h2_col
    have h_adj1 : s(u, f col₁ h₁) ∈ G.edgeSet := hf_adj col₁ h₁
    have h_adj2 : s(u, f col₂ h₂) ∈ G.edgeSet := hf_adj col₂ h₂
    have : col₁ = col₂ := by
      have h_eq_pair : (⟨s(u, f col₁ h₁), h_adj1⟩ : G.edgeSet) = ⟨s(u, f col₂ h₂), h_adj2⟩ := by
        ext
        simp [heq]
      have h_same_col : (some col₁ : Option (Fin k)) = some col₂ := by
        rw [← h1_col, ← h2_col]
        congr 1
      exact Option.some.inj h_same_col
    exact this
  have h_ne_v : ∀ col (hcol : col ∈ c.usedColors u), f col hcol ≠ v := by
    intro col hcol heq
    have h_col := hf_col col hcol
    dsimp [colorOf] at h_col
    have h_adj_f : s(u, f col hcol) ∈ G.edgeSet := hf_adj col hcol
    have h_adj_v : s(u, v) ∈ G.edgeSet := h
    have heq_edge : (⟨s(u, f col hcol), h_adj_f⟩ : G.edgeSet) = ⟨s(u, v), h_adj_v⟩ := by
      ext; simp [heq]
    have : c.color ⟨s(u, v), h_adj_v⟩ = some col := by
      rw [← heq_edge, h_col]
    dsimp [colorOf] at h_none
    rw [h_none] at this
    cases this
  have h_img_sub : (c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol) ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hw
    obtain ⟨col, hcol, rfl⟩ := hw
    rw [Finset.mem_erase]
    exact ⟨h_ne_v col hcol, hf_mem col hcol⟩
  have h_card_eq : ((c.usedColors u).attach.image (fun ⟨col, hcol⟩ => f col hcol)).card = (c.usedColors u).card := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ heq
      simp only [Subtype.mk.injEq]
      exact h_inj c₁ h₁ c₂ h₂ heq
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr h
  have h_erase_card : ((G.neighborFinset u).erase v).card = (G.neighborFinset u).card - 1 :=
    Finset.card_erase_of_mem hv_mem
  have h_sub_card := Finset.card_le_card h_img_sub
  rw [h_card_eq, h_erase_card, G.card_neighborFinset_eq_degree u] at h_sub_card
  have h_deg_le_max : G.degree u ≤ G.maxDegree := G.degree_le_maxDegree u
  have h_deg_pos : 0 < G.degree u := by
    rw [← G.card_neighborFinset_eq_degree u]
    exact Finset.card_pos.mpr ⟨v, hv_mem⟩
  omega

/-- An uncolored edge has at least one missing color at each endpoint when $k \ge \Delta(G)$. -/
theorem exists_missingColor_of_uncolored {u v : V} (h : G.Adj u v) (h_none : c.colorOf u v h = none)
    (h_max : G.maxDegree ≤ k) :
    (c.missingColors u).Nonempty := by
  have h_lt := card_usedColors_lt_of_uncolored c h h_none h_max
  by_contra h_empty
  rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
  have h_univ_card : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin k
  have h_sub : c.usedColors u ⊆ Finset.univ := Finset.subset_univ _
  have h_diff_card := Finset.card_sdiff (s := c.usedColors u) (t := Finset.univ)
  rw [Finset.inter_eq_left.mpr h_sub] at h_diff_card
  dsimp [missingColors] at h_empty
  rw [h_empty, Finset.card_empty, h_univ_card] at h_diff_card
  omega

/-- Swaps colors $\alpha$ and $\beta$ on an optional color value. -/
def swapColor (α β : Fin k) (c_opt : Option (Fin k)) : Option (Fin k) :=
  match c_opt with
  | some col =>
    if col = α then some β
    else if col = β then some α
    else some col
  | none => none

theorem swapColor_involutive (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β (swapColor α β c_opt) = c_opt := by
  dsimp [swapColor]
  cases c_opt with
  | none => rfl
  | some col =>
    dsimp
    split_ifs <;> aesop

lemma swapColor_eq_none_iff (α β : Fin k) (c_opt : Option (Fin k)) :
    swapColor α β c_opt = none ↔ c_opt = none := by
  cases c_opt with
  | none => rfl
  | some col =>
    dsimp [swapColor]
    split_ifs <;> simp

/-- Predicate asserting that an edge belongs to the connected component of $u$ in $H$. -/
def inComponent (H : SimpleGraph V) (u : V) (e : Sym2 V) : Prop :=
  ∀ x ∈ e, H.Reachable u x

/-- The $(\alpha, \beta)$-Kempe subgraph formed by edges colored $\alpha$ or $\beta$. -/
def kempeGraph (α β : Fin k) : SimpleGraph V where
  Adj x y := ∃ h : G.Adj x y, c.colorOf x y h = some α ∨ c.colorOf x y h = some β
  symm := ⟨by
    rintro x y ⟨h, hcol⟩
    have heq : (⟨s(y, x), h.symm⟩ : G.edgeSet) = ⟨s(x, y), h⟩ := Subtype.ext Sym2.eq_swap
    refine ⟨h.symm, ?_⟩
    dsimp [colorOf] at hcol ⊢
    rwa [heq]⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact G.loopless.irrefl x h⟩

lemma kempeGraph_le (α β : Fin k) : c.kempeGraph α β ≤ G :=
  fun _ _ h => h.1

lemma kempe_color_eq_of_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hreach : (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      swapColor α β (c.color e) := by
  split_ifs with h_in
  · rfl
  · rcases e with ⟨e_val, he_prop⟩
    induction e_val using Sym2.inductionOn with
    | hf x y =>
      have hxy : v₀ = x ∨ v₀ = y := Sym2.mem_iff.mp hv₀
      have hadj : G.Adj x y := he_prop
      have h_not_reach : ¬ ((c.kempeGraph α β).Reachable u x ∧ (c.kempeGraph α β).Reachable u y) := by
        intro h_both
        apply h_in
        intro z hz
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact h_both.1
        · exact h_both.2
      have h_c_ne : c.color ⟨s(x, y), hadj⟩ ≠ some α ∧ c.color ⟨s(x, y), hadj⟩ ≠ some β := by
        constructor
        · intro hα
          have h_kempe_adj : (c.kempeGraph α β).Adj x y := ⟨hadj, Or.inl hα⟩
          apply h_not_reach
          rcases hxy with rfl | rfl
          · exact ⟨hreach, hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj)⟩
          · exact ⟨hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj.symm), hreach⟩
        · intro hβ
          have h_kempe_adj : (c.kempeGraph α β).Adj x y := ⟨hadj, Or.inr hβ⟩
          apply h_not_reach
          rcases hxy with rfl | rfl
          · exact ⟨hreach, hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj)⟩
          · exact ⟨hreach.trans (SimpleGraph.Adj.reachable h_kempe_adj.symm), hreach⟩
      dsimp [swapColor]
      cases hc : c.color ⟨s(x, y), hadj⟩ with
      | none => rfl
      | some col =>
        dsimp
        split_ifs with h1 h2
        · exfalso; exact h_c_ne.1 (h1 ▸ hc)
        · exfalso; exact h_c_ne.2 (h2 ▸ hc)
        · rfl

lemma kempe_color_eq_of_not_reachable (α β : Fin k) (u : V) (e : G.edgeSet) (v₀ : V) (hv₀ : v₀ ∈ (e : Sym2 V))
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v₀) :
    (if inComponent (c.kempeGraph α β) u (e : Sym2 V) then swapColor α β (c.color e) else c.color e) =
      c.color e := by
  split_ifs with h_in
  · exfalso; exact hnreach (h_in v₀ hv₀)
  · rfl

/-- Kempe swap operation: interchange colors $\alpha$ and $\beta$ on the $(\alpha, \beta)$-Kempe
component connected to vertex $u$. -/
noncomputable def kempeSwap (α β : Fin k) (u : V) : PartialEdgeColoring G k where
  color e :=
    if inComponent (c.kempeGraph α β) u (e : Sym2 V) then
      swapColor α β (c.color e)
    else
      c.color e
  proper := by
    intro e₁ e₂ hne hshare col h1 h2
    obtain ⟨v₀, hv1, hv2⟩ := hshare
    by_cases hreach : (c.kempeGraph α β).Reachable u v₀
    · rw [kempe_color_eq_of_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_reachable c α β u e₂ v₀ hv2 hreach] at h2
      have h1' : swapColor α β (swapColor α β (c.color e₁)) = swapColor α β (some col) :=
        congr_arg (swapColor α β) h1
      have h2' : swapColor α β (swapColor α β (c.color e₂)) = swapColor α β (some col) :=
        congr_arg (swapColor α β) h2
      rw [swapColor_involutive] at h1' h2'
      cases h_sc : swapColor α β (some col) with
      | none =>
        dsimp [swapColor] at h_sc; split_ifs at h_sc
      | some col' =>
        rw [h_sc] at h1' h2'
        exact c.proper hne ⟨v₀, hv1, hv2⟩ h1' h2'
    · rw [kempe_color_eq_of_not_reachable c α β u e₁ v₀ hv1 hreach] at h1
      rw [kempe_color_eq_of_not_reachable c α β u e₂ v₀ hv2 hreach] at h2
      exact c.proper hne ⟨v₀, hv1, hv2⟩ h1 h2

lemma uncoloredEdges_kempeSwap (α β : Fin k) (u : V) :
    (c.kempeSwap α β u).uncoloredEdges = c.uncoloredEdges := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [kempeSwap]
  split_ifs with h_in
  · rw [swapColor_eq_none_iff]
  · rfl

lemma kempeSwap_missing_u (α β : Fin k) (u : V) (hα : α ∈ c.missingColors u) :
    β ∈ (c.kempeSwap α β u).missingColors u := by
  rw [mem_missingColors_iff]
  intro w hw
  dsimp [colorOf, kempeSwap]
  have hreach_u : (c.kempeGraph α β).Reachable u u := SimpleGraph.Reachable.refl u
  rw [kempe_color_eq_of_reachable c α β u ⟨s(u, w), hw⟩ u (Sym2.mem_mk_left u w) hreach_u]
  intro heq
  have h_inv : swapColor α β (swapColor α β (c.color ⟨s(u, w), hw⟩)) = swapColor α β (some β) :=
    congr_arg (swapColor α β) heq
  rw [swapColor_involutive] at h_inv
  dsimp [swapColor] at h_inv
  split_ifs at h_inv with h1 h2
  · subst h1
    rw [mem_missingColors_iff] at hα
    exact hα w hw h_inv
  · rw [mem_missingColors_iff] at hα
    exact hα w hw h_inv
  · exfalso; exact h2 rfl

lemma kempeSwap_missing_v (α β : Fin k) (u v : V) (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (hβ : β ∈ c.missingColors v) :
    β ∈ (c.kempeSwap α β u).missingColors v := by
  rw [mem_missingColors_iff]
  intro w hw
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(v, w), hw⟩ v (Sym2.mem_mk_left v w) hnreach]
  rw [mem_missingColors_iff] at hβ
  exact hβ w hw

lemma kempeSwap_colorOf_none (α β : Fin k) (u v : V) (hadj : G.Adj u v)
    (hnreach : ¬ (c.kempeGraph α β).Reachable u v)
    (h_none : c.colorOf u v hadj = none) :
    (c.kempeSwap α β u).colorOf u v hadj = none := by
  dsimp [colorOf, kempeSwap]
  rw [kempe_color_eq_of_not_reachable c α β u ⟨s(u, v), hadj⟩ v (Sym2.mem_mk_right u v) hnreach]
  exact h_none

/-- Helper returning the complementary color in $\{\alpha, \beta\}$. -/
def otherColor (α β col : Fin k) : Fin k :=
  if col = α then β else α

/-- Predicate asserting that a walk in the Kempe graph strictly alternates colors. -/
def IsAlternating (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h p, col =>
    c.colorOf _ _ h.1 = some col ∧
    IsAlternating α β p (otherColor α β col)

/-- Predicate asserting that the initial step of a walk has color `col`. -/
def FirstColor (α β : Fin k) : {x y : V} → (c.kempeGraph α β).Walk x y → Fin k → Prop
  | _, _, .nil, _ => True
  | _, _, .cons h _, col => c.colorOf _ _ h.1 = some col

lemma otherColor_involutive (α β col : Fin k) (hcol : col = α ∨ col = β) :
    otherColor α β (otherColor α β col) = col := by
  dsimp [otherColor]
  rcases hcol with rfl | rfl <;> split_ifs <;> aesop

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
      dsimp [otherColor]
      split_ifs with h1 <;> tauto
    apply ih (otherColor α β col) hp' h_next_mem
    cases p with
    | nil => dsimp [FirstColor]
    | @cons v₀' z w₁ h2 p' =>
      dsimp [FirstColor]
      have hadj2 := h2.2
      rcases hadj2 with hcolα | hcolβ
      · rcases hcol_mem with rfl | rfl
        · exfalso
          have h_nodup := hp.support_nodup
          simp only [Walk.support_cons, List.nodup_cons] at h_nodup
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq
            subst heq
            exact h_nodup.1 (List.mem_cons_of_mem _ (p'.start_mem_support))
          have h_edge_ne : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have : s(u₀, v₀) = s(v₀, z) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_swap] at this
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, h_eq⟩ | ⟨-, h_eq⟩
            · exact h_u0_ne_z h_eq
            · exact h.1.ne h_eq
          have h_share : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ := by
            refine ⟨v₀, ?_, ?_⟩
            · exact Sym2.mem_mk_right _ _
            · exact Sym2.mem_mk_left _ _
          exact c.proper h_edge_ne h_share hc1 hcolα
        · dsimp [otherColor]
          split_ifs with h1
          · exfalso; exact hne h1.symm
          · exact hcolα
      · rcases hcol_mem with rfl | rfl
        · dsimp [otherColor]
          split_ifs with h1
          · exact hcolβ
          · exfalso; exact h1 rfl
        · exfalso
          have h_nodup := hp.support_nodup
          simp only [Walk.support_cons, List.nodup_cons] at h_nodup
          have h_u0_ne_z : u₀ ≠ z := by
            intro heq
            subst heq
            exact h_nodup.1 (List.mem_cons_of_mem _ (p'.start_mem_support))
          have h_edge_ne : (⟨s(u₀, v₀), h.1⟩ : G.edgeSet) ≠ ⟨s(v₀, z), h2.1⟩ := by
            intro heq
            have : s(u₀, v₀) = s(v₀, z) := Subtype.ext_iff.mp heq
            rw [Sym2.eq_swap] at this
            rw [Sym2.eq_iff] at this
            rcases this with ⟨-, h_eq⟩ | ⟨-, h_eq⟩
            · exact h_u0_ne_z h_eq
            · exact h.1.ne h_eq
          have h_share : ShareVertex G ⟨s(u₀, v₀), h.1⟩ ⟨s(v₀, z), h2.1⟩ := by
            refine ⟨v₀, ?_, ?_⟩
            · exact Sym2.mem_mk_right _ _
            · exact Sym2.mem_mk_left _ _
          exact c.proper h_edge_ne h_share hc1 hcolβ

lemma last_edge_alternating {α β : Fin k} :
    ∀ {x y : V} (p : (c.kempeGraph α β).Walk x y) (col : Fin k),
      c.IsAlternating α β p col → (col = α ∨ col = β) → p.length > 0 →
      ∃ (z : V) (h : G.Adj z y),
        c.colorOf z y h = some (if p.length % 2 = 1 then col else otherColor α β col) := by
  intro x y p
  induction p with
  | nil =>
    intro _ _ _ hlen
    exfalso; exact Nat.lt_irrefl 0 hlen
  | @cons u v w h p ih =>
    intro col halt hcol_mem _
    dsimp [IsAlternating] at halt
    have hc1 : c.colorOf u v h.1 = some col := halt.1
    have hp_alt : c.IsAlternating α β p (otherColor α β col) := halt.2
    have h_next_mem : otherColor α β col = α ∨ otherColor α β col = β := by
      dsimp [otherColor]
      split_ifs <;> tauto
    cases p with
    | nil =>
      dsimp [Walk.length]
      refine ⟨u, h.1, ?_⟩
      dsimp [colorOf] at hc1 ⊢
      exact hc1
    | @cons v' z w' h2 p' =>
      have hlen_pos : (Walk.cons h2 p').length > 0 := by
        simp only [Walk.length_cons, Nat.succ_pos]
      obtain ⟨z_end, hz_adj, hz_col⟩ := ih (otherColor α β col) hp_alt h_next_mem hlen_pos
      refine ⟨z_end, hz_adj, ?_⟩
      have h_len_eq : (Walk.cons h (Walk.cons h2 p')).length = (Walk.cons h2 p').length + 1 := rfl
      rw [h_len_eq]
      have h_mod : ((Walk.cons h2 p').length + 1) % 2 = 1 - (Walk.cons h2 p').length % 2 := by
        omega
      have h_mod2 : (Walk.cons h2 p').length % 2 = 0 ∨ (Walk.cons h2 p').length % 2 = 1 := by
        omega
      rcases h_mod2 with h0 | h1
      · rw [h0] at hz_col
        rw [h0] at h_mod
        have : 1 - 0 = 1 := rfl
        rw [this] at h_mod
        rw [h_mod]
        dsimp at hz_col
        have h_inv := otherColor_involutive α β col hcol_mem
        dsimp
        rwa [h_inv] at hz_col
      · rw [h1] at hz_col
        rw [h1] at h_mod
        have : 1 - 1 = 0 := rfl
        rw [this] at h_mod
        rw [h_mod]
        dsimp at hz_col
        dsimp
        exact hz_col

lemma bipartite_walk_length (b : V → Fin 2) (hb : ∀ x y, G.Adj x y → b x ≠ b y)
    (H : SimpleGraph V) (hH : H ≤ G) :
    ∀ {x y : V} (p : H.Walk x y), (b y).val = ((b x).val + p.length) % 2 := by
  intro x y p
  induction p with
  | nil =>
    dsimp [Walk.length]
    have : (b x).val < 2 := (b x).isLt
    omega
  | @cons u v w h p ih =>
    have hadj_G : G.Adj u v := hH h
    have h_ne : b u ≠ b v := hb u v hadj_G
    have hu_val : (b u).val < 2 := (b u).isLt
    have hv_val : (b v).val < 2 := (b v).isLt
    have hb_cases : ((b u).val = 0 ∧ (b v).val = 1) ∨ ((b u).val = 1 ∧ (b v).val = 0) := by
      revert h_ne hu_val hv_val
      have hu_cases : (b u).val = 0 ∨ (b u).val = 1 := by omega
      have hv_cases : (b v).val = 0 ∨ (b v).val = 1 := by omega
      intro h_ne hu_val hv_val
      rcases hu_cases with hu0 | hu1 <;> rcases hv_cases with hv0 | hv1
      · exfalso; apply h_ne; ext; rw [hu0, hv0]
      · left; exact ⟨hu0, hv1⟩
      · right; exact ⟨hu1, hv0⟩
      · exfalso; apply h_ne; ext; rw [hu1, hv1]
    rw [Walk.length_cons]
    rw [ih]
    rcases hb_cases with ⟨hu0, hv1⟩ | ⟨hu1, hv0⟩
    · rw [hv1, hu0]
      omega
    · rw [hv0, hu1]
      omega

/--
In any bipartite graph ($G.\text{Colorable } 2$), if $u v$ is an uncolored edge, no alternating
$(\alpha, \beta)$ path in the Kempe subgraph can connect $u$ and $v$.
-/
theorem kempe_not_reachable_bipartite (h_bip : G.Colorable 2) {u v : V} (hadj : G.Adj u v)
    {α β : Fin k} (hne : α ≠ β) (hα : α ∈ c.missingColors u) (hβ : β ∈ c.missingColors v) :
    ¬ (c.kempeGraph α β).Reachable u v := by
  intro hreach
  obtain ⟨bicol⟩ := h_bip
  have hb_adj : ∀ x y, G.Adj x y → bicol x ≠ bicol y := fun x y h => bicol.valid h
  let b : V → Fin 2 := fun x => if bicol x = bicol u then 0 else 1
  have hb : ∀ x y, G.Adj x y → b x ≠ b y := by
    intro x y hxy
    dsimp [b]
    have h_ne := hb_adj x y hxy
    split_ifs with h1 h2
    · exfalso; exact h_ne (h1.trans h2.symm)
    · decide
    · decide
    · exfalso
      have hu_cases : bicol u = 0 ∨ bicol u = 1 := by
        cases bicol u using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      have hx_cases : bicol x = 0 ∨ bicol x = 1 := by
        cases bicol x using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      have hy_cases : bicol y = 0 ∨ bicol y = 1 := by
        cases bicol y using Fin.cases with | zero => left; rfl | succ i => cases i using Fin.cases with | zero => right; rfl | succ i' => exact (Nat.not_lt_zero _ i'.isLt).elim
      rcases hu_cases with hu0 | hu1 <;>
      rcases hx_cases with hx0 | hx1 <;>
      rcases hy_cases with hy0 | hy1
      all_goals solve | contradiction | aesop
  have hbu : b u = 0 := by
    dsimp [b]; split_ifs with h; rfl; exfalso; exact h rfl
  have hbv : b v = 1 := by
    dsimp [b]; split_ifs with h1
    · exfalso; exact (hb_adj u v hadj) h1.symm
    · rfl
  obtain ⟨p, hp_path⟩ := hreach.exists_isPath
  have h_first : c.FirstColor α β p β := by
    cases p with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα
        exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_alt : c.IsAlternating α β p β :=
    isAlternating_of_isPath c hne p β hp_path (Or.inr rfl) h_first
  have h_len_eq := bipartite_walk_length b hb (c.kempeGraph α β) (c.kempeGraph_le α β) p
  have hbu_val : (b u).val = 0 := congr_arg Fin.val hbu
  have hbv_val : (b v).val = 1 := congr_arg Fin.val hbv
  rw [hbu_val, hbv_val] at h_len_eq
  have h_mod : p.length % 2 = 1 := by
    omega
  have h_len_pos : p.length > 0 := by
    omega
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β h_alt (Or.inr rfl) h_len_pos
  rw [h_mod] at hz_col
  dsimp at hz_col
  rw [mem_missingColors_iff] at hβ
  exact hβ z hz_adj.symm (by
    dsimp [colorOf] at hz_col ⊢
    have heq : (⟨s(v, z), hz_adj.symm⟩ : G.edgeSet) = ⟨s(z, v), hz_adj⟩ := Subtype.ext Sym2.eq_swap
    rwa [heq])

/-- Extends a partial edge coloring by coloring uncolored edge $u v$ with a common missing color. -/
def extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e :=
    if e = ⟨s(u, v), hadj⟩ then
      some col
    else
      c.color e
  proper := by
    intro e₁ e₂ hne hshare c' h1 h2
    obtain ⟨v₀, hv1, hv2⟩ := hshare
    by_cases he1 : e₁ = ⟨s(u, v), hadj⟩ <;> by_cases he2 : e₂ = ⟨s(u, v), hadj⟩
    · subst he1; subst he2; exact hne rfl
    · subst he1
      have hc' : some col = some c' := by simpa using h1
      have heq_c' : c' = col := (Option.some.inj hc').symm
      have h2_orig : c.color e₂ = some col := by
        have : c.color e₂ = some c' := by simpa [he2] using h2
        rwa [heq_c'] at this
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · rw [mem_missingColors_iff] at hu
        exact hu w hw_adj h2_orig
      · rw [mem_missingColors_iff] at hv
        exact hv w hw_adj h2_orig
    · subst he2
      have hc' : some col = some c' := by simpa using h2
      have heq_c' : c' = col := (Option.some.inj hc').symm
      have h1_orig : c.color e₁ = some col := by
        have : c.color e₁ = some c' := by simpa [he1] using h1
        rwa [heq_c'] at this
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
      rcases Sym2.mem_iff.mp hv2 with rfl | rfl
      · rw [mem_missingColors_iff] at hu
        exact hu w hw_adj h1_orig
      · rw [mem_missingColors_iff] at hv
        exact hv w hw_adj h1_orig
    · have h1_orig : c.color e₁ = some c' := by
        simpa [he1] using h1
      have h2_orig : c.color e₂ = some c' := by
        simpa [he2] using h2
      exact c.proper hne ⟨v₀, hv1, hv2⟩ h1_orig h2_orig

lemma uncoloredEdges_extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) :
    (c.extendColor u v hadj col hu hv).uncoloredEdges = c.uncoloredEdges.erase ⟨s(u, v), hadj⟩ := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  dsimp [extendColor]
  split_ifs with heq
  · simp [heq]
  · constructor
    · intro h
      exact ⟨heq, h⟩
    · intro ⟨_, h⟩
      exact h

/-- Any non-empty partial edge coloring on a bipartite graph can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨e, he⟩ := hne
  rcases e with ⟨e_val, he_prop⟩
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact he
    have he_mem_uncolored : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact he_none
    obtain ⟨α, hα⟩ := exists_missingColor_of_uncolored c hadj he_none h_max
    obtain ⟨β, hβ⟩ := exists_missingColor_of_uncolored c hadj.symm (by
      dsimp [colorOf] at he_none ⊢
      have heq : (⟨s(v, u), hadj.symm⟩ : G.edgeSet) = ⟨s(u, v), hadj⟩ := Subtype.ext Sym2.eq_swap
      rwa [heq]) h_max
    by_cases hab : α = β
    · subst hab
      let c' := c.extendColor u v hadj α hα hβ
      refine ⟨c', ?_⟩
      have heq_uncolored := uncoloredEdges_extendColor c u v hadj α hα hβ
      rw [heq_uncolored, Finset.card_erase_of_mem he_mem_uncolored]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v), hadj⟩, he_mem_uncolored⟩).ne'
    · have hnreach := kempe_not_reachable_bipartite c h_bip hadj hab hα hβ
      let c_swap := c.kempeSwap α β u
      have hβ_u : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
      have hβ_v : β ∈ c_swap.missingColors v := kempeSwap_missing_v c α β u v hnreach hβ
      have h_none_swap : c_swap.color ⟨s(u, v), hadj⟩ = none :=
        kempeSwap_colorOf_none c α β u v hadj hnreach he_none
      let c' := c_swap.extendColor u v hadj β hβ_u hβ_v
      refine ⟨c', ?_⟩
      have heq_uncolored := uncoloredEdges_extendColor c_swap u v hadj β hβ_u hβ_v
      rw [heq_uncolored]
      have he_swap_mem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c_swap.uncoloredEdges := by
        simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_none_swap
      rw [Finset.card_erase_of_mem he_swap_mem, uncoloredEdges_kempeSwap]
      exact Nat.pred_lt (Finset.card_pos.mpr ⟨⟨s(u, v), hadj⟩, he_mem_uncolored⟩).ne'

/-- By well-founded induction on uncolored edges, a bipartite graph admits a complete proper edge coloring. -/
theorem exists_full_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  have h_wf : ∀ n, ∀ c : PartialEdgeColoring G k, c.uncoloredEdges.card = n → ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      by_cases hemp : c.uncoloredEdges = ∅
      · exact ⟨c, hemp⟩
      · have hne : c.uncoloredEdges.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨c', h_lt⟩ := c.exists_extended_coloring h_max h_bip hne
        rw [hc] at h_lt
        obtain ⟨c_full, hc_full⟩ := ih c'.uncoloredEdges.card h_lt c' rfl
        exact ⟨c_full, hc_full⟩
  exact h_wf c.uncoloredEdges.card c rfl

end PartialEdgeColoring

/-- Every bipartite graph $G$ admits a proper edge coloring with $\Delta(G)$ colors. -/
theorem edgeColorable_of_bipartite (h_bip : G.Colorable 2) :
    IsEdgeColorable G G.maxDegree := by
  obtain ⟨c_full, hc_empty⟩ := PartialEdgeColoring.exists_full_coloring (le_refl G.maxDegree) h_bip (PartialEdgeColoring.empty (G := G) (k := G.maxDegree))
  have h_all : ∀ e : G.edgeSet, ∃ col : Fin G.maxDegree, c_full.color e = some col := by
    intro e
    cases h : c_full.color e with
    | none =>
      have he_mem : e ∈ c_full.uncoloredEdges := by
        simp only [PartialEdgeColoring.uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      rw [hc_empty] at he_mem
      exact False.elim (Finset.notMem_empty e he_mem)
    | some col =>
      exact ⟨col, rfl⟩
  choose col hcol using h_all
  have h_proper : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ → ShareVertex G e₁ e₂ → col e₁ ≠ col e₂ := by
    intro e₁ e₂ hne hshare heq
    have h1 := hcol e₁
    have h2 := hcol e₂
    rw [heq] at h1
    exact c_full.proper hne hshare h1 h2
  exact ⟨⟨col, h_proper⟩⟩

/--
Vizing's Theorem (1964):
For any finite simple graph $G$ with maximum degree $\Delta(G)$, the edge chromatic number
(chromatic index) $\chi'(G)$ satisfies:
$$\Delta(G) \le \chi'(G) \le \Delta(G) + 1$$
-/
axiom vizings_theorem [Fintype G.edgeSet] :
    G.maxDegree ≤ chromaticIndex G ∧ chromaticIndex G ≤ G.maxDegree + 1

/-- A graph is Class 1 if its edge chromatic number achieves the maximum degree $\Delta(G)$. -/
def IsClassOne [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree

/-- A graph is Class 2 if its edge chromatic number is $\Delta(G) + 1$. -/
def IsClassTwo [Fintype G.edgeSet] : Prop :=
  chromaticIndex G = G.maxDegree + 1

/-- Vizing's Classification: Every finite simple graph is either Class 1 or Class 2. -/
theorem vizing_classification [Fintype G.edgeSet] :
    IsClassOne G ∨ IsClassTwo G := by
  have ⟨hle, hub⟩ := vizings_theorem G
  dsimp [IsClassOne, IsClassTwo]
  omega

/--
König's Line Coloring Theorem (1916):
Every bipartite graph is Class 1, i.e., $\chi'(G) = \Delta(G)$.
-/
theorem konig_edge_coloring [Fintype G.edgeSet] (h_bip : G.Colorable 2) :
    IsClassOne G := by
  dsimp [IsClassOne]
  have h_ge := chromatic_index_ge_maxDegree G
  have h_le : chromaticIndex G ≤ G.maxDegree := by
    dsimp [chromaticIndex]
    have h_colorable := edgeColorable_of_bipartite G h_bip
    have h_mem : G.maxDegree ∈ {k | IsEdgeColorable G k} := h_colorable
    exact csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ h_mem
  omega

end SimpleGraph



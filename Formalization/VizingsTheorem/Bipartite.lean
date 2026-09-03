import Formalization.VizingsTheorem.Kempe

open scoped BigOperators
open Classical

/-!
# Bipartite Edge Colorings and König's Theorem Foundation

This module formalizes the shift-step operation on partial edge colorings,
the non-reachability lemma in bipartite graphs, and the existence of full edge colorings
for bipartite graphs with $k \ge \Delta(G)$ colors.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

namespace PartialEdgeColoring

variable {G} {k : ℕ} (c : PartialEdgeColoring G k)

def shiftStep (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e :=
    if e = ⟨s(u, v), huv⟩ then some col
    else if e = ⟨s(u, w), huw⟩ then none
    else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ c' h1 h2
    have he_vw : (⟨s(u, v), huv⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩ := by
      intro heq; have : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq]; exact h_col
      rw [mem_missingColors_iff] at h_miss; exact h_miss u huv.symm (by rwa [colorOf_symm])
    by_cases he1_v : e₁ = ⟨s(u, v), huv⟩
    · have hc' : c' = col := (Option.some.inj (by simpa [he1_v] using h1)).symm
      have he2_v : e₂ ≠ ⟨s(u, v), huv⟩ := by rintro rfl; exact hne he1_v
      have he2_w : e₂ ≠ ⟨s(u, w), huw⟩ := by rintro rfl; simp [he_vw.symm] at h2
      have h2_orig : c.color e₂ = some c' := by simpa [he2_v, he2_w] using h2
      rw [hc'] at h2_orig
      obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp (he1_v ▸ hv1) with rfl | rfl
      · exact c.proper he2_w.symm ⟨v₀, Sym2.mem_mk_left v₀ w, Sym2.mem_mk_left v₀ z⟩ h_col h2_orig
      · rw [mem_missingColors_iff] at h_miss; exact h_miss z hz_adj h2_orig
    · by_cases he2_v : e₂ = ⟨s(u, v), huv⟩
      · have hc' : c' = col := (Option.some.inj (by simpa [he2_v] using h2)).symm
        have he1_v' : e₁ ≠ ⟨s(u, v), huv⟩ := he1_v
        have he1_w : e₁ ≠ ⟨s(u, w), huw⟩ := by rintro rfl; simp [he_vw.symm] at h1
        have h1_orig : c.color e₁ = some c' := by simpa [he1_v', he1_w] using h1
        rw [hc'] at h1_orig
        obtain ⟨z, hz_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
        rcases Sym2.mem_iff.mp (he2_v ▸ hv2) with rfl | rfl
        · exact c.proper he1_w ⟨v₀, Sym2.mem_mk_left v₀ z, Sym2.mem_mk_left v₀ w⟩ h1_orig h_col
        · rw [mem_missingColors_iff] at h_miss; exact h_miss z hz_adj h1_orig
      · by_cases he1_w : e₁ = ⟨s(u, w), huw⟩
        · subst he1_w; simp [he1_v] at h1
        · by_cases he2_w : e₂ = ⟨s(u, w), huw⟩
          · subst he2_w; simp [he2_v] at h2
          · exact c.proper hne ⟨v₀, hv1, hv2⟩ (by simpa [he1_v, he1_w] using h1) (by simpa [he2_v, he2_w] using h2)

lemma card_uncoloredEdges_shiftStep [Fintype G.edgeSet] (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (h_none : c.colorOf u v huv = none) :
    (c.shiftStep u v w huv huw col h_col h_miss).uncoloredEdges.card = c.uncoloredEdges.card := by
  have he_vw : (⟨s(u, v), huv⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩ := by
    intro heq; have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq]; exact h_col
    dsimp [colorOf] at h_none; rw [h_none] at hc; cases hc
  have he_v_mem : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_none
  have he_w_not_mem : (⟨s(u, w), huw⟩ : G.edgeSet) ∉ c.uncoloredEdges := by
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hc
    dsimp [colorOf] at h_col
    rw [hc] at h_col
    cases h_col
  have heq_set : (c.shiftStep u v w huv huw col h_col h_miss).uncoloredEdges =
      insert ⟨s(u, w), huw⟩ (c.uncoloredEdges.erase ⟨s(u, v), huv⟩) := by
    ext e
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_erase]
    dsimp [shiftStep]
    split_ifs with he1 he2
    · simp [he1, he_vw]
    · simp [he2]
    · constructor
      · intro h; exact Or.inr ⟨he1, h⟩
      · rintro (rfl | ⟨-, h⟩)
        · exfalso; exact he2 rfl
        · exact h
  rw [heq_set, Finset.card_insert_of_notMem (by simp [he_vw.symm, he_w_not_mem]), Finset.card_erase_of_mem he_v_mem]
  have := Finset.card_pos.mpr ⟨_, he_v_mem⟩; omega

lemma shiftStep_colorOf_none (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) :
    (c.shiftStep u v w huv huw col h_col h_miss).colorOf u w huw = none := by
  dsimp [colorOf, shiftStep]
  have he_vw : (⟨s(u, w), huw⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩ := by
    intro heq; have hc : c.color ⟨s(u, v), huv⟩ = some col := by rw [heq.symm]; exact h_col
    rw [mem_missingColors_iff] at h_miss; exact h_miss u huv.symm (by rwa [colorOf_symm])
  simp [he_vw]

lemma shiftStep_missing_u (u v w : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (α : Fin k) (hα : α ∈ c.missingColors u) :
    α ∈ (c.shiftStep u v w huv huw col h_col h_miss).missingColors u := by
  rw [mem_missingColors_iff] at hα ⊢
  intro z hz
  dsimp [colorOf, shiftStep]
  split_ifs with he1 he2
  · intro heq; have hc : col = α := Option.some.inj heq; subst hc; exact hα w huw h_col
  · intro heq; cases heq
  · exact hα z hz

lemma shiftStep_missing_of_ne_v (u v w x : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (hxv : x ≠ v) (γ : Fin k) (hγ : γ ∈ c.missingColors x) :
    γ ∈ (c.shiftStep u v w huv huw col h_col h_miss).missingColors x := by
  rcases eq_or_ne x u with rfl | hxu
  · exact c.shiftStep_missing_u x v w huv huw col h_col h_miss γ hγ
  · rw [mem_missingColors_iff] at hγ ⊢
    intro z hz
    dsimp [colorOf, shiftStep]
    have he1 : (⟨s(x, z), hz⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩ := by
      intro heq
      have : s(x, z) = s(u, v) := Subtype.ext_iff.mp heq
      rw [Sym2.eq_iff] at this
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxu rfl
      · exact hxv rfl
    split_ifs with he_v he_w
    · exfalso; exact he1 he_v
    · intro heq; cases heq
    · exact hγ z hz

lemma shiftStep_colorOf_of_ne (u v w y z : V) (huv : G.Adj u v) (huw : G.Adj u w)
    (col : Fin k) (h_col : c.colorOf u w huw = some col)
    (h_miss : col ∈ c.missingColors v) (hyz : G.Adj y z)
    (h_ne1 : (⟨s(y, z), hyz⟩ : G.edgeSet) ≠ ⟨s(u, v), huv⟩)
    (h_ne2 : (⟨s(y, z), hyz⟩ : G.edgeSet) ≠ ⟨s(u, w), huw⟩) :
    (c.shiftStep u v w huv huw col h_col h_miss).colorOf y z hyz = c.colorOf y z hyz := by
  dsimp [colorOf, shiftStep]; simp [h_ne1, h_ne2]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma bipartite_walk_length (b : V → Bool) (hb : ∀ x y, G.Adj x y → b y = !b x)
    (H : SimpleGraph V) (hH : H ≤ G) :
    ∀ {x y : V} (p : H.Walk x y), b y = if p.length % 2 = 1 then !b x else b x
  | x, _, .nil => by simp
  | x, y, @Walk.cons _ _ _ v _ h p => by
    have ih := bipartite_walk_length b hb H hH p
    have h_adj := hb x v (hH h)
    rw [Walk.length_cons, ih, h_adj]
    have hcases : p.length % 2 = 0 ∨ p.length % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · have : (p.length + 1) % 2 = 1 := by omega
      simp [h0, this]
    · have : (p.length + 1) % 2 = 0 := by omega
      simp [h1, this]

omit [DecidableEq V] in
/--
In any bipartite graph ($G.\text{Colorable } 2$), if $u v$ is an uncolored edge, no alternating
$(\alpha, \beta)$ path in the Kempe subgraph can connect $u$ and $v$.
-/
theorem kempe_not_reachable_bipartite (h_bip : G.Colorable 2) {u v : V} (hadj : G.Adj u v)
    {α β : Fin k} (hne : α ≠ β) (hα : α ∈ c.missingColors u) (hβ : β ∈ c.missingColors v) :
    ¬ (c.kempeGraph α β).Reachable u v := by
  intro hreach
  obtain ⟨bicol⟩ := h_bip
  let b : V → Bool := fun x => (bicol x).val == 0
  have hb : ∀ x y, G.Adj x y → b y = !b x := by
    intro x y hxy
    have hne' : (bicol x).val ≠ (bicol y).val := fun h => bicol.valid hxy (Fin.ext h)
    have hx := (bicol x).isLt; have hy := (bicol y).isLt
    dsimp [b]
    have : (bicol x).val = 0 ∨ (bicol x).val = 1 := by omega
    have : (bicol y).val = 0 ∨ (bicol y).val = 1 := by omega
    rcases ‹(bicol x).val = 0 ∨ (bicol x).val = 1› with hx0 | hx1 <;>
    rcases ‹(bicol y).val = 0 ∨ (bicol y).val = 1› with hy0 | hy1 <;> simp [*] <;> omega
  obtain ⟨p, hp_path⟩ := hreach.exists_isPath
  have h_first : c.FirstColor α β p β := by
    cases p with
    | nil => dsimp [FirstColor]
    | cons h p' =>
      dsimp [FirstColor]
      rcases h.2 with hcolα | hcolβ
      · rw [mem_missingColors_iff] at hα; exact (hα _ h.1 hcolα).elim
      · exact hcolβ
  have h_alt := isAlternating_of_isPath c hne p β hp_path (Or.inr rfl) h_first
  have h_len_eq := bipartite_walk_length b hb (c.kempeGraph α β) (c.kempeGraph_le α β) p
  have hbv := hb u v hadj
  rw [hbv] at h_len_eq
  have h_mod : p.length % 2 = 1 := by
    by_contra h0
    have : p.length % 2 = 0 := by omega
    rw [this] at h_len_eq
    revert h_len_eq; cases b u <;> decide
  have h_len_pos : p.length > 0 := by omega
  obtain ⟨z, hz_adj, hz_col⟩ := last_edge_alternating c p β h_alt (Or.inr rfl) h_len_pos
  rw [h_mod] at hz_col
  rw [mem_missingColors_iff] at hβ
  exact hβ z hz_adj.symm (by rwa [colorOf_symm])

/-- Extends a partial edge coloring by coloring uncolored edge $u v$ with a common missing color. -/
def extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) : PartialEdgeColoring G k where
  color e := if e = ⟨s(u, v), hadj⟩ then some col else c.color e
  proper := by
    intro e₁ e₂ hne ⟨v₀, hv1, hv2⟩ c' h1 h2
    by_cases he1 : e₁ = ⟨s(u, v), hadj⟩ <;> by_cases he2 : e₂ = ⟨s(u, v), hadj⟩
    · exact hne (he1.trans he2.symm)
    · have hc' : c' = col := (Option.some.inj (by simpa [he1] using h1)).symm
      have h2_orig : c.color e₂ = some c' := by simpa [he2] using h2
      rw [hc'] at h2_orig
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₂ v₀ hv2
      rcases Sym2.mem_iff.mp (he1 ▸ hv1) with rfl | rfl
      · rw [mem_missingColors_iff] at hu; exact hu w hw_adj h2_orig
      · rw [mem_missingColors_iff] at hv; exact hv w hw_adj h2_orig
    · have hc' : c' = col := (Option.some.inj (by simpa [he2] using h2)).symm
      have h1_orig : c.color e₁ = some c' := by simpa [he1] using h1
      rw [hc'] at h1_orig
      obtain ⟨w, hw_adj, rfl⟩ := edge_eq_of_mem G e₁ v₀ hv1
      rcases Sym2.mem_iff.mp (he2 ▸ hv2) with rfl | rfl
      · rw [mem_missingColors_iff] at hu; exact hu w hw_adj h1_orig
      · rw [mem_missingColors_iff] at hv; exact hv w hw_adj h1_orig
    · exact c.proper hne ⟨v₀, hv1, hv2⟩ (by simpa [he1] using h1) (by simpa [he2] using h2)

lemma uncoloredEdges_extendColor (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v) :
    (c.extendColor u v hadj col hu hv).uncoloredEdges = c.uncoloredEdges.erase ⟨s(u, v), hadj⟩ := by
  ext e
  simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  dsimp [extendColor]
  split_ifs with heq <;> simp [heq]

lemma card_uncoloredEdges_extendColor_lt (u v : V) (hadj : G.Adj u v) (col : Fin k)
    (hu : col ∈ c.missingColors u) (hv : col ∈ c.missingColors v)
    (hnone : c.colorOf u v hadj = none) :
    (c.extendColor u v hadj col hu hv).uncoloredEdges.card < c.uncoloredEdges.card := by
  have he_mem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ c.uncoloredEdges := by
    simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and]; exact hnone
  rw [uncoloredEdges_extendColor, Finset.card_erase_of_mem he_mem]
  exact Nat.pred_lt (Finset.card_pos.mpr ⟨_, he_mem⟩).ne'

/-- Any non-empty partial edge coloring on a bipartite graph can be extended to strictly fewer uncolored edges. -/
theorem exists_extended_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (hne : c.uncoloredEdges.Nonempty) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges.card < c.uncoloredEdges.card := by
  obtain ⟨⟨e_val, he_prop⟩, he⟩ := hne
  induction e_val using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := he_prop
    have he_none : c.colorOf u v hadj = none := by
      simp only [uncoloredEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he; exact he
    obtain ⟨α, hα⟩ := exists_missingColor_of_uncolored c hadj he_none h_max
    obtain ⟨β, hβ⟩ := exists_missingColor_of_uncolored c hadj.symm (by rwa [colorOf_symm]) h_max
    by_cases hab : α = β
    · subst hab
      exact ⟨c.extendColor u v hadj α hα hβ, c.card_uncoloredEdges_extendColor_lt u v hadj α hα hβ he_none⟩
    · have hnreach := kempe_not_reachable_bipartite c h_bip hadj hab hα hβ
      let c_swap := c.kempeSwap α β u
      have hβ_u : β ∈ c_swap.missingColors u := kempeSwap_missing_u c α β u hα
      have hβ_v : β ∈ c_swap.missingColors v := kempeSwap_missing_v c α β u v hnreach hβ
      have h_none_swap : c_swap.colorOf u v hadj = none := kempeSwap_colorOf_none c α β u v hadj hnreach he_none
      refine ⟨c_swap.extendColor u v hadj β hβ_u hβ_v, ?_⟩
      have hlt := c_swap.card_uncoloredEdges_extendColor_lt u v hadj β hβ_u hβ_v h_none_swap
      rwa [uncoloredEdges_kempeSwap] at hlt

/-- By well-founded induction on uncolored edges, a bipartite graph admits a complete proper edge coloring. -/
theorem exists_full_coloring (h_max : G.maxDegree ≤ k) (h_bip : G.Colorable 2)
    (c : PartialEdgeColoring G k) :
    ∃ c' : PartialEdgeColoring G k, c'.uncoloredEdges = ∅ := by
  by_cases h : c.uncoloredEdges = ∅
  · exact ⟨c, h⟩
  · obtain ⟨c', hlt⟩ := c.exists_extended_coloring h_max h_bip (Finset.nonempty_iff_ne_empty.mpr h)
    obtain ⟨c'', h''⟩ := exists_full_coloring h_max h_bip c'
    exact ⟨c'', h''⟩
termination_by c.uncoloredEdges.card

end PartialEdgeColoring

end SimpleGraph

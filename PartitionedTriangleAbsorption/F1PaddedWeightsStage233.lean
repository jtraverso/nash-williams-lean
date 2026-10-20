/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1TemplateWeightsStage233

/-!
# Exact positive F1 weights for nearly balanced classes (dummy padding)

Let `W` be the active vertex set of a graph `H` on an arbitrary vertex type, with classes
`p : V → Fin 4` of sizes `t - s ≤ n_i ≤ t` inside `W`. We embed `W` class-preservingly into the
template `Fin 4 × Fin t`; the unused template vertices are isolated dummies. A real vertex sees at
most `3s` dummy template neighbours (its own class and the two opposite classes), so a real
missing-degree bound `D` becomes the template damage bound `D + 3s`. The equal-class theorem
`f1_template_exact_weights` then applies; restricting back gives exact loads one on the real
F1 triangles of `H` with weights in `[1/(2n), 3/n]`, `n = |W|`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1BalanceGateStage228 TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A class-preserving map of `W` into the template, injective on `W`. -/
theorem exists_class_embedding (p : V → Fin 4) (W : Finset V) {t : ℕ} (ht : 0 < t)
    (hle : ∀ i, (W.filter fun v => p v = i).card ≤ t) :
    ∃ ι : V → Fin 4 × Fin t, (∀ v, (ι v).1 = p v) ∧ Set.InjOn ι W := by
  classical
  have he : ∀ i, Nonempty ({v // v ∈ W.filter fun v => p v = i} ↪ Fin t) := fun i =>
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_coe, Fintype.card_fin]; exact hle i)
  let e : ∀ i, {v // v ∈ W.filter fun v => p v = i} ↪ Fin t := fun i => (he i).some
  let g : Fin 4 → V → Fin t := fun i v =>
    if h : v ∈ W.filter (fun v => p v = i) then e i ⟨v, h⟩ else ⟨0, ht⟩
  refine ⟨fun v => (p v, g (p v) v), fun v => rfl, ?_⟩
  intro v hv v' hv' heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hp, hg⟩ := heq
  have hmem : v ∈ W.filter fun x => p x = p v := mem_filter.mpr ⟨hv, rfl⟩
  have hmem' : v' ∈ W.filter fun x => p x = p v := mem_filter.mpr ⟨hv', hp.symm⟩
  rw [← hp] at hg
  simp only [g, dif_pos hmem, dif_pos hmem'] at hg
  exact congrArg Subtype.val ((e (p v)).injective hg)

theorem opp_cases {i j : Fin 4} (h : Opp i j) : j = first1 i ∨ j = second1 i := by
  fin_cases i <;> fin_cases j <;> simp [Opp] at h <;> simp [first1, second1]

/-! ### Transport of a graph along a class embedding -/

section Transport

variable {t : ℕ} (p : V → Fin 4) (W : Finset V) (ι : V → Fin 4 × Fin t)
  (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The image of `H` in the template; vertices outside `ι '' W` are isolated dummies. -/
def pushG : SimpleGraph (Fin 4 × Fin t) :=
  SimpleGraph.fromRel fun a b => ∃ u v, H.Adj u v ∧ ι u = a ∧ ι v = b

variable {p W ι H}

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
theorem pushG_adj_cases {a b : Fin 4 × Fin t} (h : (pushG ι H).Adj a b) :
    ∃ u v, H.Adj u v ∧ ι u = a ∧ ι v = b := by
  obtain ⟨-, h | ⟨u, v, huv, hu, hv⟩⟩ := h
  · exact h
  · exact ⟨v, u, huv.symm, hv, hu⟩

variable (hinj : Set.InjOn ι W) (hHW : ∀ u v, H.Adj u v → u ∈ W)
include hinj hHW

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
theorem pushG_adj_iff {u v : V} (hu : u ∈ W) (hv : v ∈ W) :
    (pushG ι H).Adj (ι u) (ι v) ↔ H.Adj u v := by
  constructor
  · intro h
    obtain ⟨u', v', h', hu', hv'⟩ := pushG_adj_cases h
    have e1 : u' = u := hinj (hHW _ _ h') hu hu'
    have e2 : v' = v := hinj (hHW _ _ h'.symm) hv hv'
    rw [← e1, ← e2]; exact h'
  · intro h
    refine ⟨fun e => H.ne_of_adj h (hinj hu hv e), Or.inl ⟨u, v, h, rfl, rfl⟩⟩

omit [DecidableRel H.Adj] hinj in
theorem copies_sub_W {s : Finset V} (hs : s ∈ copies p F1 H) : s ⊆ W := by
  intro x hx
  obtain ⟨hcl, -⟩ := mem_copies_iff.mp hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcl.card_eq
  have h3 := SimpleGraph.is3Clique_triple_iff.mp hcl
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hHW _ _ h3.1
  · exact hHW _ _ h3.1.symm
  · exact hHW _ _ h3.2.1.symm

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] hHW in
theorem image_injOn_W {s s' : Finset V} (hs : s ⊆ W) (hs' : s' ⊆ W)
    (h : s.image ι = s'.image ι) : s = s' := by
  ext x
  constructor
  · intro hx
    have : ι x ∈ s'.image ι := h ▸ mem_image_of_mem ι hx
    obtain ⟨y, hy, hxy⟩ := mem_image.mp this
    rw [← hinj (hs' hy) (hs hx) hxy]; exact hy
  · intro hx
    have : ι x ∈ s.image ι := h ▸ mem_image_of_mem ι hx
    obtain ⟨y, hy, hxy⟩ := mem_image.mp this
    rw [← hinj (hs hy) (hs' hx) hxy]; exact hy

variable (hι1 : ∀ v, (ι v).1 = p v)
include hι1

omit [DecidableRel H.Adj] in
theorem image_mem_copies {s : Finset V} (hs : s ∈ copies p F1 H) :
    s.image ι ∈ copies Prod.fst F1 (pushG ι H) := by
  have hsW := copies_sub_W hHW hs
  obtain ⟨hcl, htype⟩ := mem_copies_iff.mp hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcl.card_eq
  have h3 := SimpleGraph.is3Clique_triple_iff.mp hcl
  have ha : a ∈ W := hsW (by simp)
  have hb : b ∈ W := hsW (by simp)
  have hc : c ∈ W := hsW (by simp)
  have hab' : ι a ≠ ι b := fun e => hab (hinj ha hb e)
  have hac' : ι a ≠ ι c := fun e => hac (hinj ha hc e)
  have hbc' : ι b ≠ ι c := fun e => hbc (hinj hb hc e)
  rw [image_insert, image_insert, image_singleton]
  refine mem_copies_iff.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr
    ⟨(pushG_adj_iff hinj hHW ha hb).mpr h3.1, (pushG_adj_iff hinj hHW ha hc).mpr h3.2.1,
      (pushG_adj_iff hinj hHW hb hc).mpr h3.2.2⟩, ?_⟩
  rw [map_three Prod.fst hab' hac' hbc', hι1, hι1, hι1]
  rw [map_three p hab hac hbc] at htype
  exact htype

omit [DecidableRel H.Adj] in
theorem exists_preimage_copy {s' : Finset (Fin 4 × Fin t)}
    (hs' : s' ∈ copies Prod.fst F1 (pushG ι H)) :
    ∃ s ∈ copies p F1 H, s.image ι = s' := by
  obtain ⟨hcl, htype⟩ := mem_copies_iff.mp hs'
  obtain ⟨a', b', c', hab, hac, hbc, rfl⟩ := card_eq_three.mp hcl.card_eq
  have h3 := SimpleGraph.is3Clique_triple_iff.mp hcl
  obtain ⟨a, b, hab0, rfl, rfl⟩ := pushG_adj_cases h3.1
  obtain ⟨a2, c, hac0, ha2, rfl⟩ := pushG_adj_cases h3.2.1
  have ha : a ∈ W := hHW _ _ hab0
  have hb : b ∈ W := hHW _ _ hab0.symm
  have hc : c ∈ W := hHW _ _ hac0.symm
  have e2 : a2 = a := hinj (hHW _ _ hac0) ha ha2
  subst e2
  have hbc0 : H.Adj b c := (pushG_adj_iff hinj hHW hb hc).mp h3.2.2
  have hab1 : a2 ≠ b := H.ne_of_adj hab0
  have hac1 : a2 ≠ c := H.ne_of_adj hac0
  have hbc1 : b ≠ c := H.ne_of_adj hbc0
  refine ⟨{a2, b, c}, mem_copies_iff.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr
    ⟨hab0, hac0, hbc0⟩, ?_⟩, by rw [image_insert, image_insert, image_singleton]⟩
  rw [map_three Prod.fst hab hac hbc, hι1, hι1, hι1] at htype
  rw [map_three p hab1 hac1 hbc1]
  exact htype

omit [DecidableRel H.Adj] in
/-- **Load transfer**: loads of weights pulled back along `ι` equal template loads. -/
theorem load_pullback (w' : Finset (Fin 4 × Fin t) → ℝ) {u v : V} (huv : H.Adj u v) :
    load (copies p F1 H) (fun s => w' (s.image ι)) s(u, v) =
      load (copies Prod.fst F1 (pushG ι H)) w' s(ι u, ι v) := by
  have hu : u ∈ W := hHW _ _ huv
  have hv : v ∈ W := hHW _ _ huv.symm
  have hne : u ≠ v := H.ne_of_adj huv
  have hne' : ι u ≠ ι v := fun e => hne (hinj hu hv e)
  unfold load
  have hinjA : ∀ x ∈ (copies p F1 H).filter (fun s => s(u, v) ∈ triEdges s),
      ∀ y ∈ (copies p F1 H).filter (fun s => s(u, v) ∈ triEdges s),
      x.image ι = y.image ι → x = y := fun x hx y hy h =>
    image_injOn_W hinj (copies_sub_W hHW (mem_filter.mp hx).1)
      (copies_sub_W hHW (mem_filter.mp hy).1) h
  calc _ = ∑ s' ∈ ((copies p F1 H).filter (fun s => s(u, v) ∈ triEdges s)).image
        (fun s => s.image ι), w' s' := (sum_image hinjA).symm
    _ = _ := by
      congr 1
      ext s'
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨s, ⟨hs, he⟩, rfl⟩
        obtain ⟨hus, hvs, -⟩ := mem_triEdges_iff.mp he
        exact ⟨image_mem_copies hinj hHW hι1 hs,
          mem_triEdges_iff.mpr ⟨mem_image_of_mem ι hus, mem_image_of_mem ι hvs, hne'⟩⟩
      · rintro ⟨hs', he⟩
        obtain ⟨s, hs, rfl⟩ := exists_preimage_copy hinj hHW hι1 hs'
        have hsW := copies_sub_W hHW hs
        obtain ⟨hus, hvs, -⟩ := mem_triEdges_iff.mp he
        have hus' : u ∈ s := by
          obtain ⟨y, hy, hyu⟩ := mem_image.mp hus
          rw [← hinj (hsW hy) hu hyu]; exact hy
        have hvs' : v ∈ s := by
          obtain ⟨y, hy, hyv⟩ := mem_image.mp hvs
          rw [← hinj (hsW hy) hv hyv]; exact hy
        exact ⟨s, ⟨hs, mem_triEdges_iff.mpr ⟨hus', hvs', hne⟩⟩, rfl⟩

noncomputable instance (ι : V → Fin 4 × Fin t) (H : SimpleGraph V) :
    DecidableRel (pushG ι H).Adj := Classical.decRel _

omit [DecidableEq V] hι1 in
theorem pushG_edgeFinset :
    (pushG ι H).edgeFinset = H.edgeFinset.image (Sym2.map ι) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_image]
    constructor
    · intro h
      obtain ⟨u, v, huv, rfl, rfl⟩ := pushG_adj_cases h
      exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv, by simp⟩
    · rintro ⟨e, he, hmap⟩
      induction e using Sym2.ind with
      | _ u v =>
        have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rw [Sym2.map_mk, Sym2.eq_iff] at hmap
        rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (pushG_adj_iff hinj hHW (hHW _ _ huv) (hHW _ _ huv.symm)).mpr huv
        · exact ((pushG_adj_iff hinj hHW (hHW _ _ huv) (hHW _ _ huv.symm)).mpr huv).symm

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] hinj hHW in
theorem charge_map (e : Sym2 V) : charge Prod.fst (Sym2.map ι e) = charge p e := by
  induction e using Sym2.ind with
  | _ u v => simp [charge, hι1]

omit [DecidableEq V] in
/-- **Balance is preserved by the padding.** -/
theorem balance_pushG : balance Prod.fst (pushG ι H).edgeFinset = balance p H.edgeFinset := by
  unfold balance
  rw [pushG_edgeFinset hinj hHW, sum_image]
  · exact sum_congr rfl fun e _ => charge_map hι1 e
  · intro e he e' he' h
    induction e using Sym2.ind with
    | _ u v =>
    induction e' using Sym2.ind with
    | _ u' v' =>
      have huv := SimpleGraph.mem_edgeFinset.mp he
      have huv' := SimpleGraph.mem_edgeFinset.mp he'
      have hu := hHW _ _ huv; have hv := hHW _ _ huv.symm
      have hu' := hHW _ _ huv'; have hv' := hHW _ _ huv'.symm
      simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hinj hu hu' h1, hinj hv hv' h2⟩
      · exact Or.inr ⟨hinj hu hv' h1, hinj hv hu' h2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] hHW in
/-- Dummy template vertices of class `c`: at most `s` of them. -/
theorem card_dummies {s : ℕ} (c : Fin 4) (hc : t ≤ (W.filter fun v => p v = c).card + s) :
    (univ.filter fun w' : Fin 4 × Fin t => w'.1 = c ∧ w' ∉ W.image ι).card ≤ s := by
  have hcls : (univ.filter fun w' : Fin 4 × Fin t => w'.1 = c).card = t := by
    rw [show (univ.filter fun w' : Fin 4 × Fin t => w'.1 = c) =
        ({c} : Finset (Fin 4)) ×ˢ (univ : Finset (Fin t)) by ext ⟨i, k⟩; simp [eq_comm], card_product]
    simp
  have himg : ((W.filter fun v => p v = c).image ι).card = (W.filter fun v => p v = c).card :=
    card_image_of_injOn (hinj.mono (by intro x hx; exact (mem_filter.mp hx).1))
  have hsub : (W.filter fun v => p v = c).image ι ⊆
      univ.filter fun w' : Fin 4 × Fin t => w'.1 = c := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    simp [hι1, (mem_filter.mp hy).2]
  have hB : (univ.filter fun w' : Fin 4 × Fin t => w'.1 = c ∧ w' ∉ W.image ι) ⊆
      (univ.filter fun w' : Fin 4 × Fin t => w'.1 = c) \ (W.filter fun v => p v = c).image ι := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine mem_sdiff.mpr ⟨by simp [hx.1], fun h => hx.2 ?_⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.mp h
    exact mem_image_of_mem ι (mem_filter.mp hy).1
  have := card_le_card hB
  rw [card_sdiff_of_subset hsub, hcls, himg] at this
  omega

omit [Fintype V] in
/-- **Padding damage**: a real vertex misses at most its real missing degree plus `3s` template
edges (the dummies of its own class and of the two opposite classes). -/
theorem pushG_damage {s : ℕ} (hc : ∀ c, t ≤ (W.filter fun v => p v = c).card + s) {u : V}
    (hu : u ∈ W) :
    (univ.filter fun w' => (templateGraph t).Adj (ι u) w' ∧ ¬ (pushG ι H).Adj (ι u) w').card ≤
      (W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧ ¬ H.Adj u w).card + 3 * s := by
  let B : Fin 4 → Finset (Fin 4 × Fin t) := fun c =>
    univ.filter fun w' : Fin 4 × Fin t => w'.1 = c ∧ w' ∉ W.image ι
  have hsub : (univ.filter fun w' => (templateGraph t).Adj (ι u) w' ∧
      ¬ (pushG ι H).Adj (ι u) w') ⊆
      (W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧ ¬ H.Adj u w).image ι ∪
        (B (p u) ∪ (B (first1 (p u)) ∪ B (second1 (p u)))) := by
    intro w' hw'
    simp only [mem_filter, mem_univ, true_and] at hw'
    obtain ⟨⟨hne, hcl⟩, hnot⟩ := hw'
    rw [hι1] at hcl
    by_cases him : w' ∈ W.image ι
    · obtain ⟨w, hw, rfl⟩ := mem_image.mp him
      refine mem_union_left _ (mem_image_of_mem ι (mem_filter.mpr ⟨hw, ?_, ?_, ?_⟩))
      · rintro rfl; exact hne rfl
      · rw [hι1] at hcl; exact hcl
      · exact fun h => hnot ((pushG_adj_iff hinj hHW hu hw).mpr h)
    · refine mem_union_right _ ?_
      rcases hcl with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h.symm, him⟩)
      · rcases opp_cases h with h' | h'
        · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h', him⟩))
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h', him⟩))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := card_image_le (s := W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧
    ¬ H.Adj u w) (f := ι)
  have h2 := card_union_le (B (p u)) (B (first1 (p u)) ∪ B (second1 (p u)))
  have h3 := card_union_le (B (first1 (p u))) (B (second1 (p u)))
  have b1 := card_dummies hinj hι1 (p u) (hc _)
  have b2 := card_dummies hinj hι1 (first1 (p u)) (hc _)
  have b3 := card_dummies hinj hι1 (second1 (p u)) (hc _)
  simp only [B] at h2 h3 ⊢
  omega

end Transport

/-! ### The padded weighting theorem -/

/-- **Exact positive F1 weights for nearly balanced classes.** `W` is the active vertex set of
`H` (every edge of `H` lies in `W`); `H` uses only F1-allowed pairs; the classes inside `W` have
sizes between `t - s` and `t`, `t ≥ 640`; every vertex of `H` that has an edge misses at most `D`
allowed partners inside `W`; `D + 3s ≤ t/640`; and `H` has zero signed charge. Then the actual
F1 triangles of `H` carry weights in `[1/(2|W|), 3/|W|]` with load exactly one on every edge. -/
theorem f1_padded_exact_weights (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (W : Finset V) {t s : ℕ} (ht : 640 ≤ t)
    (hcls : ∀ i, t ≤ (W.filter fun v => p v = i).card + s ∧ (W.filter fun v => p v = i).card ≤ t)
    (hHW : ∀ u v, H.Adj u v → u ∈ W)
    (hallowed : ∀ u v, H.Adj u v → p u = p v ∨ Opp (p u) (p v))
    {D : ℝ} (hD : D + 3 * s ≤ t / 640)
    (hdmg : ∀ u, (∃ v, H.Adj u v) →
      ((W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧ ¬ H.Adj u w).card : ℝ) ≤ D)
    (hbal : balance p H.edgeFinset = 0) :
    ∃ w : Finset V → ℝ,
      (∀ e ∈ H.edgeFinset, load (copies p F1 H) w e = 1) ∧
      (∀ x ∈ copies p F1 H, 1 / (2 * W.card) ≤ w x ∧ w x ≤ 3 / W.card) ∧
      (∀ x ∉ copies p F1 H, w x = 0) := by
  obtain ⟨ι, hι1, hinj⟩ := exists_class_embedding p W (by omega : 0 < t) (fun i => (hcls i).2)
  have hle : pushG ι H ≤ templateGraph t := by
    intro a b h
    obtain ⟨u, v, huv, rfl, rfl⟩ := pushG_adj_cases h
    refine ⟨h.ne, ?_⟩
    rw [hι1, hι1]; exact hallowed u v huv
  have hdmg' : ∀ a, (∃ b, (pushG ι H).Adj a b) →
      ((univ.filter fun w' => (templateGraph t).Adj a w' ∧ ¬ (pushG ι H).Adj a w').card : ℝ) ≤
        D + 3 * s := by
    rintro a ⟨b, hab⟩
    obtain ⟨u, v, huv, rfl, rfl⟩ := pushG_adj_cases hab
    have h1 := pushG_damage hinj hHW hι1 (fun c => (hcls c).1) (hHW _ _ huv)
    have h2 := hdmg u ⟨v, huv⟩
    have : ((univ.filter fun w' => (templateGraph t).Adj (ι u) w' ∧
        ¬ (pushG ι H).Adj (ι u) w').card : ℝ) ≤
        ((W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧ ¬ H.Adj u w).card : ℝ) +
          3 * s := by exact_mod_cast h1
    linarith
  have hbal' : balance Prod.fst (pushG ι H).edgeFinset = 0 := by
    rw [balance_pushG hinj hHW hι1]; exact hbal
  obtain ⟨w', hload, hrange, hzero⟩ :=
    f1_template_exact_weights (pushG ι H) ht hle hD hdmg' hbal'
  refine ⟨fun x => if x ∈ copies p F1 H then w' (x.image ι) else 0, ?_, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have h1 : load (copies p F1 H) (fun x => if x ∈ copies p F1 H then w' (x.image ι) else 0)
          s(u, v) = load (copies p F1 H) (fun x => w' (x.image ι)) s(u, v) := by
        unfold load
        exact sum_congr rfl fun x hx => if_pos (mem_filter.mp hx).1
      rw [h1, load_pullback hinj hHW hι1 w' huv]
      exact hload _ (SimpleGraph.mem_edgeFinset.mpr ((pushG_adj_iff hinj hHW (hHW _ _ huv)
        (hHW _ _ huv.symm)).mpr huv))
  · intro x hx
    simp only [if_pos hx]
    obtain ⟨h1, h2⟩ := hrange _ (image_mem_copies hinj hHW hι1 hx)
    -- size of `W`
    have hcard : W.card = ∑ i, (W.filter fun v => p v = i).card :=
      card_eq_sum_card_fiberwise (fun v _ => mem_univ (p v))
    have hsum := hcard
    rw [Fin.sum_univ_four] at hsum
    have l0 := hcls 0; have l1 := hcls 1; have l2 := hcls 2; have l3 := hcls 3
    -- there is an edge, so `D ≥ 0`
    obtain ⟨hcl, -⟩ := mem_copies_iff.mp hx
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcl.card_eq
    have hadj := (SimpleGraph.is3Clique_triple_iff.mp hcl).1
    have hD0 : 0 ≤ D := le_trans (Nat.cast_nonneg _) (hdmg a ⟨b, hadj⟩)
    have hs : (3 * s : ℝ) ≤ t / 640 := by linarith
    have hsN : 2 * s ≤ t := by
      have : (2 * s : ℝ) ≤ t := by
        have : (t : ℝ) / 640 ≤ t := by
          have : (0 : ℝ) ≤ t := Nat.cast_nonneg _
          linarith
        linarith
      exact_mod_cast this
    have hW1 : 2 * t ≤ W.card := by omega
    have hW2 : W.card ≤ 4 * t := by omega
    have ht640 : (640 : ℝ) ≤ t := by exact_mod_cast ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hW1' : (2 * t : ℝ) ≤ W.card := by exact_mod_cast hW1
    have hW2' : (W.card : ℝ) ≤ 4 * t := by exact_mod_cast hW2
    have hWpos : (0 : ℝ) < W.card := by linarith
    constructor
    · refine le_trans ?_ h1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    · refine h2.trans ?_
      rw [div_le_div_iff₀ (by positivity) hWpos]; linarith
  · intro x hx
    simp only [if_neg hx]

end PartitionedTriangleAbsorption.F1TemplateStage233

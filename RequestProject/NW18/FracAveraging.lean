/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Defs

/-!
# Fractional packings with prescribed loads (Proposition 11.8, Lemma 11.9)

Deterministic tools from §11 of the paper used to turn fractional decompositions of all graphs
`G - H` (`H` of small maximum degree) into fractional packings with any prescribed loads close
to `1`.
-/

namespace NashWilliams18

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The load at the pair `{u, v}` of a weighting `w` of the triangles of `Gr`. -/
def load (Gr : SimpleGraph W) [DecidableRel Gr.Adj] (w : Finset W → ℝ) (u v : W) : ℝ :=
  ∑ t ∈ Gr.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t

/-- The graph `Gr - R` for a finite edge set `R`. -/
abbrev del (Gr : SimpleGraph W) (R : Finset (Sym2 W)) : SimpleGraph W :=
  Gr.deleteEdges (R : Set (Sym2 W))

/-- Extending a weighting of the triangles of `Gr - R` by zero to the triangles of `Gr`. -/
noncomputable def extendDel (Gr : SimpleGraph W) [DecidableRel Gr.Adj] (R : Finset (Sym2 W))
    (w : Finset W → ℝ) : Finset W → ℝ :=
  fun t => if t ∈ (del Gr R).cliqueFinset 3 then w t else 0

lemma cliqueFinset_del_subset (Gr : SimpleGraph W) [DecidableRel Gr.Adj]
    (R : Finset (Sym2 W)) : (del Gr R).cliqueFinset 3 ⊆ Gr.cliqueFinset 3 := by
  intro t ht
  simp only [SimpleGraph.mem_cliqueFinset_iff] at ht ⊢
  exact ht.mono (SimpleGraph.deleteEdges_le _)

lemma load_extendDel (Gr : SimpleGraph W) [DecidableRel Gr.Adj] (R : Finset (Sym2 W))
    (w : Finset W → ℝ) (u v : W) :
    load Gr (extendDel Gr R w) u v = load (del Gr R) w u v := by
  unfold load extendDel
  rw [← sum_filter_add_sum_filter_not (Gr.cliqueFinset 3 |>.filter fun t => u ∈ t ∧ v ∈ t)
    (fun t => t ∈ (del Gr R).cliqueFinset 3)]
  rw [sum_eq_zero (s := filter (fun t => t ∉ (del Gr R).cliqueFinset 3) _)
    (fun t ht => by simp only [mem_filter] at ht; simp [ht.2])]
  rw [add_zero]
  refine sum_congr ?_ (fun t ht => by rw [mem_filter] at ht; rw [if_pos ht.1])
  ext t
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
  · rintro ⟨h', h⟩; exact ⟨⟨cliqueFinset_del_subset Gr R h', h⟩, h'⟩

lemma load_del_eq_zero (Gr : SimpleGraph W) [DecidableRel Gr.Adj] (R : Finset (Sym2 W))
    (w : Finset W → ℝ) {u v : W} (huv : u ≠ v) (h : s(u, v) ∈ R) :
    load (del Gr R) w u v = 0 := by
  unfold load
  refine sum_eq_zero fun t ht => ?_
  simp only [mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  have := ht.1.1 ht.2.1 ht.2.2 huv
  simp [SimpleGraph.deleteEdges_adj, h] at this

/-- **Proposition 11.8.** If `Gr - R'` has a fractional triangle decomposition for every
`R' ⊆ R`, then every target `φ : R → [0, 1]` is the load (on `R`) of a fractional triangle
packing of `Gr` that has load `1` on all other edges. -/
theorem prop_11_8 (R : Finset (Sym2 W)) :
    ∀ (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
      (∀ R' ⊆ R, NashWilliams.HasFractionalTriangleDecomposition (del Gr R')) →
      ∀ φ : Sym2 W → ℝ, (∀ e ∈ R, 0 ≤ φ e ∧ φ e ≤ 1) →
      ∃ w : Finset W → ℝ, (∀ t, 0 ≤ w t) ∧
        ∀ u v, Gr.Adj u v → load Gr w u v = if s(u, v) ∈ R then φ s(u, v) else 1 := by
  induction R using Finset.induction_on with
  | empty =>
    intro Gr _ hR φ _
    obtain ⟨w, hw0, hw⟩ := hR ∅ (empty_subset _)
    refine ⟨w, hw0, fun u v huv => ?_⟩
    simp only [Finset.notMem_empty, if_false]
    have := hw u v (by simpa [del] using huv)
    simpa [load, del] using this
  | insert e R₀ he ih =>
    intro Gr _ hR φ hφ
    obtain ⟨w₁, hw₁0, hw₁⟩ := ih Gr (fun R' hR' => hR R' (hR'.trans (subset_insert _ _))) φ
      (fun f hf => hφ f (mem_insert_of_mem hf))
    obtain ⟨w₀, hw₀0, hw₀⟩ := ih (del Gr {e}) (fun R' hR' => by
        have h := hR (insert e R') (insert_subset_insert _ hR')
        convert h using 1
        simp only [del, SimpleGraph.deleteEdges_deleteEdges, coe_insert, coe_singleton]
        rfl) φ
      (fun f hf => hφ f (mem_insert_of_mem hf))
    obtain ⟨hφe0, hφe1⟩ := hφ e (mem_insert_self _ _)
    refine ⟨fun t => φ e * w₁ t + (1 - φ e) * extendDel Gr {e} w₀ t, fun t => ?_,
      fun u v huv => ?_⟩
    · have : 0 ≤ extendDel Gr {e} w₀ t := by
        unfold extendDel; split_ifs
        · exact hw₀0 t
        · exact le_rfl
      have := hw₁0 t
      have : 0 ≤ 1 - φ e := by linarith
      positivity
    · have hsplit : load Gr (fun t => φ e * w₁ t + (1 - φ e) * extendDel Gr {e} w₀ t) u v =
          φ e * load Gr w₁ u v + (1 - φ e) * load Gr (extendDel Gr {e} w₀) u v := by
        unfold load; rw [sum_add_distrib, mul_sum, mul_sum]
      rw [hsplit, load_extendDel, hw₁ u v huv]
      by_cases hue : s(u, v) = e
      · subst hue
        rw [load_del_eq_zero Gr _ w₀ huv.ne (mem_singleton_self _)]
        simp [he]
      · have huv' : (del Gr {e}).Adj u v := by
          simp [del, SimpleGraph.deleteEdges_adj, huv, hue]
        rw [hw₀ u v huv']
        by_cases hR : s(u, v) ∈ R₀
        · simp [hR]; ring
        · simp [hR, hue]

end NashWilliams18

namespace NashWilliams18

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] in
/-- Greedy edge-partition: an edge set of maximum degree `≤ Δ` can be split into `C` classes of
maximum degree `≤ d` as soon as `2Δ ≤ C d`. (Replaces Vizing's theorem in Lemma 11.9.) -/
theorem exists_edge_partition (Δ d C : ℕ) (hC : 1 ≤ C) (hCd : 2 * Δ ≤ C * d) :
    ∀ E : Finset (Sym2 W), (∀ e ∈ E, ¬ e.IsDiag) → (∀ v, (E.filter (fun f => v ∈ f)).card ≤ Δ) →
      ∃ c : Sym2 W → Fin C, ∀ v (i : Fin C),
        (E.filter (fun f => v ∈ f ∧ c f = i)).card ≤ d := by
  intro E
  induction E using Finset.induction_on with
  | empty => intro _ _; exact ⟨fun _ => ⟨0, hC⟩, fun v i => by simp⟩
  | insert e E₀ he ih =>
    intro hdiag hdeg
    obtain ⟨c₀, hc₀⟩ := ih (fun f hf => hdiag f (mem_insert_of_mem hf)) (fun v =>
      le_trans (card_le_card (filter_subset_filter _ (subset_insert _ _))) (hdeg v))
    -- the number of saturated colours at an end `a` of `e`
    have hbad : ∀ a, a ∈ e → (univ.filter (fun i : Fin C =>
        d ≤ (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card)).card * d + 1 ≤ Δ := by
      intro a ha
      have hfib : (E₀.filter (fun f => a ∈ f)).card =
          ∑ i : Fin C, (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card := by
        rw [card_eq_sum_card_fiberwise (f := c₀) (t := univ) (fun _ _ => by simp)]
        refine sum_congr rfl fun i _ => ?_
        rw [filter_filter]
      have hdegE : (E₀.filter (fun f => a ∈ f)).card + 1 ≤ Δ := by
        have h := hdeg a
        rw [filter_insert, if_pos ha, card_insert_of_notMem (by simp [he])] at h
        exact h
      have hle : (univ.filter (fun i : Fin C =>
          d ≤ (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card)).card * d ≤
          ∑ i : Fin C, (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card := by
        calc _ = ∑ i ∈ univ.filter (fun i : Fin C =>
              d ≤ (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card), d := by
              rw [sum_const, smul_eq_mul]
          _ ≤ ∑ i ∈ univ.filter (fun i : Fin C =>
              d ≤ (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card),
                (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card :=
              sum_le_sum fun i hi => (mem_filter.mp hi).2
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              (fun _ _ _ => Nat.zero_le _)
      omega
    induction e using Sym2.ind with
    | _ a b =>
    have hab : a ≠ b := by
      have := hdiag s(a, b) (mem_insert_self _ _); simpa using this
    have ha := hbad a (Sym2.mem_mk_left a b)
    have hb := hbad b (Sym2.mem_mk_right a b)
    set Ba := univ.filter (fun i : Fin C => d ≤ (E₀.filter (fun f => a ∈ f ∧ c₀ f = i)).card)
    set Bb := univ.filter (fun i : Fin C => d ≤ (E₀.filter (fun f => b ∈ f ∧ c₀ f = i)).card)
    have hunion : (Ba ∪ Bb).card < C := by
      have h1 := card_union_le Ba Bb
      by_contra hcon; push_neg at hcon
      have h2 : C * d ≤ (Ba.card + Bb.card) * d := Nat.mul_le_mul_right _ (hcon.trans h1)
      nlinarith
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ Ba ∪ Bb := by
      by_contra hcon; push_neg at hcon
      have : (univ : Finset (Fin C)) ⊆ Ba ∪ Bb := fun i _ => hcon i
      have := card_le_card this
      simp at this; omega
    simp only [mem_union, Ba, Bb, mem_filter, mem_univ, true_and, not_or, not_le] at hi₀
    refine ⟨Function.update c₀ s(a, b) i₀, fun v i => ?_⟩
    have hsplit : (insert s(a, b) E₀).filter (fun f => v ∈ f ∧ Function.update c₀ s(a, b) i₀ f = i)
        ⊆ insert s(a, b) (E₀.filter (fun f => v ∈ f ∧ c₀ f = i)) := by
      intro f hf
      simp only [mem_filter, mem_insert] at hf ⊢
      rcases hf with ⟨rfl | hf, hv, hc⟩
      · left; rfl
      · right
        have hne : f ≠ s(a, b) := fun h => he (h ▸ hf)
        rw [Function.update_of_ne hne] at hc
        exact ⟨hf, hv, hc⟩
    by_cases hvi : (v = a ∨ v = b) ∧ i = i₀
    · refine (card_le_card hsplit).trans ((card_insert_le _ _).trans ?_)
      obtain ⟨hv, rfl⟩ := hvi
      rcases hv with rfl | rfl <;> omega
    · have hsub : (insert s(a, b) E₀).filter
          (fun f => v ∈ f ∧ Function.update c₀ s(a, b) i₀ f = i) ⊆
          E₀.filter (fun f => v ∈ f ∧ c₀ f = i) := by
        intro f hf
        have hf' := hsplit hf
        rcases mem_insert.mp hf' with rfl | h
        · exfalso
          simp only [mem_filter, Function.update_self, Sym2.mem_iff] at hf
          exact hvi ⟨hf.2.1, hf.2.2.symm⟩
        · exact h
      exact (card_le_card hsub).trans (hc₀ v i)

/-- **Lemma 11.9** (with the edge partition given explicitly).  Suppose the edges of `Gr` are
split into `C` classes of maximum degree `≤ d`, and `Gr - H` has a fractional triangle
decomposition whenever `H` has maximum degree `≤ d`.  Then every target `φ` with values in
`[1 - 1/C, 1]` on the edges is the load of a fractional triangle packing of `Gr`. -/
theorem lemma_11_9 (Gr : SimpleGraph W) [DecidableRel Gr.Adj] (d C : ℕ) (hC : 1 ≤ C)
    (c : Sym2 W → Fin C)
    (hc : ∀ v (i : Fin C), (Gr.edgeFinset.filter (fun f => v ∈ f ∧ c f = i)).card ≤ d)
    (hfrac : ∀ H : Finset (Sym2 W), (∀ v, (H.filter (fun f => v ∈ f)).card ≤ d) →
      NashWilliams.HasFractionalTriangleDecomposition (del Gr H))
    (φ : Sym2 W → ℝ) (hφ : ∀ e ∈ Gr.edgeFinset, 1 - 1 / (C : ℝ) ≤ φ e ∧ φ e ≤ 1) :
    ∃ w : Finset W → ℝ, (∀ t, 0 ≤ w t) ∧ ∀ u v, Gr.Adj u v → load Gr w u v = φ s(u, v) := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  set R : Fin C → Finset (Sym2 W) := fun i => Gr.edgeFinset.filter (fun f => c f = i)
  have hw : ∀ i : Fin C, ∃ w : Finset W → ℝ, (∀ t, 0 ≤ w t) ∧ ∀ u v, Gr.Adj u v →
      load Gr w u v = if s(u, v) ∈ R i then 1 - C * (1 - φ s(u, v)) else 1 := by
    intro i
    refine prop_11_8 (R i) Gr (fun R' hR' => hfrac R' fun v => ?_)
      (fun e => 1 - C * (1 - φ e)) (fun e he => ?_)
    · refine (card_le_card fun f hf => ?_).trans (hc v i)
      simp only [mem_filter] at hf ⊢
      have := hR' hf.1
      simp only [R, mem_filter] at this
      exact ⟨this.1, hf.2, this.2⟩
    · simp only [R, mem_filter] at he
      obtain ⟨h1, h2⟩ := hφ e he.1
      have h3 : (C : ℝ) * (1 / C) = 1 := by field_simp
      constructor <;> nlinarith
  choose w hw0 hwload using hw
  refine ⟨fun t => (1 / (C : ℝ)) * ∑ i, w i t, fun t => ?_, fun u v huv => ?_⟩
  · have := fun i => hw0 i t
    have : 0 ≤ ∑ i, w i t := sum_nonneg fun i _ => this i
    positivity
  · have hl : load Gr (fun t => (1 / (C : ℝ)) * ∑ i, w i t) u v =
        (1 / (C : ℝ)) * ∑ i, load Gr (w i) u v := by
      unfold load; rw [← mul_sum, sum_comm]
    rw [hl]
    simp_rw [hwload _ u v huv]
    have hmem : ∀ i, (s(u, v) ∈ R i ↔ c s(u, v) = i) := by
      intro i; simp [R, huv]
    simp_rw [hmem]
    have : ∑ i : Fin C, (if c s(u, v) = i then 1 - C * (1 - φ s(u, v)) else (1 : ℝ)) =
        C + (- C * (1 - φ s(u, v))) := by
      have : ∀ i : Fin C, (if c s(u, v) = i then 1 - C * (1 - φ s(u, v)) else (1 : ℝ)) =
          1 + (if c s(u, v) = i then - C * (1 - φ s(u, v)) else 0) := by
        intro i; split_ifs <;> ring
      simp_rw [this, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
      simp
    rw [this]
    field_simp
    ring

end NashWilliams18

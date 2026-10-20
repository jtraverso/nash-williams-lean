/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.WalkCount
public import RequestProject.NW18.Glue

@[expose] public section

/-!
# The two phases of the proof of the configuration count

* Phase 1 (common neighbourhood `N` of `v₁, v₂`, walks of length five from `u₁` to `u₂`):
  if there are few such walks then `|N| ≈ n/2`, `N` is structured, and `u₂` has at most about
  `|N|/2` neighbours in `N`.
* Phase 2 uses the stability lemma on a large part of the complement of `N`.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma nbIn_univ (y : V) : nbIn G univ y = G.neighborFinset y := by
  ext z; simp [nbIn, SimpleGraph.mem_neighborFinset]

/-- Every vertex is adjacent to all but `n/4` vertices of any set. -/
lemma card_nbIn_ge (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (S : Finset V) (y : V) :
    (S.card : ℝ) - Fintype.card V / 4 ≤ (nbIn G S y).card := by
  have h1 := card_filter_add_card_filter_not (s := S) (G.Adj y)
  have h2 : (S.filter (fun z => ¬ G.Adj y z)).card ≤ Fintype.card V - G.degree y := by
    have hsub : S.filter (fun z => ¬ G.Adj y z) ⊆ univ \ G.neighborFinset y := by
      intro z hz
      simp only [mem_filter] at hz
      simp [SimpleGraph.mem_neighborFinset, hz.2]
    refine (card_le_card hsub).trans ?_
    rw [card_sdiff_of_subset (subset_univ _), card_univ, SimpleGraph.card_neighborFinset_eq_degree]
  have h3 : G.minDegree ≤ G.degree y := G.minDegree_le_degree y
  have h4 : G.degree y ≤ Fintype.card V := (G.degree_lt_card_verts y).le
  have h5 : ((S.filter (fun z => ¬ G.Adj y z)).card : ℝ) ≤ Fintype.card V - G.degree y := by
    rw [← Nat.cast_sub h4]; exact_mod_cast h2
  have h6 : (3 : ℝ) * Fintype.card V ≤ 4 * G.minDegree := by exact_mod_cast hδ
  have h7 : (G.minDegree : ℝ) ≤ G.degree y := by exact_mod_cast h3
  have h8 : ((nbIn G S y).card : ℝ) + (S.filter (fun z => ¬ G.Adj y z)).card = S.card := by
    exact_mod_cast h1
  linarith

omit [DecidableEq V] in
lemma comNb_eq (v₁ v₂ : V) : comNb G v₁ v₂ = nbIn G (nbIn G univ v₁) v₂ := by
  ext x; simp [comNb, nbIn]

lemma card_comNb_ge (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (v₁ v₂ : V) :
    (Fintype.card V : ℝ) / 2 ≤ (comNb G v₁ v₂).card := by
  rw [comNb_eq]
  have h1 := card_nbIn_ge G hδ (nbIn G univ v₁) v₂
  have h2 := card_nbIn_ge G hδ univ v₁
  rw [card_univ] at h2
  linarith

omit [Fintype V] in
/-- Codegree lower bound inside a large set. -/
lemma card_inter_ge (D A C : Finset V) (hA : A ⊆ D) (hC : C ⊆ D) :
    (A.card : ℝ) + C.card - D.card ≤ (A ∩ C).card := by
  have h1 := card_union_add_card_inter A C
  have h2 : (A ∪ C).card ≤ D.card := card_le_card (union_subset hA hC)
  have : ((A ∪ C).card : ℝ) + (A ∩ C).card = A.card + C.card := by exact_mod_cast h1
  have : ((A ∪ C).card : ℝ) ≤ D.card := by exact_mod_cast h2
  linarith

/-- **Phase 1a.**  If `D` has more than `(1/2 + γ) n` vertices and every vertex misses at most
`n/4` of them, there are many walks of length five. -/
lemma phase1a (D : Finset V) (s t : V) {γ : ℝ} (hγ : 0 ≤ γ)
    (hdeg : ∀ y, (D.card : ℝ) - Fintype.card V / 4 ≤ (nbIn G D y).card)
    (hD : (1 / 2 + γ) * Fintype.card V ≤ D.card) :
    γ * (Fintype.card V : ℝ) ^ 4 / 64 ≤ ∑ d ∈ nbIn G D t, (walk4 G D s d : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  have hq : ∀ y, n / 4 ≤ ((nbIn G D y).card : ℝ) := fun y => by
    have := hdeg y; nlinarith
  have hcod : ∀ a c, γ * n ≤ ((nbIn G D a ∩ nbIn G D c).card : ℝ) := fun a c => by
    have := card_inter_ge D _ _ (nbIn_subset G D a) (nbIn_subset G D c)
    have := hdeg a; have := hdeg c
    nlinarith
  have hw : ∀ d, (n / 4) * (n / 4) * (γ * n) ≤ (walk4 G D s d : ℝ) := fun d => by
    unfold walk4
    push_cast
    calc (n / 4) * (n / 4) * (γ * n)
        ≤ ((nbIn G D s).card : ℝ) * ((nbIn G D d).card : ℝ) * (γ * n) := by
          have := hq s; have := hq d
          have : 0 ≤ γ * n := by positivity
          gcongr
      _ = ∑ a ∈ nbIn G D s, ∑ c ∈ nbIn G D d, γ * n := by
          simp [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun a _ => sum_le_sum fun c _ => hcod a c
  calc γ * n ^ 4 / 64 = (n / 4) * ((n / 4) * (n / 4) * (γ * n)) := by ring
    _ ≤ ((nbIn G D t).card : ℝ) * ((n / 4) * (n / 4) * (γ * n)) := by
        have := hq t
        have : 0 ≤ (n / 4) * (n / 4) * (γ * n) := by positivity
        gcongr
    _ = ∑ d ∈ nbIn G D t, (n / 4) * (n / 4) * (γ * n) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun d _ => hw d

omit [Fintype V] in
lemma card_inter_ge_symmDiff (A C Y : Finset V) :
    (Y.card : ℝ) - (symmDiff A Y).card - (symmDiff C Y).card ≤ (A ∩ C).card := by
  have hsub : Y ⊆ (A ∩ C) ∪ (Y \ A) ∪ (Y \ C) := by
    intro y hy
    by_cases ha : y ∈ A <;> by_cases hc : y ∈ C <;> simp [ha, hc, hy]
  have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have h2 := card_le_symmDiff_right A Y
  have h3 := card_le_symmDiff_right C Y
  have : (Y.card : ℝ) ≤ (A ∩ C).card + (Y \ A).card + (Y \ C).card := by exact_mod_cast h1
  have : ((Y \ A).card : ℝ) ≤ (symmDiff A Y).card := by exact_mod_cast h2
  have : ((Y \ C).card : ℝ) ≤ (symmDiff C Y).card := by exact_mod_cast h3
  linarith

omit [Fintype V] in
/-- Lower bound for `walk4` from structured neighbourhoods. -/
lemma walk4_ge (D : Finset V) (s d : V) (Y A' C' : Finset V) (hA : A' ⊆ nbIn G D s)
    (hC : C' ⊆ nbIn G D d) {e : ℝ}
    (hAe : ∀ a ∈ A', ((symmDiff (nbIn G D a) Y).card : ℝ) ≤ e)
    (hCe : ∀ c ∈ C', ((symmDiff (nbIn G D c) Y).card : ℝ) ≤ e) :
    (A'.card : ℝ) * C'.card * (Y.card - 2 * e) ≤ walk4 G D s d := by
  unfold walk4
  push_cast
  calc (A'.card : ℝ) * C'.card * (Y.card - 2 * e)
      = ∑ a ∈ A', ∑ c ∈ C', ((Y.card : ℝ) - 2 * e) := by
        simp [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ a ∈ A', ∑ c ∈ C', ((nbIn G D a ∩ nbIn G D c).card : ℝ) := by
        refine sum_le_sum fun a ha => sum_le_sum fun c hc => ?_
        have := card_inter_ge_symmDiff (nbIn G D a) (nbIn G D c) Y
        linarith [hAe a ha, hCe c hc]
    _ ≤ ∑ a ∈ A', ∑ c ∈ nbIn G D d, ((nbIn G D a ∩ nbIn G D c).card : ℝ) :=
        sum_le_sum fun a _ => sum_le_sum_of_subset_of_nonneg hC (fun _ _ _ => by positivity)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hA
        (fun _ _ _ => sum_nonneg fun _ _ => by positivity)

omit [Fintype V] in
lemma card_ge_of_symmDiff (A B : Finset V) :
    (A.card : ℝ) - (symmDiff A B).card ≤ B.card := by
  have h1 := card_sdiff_add_card_inter A B
  have h2 := card_le_symmDiff_left A B
  have h3 : (A ∩ B).card ≤ B.card := card_le_card inter_subset_right
  have : ((A \ B).card : ℝ) + (A ∩ B).card = A.card := by exact_mod_cast h1
  have : ((A \ B).card : ℝ) ≤ (symmDiff A B).card := by exact_mod_cast h2
  have : ((A ∩ B).card : ℝ) ≤ B.card := by exact_mod_cast h3
  linarith

omit [Fintype V] in
lemma card_sdiff_ge (A E : Finset V) : (A.card : ℝ) - E.card ≤ (A \ E).card := by
  have h1 := card_sdiff_add_card_inter A E
  have h3 : (A ∩ E).card ≤ E.card := card_le_card inter_subset_right
  have : ((A \ E).card : ℝ) + (A ∩ E).card = A.card := by exact_mod_cast h1
  have : ((A ∩ E).card : ℝ) ≤ E.card := by exact_mod_cast h3
  linarith

omit [Fintype V] in
lemma phase1c_walk (D N₁ E W : Finset V) (u₁ d : V) {b : Bool} {e : ℝ} (hN₁ : N₁ ⊆ D)
    (hdev : ∀ x ∈ D, x ∉ E → ((symmDiff (nbIn G D x) (tgt D N₁ b x)).card : ℝ) ≤ e)
    (htgtN₁ : ∀ a ∈ N₁, tgt D N₁ b a = W) (htgtd : tgt D N₁ b d = N₁) (hdD : d ∈ D)
    (hdE : d ∉ E) (hEc : (E.card : ℝ) ≤ e) (hs : ((symmDiff (nbIn G D u₁) N₁).card : ℝ) ≤ e)
    (hem : e ≤ (D.card : ℝ) / 12) (hN₁low : (D.card : ℝ) / 2 - e ≤ N₁.card)
    (hWc : (D.card : ℝ) / 2 - e ≤ W.card) :
    ((D.card : ℝ) / 4) ^ 3 ≤ (walk4 G D u₁ d : ℝ) := by
  have hdd := hdev d hdD hdE
  rw [htgtd] at hdd
  have hA : (nbIn G D u₁ ∩ N₁) \ E ⊆ nbIn G D u₁ := sdiff_subset.trans inter_subset_left
  have hC : (nbIn G D d ∩ N₁) \ E ⊆ nbIn G D d := sdiff_subset.trans inter_subset_left
  have hAe : ∀ a ∈ (nbIn G D u₁ ∩ N₁) \ E, ((symmDiff (nbIn G D a) W).card : ℝ) ≤ e := by
    intro a ha
    obtain ⟨ha1, haE⟩ := mem_sdiff.mp ha
    have haN := (mem_inter.mp ha1).2
    have := hdev a (hN₁ haN) haE
    rwa [htgtN₁ a haN] at this
  have hCe : ∀ c ∈ (nbIn G D d ∩ N₁) \ E, ((symmDiff (nbIn G D c) W).card : ℝ) ≤ e := by
    intro c hc
    obtain ⟨hc1, hcE⟩ := mem_sdiff.mp hc
    have hcN := (mem_inter.mp hc1).2
    have := hdev c (hN₁ hcN) hcE
    rwa [htgtN₁ c hcN] at this
  have hw := walk4_ge G D u₁ d W _ _ hA hC hAe hCe
  have key : ∀ y : V, ((symmDiff (nbIn G D y) N₁).card : ℝ) ≤ e →
      (D.card : ℝ) / 2 - 3 * e ≤ (((nbIn G D y ∩ N₁) \ E).card : ℝ) := by
    intro y hy
    have h1 := card_sdiff_ge (nbIn G D y ∩ N₁) E
    have h3 : ((N₁ \ nbIn G D y).card : ℝ) ≤ (symmDiff (nbIn G D y) N₁).card := by
      exact_mod_cast card_le_symmDiff_right _ _
    have h5 := card_sdiff_add_card_inter N₁ (nbIn G D y)
    rw [inter_comm] at h5
    have h4 : (N₁.card : ℝ) ≤ (nbIn G D y ∩ N₁).card + (N₁ \ nbIn G D y).card := by
      exact_mod_cast (by omega : N₁.card ≤ (nbIn G D y ∩ N₁).card + (N₁ \ nbIn G D y).card)
    linarith
  have hAc := key u₁ hs
  have hCc := key d hdd
  have hm4 : 0 ≤ (D.card : ℝ) / 4 := by positivity
  have hA4 : (D.card : ℝ) / 4 ≤ (((nbIn G D u₁ ∩ N₁) \ E).card : ℝ) := by linarith
  have hC4 : (D.card : ℝ) / 4 ≤ (((nbIn G D d ∩ N₁) \ E).card : ℝ) := by linarith
  have hW4 : (D.card : ℝ) / 4 ≤ (W.card : ℝ) - 2 * e := by linarith
  calc ((D.card : ℝ) / 4) ^ 3 = ((D.card : ℝ) / 4) * ((D.card : ℝ) / 4) * ((D.card : ℝ) / 4) := by
        ring
    _ ≤ (((nbIn G D u₁ ∩ N₁) \ E).card : ℝ) * ((nbIn G D d ∩ N₁) \ E).card *
        (W.card - 2 * e) := by gcongr
    _ ≤ _ := hw

lemma arith_K {k m σ : ℝ} (hm : 0 < m) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 240)
    (h : k * (m / 4) ^ 3 ≤ σ ^ 6 * m ^ 4 / 2) : k ≤ σ * m := by
  have hσ5 : σ ^ 5 ≤ 1 / 32 := by
    have : σ ^ 5 ≤ (1 / 240) ^ 5 := by gcongr
    linarith [show ((1 : ℝ) / 240) ^ 5 ≤ 1 / 32 by norm_num]
  have hm3 : 0 < m ^ 3 := by positivity
  have h2 : k * m ^ 3 ≤ (32 * σ ^ 6 * m) * m ^ 3 := by
    have : k * (m / 4) ^ 3 = k * m ^ 3 / 64 := by ring
    have : σ ^ 6 * m ^ 4 / 2 = (32 * σ ^ 6 * m) * m ^ 3 / 64 := by ring
    linarith
  have h3 : k ≤ 32 * σ ^ 6 * m := le_of_mul_le_mul_right h2 hm3
  have h4 : 32 * σ ^ 6 * m ≤ σ * m := by
    have : 32 * σ ^ 6 = σ * (32 * σ ^ 5) := by ring
    rw [this]
    have : σ * (32 * σ ^ 5) ≤ σ * 1 := mul_le_mul_of_nonneg_left (by linarith) hσ0.le
    nlinarith
  linarith

/-- **Phase 1.** -/
theorem phase1 (D : Finset V) (u₁ u₂ : V) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 240)
    (hn : 0 < Fintype.card V) (hD : (Fintype.card V : ℝ) / 2 ≤ D.card)
    (hdeg : ∀ y, (D.card : ℝ) - Fintype.card V / 4 ≤ (nbIn G D y).card)
    (hW : ∑ d ∈ nbIn G D u₂, (walk4 G D u₁ d : ℝ) ≤ σ ^ 6 * (Fintype.card V : ℝ) ^ 4 / 32) :
    ∃ N₁ ⊆ D, ∃ b : Bool, ∃ E ⊆ D, (E.card : ℝ) ≤ 20 * σ * D.card ∧
      (∀ x ∈ D, x ∉ E →
        ((symmDiff (nbIn G D x) (tgt D N₁ b x)).card : ℝ) ≤ 20 * σ * D.card) ∧
      (N₁.card : ℝ) ≤ D.card / 2 + 20 * σ * D.card ∧
      ((D \ N₁).card : ℝ) ≤ D.card / 2 + 20 * σ * D.card ∧
      ((nbIn G D u₂).card : ℝ) ≤ D.card / 2 + 50 * σ * D.card := by
  set m : ℝ := (D.card : ℝ) with hm
  set n : ℝ := (Fintype.card V : ℝ) with hnn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm0 : 0 < m := by linarith
  have hmN : 0 < D.card := by
    have h := hm0; rw [hm] at h; exact_mod_cast h
  have hhalf : ∀ y, m / 2 ≤ ((nbIn G D y).card : ℝ) := fun y => by
    have := hdeg y; linarith
  have hn4 : n ^ 4 ≤ 16 * m ^ 4 := by
    have : n ≤ 2 * m := by linarith
    have h0 : 0 ≤ n := hn0.le
    calc n ^ 4 ≤ (2 * m) ^ 4 := by gcongr
      _ = 16 * m ^ 4 := by ring
  have hWm : ∑ d ∈ nbIn G D u₂, (walk4 G D u₁ d : ℝ) ≤ σ ^ 6 * m ^ 4 / 2 := by
    have : σ ^ 6 * n ^ 4 / 32 ≤ σ ^ 6 * (16 * m ^ 4) / 32 := by
      have : 0 ≤ σ ^ 6 := by positivity
      gcongr
    linarith
  -- choose `x₄`
  have hQne : (nbIn G D u₂).Nonempty := by
    rw [← card_pos]
    have h := hhalf u₂
    have h' : (0 : ℝ) < (nbIn G D u₂).card := by linarith
    exact_mod_cast h'
  obtain ⟨x₄, hx₄, hx₄w⟩ := exists_mul_card_le_sum (nbIn G D u₂) hQne
    (fun d => (walk4 G D u₁ d : ℝ))
  have hwalk : (walk4 G D u₁ x₄ : ℝ) ≤ σ ^ 6 * m ^ 3 := by
    have h1 := hhalf u₂
    have h2 : (walk4 G D u₁ x₄ : ℝ) * (m / 2) ≤ σ ^ 6 * m ^ 4 / 2 := by
      calc _ ≤ (walk4 G D u₁ x₄ : ℝ) * (nbIn G D u₂).card :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ _ := hx₄w.trans hWm
    have : (walk4 G D u₁ x₄ : ℝ) * m ≤ σ ^ 6 * m ^ 3 * m := by nlinarith
    exact le_of_mul_le_mul_right this hm0
  obtain ⟨N₁, hN₁, b, E, hE, hEc, hdev, hs, ht⟩ :=
    stab4 G D u₁ x₄ (ε := 0) (κ := σ ^ 6) hσ0 (by linarith) le_rfl (by positivity) le_rfl hmN
      (fun y => by have := hhalf y; linarith) hwalk
  set e := 20 * σ * m with he
  have hem : e ≤ m / 12 := by
    have : 20 * σ ≤ 1 / 12 := by linarith
    rw [he]; nlinarith
  have he0 : 0 ≤ e := by positivity
  -- sizes of the sides
  have hsplit : (N₁.card : ℝ) + (D \ N₁).card = m := by
    have := card_sdiff_of_subset' hN₁
    rw [hm]; exact_mod_cast (by omega : N₁.card + (D \ N₁).card = D.card)
  have hN₁low : m / 2 - e ≤ N₁.card := by
    have := card_ge_of_symmDiff (nbIn G D u₁) N₁
    linarith [hhalf u₁]
  have hN₂low : m / 2 - e ≤ (D \ N₁).card := by
    have := card_ge_of_symmDiff (nbIn G D x₄) (D \ N₁)
    linarith [hhalf x₄]
  refine ⟨N₁, hN₁, b, E, hE, hEc, hdev, by linarith, by linarith, ?_⟩
  -- Phase 1c: the wrong side
  set W := if b then D \ N₁ else N₁ with hW'
  have hWD : W ⊆ D := by rw [hW']; split_ifs; exacts [sdiff_subset, hN₁]
  have hWc : m / 2 - e ≤ W.card := by rw [hW']; split_ifs <;> linarith
  have hDW : ((D \ W).card : ℝ) ≤ m / 2 + e := by
    rw [hW']; split_ifs
    · rw [Finset.sdiff_sdiff_eq_self hN₁]; linarith
    · linarith
  have htgtN₁ : ∀ a ∈ N₁, tgt D N₁ b a = W := fun a ha => by
    rw [hW']; cases b <;> simp [tgt, ha]
  have htgtW : ∀ d ∈ W, tgt D N₁ b d = N₁ := fun d hd => by
    rw [hW'] at hd; cases b <;> simp_all [tgt]
  set K := (nbIn G D u₂ ∩ W) \ E with hK
  have hKw : ∀ d ∈ K, (m / 4) ^ 3 ≤ (walk4 G D u₁ d : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdE⟩ := mem_sdiff.mp hd
    exact phase1c_walk G D N₁ E W u₁ d hN₁ hdev htgtN₁ (htgtW d (mem_inter.mp hd1).2)
      (hWD (mem_inter.mp hd1).2) hdE hEc hs hem hN₁low hWc
  have hKc : (K.card : ℝ) ≤ σ * m := by
    have h1 : (K.card : ℝ) * (m / 4) ^ 3 ≤ σ ^ 6 * m ^ 4 / 2 := by
      calc (K.card : ℝ) * (m / 4) ^ 3 = ∑ d ∈ K, (m / 4) ^ 3 := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ d ∈ K, (walk4 G D u₁ d : ℝ) := sum_le_sum hKw
        _ ≤ ∑ d ∈ nbIn G D u₂, (walk4 G D u₁ d : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans inter_subset_left)
              (fun _ _ _ => by positivity)
        _ ≤ _ := hWm
    exact arith_K hm0 hσ0 hσ h1
  -- final count
  have hQ : ((nbIn G D u₂).card : ℝ) ≤ (D \ W).card + K.card + E.card := by
    have hsub : nbIn G D u₂ ⊆ (D \ W) ∪ K ∪ E := by
      intro x hx
      have hxD := nbIn_subset G D u₂ hx
      by_cases hxW : x ∈ W
      · by_cases hxE : x ∈ E
        · exact mem_union_right _ hxE
        · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hx, hxW⟩, hxE⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨hxD, hxW⟩))
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    exact_mod_cast this
  linarith

end NashWilliams18

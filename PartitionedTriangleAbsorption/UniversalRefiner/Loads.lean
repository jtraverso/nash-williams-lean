/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Heap

/-!
# Loads of the concrete construction

* the mod-three wires get the roots `(k mod n, k+1 mod n)` (`mdRoots`), the adjustment cycles
  the roots `(0, 1)`; their root loads are `O(N / n)` and `O(1)`;
* `card_theReqs_le`, `card_theLib_le`: sizes of the library and of the request family;
* `rootLoad_theReqs_le`: the total root load at a vertex;
* `two_mul_card_le`, `antiEdgeful_of_minDegree`: the reserve size and the anti-edge supply.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Roots of the mod-three wires. -/
noncomputable def mdRoots (u0 : V) (k : ℕ) : V × V :=
  (vtx u0 (k % Fintype.card V), vtx u0 ((k + 1) % Fintype.card V))

theorem mod_ne_succ_mod {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : k % n ≠ (k + 1) % n := by
  intro h
  have hr := Nat.mod_lt k (by omega : 0 < n)
  have hs : (k + 1) % n = (k % n + 1) % n := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [hs] at h
  rcases Nat.lt_or_ge (k % n + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h; omega
  · have : k % n + 1 = n := by omega
    rw [this, Nat.mod_self] at h; omega

omit [DecidableEq V] in
theorem mdRoots_ne (u0 : V) (hn : 2 ≤ Fintype.card V) (k : ℕ) :
    (mdRoots u0 k).1 ≠ (mdRoots u0 k).2 := by
  intro h
  have := congrArg idx h
  simp only [mdRoots] at this
  rw [idx_vtx u0 (Nat.mod_lt _ (by omega)), idx_vtx u0 (Nat.mod_lt _ (by omega))] at this
  exact mod_ne_succ_mod hn k this

theorem card_filter_add_mod_le (M c n i : ℕ) :
    ((range M).filter fun k => (k + c) % n = i).card ≤ (M + c) / n + 1 := by
  refine (card_le_card_of_injOn (fun k => (k + c) / n) (t := range ((M + c) / n + 1)) ?_ ?_).trans
    (by simp)
  · intro k hk
    have hk' := mem_range.mp (mem_filter.mp (mem_coe.mp hk)).1
    simp only [coe_range, Set.mem_Iio]
    have := Nat.div_le_div_right (c := n) (show k + c ≤ M + c by omega)
    omega
  · intro k hk k' hk' h
    have h1 := (mem_filter.mp (mem_coe.mp hk)).2
    have h2 := (mem_filter.mp (mem_coe.mp hk')).2
    have e1 := Nat.div_add_mod (k + c) n
    have e2 := Nat.div_add_mod (k' + c) n
    simp only at h
    rw [h, h1] at e1
    rw [h2] at e2
    omega

theorem rootLoad_mdReqs_le (u0 : V) (hn : 2 ≤ Fintype.card V) (hmap : ℕ → V → V) (adr : V × V)
    (N : ℕ) (x : V) :
    rootLoad (mdReqs N) (fun r => (rootPair hmap (mdRoots u0) adr r).1)
      (fun r => (rootPair hmap (mdRoots u0) adr r).2) x ≤
      12 * ((N + 1) / Fintype.card V + 1) := by
  have hn0 : 0 < Fintype.card V := by omega
  have key : ∀ c, c ≤ 1 → ((mdReqs (V := V) N).filter fun r => r ∈ (((range (N - 1)).filter
      fun k => (k + c) % Fintype.card V = idx x) ×ˢ (univ : Finset (Fin 3)) ×ˢ
        (univ : Finset Bool)).image fun q => (Req.md q.1 q.2.1 q.2.2 : Req V)).card ≤
      6 * ((N + 1) / Fintype.card V + 1) := by
    intro c hc
    refine (card_le_card (filter_subset_filter _ (subset_refl _) |>.trans
      (fun r hr => (mem_filter.mp hr).2))).trans (card_image_le.trans ?_)
    rw [card_product, card_product, card_univ, card_univ, Fintype.card_fin, Fintype.card_bool]
    have h1 := card_filter_add_mod_le (N - 1) c (Fintype.card V) (idx x)
    have h2 := Nat.div_le_div_right (c := Fintype.card V) (show N - 1 + c ≤ N + 1 by omega)
    nlinarith
  unfold rootLoad
  have hA : ((mdReqs (V := V) N).filter fun r => (rootPair hmap (mdRoots u0) adr r).1 = x) ⊆
      (mdReqs (V := V) N).filter fun r => r ∈ (((range (N - 1)).filter
        fun k => (k + 0) % Fintype.card V = idx x) ×ˢ (univ : Finset (Fin 3)) ×ˢ
          (univ : Finset Bool)).image fun q => (Req.md q.1 q.2.1 q.2.2 : Req V) := by
    intro r hr
    obtain ⟨hr, hx⟩ := mem_filter.mp hr
    refine mem_filter.mpr ⟨hr, ?_⟩
    obtain ⟨⟨k, c, b⟩, hq, rfl⟩ := mem_image.mp hr
    simp only [rootPair, mdRoots] at hx
    have := congrArg idx hx
    rw [idx_vtx u0 (Nat.mod_lt _ hn0)] at this
    refine mem_image.mpr ⟨(k, c, b), ?_, rfl⟩
    simp only [mem_product, mem_range, mem_univ, and_true, mem_filter] at hq ⊢
    exact ⟨hq, by simpa using this⟩
  have hB : ((mdReqs (V := V) N).filter fun r => (rootPair hmap (mdRoots u0) adr r).2 = x) ⊆
      (mdReqs (V := V) N).filter fun r => r ∈ (((range (N - 1)).filter
        fun k => (k + 1) % Fintype.card V = idx x) ×ˢ (univ : Finset (Fin 3)) ×ˢ
          (univ : Finset Bool)).image fun q => (Req.md q.1 q.2.1 q.2.2 : Req V) := by
    intro r hr
    obtain ⟨hr, hx⟩ := mem_filter.mp hr
    refine mem_filter.mpr ⟨hr, ?_⟩
    obtain ⟨⟨k, c, b⟩, hq, rfl⟩ := mem_image.mp hr
    simp only [rootPair, mdRoots] at hx
    have := congrArg idx hx
    rw [idx_vtx u0 (Nat.mod_lt _ hn0)] at this
    refine mem_image.mpr ⟨(k, c, b), ?_, rfl⟩
    simp only [mem_product, mem_range, mem_univ, and_true, mem_filter] at hq ⊢
    exact ⟨hq, this⟩
  exact Nat.add_le_add ((card_le_card hA).trans (key 0 (by norm_num)))
    ((card_le_card hB).trans (key 1 le_rfl)) |>.trans (by omega)

omit [Fintype V] in
theorem rootLoad_le_two_mul {I : Type*} (s : Finset I) (u v : I → V) (x : V) :
    rootLoad s u v x ≤ 2 * s.card :=
  rootLoad_le_of_subset s s u v x fun _ hi _ => hi

omit [Fintype V] in
theorem card_mdReqs_le (N : ℕ) : (mdReqs N : Finset (Req V)).card ≤ 6 * N := by
  refine card_image_le.trans ?_
  simp only [card_product, card_range, card_univ, Fintype.card_fin, Fintype.card_bool]
  omega

theorem adjCount_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) : adjCount X hmap L ≤ 2 := by
  unfold adjCount
  have := Nat.mod_lt (parReqs X hmap L).card (by norm_num : 0 < 3)
  omega

/-- Size of the library. -/
theorem card_theLib_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) :
    (theLib X hmap L mdr adr).card ≤ 17 * ∑ l ∈ range L, (links X hmap l).card + 2 := by
  refine (card_filter_le _ _).trans ((card_union_le _ _).trans ?_)
  have := card_parLib_le X hmap L
  have := card_adjLib_le (V := V) (adjCount X hmap L)
  have := adjCount_le X hmap L
  omega

/-- Size of the request family. -/
theorem card_theReqs_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) (mdr : ℕ → V × V)
    (adr : V × V) :
    (theReqs X hmap L mdr adr).card ≤ 110 * ∑ l ∈ range L, (links X hmap l).card + 16 := by
  unfold theReqs allReqs
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  have := card_parReqs_le X hmap L
  have := card_adjReqs (V := V) (adjCount X hmap L)
  have := adjCount_le X hmap L
  have := card_mdReqs_le (V := V) (theLib X hmap L mdr adr).card
  have := card_theLib_le X hmap L mdr adr
  omega

/-- Root load of all requests at a vertex. -/
theorem rootLoad_theReqs_le (u0 : V) (hn : 2 ≤ Fintype.card V) (X : Finset (Sym2 V))
    (hmap : ℕ → V → V) (L : ℕ) (adr : V × V) (x : V) :
    rootLoad (theReqs X hmap L (mdRoots u0) adr)
      (fun r => (rootPair hmap (mdRoots u0) adr r).1)
      (fun r => (rootPair hmap (mdRoots u0) adr r).2) x ≤
      ∑ l ∈ range L, (2 * (vChain (links X hmap l) x).card +
        10 * hubWeight (links X hmap l) (hmap l) x) + 8 +
      12 * (((theLib X hmap L (mdRoots u0) adr).card + 1) / Fintype.card V + 1) := by
  unfold theReqs allReqs
  refine (rootLoad_union_le _ _ _ _ x).trans ?_
  refine (Nat.add_le_add_right (rootLoad_union_le _ _ _ _ x) _).trans ?_
  have h1 := parRootLoad_le X hmap L (mdRoots u0) adr x
  have h2 := (rootLoad_le_two_mul (adjReqs (adjCount X hmap L)) (fun r =>
    (rootPair hmap (mdRoots u0) adr r).1) (fun r => (rootPair hmap (mdRoots u0) adr r).2) x)
  rw [card_adjReqs] at h2
  have h3 := adjCount_le X hmap L
  have h4 := rootLoad_mdReqs_le u0 hn hmap adr (theLib X hmap L (mdRoots u0) adr).card x
  omega

omit [Fintype V] in
/-- Handshake for a loopless edge set. -/
theorem sum_vChain_card_eq [Fintype V] (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∑ u, (vChain X u).card = 2 * X.card := by
  have h1 : ∀ u, (vChain X u).card = ∑ π ∈ X, if u ∈ π then 1 else 0 := fun u => by
    rw [vChain, card_filter]
  simp only [h1]
  rw [sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun π hπ => ?_
  rw [← card_filter]
  have : (univ.filter fun u => u ∈ π) = {endA π, endB π} := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact mem_iff_endA_endB
  rw [this, card_pair (endA_ne_endB (hX π hπ))]

omit [DecidableEq V] in
/-- The anti-edge supply of a host of minimum degree at least `3n/4`. -/
theorem antiEdgeful_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ u, 3 / 4 * (Fintype.card V : ℝ) ≤ ((univ.filter (G.Adj u)).card : ℝ)) :
    AntiEdgeful part1 triFam G (1 / 2) := by
  classical
  intro τ _ i j k _ u v _ _ _
  have hk : ∀ w : V, part1 w = k := fun w => Subsingleton.elim _ _
  have hset : (univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ part1 w = k) =
      univ.filter (G.Adj u) ∩ univ.filter (G.Adj v) := by
    ext w
    simp [hk, G.adj_comm w v]
  rw [hset]
  have h1 := card_union_add_card_inter (univ.filter (G.Adj u)) (univ.filter (G.Adj v))
  have h2 : (univ.filter (G.Adj u) ∪ univ.filter (G.Adj v)).card ≤ Fintype.card V :=
    card_le_univ _
  have h1' : ((univ.filter (G.Adj u) ∪ univ.filter (G.Adj v)).card : ℝ) +
      ((univ.filter (G.Adj u) ∩ univ.filter (G.Adj v)).card : ℝ) =
      ((univ.filter (G.Adj u)).card : ℝ) + ((univ.filter (G.Adj v)).card : ℝ) := by
    exact_mod_cast h1
  have h2' : ((univ.filter (G.Adj u) ∪ univ.filter (G.Adj v)).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast h2
  linarith [hmin u, hmin v]

end PartitionedTriangleAbsorption.UniversalRefiner

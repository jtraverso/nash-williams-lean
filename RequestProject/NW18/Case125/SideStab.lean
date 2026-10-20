/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.F0HingeCount
import RequestProject.NW18.Case125.SideCost

/-!
# Few walks of length four force a side to be close to `T₂` or `T̄₂`

`sideCost_small_of_few_walks`: if a set `D` of `m` vertices induces a graph of minimum degree
at least `(1/2 − ε) m` and two vertices `s, t ∈ D` are joined by at most `σ⁶ m³` walks of length
four inside `D`, then `G[D]` is `O(σ)`-close to `T₂(m)` or `T̄₂(m)` (in the sense of `sideCost`,
with a part of size exactly `⌊m/2⌋`).  This is the stability lemma `stab4` (applied to the graph
`padGraph G D`, which agrees with `G` inside `D` and makes every outside vertex complete to
`D`), followed by a rebalancing of the parts.

`exists_sideCost_superset` transfers closeness from `D` to a superset `C ⊇ D`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph which agrees with `G` inside `D` and is complete on all other pairs. -/
def padGraph (G : SimpleGraph V) (D : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (x ∈ D → y ∈ D → G.Adj x y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hy hx => SimpleGraph.Adj.symm (h.2 hx hy)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) :
    DecidableRel (padGraph G D).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (x ∈ D → y ∈ D → G.Adj x y)))

omit [Fintype V] in
lemma nbIn_padGraph_of_mem (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) {y : V}
    (hy : y ∈ D) : nbIn (padGraph G D) D y = nbIn G D y := by
  ext z
  rw [mem_nbIn (padGraph G D), mem_nbIn G]
  change (z ∈ D ∧ (y ≠ z ∧ (y ∈ D → z ∈ D → G.Adj y z))) ↔
    (z ∈ D ∧ G.Adj y z)
  constructor
  · rintro ⟨hz, -, h⟩; exact ⟨hz, h hy hz⟩
  · rintro ⟨hz, h⟩; exact ⟨hz, G.ne_of_adj h, fun _ _ => h⟩

omit [Fintype V] in
lemma nbIn_padGraph_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) {y : V}
    (hy : y ∉ D) : nbIn (padGraph G D) D y = D := by
  ext z
  rw [mem_nbIn (padGraph G D)]
  change (z ∈ D ∧ (y ≠ z ∧ (y ∈ D → z ∈ D → G.Adj y z))) ↔ z ∈ D
  constructor
  · rintro ⟨hz, -⟩; exact hz
  · intro hz; exact ⟨hz, fun h => hy (h ▸ hz), fun h => absurd h hy⟩

omit [Fintype V] in
lemma walk4_padGraph (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) {s t : V}
    (hs : s ∈ D) (ht : t ∈ D) : walk4 (padGraph G D) D s t = walk4 G D s t := by
  unfold walk4
  rw [nbIn_padGraph_of_mem G D hs, nbIn_padGraph_of_mem G D ht]
  refine sum_congr rfl fun a ha => sum_congr rfl fun c hc => ?_
  rw [nbIn_padGraph_of_mem G D (nbIn_subset G D s ha),
    nbIn_padGraph_of_mem G D (nbIn_subset G D t hc)]

omit [Fintype V] in
open Classical in
/-- The edit cost is bounded by the vertex deviations from the target neighbourhoods. -/
lemma sideCost_le_of_dev (G : SimpleGraph V) [DecidableRel G.Adj] (D D1 E : Finset V)
    (bip : Bool) {e : ℝ} (he : 0 ≤ e) (hdev : ∀ x ∈ D, x ∉ E →
      ((symmDiff (nbIn G D x) (tgt D D1 bip x)).card : ℝ) ≤ e) :
    (sideCost G D D1 bip : ℝ) ≤ E.card * D.card + D.card * e := by
  unfold sideCost
  suffices H : ((∑ x ∈ D, (D.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget D1 bip x y))).card
      : ℕ) : ℝ) ≤ E.card * D.card + D.card * e by
    refine le_trans (le_of_eq ?_) H
    norm_cast
    rw [card_filter, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
  push_cast
  have hrow : ∀ x ∈ D, ((D.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget D1 bip x y))).card
      : ℝ) ≤ (if x ∈ E then (D.card : ℝ) else e) := by
    intro x hx
    split_ifs with hxE
    · exact_mod_cast card_filter_le _ _
    · refine le_trans ?_ (hdev x hx hxE)
      have hsub : D.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget D1 bip x y)) ⊆
          symmDiff (nbIn G D x) (tgt D D1 bip x) := by
        intro y hy
        obtain ⟨hyD, hxy, hne⟩ := mem_filter.mp hy
        rw [mem_symmDiff, mem_nbIn]
        have htg : y ∈ tgt D D1 bip x ↔ sideTarget D1 bip x y := by
          unfold tgt sideTarget
          cases bip <;> by_cases hx1 : x ∈ D1 <;> by_cases hy1 : y ∈ D1 <;>
            simp [hx1, hy1, hyD]
        rw [htg]
        tauto
      exact_mod_cast card_le_card hsub
  calc (∑ x ∈ D, ((D.filter (fun y => x ≠ y ∧ ¬ (G.Adj x y ↔ sideTarget D1 bip x y))).card
        : ℝ)) ≤ ∑ x ∈ D, (if x ∈ E then (D.card : ℝ) else e) := sum_le_sum hrow
    _ ≤ ∑ x ∈ D, ((if x ∈ E then (D.card : ℝ) else 0) + e) := by
        refine sum_le_sum fun x _ => ?_
        split_ifs <;> linarith
    _ = ((D.filter (· ∈ E)).card : ℝ) * D.card + D.card * e := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ E.card * D.card + D.card * e := by
        have h1 : ((D.filter (· ∈ E)).card : ℝ) ≤ E.card := by
          exact_mod_cast card_le_card fun x hx => (mem_filter.mp hx).2
        nlinarith [(Nat.cast_nonneg D.card : (0:ℝ) ≤ D.card)]

omit [Fintype V] in
/-- **Few walks of length four force closeness to `T₂` or `T̄₂`** (with a part of size exactly
`⌊|D|/2⌋`). -/
theorem sideCost_small_of_few_walks (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    {s t : V} (hs : s ∈ D) (ht : t ∈ D) {σ ε : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 100)
    (hε0 : 0 ≤ ε) (hε : ε ≤ σ ^ 2)
    (hdeg : ∀ y ∈ D, (1 / 2 - ε) * D.card ≤ (nbIn G D y).card)
    (hW : (walk4 G D s t : ℝ) ≤ σ ^ 6 * D.card ^ 3) :
    ∃ X ⊆ D, X.card = D.card / 2 ∧ ∃ b : Bool,
      (sideCost G D X b : ℝ) ≤ 100 * σ * D.card ^ 2 + 4 * D.card := by
  have hm : 0 < D.card := card_pos.mpr ⟨s, hs⟩
  set m : ℝ := (D.card : ℝ) with hmdef
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hσ2 : σ ^ 2 ≤ σ / 100 := by nlinarith
  have hdeg' : ∀ y, (1 / 2 - ε) * D.card ≤ (nbIn (padGraph G D) D y).card := by
    intro y
    by_cases hy : y ∈ D
    · rw [nbIn_padGraph_of_mem G D hy]; exact hdeg y hy
    · rw [nbIn_padGraph_of_notMem G D hy]; nlinarith
  have hW' : (walk4 (padGraph G D) D s t : ℝ) ≤ σ ^ 6 * D.card ^ 3 := by
    rw [walk4_padGraph G D hs ht]; exact hW
  obtain ⟨D1, hD1, bip, E, hE, hEc, hdev, hsD, htD⟩ :=
    stab4 (padGraph G D) D s t (ε := ε) (κ := σ ^ 6) hσ0 (by linarith) hε0 hε le_rfl hm hdeg' hW'
  rw [nbIn_padGraph_of_mem G D hs] at hsD
  rw [nbIn_padGraph_of_mem G D ht] at htD
  have hdevG : ∀ x ∈ D, x ∉ E →
      ((symmDiff (nbIn G D x) (tgt D D1 bip x)).card : ℝ) ≤ 20 * σ * D.card := by
    intro x hx hxE
    rw [← nbIn_padGraph_of_mem G D hx]; exact hdev x hx hxE
  have hcost := sideCost_le_of_dev G D D1 E bip (by positivity) hdevG
  have hcost' : (sideCost G D D1 bip : ℝ) ≤ 40 * σ * m ^ 2 := by
    have : (E.card : ℝ) * m ≤ 20 * σ * m * m := mul_le_mul_of_nonneg_right hEc hm0.le
    nlinarith
  have h1 := card_ge_of_symmDiff (nbIn G D s) D1
  have h2 := card_ge_of_symmDiff (nbIn G D t) (D \ D1)
  have hsplit : (D1.card : ℝ) + (D \ D1).card = m := by
    have := card_sdiff_add_card_eq_card hD1
    rw [hmdef]; exact_mod_cast (by omega : D1.card + (D \ D1).card = D.card)
  have hds := hdeg s hs
  have hdt := hdeg t ht
  have hlo : (1 / 2 - 21 * σ) * m ≤ D1.card := by nlinarith
  have hhi : (D1.card : ℝ) ≤ (1 / 2 + 21 * σ) * m := by nlinarith
  set k : ℕ := ⌈21 * σ * m⌉₊ + 1 with hkdef
  have hkr : 21 * σ * m + 1 ≤ (k : ℝ) := by
    rw [hkdef]; push_cast; linarith [Nat.le_ceil (21 * σ * m)]
  have hkr' : (k : ℝ) ≤ 21 * σ * m + 2 := by
    rw [hkdef]; push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ 21 * σ * m by positivity)]
  have hd1 : D.card ≤ 2 * (D.card / 2) + 1 := by omega
  have hd2 : 2 * (D.card / 2) ≤ D.card := Nat.mul_div_le _ _
  have hd1' : m ≤ 2 * ((D.card / 2 : ℕ) : ℝ) + 1 := by rw [hmdef]; exact_mod_cast hd1
  have hd2' : 2 * ((D.card / 2 : ℕ) : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hd2
  have hk1 : D1.card ≤ D.card / 2 + k := by
    have : (D1.card : ℝ) ≤ ((D.card / 2 + k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hk2 : D.card / 2 ≤ D1.card + k := by
    have : ((D.card / 2 : ℕ) : ℝ) ≤ ((D1.card + k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨X, hX, hXc, hXcost⟩ :=
    exists_sideCost_rebalance G bip hD1 (D.card / 2) (Nat.div_le_self _ _) k hk1 hk2
  refine ⟨X, hX, hXc, bip, ?_⟩
  have hXcost' : (sideCost G D X bip : ℝ) ≤ sideCost G D D1 bip + 2 * m * k := by
    rw [hmdef]; exact_mod_cast hXcost
  have : 2 * m * (k : ℝ) ≤ 2 * m * (21 * σ * m + 2) := mul_le_mul_of_nonneg_left hkr' (by positivity)
  nlinarith

omit [Fintype V] in
/-- Closeness of `G[D]` transfers to `G[C]` for `C ⊇ D`, at the cost of the extra vertices. -/
lemma exists_sideCost_superset (G : SimpleGraph V) {D C X : Finset V} (hDC : D ⊆ C)
    (hX : X ⊆ D) (hXc : X.card = D.card / 2) (b : Bool) :
    ∃ X' ⊆ C, X'.card = C.card / 2 ∧
      sideCost G C X' b ≤ sideCost G D X b + 4 * (C \ D).card * C.card + 2 * C.card := by
  have h := sideCost_le_of_subset G (D := C) (D' := D) (X := X) b
  have hcs := card_sdiff_add_card_eq_card hDC
  obtain ⟨X', hX', hX'c, hX'cost⟩ := exists_sideCost_rebalance G b (hX.trans hDC) (C.card / 2)
    (Nat.div_le_self _ _) ((C \ D).card + 1) (by omega) (by omega)
  refine ⟨X', hX', hX'c, ?_⟩
  calc sideCost G C X' b ≤ sideCost G C X b + 2 * C.card * ((C \ D).card + 1) := hX'cost
    _ ≤ sideCost G D X b + 2 * (C \ D).card * C.card + 2 * C.card * ((C \ D).card + 1) := by
        omega
    _ = _ := by ring

end NashWilliams18

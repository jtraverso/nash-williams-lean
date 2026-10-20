/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ParityLoads
public import PartitionedTriangleAbsorption.UniversalRefiner.Heap

/-! # A compressed heap of labelled auxiliary hubs

The old vertex type `V` is extended by `2^(p+1)` labelled hub vertices: `HU V p = V ⊕ Fin 2^(p+1)`.
The hub count `2^p` is independent of the number of old vertices.
* level `0` sends old vertex `u` to hub `2^p + idx u mod 2^p`;
* level `l ≥ 1` sends the hub `i` to its heap parent `i / 2`.
The links of level `l ≥ 1` join hubs of index in `[2^(p+1-l), 2^(p+2-l))`; level `p+1` is empty.
No hub map fixes a link endpoint and no old vertex is ever a hub, so the root load of the
hierarchy at an old vertex is exactly twice its reserve degree.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub

open Finset AntiEdgeSelection UniversalRefiner

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Old vertices together with the auxiliary hubs. -/
abbrev HU (V : Type*) (p : ℕ) := V ⊕ Fin (2 ^ (p + 1))

/-- The hub of index `k` (reduced modulo the number of hubs). -/
def hubOf (p k : ℕ) : HU V p := Sum.inr ⟨k % 2 ^ (p + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

omit [Fintype V] [DecidableEq V] in
theorem hubOf_eq {p k : ℕ} (hk : k < 2 ^ (p + 1)) : (hubOf p k : HU V p) = Sum.inr ⟨k, hk⟩ := by
  simp [hubOf, Nat.mod_eq_of_lt hk]

/-- The hub maps of the heap. -/
noncomputable def heapH (p : ℕ) : ℕ → HU V p → HU V p
  | 0, Sum.inl u => hubOf p (2 ^ p + idx u % 2 ^ p)
  | 0, Sum.inr i => Sum.inr i
  | _ + 1, Sum.inl u => Sum.inl u
  | _ + 1, Sum.inr i => hubOf p (i / 2)

/-- Hubs of level `l`. -/
def HLevel (p l : ℕ) (x : HU V p) : Prop :=
  ∃ i : Fin (2 ^ (p + 1)), x = Sum.inr i ∧ 2 ^ (p + 1 - l) ≤ i.val ∧ i.val < 2 ^ (p + 2 - l)

variable {p : ℕ} (Xo : Finset (Sym2 V))

omit [Fintype V] in
theorem mem_mapE_inl_vertex {π : Sym2 (HU V p)} (hπ : π ∈ mapE Sum.inl Xo) {w : HU V p}
    (hw : w ∈ π) : ∃ u, w = Sum.inl u := by
  obtain ⟨e, -, rfl⟩ := mem_mapE.mp hπ
  obtain ⟨u, -, rfl⟩ := Sym2.mem_map.mp hw
  exact ⟨u, rfl⟩

theorem links_hlevel :
    ∀ l, 1 ≤ l → l ≤ p + 1 → ∀ π ∈ links (mapE Sum.inl Xo) (heapH (V := V) p) l,
      ∀ x ∈ π, HLevel p l x := by
  intro l hl1 hlp
  induction l with
  | zero => omega
  | succ m ih =>
    intro π hπ x hx
    obtain ⟨⟨π0, hπ0, rfl⟩, -⟩ := mem_nextLinks.mp hπ
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hx
    rcases m with _ | m
    · obtain ⟨u, rfl⟩ := mem_mapE_inl_vertex Xo hπ0 hw
      have hu := Nat.mod_lt (idx u) (Nat.two_pow_pos p)
      have hlt : 2 ^ p + idx u % 2 ^ p < 2 ^ (p + 1) := by rw [pow_succ]; omega
      refine ⟨⟨2 ^ p + idx u % 2 ^ p, hlt⟩, hubOf_eq hlt, ?_, ?_⟩
      · simp
      · simp only [show p + 2 - (0 + 1) = p + 1 by omega]; exact hlt
    · obtain ⟨i, rfl, hi1, hi2⟩ := ih (by omega) (by omega) π0 hπ0 w hw
      have hlt : i.val / 2 < 2 ^ (p + 1) := lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt
      refine ⟨⟨i.val / 2, hlt⟩, hubOf_eq hlt, ?_, ?_⟩
      · have e1 : p + 1 - (m + 1) = (p + 1 - (m + 1 + 1)) + 1 := by omega
        rw [e1, pow_succ 2 (p + 1 - (m + 1 + 1))] at hi1
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hi1
      · have e2 : p + 2 - (m + 1) = (p + 2 - (m + 1 + 1)) + 1 := by omega
        rw [e2, pow_succ 2 (p + 2 - (m + 1 + 1))] at hi2
        exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hi2

/-- **The hierarchy stops.** -/
theorem heap_links_last :
    links (mapE Sum.inl Xo) (heapH (V := V) p) (p + 1) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro π hπ
  have hd := (mem_nextLinks.mp hπ).2
  obtain ⟨i, hi, hi1, hi2⟩ := links_hlevel Xo (p + 1) (by omega) le_rfl π hπ _ (endA_mem π)
  obtain ⟨j, hj, hj1, hj2⟩ := links_hlevel Xo (p + 1) (by omega) le_rfl π hπ _ (endB_mem π)
  simp only [show p + 1 - (p + 1) = 0 by omega, show p + 2 - (p + 1) = 1 by omega, pow_zero,
    pow_one] at hi1 hi2 hj1 hj2
  have hij : i = j := Fin.ext (by omega)
  exact endA_ne_endB hd (by rw [hi, hj, hij])

/-- **No hub map fixes a link endpoint.** -/
theorem heap_nofix :
    ∀ l < p + 1, ∀ π ∈ links (mapE Sum.inl Xo) (heapH (V := V) p) l, ∀ u ∈ π,
      heapH p l u ≠ u := by
  intro l hl π hπ x hx
  rcases l with _ | l
  · obtain ⟨u, rfl⟩ := mem_mapE_inl_vertex Xo hπ hx
    simp [heapH, hubOf]
  · obtain ⟨i, rfl, hi1, -⟩ := links_hlevel Xo (l + 1) (by omega) (by omega) π hπ x hx
    have h2 : 2 ≤ 2 ^ (p + 1 - (l + 1)) := by
      have : 1 ≤ p + 1 - (l + 1) := by omega
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    have hlt : i.val / 2 < 2 ^ (p + 1) := lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt
    simp only [heapH, hubOf_eq hlt, ne_eq, Sum.inr.injEq, Fin.ext_iff]
    omega

/-- Links of positive level avoid old vertices. -/
theorem vChain_old_eq_empty {l : ℕ} (hl1 : 1 ≤ l) (hlp : l ≤ p + 1)
    (v : V) : vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l) (Sum.inl v) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro π hπ
  obtain ⟨hπ, hv⟩ := mem_vChain.mp hπ
  obtain ⟨i, hi, -⟩ := links_hlevel Xo l hl1 hlp π hπ _ hv
  exact Sum.inl_ne_inr hi

/-- No old vertex is a hub. -/
theorem hubWeight_old_eq_zero {l : ℕ} (hlp : l ≤ p) (v : V) :
    hubWeight (links (mapE Sum.inl Xo) (heapH (V := V) p) l) (heapH p l) (Sum.inl v) = 0 := by
  unfold hubWeight
  refine sum_eq_zero fun w hw => ?_
  have hw := (mem_filter.mp hw).2
  rcases l with _ | l
  · rcases w with u | i <;> simp [heapH, hubOf] at hw
  · rcases w with u | i
    · simp only [heapH, Sum.inl.injEq] at hw
      subst hw
      rw [vChain_old_eq_empty Xo (by omega) (by omega)]
      rfl
    · simp [heapH, hubOf] at hw

/-- **Root load of the heap hierarchy at an old vertex.** -/
theorem heap_root_old (v : V) :
    ∑ l ∈ range (p + 1), (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) l)
        (Sum.inl v)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) l) (heapH p l)
        (Sum.inl v)) = 2 * incidentLoad Xo v := by
  rw [sum_range_succ']
  have hrest : ∑ l ∈ range p, (2 * (vChain (links (mapE Sum.inl Xo) (heapH (V := V) p) (l + 1))
      (Sum.inl v)).card + 10 * hubWeight (links (mapE Sum.inl Xo) (heapH p) (l + 1))
      (heapH p (l + 1)) (Sum.inl v)) = 0 := by
    refine sum_eq_zero fun l hl => ?_
    have hl' := mem_range.mp hl
    rw [vChain_old_eq_empty Xo (by omega) (by omega),
      hubWeight_old_eq_zero Xo (by omega)]
    rfl
  rw [hrest, hubWeight_old_eq_zero Xo (by omega)]
  change 0 + (2 * incidentLoad (mapE Sum.inl Xo) (Sum.inl v) + 10 * 0) = _
  rw [incidentLoad_mapE_apply Sum.inl_injective]
  ring

omit [Fintype V] in
/-- Every level has at most `|X|` links. -/
theorem card_links_le_card (h : ℕ → HU V p → HU V p) :
    ∀ l, (links (mapE Sum.inl Xo) h l).card ≤ Xo.card
  | 0 => (card_mapE Sum.inl_injective Xo).le
  | l + 1 => card_nextLinks_le.trans (card_links_le_card h l)

omit [Fintype V] in
theorem heap_sum_links_le (h : ℕ → HU V p → HU V p) (L : ℕ) :
    ∑ l ∈ range L, (links (mapE Sum.inl Xo) h l).card ≤ L * Xo.card := by
  calc ∑ l ∈ range L, (links (mapE Sum.inl Xo) h l).card ≤ ∑ _l ∈ range L, Xo.card :=
        sum_le_sum fun l _ => card_links_le_card Xo h l
    _ = L * Xo.card := by rw [sum_const, card_range, smul_eq_mul]

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub


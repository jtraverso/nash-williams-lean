/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Producer

/-!
# The concrete hub hierarchy: a binary heap of hubs

Enumerate the vertices as `0, …, n-1` (`idx`, `vtx`).  Fix `p ≥ 1` with `2^(p+1) ≤ n`.
* level `0`: every vertex `u` is sent to the hub `2^p + (idx u + 1) mod 2^p` (`hub0`); hubs of
  level `1` are the vertices with index in `[2^p, 2^(p+1))`, and `hub0` has no fixed point;
* level `l ≥ 1`: the hub of `u` is its heap parent `idx u / 2` (`par`); the links of level `l`
  join vertices with index in `[2^(p+1-l), 2^(p+2-l))`;
* the last level `p` has a single hub (index `1`) above it, so `links (p+1) = ∅`.

Interior levels are paid by `2^p · 2^(p+1)` links and contribute `O(2^p)` root load at any
vertex; level `0` contributes `2 deg + 10 (n / 2^p + 1) maxdeg`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Index of a vertex in a fixed enumeration. -/
noncomputable def idx (u : V) : ℕ := (Fintype.equivFin V u : ℕ)

/-- Vertex of a given index (`u0` out of range). -/
noncomputable def vtx (u0 : V) (i : ℕ) : V :=
  if h : i < Fintype.card V then (Fintype.equivFin V).symm ⟨i, h⟩ else u0

omit [DecidableEq V] in
theorem idx_lt (u : V) : idx u < Fintype.card V := (Fintype.equivFin V u).isLt

omit [DecidableEq V] in
theorem idx_vtx (u0 : V) {i : ℕ} (hi : i < Fintype.card V) : idx (vtx u0 i) = i := by
  unfold idx vtx
  rw [dite_eq_left hi]
  simp

omit [DecidableEq V] in
theorem idx_inj {u w : V} (h : idx u = idx w) : u = w :=
  (Fintype.equivFin V).injective (Fin.ext h)

/-- The first hub map. -/
noncomputable def hub0 (u0 : V) (p : ℕ) (u : V) : V := vtx u0 (2 ^ p + (idx u + 1) % 2 ^ p)

/-- Heap parent. -/
noncomputable def par (u0 : V) (u : V) : V := vtx u0 (idx u / 2)

/-- The hub maps of the heap hierarchy. -/
noncomputable def heapMap (u0 : V) (p : ℕ) (l : ℕ) : V → V :=
  if l = 0 then hub0 u0 p else par u0

omit [DecidableEq V] in
theorem heapMap_zero (u0 : V) (p : ℕ) : heapMap u0 p 0 = hub0 u0 p := by simp [heapMap]

omit [DecidableEq V] in
theorem heapMap_of_ne (u0 : V) (p : ℕ) {l : ℕ} (hl : l ≠ 0) : heapMap u0 p l = par u0 := by
  simp [heapMap, hl]

/-- Vertices that are link endpoints at level `l ≥ 1`. -/
def inLevel (p l : ℕ) (u : V) : Prop := 2 ^ (p + 1 - l) ≤ idx u ∧ idx u < 2 ^ (p + 2 - l)

/-- The hub set of level `l ≥ 1`. -/
noncomputable def hset (p l : ℕ) : Finset V :=
  univ.filter fun u => 2 ^ (p + 1 - l) ≤ idx u ∧ idx u < 2 ^ (p + 2 - l)

omit [DecidableEq V] in
theorem mem_hset {p l : ℕ} {u : V} : u ∈ hset p l ↔ inLevel p l u := by
  simp [hset, inLevel]

section Heap

variable {u0 : V} {p : ℕ} {X : Finset (Sym2 V)}

omit [DecidableEq V] in
theorem idx_hub0 (h2 : 2 ^ (p + 1) ≤ Fintype.card V) (u : V) :
    idx (hub0 u0 p u) = 2 ^ p + (idx u + 1) % 2 ^ p := by
  unfold hub0
  apply idx_vtx
  have := Nat.mod_lt (idx u + 1) (Nat.two_pow_pos p)
  rw [pow_succ] at h2
  omega

omit [DecidableEq V] in
theorem idx_par (u : V) : idx (par u0 u) = idx u / 2 := by
  unfold par
  apply idx_vtx
  have := idx_lt u
  omega

/-- **Endpoints of the links of level `l ≥ 1` lie in level `l`.** -/
theorem links_inLevel (h2 : 2 ^ (p + 1) ≤ Fintype.card V) :
    ∀ l, 1 ≤ l → l ≤ p + 1 → ∀ π ∈ links X (heapMap u0 p) l, ∀ u ∈ π, inLevel p l u := by
  intro l hl1 hlp
  induction l with
  | zero => omega
  | succ m ih =>
    intro π hπ u hu
    obtain ⟨⟨π0, hπ0, rfl⟩, -⟩ := mem_nextLinks.mp hπ
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hu
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [heapMap_zero]
      unfold inLevel
      rw [idx_hub0 h2]
      have := Nat.mod_lt (idx w + 1) (Nat.two_pow_pos p)
      have e1 : p + 1 - (0 + 1) = p := by omega
      have e2 : p + 2 - (0 + 1) = p + 1 := by omega
      rw [e1, e2, pow_succ]
      omega
    · have hm0 : m ≠ 0 := by omega
      rw [heapMap_of_ne u0 p hm0]
      obtain ⟨hw1, hw2⟩ := ih (by omega) (by omega) π0 hπ0 w hw
      unfold inLevel
      rw [idx_par]
      have e1 : p + 1 - m = (p + 1 - (m + 1)) + 1 := by omega
      have e2 : p + 2 - m = (p + 2 - (m + 1)) + 1 := by omega
      rw [e1, pow_succ] at hw1
      rw [e2, pow_succ] at hw2
      constructor
      · exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hw1
      · exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hw2

/-- **The hierarchy stops: the last link family is empty.** -/
theorem links_last (h2 : 2 ^ (p + 1) ≤ Fintype.card V) :
    links X (heapMap u0 p) (p + 1) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro π hπ
  have hd := (mem_nextLinks.mp hπ).2
  have hA := links_inLevel h2 (p + 1) (by omega) le_rfl π hπ (endA π) (endA_mem π)
  have hB := links_inLevel h2 (p + 1) (by omega) le_rfl π hπ (endB π) (endB_mem π)
  unfold inLevel at hA hB
  have e1 : p + 1 - (p + 1) = 0 := by omega
  have e2 : p + 2 - (p + 1) = 1 := by omega
  rw [e1, e2] at hA hB
  simp only [pow_zero, pow_one] at hA hB
  exact endA_ne_endB hd (idx_inj (by omega))

/-- **No hub map fixes a link endpoint.** -/
theorem heap_fix (hp : 1 ≤ p) (h2 : 2 ^ (p + 1) ≤ Fintype.card V) :
    ∀ l < p + 1, ∀ π ∈ links X (heapMap u0 p) l, ∀ u ∈ π, heapMap u0 p l u ≠ u := by
  intro l hl π hπ u hu heq
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [heapMap_zero] at heq
    have h := congrArg idx heq
    rw [idx_hub0 h2] at h
    set M := 2 ^ p with hM
    have hM2 : 2 ≤ M := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    obtain ⟨t, ht⟩ : ∃ t, idx u = M + t := ⟨idx u - M, by omega⟩
    have htM : t < M := by
      have := Nat.mod_lt (idx u + 1) (by omega : 0 < M)
      omega
    have hmod : (idx u + 1) % M = (t + 1) % M := by
      rw [ht, show M + t + 1 = (t + 1) + M * 1 by ring, Nat.add_mul_mod_self_left]
    rw [hmod] at h
    rcases Nat.lt_or_ge (t + 1) M with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at h; omega
    · have : t + 1 = M := by omega
      rw [this, Nat.mod_self] at h; omega
  · have hl0' : l ≠ 0 := by omega
    rw [heapMap_of_ne u0 p hl0'] at heq
    have h := congrArg idx heq
    rw [idx_par] at h
    obtain ⟨h1, -⟩ := links_inLevel h2 l (by omega) (by omega) π hπ u hu
    have : 1 ≤ 2 ^ (p + 1 - l) := Nat.one_le_two_pow
    omega

omit [DecidableEq V] in
theorem card_hset_le {l : ℕ} (hl : 1 ≤ l) (hlp : l ≤ p + 1) : (hset (V := V) p l).card ≤ 2 ^ p := by
  have hinj : ((hset (V := V) p l).card) ≤ (Ico (2 ^ (p + 1 - l)) (2 ^ (p + 2 - l))).card := by
    refine card_le_card_of_injOn idx ?_ ?_
    · intro u hu
      have := mem_hset.mp hu
      simp only [coe_Ico, Set.mem_Ico]
      exact this
    · intro u _ w _ h; exact idx_inj h
  refine hinj.trans ?_
  rw [Nat.card_Ico]
  have e : p + 2 - l = (p + 1 - l) + 1 := by omega
  rw [e, pow_succ]
  have : 2 ^ (p + 1 - l) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

omit [DecidableEq V] in
theorem hset_disjoint {l m : ℕ} (hlm : l < m) (hm : m ≤ p + 1) :
    Disjoint (hset (V := V) p l) (hset p m) := by
  rw [disjoint_left]
  intro u hu hu'
  obtain ⟨h1, h2⟩ := mem_hset.mp hu
  obtain ⟨h3, h4⟩ := mem_hset.mp hu'
  have : 2 ^ (p + 2 - m) ≤ 2 ^ (p + 1 - l) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

omit [DecidableEq V] in
theorem sum_card_hset_le :
    ∑ l ∈ range p, (hset (V := V) p (l + 1)).card ≤ 2 ^ (p + 1) := by
  classical
  rw [← card_biUnion]
  · refine (card_le_card_of_injOn idx (t := range (2 ^ (p + 1))) ?_ ?_).trans (by simp)
    · intro u hu
      obtain ⟨l, hl, hu⟩ := mem_biUnion.mp (mem_coe.mp hu)
      obtain ⟨-, h2⟩ := mem_hset.mp hu
      have : 2 ^ (p + 2 - (l + 1)) ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [coe_range, Set.mem_Iio]
      omega
    · intro u _ w _ h; exact idx_inj h
  · intro l hl m hm hlm
    simp only [coe_range, Set.mem_Iio] at hl hm
    rcases Nat.lt_or_gt_of_ne hlm with h | h
    · exact hset_disjoint (by omega) (by omega)
    · exact (hset_disjoint (by omega) (by omega)).symm

theorem vChain_subset_image (h2 : 2 ^ (p + 1) ≤ Fintype.card V) {l : ℕ} (hl1 : 1 ≤ l)
    (hlp : l ≤ p + 1) (x : V) :
    vChain (links X (heapMap u0 p) l) x ⊆ (hset p l).image fun w => s(x, w) := by
  intro π hπ
  obtain ⟨hπ, hx⟩ := mem_vChain.mp hπ
  have hin : ∀ w ∈ π, w ∈ hset p l := fun w hw =>
    mem_hset.mpr (links_inLevel h2 l hl1 hlp π hπ w hw)
  rcases mem_iff_endA_endB.mp hx with rfl | rfl
  · exact mem_image.mpr ⟨endB π, hin _ (endB_mem π), mk_endA_endB π⟩
  · exact mem_image.mpr ⟨endA π, hin _ (endA_mem π), by rw [Sym2.eq_swap, mk_endA_endB π]⟩

theorem card_vChain_le (h2 : 2 ^ (p + 1) ≤ Fintype.card V) {l : ℕ} (hl1 : 1 ≤ l)
    (hlp : l ≤ p + 1) (x : V) :
    (vChain (links X (heapMap u0 p) l) x).card ≤ (hset (V := V) p l).card :=
  (card_le_card (vChain_subset_image h2 hl1 hlp x)).trans card_image_le

theorem card_links_le (h2 : 2 ^ (p + 1) ≤ Fintype.card V) {l : ℕ} (hl1 : 1 ≤ l)
    (hlp : l ≤ p + 1) : (links X (heapMap u0 p) l).card ≤ (hset (V := V) p l).card * 2 ^ p := by
  have hsub : links X (heapMap u0 p) l ⊆ (hset p l ×ˢ hset p l).image fun q => s(q.1, q.2) := by
    intro π hπ
    have hin : ∀ w ∈ π, w ∈ hset p l := fun w hw =>
      mem_hset.mpr (links_inLevel h2 l hl1 hlp π hπ w hw)
    exact mem_image.mpr ⟨(endA π, endB π), mem_product.mpr ⟨hin _ (endA_mem π),
      hin _ (endB_mem π)⟩, mk_endA_endB π⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_product]
  exact Nat.mul_le_mul_left _ (card_hset_le hl1 hlp)

theorem card_par_fiber_le (x : V) : (univ.filter fun u : V => par u0 u = x).card ≤ 2 := by
  refine (card_le_card_of_injOn idx (t := {2 * idx x, 2 * idx x + 1}) ?_ ?_).trans card_le_two
  · intro u hu
    have h := congrArg idx (mem_filter.mp (mem_coe.mp hu)).2
    rw [idx_par] at h
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro u _ w _ h; exact idx_inj h

theorem hubWeight_par_le (h2 : 2 ^ (p + 1) ≤ Fintype.card V) {l : ℕ} (hl1 : 1 ≤ l)
    (hlp : l ≤ p) (x : V) :
    hubWeight (links X (heapMap u0 p) l) (heapMap u0 p l) x ≤ 2 * (hset (V := V) p l).card := by
  have hl0 : l ≠ 0 := by omega
  unfold hubWeight
  rw [heapMap_of_ne u0 p hl0]
  refine (sum_le_sum fun u _ => card_vChain_le (X := X) (u0 := u0) h2 hl1 (by omega) u).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_par_fiber_le x)

theorem card_hub0_fiber_le (h2 : 2 ^ (p + 1) ≤ Fintype.card V) (x : V) :
    (univ.filter fun u : V => hub0 u0 p u = x).card ≤ Fintype.card V / 2 ^ p + 1 := by
  have hM : 0 < 2 ^ p := Nat.two_pow_pos p
  refine (card_le_card_of_injOn (fun u => (idx u + 1) / 2 ^ p)
    (t := range (Fintype.card V / 2 ^ p + 1)) ?_ ?_).trans (by simp)
  · intro u _
    simp only [coe_range, Set.mem_Iio]
    have := Nat.div_le_div_right (c := 2 ^ p) (show idx u + 1 ≤ Fintype.card V from idx_lt u)
    omega
  · intro u hu w hw h
    have hu' := congrArg idx (mem_filter.mp (mem_coe.mp hu)).2
    have hw' := congrArg idx (mem_filter.mp (mem_coe.mp hw)).2
    rw [idx_hub0 h2] at hu' hw'
    have hmod : (idx u + 1) % 2 ^ p = (idx w + 1) % 2 ^ p := by omega
    apply idx_inj
    have e1 := Nat.div_add_mod (idx u + 1) (2 ^ p)
    have e2 := Nat.div_add_mod (idx w + 1) (2 ^ p)
    simp only at h
    rw [h, hmod] at e1
    omega

theorem hubWeight_hub0_le (h2 : 2 ^ (p + 1) ≤ Fintype.card V) (D : ℕ)
    (hD : ∀ u, (vChain X u).card ≤ D) (x : V) :
    hubWeight X (heapMap u0 p 0) x ≤ (Fintype.card V / 2 ^ p + 1) * D := by
  unfold hubWeight
  rw [heapMap_zero]
  refine (sum_le_sum fun u _ => hD u).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_hub0_fiber_le h2 x)

/-- **Size of the hierarchy.** -/
theorem heap_sum_links (h2 : 2 ^ (p + 1) ≤ Fintype.card V) :
    ∑ l ∈ range (p + 1), (links X (heapMap u0 p) l).card ≤ X.card + 2 ^ (p + 1) * 2 ^ p := by
  rw [sum_range_succ']
  have : ∑ l ∈ range p, (links X (heapMap u0 p) (l + 1)).card ≤ 2 ^ (p + 1) * 2 ^ p := by
    refine (sum_le_sum fun l hl => card_links_le h2 (by omega)
      (by simp at hl; omega)).trans ?_
    rw [← sum_mul]
    exact Nat.mul_le_mul_right _ sum_card_hset_le
  have h0 : links X (heapMap u0 p) 0 = X := rfl
  rw [h0]
  omega

/-- **Root load of the hierarchy at a vertex.** -/
theorem heap_root (h2 : 2 ^ (p + 1) ≤ Fintype.card V) (D : ℕ)
    (hD : ∀ u, (vChain X u).card ≤ D) (x : V) :
    ∑ l ∈ range (p + 1), (2 * (vChain (links X (heapMap u0 p) l) x).card +
        10 * hubWeight (links X (heapMap u0 p) l) (heapMap u0 p l) x) ≤
      2 * D + 10 * ((Fintype.card V / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) := by
  rw [sum_range_succ']
  have h0 := hubWeight_hub0_le (u0 := u0) h2 D hD x
  have hd := hD x
  have : ∑ l ∈ range p, (2 * (vChain (links X (heapMap u0 p) (l + 1)) x).card +
      10 * hubWeight (links X (heapMap u0 p) (l + 1)) (heapMap u0 p (l + 1)) x) ≤
      22 * 2 ^ (p + 1) := by
    have hsum : ∑ l ∈ range p, 22 * (hset (V := V) p (l + 1)).card ≤ 22 * 2 ^ (p + 1) := by
      rw [← mul_sum]
      exact Nat.mul_le_mul_left 22 sum_card_hset_le
    refine (sum_le_sum fun l hl => ?_).trans hsum
    have hl' : l < p := mem_range.mp hl
    have h1 := card_vChain_le (X := X) (u0 := u0) h2 (l := l + 1) (by omega) (by omega) x
    have h3 := hubWeight_par_le (X := X) (u0 := u0) h2 (l := l + 1) (by omega) (by omega) x
    omega
  have hl0 : links X (heapMap u0 p) 0 = X := rfl
  rw [hl0]
  omega

end Heap

end PartitionedTriangleAbsorption.UniversalRefiner

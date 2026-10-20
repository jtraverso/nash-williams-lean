/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagonAbsorber
public import PartitionedTriangleAbsorption.SignedCertificate.Localization
public import PartitionedTriangleAbsorption.CoherentTransformer.Refutation
public import PartitionedTriangleAbsorption.CloneSupply.Basic

/-! # Stage 49 controls

1. **Bridge control** (`BridgeControl`). Four cliques `A₀, A₁` (part `0`), `B₀, B₁`
   (part `1`) of order `L + 2`, all cross-part edges, and only the two bridges
   `a₀b₀, a₁b₁` between `A₀` and `A₁`. The host is F0-anti-edgeful with `α = 1/8`. The
   source is the union of the two physical F0 triangles `a₀b₀c₀, a₁b₁c₁`, with a
   *positive* certificate (both coefficients `+1`) and an F0 decomposition. Once
   `β n > 2`, every good clone of `a₀` lies in `A₀`, every good clone of `b₀` lies in `A₁`,
   and no two such clones outside the excluded set are adjacent: the old same-word
   destination (clone every position and keep every source edge) is impossible, already
   for the source edge `a₀b₀`. Good clones exist (`clone_a0_exists`, `clone_b0_exists`),
   so the failure is not vacuous.
2. **Star control** (`StarControl`). The physical 4-cycle source of the coherent
   transformer refutation has coarse F0 charge `2(e₀₀ + e₁₁) - e₀₁ = 2`, hence admits
   **no** signed physical F0 certificate. It is not an instance of the Stage 49 candidate.
3. **Item-5 control** (`CountControl`). Two modes alone do not force equal part-pair
   counts: a `001` triangle `P`, a disjoint `011` triangle `Q` and `A = ∅` form a two-mode
   solution with different `00`-counts. Equal counts are an additional requirement, which
   the fresh destination of `SignedCertificate.Packing` meets by construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate

open Finset TypedApplicationLinks

/-- Triangles on disjoint vertex sets have disjoint edge sets. -/
theorem disjoint_triEdges_of_disjoint {V : Type*} [DecidableEq V] {s t : Finset V}
    (h : Disjoint s t) : Disjoint (triEdges s) (triEdges t) := by
  rw [disjoint_left]
  intro e hs ht
  induction e using Sym2.ind with
  | _ a b =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff] at hs ht
    exact disjoint_left.mp h hs.1.1 ht.1.1

namespace BridgeControl

open CloneSupply

variable (L : ℕ)

/-- Vertices: block (`0 = A₀, 1 = A₁, 2 = B₀, 3 = B₁`) and index. -/
abbrev BV := Fin 4 × Fin (L + 2)

/-- The host: cliques on blocks, all cross-part edges, two bridges `(0,i)(1,i)`, `i < 2`. -/
def host : SimpleGraph (BV L) where
  Adj u v := ¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) ∧
    (u.1.val = v.1.val ∨ u.1.val / 2 ≠ v.1.val / 2 ∨
      (u.1.val = 0 ∧ v.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2) ∨
      (v.1.val = 0 ∧ u.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2))
  symm := ⟨fun u v h => ⟨fun h' => h.1 ⟨h'.1.symm, h'.2.symm⟩, by omega⟩⟩
  loopless := ⟨fun u h => h.1 ⟨rfl, rfl⟩⟩

instance : DecidableRel (host L).Adj := fun u v =>
  inferInstanceAs (Decidable (¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) ∧
    (u.1.val = v.1.val ∨ u.1.val / 2 ≠ v.1.val / 2 ∨
      (u.1.val = 0 ∧ v.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2) ∨
      (v.1.val = 0 ∧ u.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2))))

theorem adj_iff {u v : BV L} : (host L).Adj u v ↔ ¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) ∧
    (u.1.val = v.1.val ∨ u.1.val / 2 ≠ v.1.val / 2 ∨
      (u.1.val = 0 ∧ v.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2) ∨
      (v.1.val = 0 ∧ u.1.val = 1 ∧ u.2.val = v.2.val ∧ u.2.val < 2)) := Iff.rfl

/-- Parts: blocks `0, 1` are part `0`, blocks `2, 3` are part `1`. -/
def part (v : BV L) : Fin 2 := ⟨v.1.val / 2, by omega⟩

theorem part_eq_iff {v : BV L} {k : Fin 2} : part L v = k ↔ v.1.val / 2 = k.val := by
  simp [part, Fin.ext_iff]

theorem card_BV : Fintype.card (BV L) = 4 * (L + 2) := by simp

theorem vert_eq_iff {u v : BV L} : u = v ↔ u.1.val = v.1.val ∧ u.2.val = v.2.val := by
  simp [Prod.ext_iff, Fin.ext_iff]

/-- The six source vertices. -/
def a0 : BV L := (0, 0)
def a1 : BV L := (0, 1)
def b0 : BV L := (1, 0)
def b1 : BV L := (1, 1)
def c0 : BV L := (2, 0)
def c1 : BV L := (2, 1)

@[simp] theorem a0_val : (a0 L).1.val = 0 ∧ (a0 L).2.val = 0 := ⟨rfl, rfl⟩
@[simp] theorem a1_val : (a1 L).1.val = 0 ∧ (a1 L).2.val = 1 := ⟨rfl, rfl⟩
@[simp] theorem b0_val : (b0 L).1.val = 1 ∧ (b0 L).2.val = 0 := ⟨rfl, rfl⟩
@[simp] theorem b1_val : (b1 L).1.val = 1 ∧ (b1 L).2.val = 1 := ⟨rfl, rfl⟩
@[simp] theorem c0_val : (c0 L).1.val = 2 ∧ (c0 L).2.val = 0 := ⟨rfl, rfl⟩
@[simp] theorem c1_val : (c1 L).1.val = 2 ∧ (c1 L).2.val = 1 := ⟨rfl, rfl⟩

theorem part_src0 : part L (a0 L) = 0 ∧ part L (b0 L) = 0 ∧ part L (a1 L) = 0 ∧
    part L (b1 L) = 0 := by
  simp [part_eq_iff]

theorem part_src1 : part L (c0 L) = 1 ∧ part L (c1 L) = 1 := by
  simp [part_eq_iff]

/-- The two source triangles. -/
def T0 : Finset (BV L) := {a0 L, b0 L, c0 L}
def T1 : Finset (BV L) := {a1 L, b1 L, c1 L}

/-- The source: two vertex-disjoint physical F0 triangles. -/
def src : Finset (Sym2 (BV L)) := triEdges (T0 L) ∪ triEdges (T1 L)

/-! #### The host is F0-anti-edgeful -/

theorem f0_same : ∀ i j k : Fin 2, ({i, j, k} : Multiset (Fin 2)) ∈ F0 → i = j → k ≠ i := by
  decide

theorem card_block_erase (b : Fin 4) (u : BV L) (hu : u.1 = b) :
    ((({b} : Finset (Fin 4)) ×ˢ (univ : Finset (Fin (L + 2)))).erase u).card = L + 1 := by
  rw [card_erase_of_mem (mem_product.mpr ⟨mem_singleton.mpr hu, mem_univ _⟩),
    card_product, card_singleton, card_univ, Fintype.card_fin]
  omega

theorem card_half (k : Fin 2) :
    ((univ.filter fun b : Fin 4 => b.val / 2 = k.val) ×ˢ (univ : Finset (Fin (L + 2)))).card =
      2 * (L + 2) := by
  rw [card_product, card_univ, Fintype.card_fin]
  congr 1
  fin_cases k <;> decide

/-- **The bridge host is F0-anti-edgeful with `α = 1/8`** (hence for every `α ≤ 1/8`). -/
theorem antiEdgeful (α : ℝ) (hα : α ≤ 1 / 8) : AntiEdgeful (part L) F0 (host L) α := by
  intro τ hτ i j k hτeq u v huv hu hv
  subst hτeq
  have hne : ¬(u.1.val = v.1.val ∧ u.2.val = v.2.val) := fun h => huv ((vert_eq_iff L).mpr h)
  rw [part_eq_iff] at hu hv
  have key : ∃ S : Finset (BV L), L + 1 ≤ S.card ∧
      S ⊆ univ.filter (fun w => (host L).Adj u w ∧ (host L).Adj w v ∧ part L w = k) := by
    by_cases hij : i = j
    · have hk := f0_same i j k hτ hij
      have hkv : k.val ≠ i.val := fun h => hk (Fin.ext h)
      have hij' : i.val = j.val := by rw [hij]
      refine ⟨(univ.filter fun b : Fin 4 => b.val / 2 = k.val) ×ˢ univ, ?_, ?_⟩
      · rw [card_half]; omega
      · intro w hw
        simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hw
        simp only [mem_filter, mem_univ, true_and, adj_iff, part_eq_iff]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hw⟩ <;> omega
    · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hk : k.val = i.val ∨ k.val = j.val := by omega
      rcases hk with hk | hk
      · refine ⟨(({u.1} : Finset (Fin 4)) ×ˢ univ).erase u, by rw [card_block_erase L _ u rfl], ?_⟩
        intro w hw
        simp only [mem_erase, mem_product, mem_singleton, mem_univ, and_true, ne_eq,
          vert_eq_iff] at hw
        have h1 : w.1.val = u.1.val := by rw [hw.2]
        simp only [mem_filter, mem_univ, true_and, adj_iff, part_eq_iff]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
      · refine ⟨(({v.1} : Finset (Fin 4)) ×ˢ univ).erase v, by rw [card_block_erase L _ v rfl], ?_⟩
        intro w hw
        simp only [mem_erase, mem_product, mem_singleton, mem_univ, and_true, ne_eq,
          vert_eq_iff] at hw
        have h1 : w.1.val = v.1.val := by rw [hw.2]
        simp only [mem_filter, mem_univ, true_and, adj_iff, part_eq_iff]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
  obtain ⟨S, hS, hSsub⟩ := key
  have h1 := hS.trans (card_le_card hSsub)
  have h2 : ((L : ℝ) + 1) ≤ ((univ.filter (fun w => (host L).Adj u w ∧ (host L).Adj w v ∧
      part L w = k)).card : ℝ) := by exact_mod_cast h1
  rw [card_BV]
  push_cast
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have : α * (4 * ((L : ℝ) + 2)) ≤ 1 / 8 * (4 * ((L : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right hα (by positivity)
  linarith

/-! #### The source and its positive certificate -/

theorem T0_clique : (host L).IsNClique 3 (T0 L) := by
  rw [T0, SimpleGraph.is3Clique_triple_iff]
  simp only [adj_iff, a0_val, b0_val, c0_val]
  decide

theorem T1_clique : (host L).IsNClique 3 (T1 L) := by
  rw [T1, SimpleGraph.is3Clique_triple_iff]
  simp only [adj_iff, a1_val, b1_val, c1_val]
  decide

theorem T0_type : (T0 L).val.map (part L) ∈ F0 := by
  have : (T0 L).val.map (part L) = {0, 0, 1} := by
    rw [T0, insert_val_of_notMem (by simp [vert_eq_iff]),
      insert_val_of_notMem (by simp [vert_eq_iff])]
    simp only [Multiset.map_cons, singleton_val, Multiset.map_singleton]
    rw [(part_src0 L).1, (part_src0 L).2.1, (part_src1 L).1]
    rfl
  rw [this]; decide

theorem T1_type : (T1 L).val.map (part L) ∈ F0 := by
  have : (T1 L).val.map (part L) = {0, 0, 1} := by
    rw [T1, insert_val_of_notMem (by simp [vert_eq_iff]),
      insert_val_of_notMem (by simp [vert_eq_iff])]
    simp only [Multiset.map_cons, singleton_val, Multiset.map_singleton]
    rw [(part_src0 L).2.2.1, (part_src0 L).2.2.2, (part_src1 L).2]
    rfl
  rw [this]; decide

theorem T0_T1_disjoint : Disjoint (T0 L) (T1 L) := by
  simp [T0, T1, vert_eq_iff]

/-- The certificate triangles: `t 0 = a₀b₀c₀`, `t 1 = a₁b₁c₁`. -/
def tri : Fin 2 → Finset (BV L) := ![T0 L, T1 L]

/-- **Positive physical certificate** with coefficients `(1, 1)`. -/
theorem src_cert : IsSignedCert (part L) (host L) (src L) (tri L) (fun _ => 1) := by
  refine ⟨fun j => ?_, fun e => ?_⟩
  · fin_cases j
    · exact ⟨T0_clique L, T0_type L⟩
    · exact ⟨T1_clique L, T1_type L⟩
  · rw [src, ind_union_of_disjoint (disjoint_triEdges_of_disjoint (T0_T1_disjoint L)),
      Fin.sum_univ_two]
    simp [tri]

theorem certWeight_src : certWeight (fun _ : Fin 2 => (1 : ℤ)) = 2 := by
  simp [certWeight]

/-- The source is itself F0-decomposable (it is not a merely formal source). -/
theorem src_hasDecomp : HasDecomp (part L) F0 (src L) := by
  refine ⟨{T0 L, T1 L}, ?_, ?_, ?_⟩
  · intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨(T0_clique L).card_eq, T0_type L⟩
    · exact ⟨(T1_clique L).card_eq, T1_type L⟩
  · intro s hs u hu hsu
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
    rcases hs with rfl | rfl <;> rcases hu with rfl | rfl
    · exact absurd rfl hsu
    · exact disjoint_triEdges_of_disjoint (T0_T1_disjoint L)
    · exact (disjoint_triEdges_of_disjoint (T0_T1_disjoint L)).symm
    · exact absurd rfl hsu
  · rw [biUnion_insert, singleton_biUnion, src]

theorem src_subset : src L ⊆ (host L).edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  rcases mem_union.mp he with h | h <;>
  · induction e using Sym2.ind with
    | _ a b =>
      simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at h
      first
      | exact (T0_clique L).1 h.1.1 h.1.2 h.2
      | exact (T1_clique L).1 h.1.1 h.1.2 h.2

theorem ab0_mem_src : s(a0 L, b0 L) ∈ src L := by
  refine mem_union_left _ ?_
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, T0, mem_insert,
    mem_singleton]
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [vert_eq_iff]; simp

theorem a1_mem_src : s(a1 L, b1 L) ∈ src L := by
  refine mem_union_right _ ?_
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff, T1, mem_insert,
    mem_singleton]
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  rw [vert_eq_iff]; simp

/-! #### Good clones of `a₀` and `b₀` live in different blocks -/

theorem common_a0_le (y : BV L) (hy : y.1.val = 1) :
    commonCount (part L) (host L) 0 (a0 L) y ≤ 2 := by
  have hsub : partNbrs (part L) (host L) 0 (a0 L) ∩ partNbrs (part L) (host L) 0 y ⊆
      {a1 L, b0 L} := by
    intro w hw
    simp only [mem_inter, mem_partNbrs, part_eq_iff, adj_iff, a0_val, Fin.val_zero] at hw
    simp only [mem_insert, mem_singleton, vert_eq_iff, a1_val, b0_val]
    omega
  exact (card_le_card hsub).trans card_le_two

theorem common_b0_le (y : BV L) (hy : y.1.val = 0) :
    commonCount (part L) (host L) 0 (b0 L) y ≤ 2 := by
  have hsub : partNbrs (part L) (host L) 0 (b0 L) ∩ partNbrs (part L) (host L) 0 y ⊆
      {b1 L, a0 L} := by
    intro w hw
    simp only [mem_inter, mem_partNbrs, part_eq_iff, adj_iff, b0_val, Fin.val_zero] at hw
    simp only [mem_insert, mem_singleton, vert_eq_iff, b1_val, a0_val]
    omega
  exact (card_le_card hsub).trans card_le_two

theorem clone_a0_block {α : ℝ} (hβ : 2 < beta α * Fintype.card (BV L)) {y : BV L}
    (hy : y ∈ cloneSet (part L) (host L) α 0 (a0 L)) : y.1.val = 0 := by
  rw [mem_cloneSet, part_eq_iff] at hy
  by_contra h
  have h1 : y.1.val = 1 := by simp only [Fin.val_zero] at hy; omega
  have := common_a0_le L y h1
  have : (commonCount (part L) (host L) 0 (a0 L) y : ℝ) ≤ 2 := by exact_mod_cast this
  linarith [hy.2]

theorem clone_b0_block {α : ℝ} (hβ : 2 < beta α * Fintype.card (BV L)) {y : BV L}
    (hy : y ∈ cloneSet (part L) (host L) α 0 (b0 L)) : y.1.val = 1 := by
  rw [mem_cloneSet, part_eq_iff] at hy
  by_contra h
  have h1 : y.1.val = 0 := by simp only [Fin.val_zero] at hy; omega
  have := common_b0_le L y h1
  have : (commonCount (part L) (host L) 0 (b0 L) y : ℝ) ≤ 2 := by exact_mod_cast this
  linarith [hy.2]

/-- **Same-word cloning fails on the source edge `a₀b₀`.** Whatever excluded set `Z`
contains the source vertices, no good clone of `a₀` outside `Z` is adjacent to any good
clone of `b₀` outside `Z`, as soon as `β n > 2`. -/
theorem no_same_word_clone {α : ℝ} (hβ : 2 < beta α * Fintype.card (BV L)) (Z : Finset (BV L))
    (hZ : ∀ e ∈ src L, ∀ v ∈ e, v ∈ Z) {y₀ y₁ : BV L}
    (h₀ : y₀ ∈ cloneSet (part L) (host L) α 0 (a0 L)) (h₀Z : y₀ ∉ Z)
    (h₁ : y₁ ∈ cloneSet (part L) (host L) α 0 (b0 L)) :
    ¬ (host L).Adj y₀ y₁ := by
  have e0 := clone_a0_block L hβ h₀
  have e1 := clone_b0_block L hβ h₁
  have na0 : y₀ ≠ a0 L := fun h => h₀Z (h ▸ hZ _ (ab0_mem_src L) _ (Sym2.mem_mk_left _ _))
  have na1 : y₀ ≠ a1 L := fun h => h₀Z (h ▸ hZ _ (a1_mem_src L) _ (Sym2.mem_mk_left _ _))
  rw [ne_eq, vert_eq_iff] at na0 na1
  simp only [a0_val, a1_val] at na0 na1
  rw [adj_iff]
  omega

/-! #### Good clones exist (the failure is not vacuous) -/

theorem clone_exists_aux (hL1 : 1 ≤ L) (b : Fin 4) (hb : b.val < 2) {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ 1 / 8) (x y : BV L)
    (hx : x.1 = b) (hy : y.1 = b) (hxy : x ≠ y) :
    y ∈ cloneSet (part L) (host L) α 0 x := by
  rw [mem_cloneSet, part_eq_iff]
  refine ⟨by simp [hy]; omega, ?_⟩
  have hsub : ((({b} : Finset (Fin 4)) ×ˢ (univ : Finset (Fin (L + 2)))).erase x).erase y ⊆
      partNbrs (part L) (host L) 0 x ∩ partNbrs (part L) (host L) 0 y := by
    intro w hw
    simp only [mem_erase, mem_product, mem_singleton, mem_univ, and_true, ne_eq,
      vert_eq_iff] at hw
    have hw1 : w.1.val = b.val := by rw [hw.2.2]
    have hx1 : x.1.val = b.val := by rw [hx]
    have hy1 : y.1.val = b.val := by rw [hy]
    simp only [mem_inter, mem_partNbrs, part_eq_iff, adj_iff, Fin.val_zero]
    omega
  have hcard : Finset.card (((({b} : Finset (Fin 4)) ×ˢ
      (univ : Finset (Fin (L + 2)))).erase x).erase y) = L := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨hxy.symm, mem_product.mpr ⟨mem_singleton.mpr hy,
      mem_univ _⟩⟩), card_block_erase L b x hx]
    omega
  have h1 := card_le_card hsub
  rw [hcard] at h1
  have h2 : (L : ℝ) ≤ commonCount (part L) (host L) 0 x y := by
    unfold commonCount; exact_mod_cast h1
  rw [card_BV, beta]
  push_cast
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have ha2 : α ^ 2 ≤ 1 / 64 := by nlinarith
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have : α ^ 2 / 2 * (4 * ((L : ℝ) + 2)) ≤ 1 / 64 / 2 * (4 * ((L : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

theorem mem_src_vert {e : Sym2 (BV L)} (he : e ∈ src L) {v : BV L} (hv : v ∈ e) :
    v ∈ T0 L ∨ v ∈ T1 L := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases mem_union.mp he with h | h <;>
    · simp only [triEdges, mem_filter, mk_mem_sym2_iff] at h
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · first | exact Or.inl h.1.1 | exact Or.inr h.1.1
      · first | exact Or.inl h.1.2 | exact Or.inr h.1.2

/-- A fresh vertex of block `b` (index `L + 1 ≥ 2`, so off the source). -/
def fresh (b : Fin 4) : BV L := (b, Fin.last (L + 1))

theorem fresh_not_src (hL1 : 1 ≤ L) (b : Fin 4) : ∀ e ∈ src L, fresh L b ∉ e := by
  intro e he hv
  rcases mem_src_vert L he hv with h | h <;>
  · simp only [T0, T1, mem_insert, mem_singleton, vert_eq_iff, fresh, Fin.val_last,
      a0_val, b0_val, c0_val, a1_val, b1_val, c1_val] at h
    omega

theorem clone_a0_exists (hL1 : 1 ≤ L) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 8) :
    fresh L 0 ∈ cloneSet (part L) (host L) α 0 (a0 L) ∧ ∀ e ∈ src L, fresh L 0 ∉ e :=
  ⟨clone_exists_aux L hL1 0 (by decide) hα0 hα _ _ rfl rfl
    (by rw [ne_eq, vert_eq_iff]; simp [fresh]), fresh_not_src L hL1 0⟩

theorem clone_b0_exists (hL1 : 1 ≤ L) {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 8) :
    fresh L 1 ∈ cloneSet (part L) (host L) α 0 (b0 L) ∧ ∀ e ∈ src L, fresh L 1 ∉ e :=
  ⟨clone_exists_aux L hL1 1 (by decide) hα0 hα _ _ rfl rfl
    (by rw [ne_eq, vert_eq_iff]; simp [fresh]), fresh_not_src L hL1 1⟩

/-- **Bridge obstruction to same-word cloning** (`α = 1/8`, `n = 4(L + 2)`, `L ≥ 63`, so
`β n > 2`). The host is F0-anti-edgeful; the source consists of two physical F0
triangles, has a positive certificate of weight `2` and an F0 decomposition; good clones
of `a₀` and of `b₀` off the source exist; yet for **every** excluded set `Z` containing the
source vertices, no good clone of `a₀` outside `Z` is adjacent to any good clone of `b₀`.
So the source edge `a₀b₀` cannot be kept by any choice of clones. -/
theorem bridge_obstruction (hL : 63 ≤ L) :
    AntiEdgeful (part L) F0 (host L) (1 / 8) ∧ src L ⊆ (host L).edgeFinset ∧
      IsSignedCert (part L) (host L) (src L) (tri L) (fun _ => 1) ∧
      certWeight (fun _ : Fin 2 => (1 : ℤ)) = 2 ∧ HasDecomp (part L) F0 (src L) ∧
      s(a0 L, b0 L) ∈ src L ∧
      (∃ y ∈ cloneSet (part L) (host L) (1 / 8) 0 (a0 L), ∀ e ∈ src L, y ∉ e) ∧
      (∃ y ∈ cloneSet (part L) (host L) (1 / 8) 0 (b0 L), ∀ e ∈ src L, y ∉ e) ∧
      ∀ Z : Finset (BV L), (∀ e ∈ src L, ∀ v ∈ e, v ∈ Z) →
        ∀ y₀ ∈ cloneSet (part L) (host L) (1 / 8) 0 (a0 L), y₀ ∉ Z →
        ∀ y₁ ∈ cloneSet (part L) (host L) (1 / 8) 0 (b0 L), ¬ (host L).Adj y₀ y₁ := by
  have hL1 : 1 ≤ L := by omega
  have hβ : 2 < beta (1 / 8) * Fintype.card (BV L) := by
    rw [card_BV, beta]
    have : (63 : ℝ) ≤ L := by exact_mod_cast hL
    push_cast; nlinarith
  obtain ⟨ha, ha'⟩ := clone_a0_exists L hL1 (α := 1 / 8) (by norm_num) le_rfl
  obtain ⟨hb, hb'⟩ := clone_b0_exists L hL1 (α := 1 / 8) (by norm_num) le_rfl
  exact ⟨antiEdgeful L _ le_rfl, src_subset L, src_cert L, certWeight_src, src_hasDecomp L,
    ab0_mem_src L, ⟨_, ha, ha'⟩, ⟨_, hb, hb'⟩,
    fun Z hZ y₀ h₀ h₀Z y₁ h₁ => no_same_word_clone L hβ Z hZ h₀ h₀Z h₁⟩

end BridgeControl

/-! ### Star control: the coherent-transformer source is not certified -/

namespace StarControl

open CoherentTransformer CoherentTransformer.Refutation CoherentTransformer.BipartiteLinkHost

variable (L : ℕ)

/-- The 4-cycle source `Hx` of the coherent-transformer refutation. -/
abbrev starSource (m : Fin L) : Finset (Sym2 (Fin 6 × Fin L)) :=
  trailEdges succ4 (rootMap L m)

theorem pairCount_starSource (m : Fin L) (a b : Fin 2) :
    pairCount (hp L) (starSource L m) a b =
      (univ.filter fun i : Fin 4 => s(part (cls i), part (cls (succ4 i))) = s(a, b)).card := by
  unfold pairCount starSource trailEdges
  rw [filter_image, card_image_of_injective _ (physicalTrail L m).2.1]
  rfl

/-- The source cycle has one `00` edge, one `11` edge and two `01` edges. -/
theorem starSource_counts (m : Fin L) :
    pairCount (hp L) (starSource L m) 0 0 = 1 ∧ pairCount (hp L) (starSource L m) 1 1 = 1 ∧
      pairCount (hp L) (starSource L m) 0 1 = 2 := by
  simp only [pairCount_starSource]
  decide

/-- **Its coarse F0 charge is `2`.** -/
theorem starSource_coarse_charge (m : Fin L) :
    2 * ((pairCount (hp L) (starSource L m) 0 0 : ℤ) + pairCount (hp L) (starSource L m) 1 1) -
      pairCount (hp L) (starSource L m) 0 1 = 2 := by
  obtain ⟨h1, h2, h3⟩ := starSource_counts L m
  rw [h1, h2, h3]; norm_num

/-- **The star-charge source admits no signed physical F0 certificate**, of any weight; so it
is not an input of the Stage 49 candidate. -/
theorem starSource_not_certified (m : Fin L) {ι : Type*} [Fintype ι] (t : ι → Finset _)
    (c : ι → ℤ) : ¬ IsSignedCert (hp L) (host L) (starSource L m) t c := fun h => by
  have := coarse_charge_of_cert (hp L) (host L) h
  rw [starSource_coarse_charge] at this
  norm_num at this

end StarControl

/-! ### Item-5 control: two modes do not force equal part-pair counts -/

namespace CountControl

/-- Parts of six vertices: `{0, 1, 2}` is a `001` triangle, `{3, 4, 5}` a `011` triangle. -/
def cp : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

/-- A single `001` triangle. -/
def P : Finset (Sym2 (Fin 6)) := triEdges {0, 1, 2}

/-- A disjoint `011` triangle. -/
def Q : Finset (Sym2 (Fin 6)) := triEdges {3, 4, 5}

theorem hasDecomp_single {V : Type*} [DecidableEq V] {p : V → Fin 2} {s : Finset V}
    (h : IsTypedTri p F0 s) : HasDecomp p F0 (triEdges s) :=
  ⟨{s}, by simpa using h, by simp, by simp⟩

theorem P_dec : HasDecomp cp F0 P := hasDecomp_single ⟨by decide, by unfold cp F0; decide⟩

theorem Q_dec : HasDecomp cp F0 Q := hasDecomp_single ⟨by decide, by unfold cp F0; decide⟩

theorem P_eq : P = {s(0, 1), s(0, 2), s(1, 2)} :=
  DoubleHexagon.triEdges_triple _ _ _ (by decide) (by decide) (by decide)

theorem Q_eq : Q = {s(3, 4), s(3, 5), s(4, 5)} :=
  DoubleHexagon.triEdges_triple _ _ _ (by decide) (by decide) (by decide)

/-- `(∅, Q)` is a two-mode solution for `P`. -/
theorem twoMode : IsTwoMode cp P ∅ Q :=
  ⟨disjoint_empty_right _, by rw [P_eq, Q_eq]; decide, disjoint_empty_left _, Q_dec,
    by simpa using P_dec, by simpa using Q_dec⟩

/-- **…but the `00`-counts differ** (`1` versus `0`), so item 5 of the candidate is an
additional requirement, not a consequence of the two modes. -/
theorem counts_differ : pairCount cp Q 0 0 ≠ pairCount cp P 0 0 := by
  rw [P_eq, Q_eq]
  decide

end CountControl

end PartitionedTriangleAbsorption.SignedCertificate

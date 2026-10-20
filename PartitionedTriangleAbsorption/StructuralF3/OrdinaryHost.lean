/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Main
public import PartitionedTriangleAbsorption.StructuralF3.HostCycles

/-! # The ordinary refiner in the complete four-class host

The accepted `UniversalRefiner.exists_universal_refiner` assumes minimum degree `3n/4`, which a
complete four-class host with classes of size at least `γ n` need not have. Its only use of
that hypothesis is the anti-edge supply `AntiEdgeful part1 triFam G (1/2)`. This module
re-runs the unchanged proof (`producer_of_hierarchy_alpha`, `exists_universal_refiner_alpha`)
for an arbitrary anti-edge constant `α`, with the selection budget `alpha_family_budget`
(requiring `8λ ≤ α`), and proves that the four-class host has `α = 2γ`
(`antiEdgeful_part1_host`). No accepted module is changed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

open Finset AntiEdgeSelection OnePart UniversalRefiner

/-- The selection budget for an anti-edge constant `α ≥ 8λ`. -/
theorem alpha_family_budget (lam rho n M d r q alpha : ℝ) (hlam : 0 < lam)
    (hsmall : lam ≤ 1 / 64) (hrho : 0 ≤ rho)
    (hscale : 16777216 * rho ≤ lam * lam) (hn : 0 < n)
    (hM : M ≤ 512 * rho * n ^ 2) (hd : d ≤ 2 * rho * n)
    (hr : r ≤ 3 * lam * n) (hqlo : lam * n / 128 ≤ q)
    (hqhi : q ≤ lam * n / 64) (halpha : 8 * lam ≤ alpha) :
    M / q + 2 * (d + r + 2 * q) < alpha * n := by
  have hden : 0 < lam * n / 128 := by positivity
  have hq : 0 < q := hden.trans_le hqlo
  have hmnon : 0 ≤ 512 * rho * n ^ 2 := by positivity
  have hratio : M / q ≤ (65536 * rho / lam) * n := by
    calc
      M / q ≤ (512 * rho * n ^ 2) / q := div_le_div_of_nonneg_right hM hq.le
      _ ≤ (512 * rho * n ^ 2) / (lam * n / 128) :=
        div_le_div_of_nonneg_left hmnon hden hqlo
      _ = _ := by field_simp; ring
  have hsmallratio : 65536 * rho / lam ≤ lam / 256 := by
    rw [div_le_iff₀ hlam]; nlinarith
  have hrho' : 4 * rho ≤ lam / 16 := by nlinarith
  have h1 : (65536 * rho / lam) * n ≤ lam / 256 * n := mul_le_mul_of_nonneg_right hsmallratio hn.le
  have h2 : 4 * rho * n ≤ lam / 16 * n := mul_le_mul_of_nonneg_right hrho' hn.le
  have h3 : 0 < lam * n := by positivity
  nlinarith

theorem exists_two_other : ∀ a b : Fin 4, ∃ c1 c2 : Fin 4, c1 ≠ a ∧ c1 ≠ b ∧
    c2 ≠ a ∧ c2 ≠ b ∧ c1 ≠ c2 := by decide

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The complete four-class host has the anti-edge supply `2γ` for the one-part family. -/
theorem antiEdgeful_part1_host (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (γ : ℝ)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => cls v = i).card : ℝ)) :
    AntiEdgeful part1 triFam G (2 * γ) := by
  classical
  intro τ _ i j k _ u v _ _ _
  obtain ⟨c1, c2, h1u, h1v, h2u, h2v, h12⟩ : ∃ c1 c2 : Fin 4, c1 ≠ cls u ∧ c1 ≠ cls v ∧
      c2 ≠ cls u ∧ c2 ≠ cls v ∧ c1 ≠ c2 := by
    exact exists_two_other (cls u) (cls v)
  have hsub : (univ.filter fun w => cls w = c1) ∪ (univ.filter fun w => cls w = c2) ⊆
      univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ part1 w = k := by
    intro w hw
    have hk : part1 w = k := Subsingleton.elim _ _
    rcases mem_union.mp hw with hw | hw <;>
    · have hc := (mem_filter.mp hw).2
      refine mem_filter.mpr ⟨mem_univ _, (hG u w).mpr ?_, (hG w v).mpr ?_, hk⟩
      · rw [hc]; first | exact Ne.symm h1u | exact Ne.symm h2u
      · rw [hc]; first | exact h1v | exact h2v
  have hdisj : Disjoint (univ.filter fun w => cls w = c1) (univ.filter fun w => cls w = c2) :=
    disjoint_filter.mpr fun w _ h1 h2 => h12 (h1.symm.trans h2)
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at hcard
  have hc : ((((univ.filter fun w => cls w = c1).card +
      (univ.filter fun w => cls w = c2).card : ℕ)) : ℝ) ≤
      ((univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ part1 w = k).card : ℝ) := by
    exact_mod_cast hcard
  push_cast at hc
  linarith [hcls c1, hcls c2]

theorem producer_of_hierarchy_alpha (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset (Sym2 V))
    (hXG : X ⊆ G.edgeFinset) (hmap : ℕ → V → V) (L : ℕ) (hlast : links X hmap L = ∅)
    (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    (mdr : ℕ → V × V) (hmd : ∀ k, (mdr k).1 ≠ (mdr k).2) (adr : V × V) (had : adr.1 ≠ adr.2)
    (α : ℝ) (hanti : AntiEdgeful part1 triFam G α) (d : ℝ) (hXd : DegBounded X d) (r q : ℕ)
    (hq : 0 < q)
    (hroot : ∀ x, rootLoad (theReqs X hmap L mdr adr) (fun r => (rootPair hmap mdr adr r).1)
      (fun r => (rootPair hmap mdr adr r).2) x ≤ r)
    (hbudget : ((theReqs X hmap L mdr adr).card : ℝ) / q + 2 * (d + r + 2 * q) <
      α * (Fintype.card V : ℝ)) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3)) (P : ℕ × Bool × Fin 3 × Fin 3 →
        Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := part1) (F := triFam) indices P X R ∧
      (∀ j ∈ indices, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧
        (∀ v, Even (incidentLoad (P j) v)) ∧ 3 ∣ (P j).card ∧ (P j).card ≤ 42) ∧
      (∀ v, incidentLoad R v ≤ r + 2 * q) ∧
      indices.card ≤ 18 * (theLib X hmap L mdr adr).card ∧
      ∀ v, ∑ j ∈ indices, incidentLoad (P j) v ≤ 594 * incidentLoad X v + 630 * (r + 2 * q) := by
  set rt := rootPair hmap mdr adr with hrt
  set s := theReqs X hmap L mdr adr with hs
  obtain ⟨f, hf, hdis, haux⟩ := exists_compatible_family part1 triFam G α d hanti X hXd ∅
    (fun r => (rt r).1) (fun r => (rt r).2) (fun _ => 0) s (theReqs_roots_ne hfix hmd had)
    (fun _ _ => by simp [triFam, part1]) r q hq hroot (by simpa using hbudget)
  have hR : Realises G X s rt f :=
    { roots_ne := theReqs_roots_ne hfix hmd had
      adj_left := fun r hr => (hf r hr).1
      adj_right := fun r hr => (hf r hr).2.1
      avoid_left := fun r hr => (hf r hr).2.2.2.2.1
      avoid_right := fun r hr => (hf r hr).2.2.2.2.2
      disj := hdis
      reserve := fun e he => SimpleGraph.mem_edgeFinset.mp (hXG he) }
  have hLD := layerData hlast hR
  set C := theLib X hmap L mdr adr with hC
  set N := C.card with hN
  set B := theB X hmap L mdr adr f with hB
  set W := theW hmap mdr adr f with hW
  set Rp := theRpar X hmap L mdr adr f with hRp
  set fam := familyEdges s (fun r => (rt r).1) (fun r => (rt r).2) f with hfam
  have hfamG : fam ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨r, hr, he⟩ := mem_biUnion.mp he
    simp only [pathEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact SimpleGraph.mem_edgeFinset.mpr (hf r hr).1
    · exact SimpleGraph.mem_edgeFinset.mpr (hf r hr).2.1.symm
  have hfamInc : ∀ v, incidentLoad fam v ≤ r + 2 * q := fun v =>
    (family_incident_card_le s _ _ f v).trans (Nat.add_le_add (hroot v)
      (Nat.mul_le_mul_left 2 (haux v)))
  have hRpfam : Rp ⊆ fam := by
    change physU rt f (parRem X hmap L ∪ adjRem (adjCount X hmap L)) ⊆ fam
    rw [parRem_eq, adjRem_eq, ← image_union]
    refine physU_subset_family ?_
    intro r hr
    simp only [hs, theReqs, allReqs, mem_union]
    rcases mem_union.mp hr with h | h <;> tauto
  have hWfam : ModThreeLayer.wires N W ⊆ fam := by
    intro e he
    obtain ⟨k, hk, c, hkc⟩ := ModThreeLayer.mem_wires.mp he
    have himg : ({Sum.inl (Req.md k c false), Sum.inl (Req.md k c true)} : Finset (Atom V)) =
        ({Req.md k c false, Req.md k c true} : Finset (Req V)).image Sum.inl := by simp
    have hsub : ({Req.md k c false, Req.md k c true} : Finset (Req V)) ⊆ s := by
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> exact md_mem_theReqs hk c _
    have : W k c ⊆ fam := by
      change physU rt f _ ⊆ fam
      rw [himg]
      exact physU_subset_family hsub
    exact this hkc
  have hRfam : Rp ∪ ModThreeLayer.wires N W ⊆ fam := union_subset hRpfam hWfam
  have hBcard : ∀ i < N, (B i).card ≤ 22 := fun i _ =>
    (card_physU_le rt f _).trans ((Nat.mul_le_mul_left 2 (card_piece_le X hmap _)).trans
      (by norm_num))
  have hWcard : ∀ i c, (W i c).card ≤ 4 := fun i c =>
    (card_physU_le rt f _).trans ((Nat.mul_le_mul_left 2 card_le_two).trans (by norm_num))
  refine ⟨ModThreeLayer.layeredIndices N B W, ModThreeLayer.layeredPiece N B W,
    Rp ∪ ModThreeLayer.wires N W, hRfam.trans hfamG, ModThreeLayer.layered_rem_disjoint hLD,
    ModThreeLayer.layered_refinesReserve hLD, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hsub := ModThreeLayer.layeredPiece_subset hLD j hj
    have hloop := ModThreeLayer.loopless_of_subset hLD hsub
    obtain ⟨h3, hev⟩ :=
      (isIntDiv_part1_iff _ hloop).mp (ModThreeLayer.layeredPiece_isIntDiv hLD j hj)
    exact ⟨hsub, hloop, hev, h3,
      card_layeredPiece_le hBcard hWcard (ModThreeLayer.mem_layeredIndices.mp hj).1⟩
  · intro v
    exact (ModThreeLayer.incidentLoad_mono hRfam v).trans (hfamInc v)
  · unfold ModThreeLayer.layeredIndices
    refine (card_filter_le _ _).trans ?_
    simp [card_product]
    omega
  · intro v
    have hlay := ModThreeLayer.layered_incidence_le hLD v
    have hBsum : ∑ k ∈ range N, incidentLoad (B k) v ≤
        33 * (incidentLoad X v + (r + 2 * q)) := by
      have h1 : ∑ k ∈ range N, incidentLoad (B k) v =
          ∑ i ∈ C, incidentLoad (physU rt f (piece X hmap i)) v :=
        sum_range_enum (C := C) fun i => incidentLoad (physU rt f (piece X hmap i)) v
      rw [h1]
      have hCfull : C ⊆ fullLib X hmap L (adjCount X hmap L) := filter_subset _ _
      calc ∑ i ∈ C, incidentLoad (physU rt f (piece X hmap i)) v
          ≤ ∑ i ∈ fullLib X hmap L (adjCount X hmap L),
              incidentLoad (physU rt f (piece X hmap i)) v :=
            sum_le_sum_of_subset hCfull
        _ ≤ ∑ i ∈ fullLib X hmap L (adjCount X hmap L),
              ∑ a ∈ piece X hmap i, incidentLoad (phys rt f a) v :=
            sum_le_sum fun i _ => incidentLoad_physU_le rt f _ v
        _ ≤ 33 * ∑ a ∈ parRem X hmap L ∪ adjRem (adjCount X hmap L) ∪ X.image Sum.inr,
              incidentLoad (phys rt f a) v :=
            sum_pieces_le X hmap L _ _ (fun i hi => piece_subset X hmap L _ hi) _
        _ = 33 * incidentLoad (Rp ∪ X) v := by
            rw [← hR.incidentLoad_physU (union_subset parRem_adjRem_subset_dom
              subset_union_right), physU_union, physU_inr]
            rfl
        _ ≤ 33 * (incidentLoad X v + (r + 2 * q)) := by
            refine Nat.mul_le_mul_left 33 ((ModThreeLayer.incidentLoad_union_le _ _ v).trans ?_)
            have := (ModThreeLayer.incidentLoad_mono hRpfam v).trans (hfamInc v)
            omega
    have hWinc := (ModThreeLayer.incidentLoad_mono hWfam v).trans (hfamInc v)
    omega


/-- **The universal bounded ordinary refiner, for an anti-edge constant `α`.** Same
conclusion as `UniversalRefiner.exists_universal_refiner`; the minimum-degree hypothesis is
replaced by `AntiEdgeful part1 triFam G α` with `8λ ≤ α`. -/
theorem exists_universal_refiner_alpha (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (lam rho : ℝ)
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (hX : DegBounded X (2 * rho * Fintype.card V)) (alpha : ℝ) (halpha : 8 * lam ≤ alpha)
    (hanti : AntiEdgeful part1 triFam G alpha) :
    ∃ (indices : Finset (ℕ × Bool × Fin 3 × Fin 3))
      (P : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := part1) (F := triFam) indices P X R ∧
      (∀ j ∈ indices, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧
        (∀ v, Even (incidentLoad (P j) v)) ∧ 3 ∣ (P j).card ∧ (P j).card ≤ 42) ∧
      DegBounded R (4 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  set n := Fintype.card V with hn
  obtain ⟨p, hp1, h2, hP1, hP2⟩ := exists_heap_height n lam rho hlam hlam64 hrho hscale hn1
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have hP2pos : 0 < P2 := by positivity
  have hn4 : 4 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨u0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 2 ^ 30 * rho ≤ lam := by nlinarith
  have hrn : rho * n ≤ lam * n / 2 ^ 30 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hrn2 : 1 ≤ rho * (n : ℝ) ^ 2 := by nlinarith
  -- the construction
  set hmap := heapMap u0 p with hhmap
  set mdr := mdRoots u0 with hmdr
  set adr : V × V := (vtx u0 0, vtx u0 1) with hadr
  have had : adr.1 ≠ adr.2 := by
    intro h
    have := congrArg idx h
    simp only [hadr] at this
    rw [idx_vtx u0 (by omega), idx_vtx u0 (by omega)] at this
    exact absurd this (by norm_num)
  have hXloop : ∀ e ∈ X, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))
  set D := ⌊2 * rho * n⌋₊ with hDdef
  have hD : ∀ u, (vChain X u).card ≤ D := fun u => Nat.le_floor (hX u)
  have hDR : (D : ℝ) ≤ 2 * rho * n := Nat.floor_le (by positivity)
  -- size of the reserve
  have hXcard : (X.card : ℝ) ≤ rho * (n : ℝ) ^ 2 := by
    have h1 := sum_vChain_card_eq X hXloop
    have h2' : ∀ u, ((vChain X u).card : ℝ) ≤ 2 * rho * n := fun u => hX u
    have h3 : ((∑ u, (vChain X u).card : ℕ) : ℝ) ≤ n * (2 * rho * n) := by
      push_cast
      calc ∑ u, ((vChain X u).card : ℝ) ≤ ∑ _u : V, 2 * rho * n := sum_le_sum fun u _ => h2' u
        _ = n * (2 * rho * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
    rw [h1] at h3
    push_cast at h3
    nlinarith
  -- size of the hierarchy
  set S := ∑ l ∈ range (p + 1), (links X hmap l).card with hSdef
  have hS : S ≤ X.card + 2 ^ (p + 1) * 2 ^ p := heap_sum_links h2
  have hSR : (S : ℝ) ≤ 2 * rho * (n : ℝ) ^ 2 :=
    size_bound_real X.card S p n lam rho hlam hrho hscale hS hXcard hP2
  set N := (theLib X hmap (p + 1) mdr adr).card with hNdef
  have hN : N ≤ 17 * S + 2 := card_theLib_le X hmap (p + 1) mdr adr
  have hNR : (N : ℝ) ≤ 34 * rho * (n : ℝ) ^ 2 + 2 := by
    have : (N : ℝ) ≤ 17 * S + 2 := by exact_mod_cast hN
    linarith
  have hM : (theReqs X hmap (p + 1) mdr adr).card ≤ 110 * S + 16 :=
    card_theReqs_le X hmap (p + 1) mdr adr
  have hMR : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) ≤ 512 * rho * (n : ℝ) ^ 2 := by
    have : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) ≤ 110 * S + 16 := by exact_mod_cast hM
    nlinarith
  -- root load
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = 2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
    12 * ((N + 1) / n + 1) := ⟨_, rfl⟩
  have hroot : ∀ x, rootLoad (theReqs X hmap (p + 1) mdr adr)
      (fun r => (rootPair hmap mdr adr r).1) (fun r => (rootPair hmap mdr adr r).2) x ≤ r := by
    intro x
    have h1 : rootLoad (theReqs X hmap (p + 1) mdr adr)
        (fun r => (rootPair hmap mdr adr r).1) (fun r => (rootPair hmap mdr adr r).2) x ≤
        ∑ l ∈ range (p + 1), (2 * (vChain (links X hmap l) x).card +
          10 * hubWeight (links X hmap l) (hmap l) x) + 8 + 12 * ((N + 1) / n + 1) :=
      rootLoad_theReqs_le u0 (by omega) X hmap (p + 1) adr x
    have h3 : ∑ l ∈ range (p + 1), (2 * (vChain (links X hmap l) x).card +
          10 * hubWeight (links X hmap l) (hmap l) x) ≤
        2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) :=
      heap_root (u0 := u0) (X := X) h2 D hD x
    omega
  have hrR : (r : ℝ) ≤ lam * n := by
    rw [hrdef]
    exact root_bound_real n p D N lam rho hlam hlam64 hrho hscale hn2 hnR hP1 hP2 hDR hNR
  -- quota and budget
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = ⌊lam * n / 64⌋₊ := ⟨_, rfl⟩
  have hqhi : (q : ℝ) ≤ lam * n / 64 := by rw [hqdef]; exact Nat.floor_le (by positivity)
  have hqlo : lam * n / 128 ≤ (q : ℝ) := by
    have := Nat.lt_floor_add_one (lam * n / 64)
    rw [hqdef]
    linarith
  have hq : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  have hbudget : ((theReqs X hmap (p + 1) mdr adr).card : ℝ) / q +
      2 * (2 * rho * n + r + 2 * q) < alpha * (n : ℝ) := by
    have hr3 : (r : ℝ) ≤ 3 * lam * n := by linarith
    have hsc : 16777216 * rho ≤ lam * lam := by nlinarith
    generalize ((theReqs X hmap (p + 1) mdr adr).card : ℝ) = Mv at hMR ⊢
    generalize (r : ℝ) = rv at hr3 ⊢
    generalize (q : ℝ) = qv at hqlo hqhi ⊢
    generalize (n : ℝ) = nv at hnpos hMR hr3 hqlo hqhi ⊢
    exact alpha_family_budget lam rho nv Mv (2 * rho * nv) rv qv alpha
      hlam hlam64 hrho.le hsc hnpos hMR le_rfl hr3 hqlo hqhi halpha
  obtain ⟨indices, P, R, hRG, hRX, href, hpieces, hRdeg, hcard, hinc⟩ :=
    producer_of_hierarchy_alpha G X hXG hmap (p + 1) (links_last h2) (heap_fix hp1 h2) mdr
      (mdRoots_ne u0 (by omega)) adr had alpha hanti (2 * rho * n) hX
      r q hq hroot hbudget
  refine ⟨indices, P, R, hRG, hRX, href, hpieces, ?_, ?_, ?_⟩
  · intro v
    have h1 : ((incidentLoad R v : ℕ) : ℝ) ≤ r + 2 * q := by exact_mod_cast hRdeg v
    change ((incidentLoad R v : ℕ) : ℝ) ≤ _
    linarith only [h1, hrR, hqhi, hn2]
  · have h1 : (indices.card : ℝ) ≤ 18 * N := by exact_mod_cast hcard
    linarith only [h1, hNR, hrn2]
  · intro v
    have h1 : ((∑ j ∈ indices, incidentLoad (P j) v : ℕ) : ℝ) ≤
        594 * incidentLoad X v + 630 * (r + 2 * q) := by exact_mod_cast hinc v
    have h2' : (incidentLoad X v : ℝ) ≤ 2 * rho * n := hX v
    have h3 : 594 * (incidentLoad X v : ℝ) ≤ 1188 * (rho * n) := by linarith only [h2']
    have h4 : 630 * ((r : ℝ) + 2 * q) ≤ 650 * (lam * n) := by linarith only [hrR, hqhi, hn2]
    have h5 : 1188 * (rho * n) ≤ lam * n := by linarith only [hrn, hn2]
    linarith only [h1, h3, h4, h5, hn2]

end PartitionedTriangleAbsorption.StructuralF3

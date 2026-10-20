/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Assembly

/-!
# The producer, for an abstract hub hierarchy

`producer_of_hierarchy`: for any hub maps whose link families end empty and whose maps have
no fixed point on link endpoints, any root load bound `r`, auxiliary quota `q` and the strict
selection budget of `AntiEdgeSelection.exists_compatible_family`, there is a fixed physical
library refining every divisible leftover of `X` (`RefinerAssembly.RefinesReserve`), with
explicit size and incidence bounds.  The concrete hub hierarchy and the numerical budgets are
supplied in `UniversalRefiner.Main`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection OnePart

variable {V : Type*} [DecidableEq V]

theorem pos_enum {C : Finset (LibIdx V)} {k : ℕ} (hk : k < C.card) :
    pos C (enum C k) = k := by
  unfold pos
  rw [dite_eq_left (enum_mem hk)]
  unfold enum
  simp only [dite_eq_left hk, Subtype.coe_eta, Equiv.apply_symm_apply]

omit [DecidableEq V] in
theorem sum_range_enum {C : Finset (LibIdx V)} (g : LibIdx V → ℕ) :
    ∑ k ∈ range C.card, g (enum C k) = ∑ i ∈ C, g i := by
  classical
  refine sum_nbij' (enum C) (pos C) ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact enum_mem (mem_range.mp hk)
  · intro i hi; exact mem_range.mpr (pos_lt hi)
  · intro k hk; exact pos_enum (mem_range.mp hk)
  · intro i hi; exact enum_pos hi
  · intro k _; rfl

theorem card_physU_le (rt : Req V → V × V) (f : Req V → V) (A : Finset (Atom V)) :
    (physU rt f A).card ≤ 2 * A.card := by
  unfold physU
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum fun a _ => card_phys_le rt f a

theorem incidentLoad_physU_le (rt : Req V → V × V) (f : Req V → V) (A : Finset (Atom V))
    (v : V) : incidentLoad (physU rt f A) v ≤ ∑ a ∈ A, incidentLoad (phys rt f a) v := by
  unfold incidentLoad physU
  rw [filter_biUnion]
  exact card_biUnion_le

theorem card_piece_le (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (i : LibIdx V) :
    (piece X hmap i).card ≤ 11 := by
  cases i with
  | alt l π x ca cb cs => exact card_altAtoms_le π x ca cb cs
  | cyc l σ => exact card_le_two.trans (by norm_num)
  | adj k => exact card_le_two.trans (by norm_num)

variable [Fintype V]

theorem theReqs_roots_ne {X : Finset (Sym2 V)} {hmap : ℕ → V → V} {L : ℕ} {mdr : ℕ → V × V}
    {adr : V × V} (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    (hmd : ∀ k, (mdr k).1 ≠ (mdr k).2) (had : adr.1 ≠ adr.2) :
    ∀ r ∈ theReqs X hmap L mdr adr,
      (rootPair hmap mdr adr r).1 ≠ (rootPair hmap mdr adr r).2 := by
  intro r hr
  simp only [theReqs, allReqs, mem_union] at hr
  rcases hr with (hr | hr) | hr
  · have hA : (Sum.inl r : Atom V) ∈ parRem X hmap L := by
      rw [parRem_eq]; exact mem_image_of_mem _ hr
    obtain ⟨l, hl, hA⟩ := mem_biUnion.mp hA
    cases r with
    | ep l' u j b =>
      obtain ⟨rfl, hj⟩ := ep_mem_levelAtoms.mp hA
      obtain ⟨π, hπ⟩ : (vChain (links X hmap l') u).Nonempty := card_pos.mp (by omega)
      obtain ⟨hπ, hu⟩ := mem_vChain.mp hπ
      exact (hfix l' (mem_range.mp hl) π hπ u hu).symm
    | pr l' σ j b =>
      obtain ⟨-, hσ, -⟩ := pr_mem_levelAtoms.mp hA
      exact endA_ne_endB (mem_nextLinks.mp hσ).2
    | tm l' σ b =>
      obtain ⟨-, hσ⟩ := tm_mem_levelAtoms.mp hA
      exact endA_ne_endB (mem_nextLinks.mp hσ).2
    | md k c b => exact absurd hA md_not_mem_levelAtoms
    | adj k b => exact absurd hA adj_not_mem_levelAtoms
  · obtain ⟨k, -, hk⟩ := mem_biUnion.mp hr
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact had
  · obtain ⟨q, -, rfl⟩ := mem_image.mp hr
    exact hmd q.1

omit [Fintype V] in
theorem card_layeredPiece_le {N : ℕ} {B : ℕ → Finset (Sym2 V)} {W : ℕ → Fin 3 → Finset (Sym2 V)}
    (hB : ∀ i < N, (B i).card ≤ 22) (hW : ∀ i c, (W i c).card ≤ 4)
    {j : ℕ × Bool × Fin 3 × Fin 3} (hj : j.1 < N) :
    (ModThreeLayer.layeredPiece N B W j).card ≤ 42 := by
  obtain ⟨i, sel, a, b⟩ := j
  have h1 : (if sel then B i else ∅).card ≤ 22 := by
    split_ifs
    · exact hB i hj
    · simp
  have h2 : (ModThreeLayer.leftPart W i a).card ≤ 12 := by
    unfold ModThreeLayer.leftPart
    split_ifs
    · simp
    · refine card_biUnion_le.trans ((sum_le_sum fun k _ => hW (i - 1) k).trans ?_)
      rw [sum_const, smul_eq_mul]
      have : (univ.filter fun k : Fin 3 => a ≤ k).card ≤ 3 :=
        (card_filter_le _ _).trans (by simp)
      omega
  have h3 : (ModThreeLayer.rightPart N W i b).card ≤ 8 := by
    unfold ModThreeLayer.rightPart
    split_ifs
    · refine card_biUnion_le.trans ((sum_le_sum fun k _ => hW i k).trans ?_)
      rw [sum_const, smul_eq_mul, ModThreeLayer.card_filter_lt]
      have := b.isLt
      omega
    · simp
  unfold ModThreeLayer.layeredPiece
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  simp only at h1 h2 h3 ⊢
  omega

/-- **The producer for an abstract hub hierarchy.** -/
theorem producer_of_hierarchy (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset (Sym2 V))
    (hXG : X ⊆ G.edgeFinset) (hmap : ℕ → V → V) (L : ℕ) (hlast : links X hmap L = ∅)
    (hfix : ∀ l < L, ∀ π ∈ links X hmap l, ∀ u ∈ π, hmap l u ≠ u)
    (mdr : ℕ → V × V) (hmd : ∀ k, (mdr k).1 ≠ (mdr k).2) (adr : V × V) (had : adr.1 ≠ adr.2)
    (hanti : AntiEdgeful part1 triFam G (1 / 2)) (d : ℝ) (hXd : DegBounded X d) (r q : ℕ)
    (hq : 0 < q)
    (hroot : ∀ x, rootLoad (theReqs X hmap L mdr adr) (fun r => (rootPair hmap mdr adr r).1)
      (fun r => (rootPair hmap mdr adr r).2) x ≤ r)
    (hbudget : ((theReqs X hmap L mdr adr).card : ℝ) / q + 2 * (d + r + 2 * q) <
      1 / 2 * (Fintype.card V : ℝ)) :
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
  obtain ⟨f, hf, hdis, haux⟩ := exists_compatible_family part1 triFam G (1 / 2) d hanti X hXd ∅
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

end PartitionedTriangleAbsorption.UniversalRefiner

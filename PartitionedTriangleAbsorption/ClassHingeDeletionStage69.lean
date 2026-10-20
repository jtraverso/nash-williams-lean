/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Ledger
public import PartitionedTriangleAbsorption.ClassCertificateLocalStage67
public import PartitionedTriangleAbsorption.SparseReserveGeometry

/-! # Structural hinge supply after physical edge deletion

All hinge counts refer to actual seven-edge sets, not projected type vectors.
Original root triangles may use deleted edges; a downstream consumer must supply
its own surviving root triangles. No universal common-neighbour query is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassHingeDeletionStage69

open Finset ClassReserveStage65 ClassAwareHingesStage64 PhysicalHingeSupply
  SignedHinge BernoulliBlocks ClassCertificate TypedApplicationLinks
  ClassRepresentativesStage65 SparseReserveGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
theorem hinge_count_after_deletion (cls : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    {t : ℕ} (p : V → Fin t) (hp : ∀ a b, cls a = cls b → p a = p b)
    (F : Finset (Multiset (Fin t))) {u v w z : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (huz : G.Adj u z)
    (hvw : G.Adj v w) (hvz : G.Adj v z) (hwz : w ≠ z)
    (hS : ({u, v, w} : Finset V).val.map p ∈ F)
    (hS' : ({u, v, z} : Finset V).val.map p ∈ F)
    (B : Finset (Sym2 V)) (d : ℝ) (hB : DegBounded B d) :
    ((xCand cls u).card : ℝ) * (xCand cls v).card - 7 * (Fintype.card V * d) ≤
      (((G.edgeFinset \ B).powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)).card : ℝ) := by
  classical
  let P := xCand cls u ×ˢ xCand cls v
  let good := P.filter fun q => Disjoint (hingeEdges u v w z q.1 q.2) B
  let K := (G.edgeFinset \ B).powerset.filter fun H =>
    IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6
  have hdata : ∀ q ∈ P, SixDistinct u v w z q.1 q.2 ∧
      hingeEdges u v w z q.1 q.2 ∈ G.edgeFinset.powerset.filter (fun H =>
        IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6) := by
    intro q hq
    have h := cross_pair_hinge cls hG hp huv huw huz hvw hvz hwz hS hS'
      (fun _ => true) (q := q) (by simpa [crossSampled, marked, P] using hq)
    simpa [sampledEdges] using h
  have hmaps : ∀ q ∈ good, hingeEdges u v w z q.1 q.2 ∈ K := by
    intro q hq
    obtain ⟨hqP, hqB⟩ := mem_filter.mp hq
    obtain ⟨_, hmem⟩ := hdata q hqP
    obtain ⟨hpow, hH⟩ := mem_filter.mp hmem
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hH⟩
    intro e he
    exact mem_sdiff.mpr ⟨mem_powerset.mp hpow he, disjoint_left.mp hqB he⟩
  have hgood : good.card ≤ K.card := by
    refine card_le_card_of_injOn (fun q => hingeEdges u v w z q.1 q.2) hmaps ?_
    intro q hq q' hq' heq
    obtain ⟨hx, hy⟩ := hingeEdges_inj (hdata q (mem_filter.mp hq).1).1
      (hdata q' (mem_filter.mp hq').1).1 heq
    exact Prod.ext hx hy
  have hbad : (P.filter fun q => ¬ Disjoint (hingeEdges u v w z q.1 q.2) B).card ≤
      (badPairs B u v w z).card :=
    card_le_card fun q hq => mem_badPairs_of_meets (mem_filter.mp hq).2
  have hsplit := card_filter_add_card_filter_not
    (s := P) (fun q => Disjoint (hingeEdges u v w z q.1 q.2) B)
  have hcount : P.card ≤ K.card + (badPairs B u v w z).card := by
    change (P.filter fun q => Disjoint (hingeEdges u v w z q.1 q.2) B).card ≤ _ at hgood
    omega
  have hcountR : (P.card : ℝ) ≤ (K.card : ℝ) + (badPairs B u v w z).card := by
    exact_mod_cast hcount
  have hbound := card_badPairs_le hB u v w z
  have hprod : (P.card : ℝ) = ((xCand cls u).card : ℝ) * (xCand cls v).card := by
    simp [P, card_product]
  rw [hprod] at hcountR
  linarith

omit [DecidableEq V] in
theorem coarse_antiEdgeful (cls : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    (γ : ℝ) (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ)) :
    AntiEdgeful (coarse cls) F0 G γ := by
  classical
  intro τ hτ i j k hijk u v _ hu hv
  have htype : ({coarse cls u, coarse cls v, k} : Multiset (Fin 2)) ∈ F0 := by
    rw [hu, hv, ← hijk]
    exact hτ
  obtain ⟨c, hcu, hcv, hck⟩ := MultipartiteBoundaryStage64.common_class
    (cls u) (cls v) k htype
  have hsub : classSet cls c ⊆ univ.filter fun w =>
      G.Adj u w ∧ G.Adj w v ∧ coarse cls w = k := by
    intro w hw
    have hc := (mem_filter.mp hw).2
    exact mem_filter.mpr ⟨mem_univ _, (hG _ _).mpr (by simpa [hc] using hcu.symm),
      (hG _ _).mpr (by simpa [hc] using hcv), by simpa [coarse, hc] using hck⟩
  exact (hsize c).trans (by exact_mod_cast card_le_card hsub)

open Classical in
theorem hingeSupply_after_deletion (cls : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b)
    {t : ℕ} (p : V → Fin t) (hp : ∀ a b, cls a = cls b → p a = p b)
    (F : Finset (Multiset (Fin t))) (B : Finset (Sym2 V))
    (γ δ : ℝ)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (hlarge : 2 ≤ γ * Fintype.card V) (hδ : δ ≤ γ ^ 2 / 56)
    (hB : DegBounded B (δ * Fintype.card V)) :
    HingeSupply p F (withoutEdges G B) (γ ^ 2 / 8) 6 := by
  classical
  intro S S' hS hS' h1
  obtain ⟨u, v, w, z, -, -, -, -, -, hwz, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq h1
  have hsub : withoutEdges G B ≤ G := fun a b h => (withoutEdges_adj G B a b).mp h |>.1
  obtain ⟨huv, huw, hvw⟩ := SimpleGraph.is3Clique_triple_iff.mp (hS.1.mono hsub)
  obtain ⟨_, huz, hvz⟩ := SimpleGraph.is3Clique_triple_iff.mp (hS'.1.mono hsub)
  have hcount := hinge_count_after_deletion cls G hG p hp F huv huw huz hvw hvz hwz
    hS.2 hS'.2 B (δ * Fintype.card V) hB
  have hu := xCand_card_ge u (by simpa [fibre, classSet] using hsize (cls u))
  have hv := xCand_card_ge v (by simpa [fibre, classSet] using hsize (cls v))
  have hprod : (γ * Fintype.card V - 1) ^ 2 ≤
      ((xCand cls u).card : ℝ) * (xCand cls v).card := by
    have ha : 0 ≤ γ * Fintype.card V - 1 := by linarith
    have h := mul_le_mul hu hv ha (by positivity)
    simpa [pow_two] using h
  have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hδn := mul_le_mul_of_nonneg_right hδ (sq_nonneg (Fintype.card V : ℝ))
  have hscale : γ ^ 2 / 8 * (Fintype.card V : ℝ) ^ 2 ≤
      ((xCand cls u).card : ℝ) * (xCand cls v).card -
        7 * (Fintype.card V * (δ * Fintype.card V)) := by
    nlinarith [sq_nonneg (γ * Fintype.card V - 2)]
  refine ⟨6, by decide, ?_⟩
  norm_num
  apply (hscale.trans hcount).trans
  exact_mod_cast (card_le_card (by
    intro H hH
    obtain ⟨hHE, hhinge⟩ := mem_filter.mp hH
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hhinge⟩
    intro e he
    have heB := mem_powerset.mp hHE he
    have heG := (mem_sdiff.mp heB).1
    simp only [SimpleGraph.mem_edgeFinset, withoutEdges, ReserveCoverDown.reserveGraph,
      SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
    exact ⟨heB, G.not_isDiag_of_mem_edgeFinset heG⟩))

end PartitionedTriangleAbsorption.ClassHingeDeletionStage69

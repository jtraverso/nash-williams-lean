/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveMean
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.TernaryCopies

@[expose] public section

/-!
# Averaged octahedron and prism placements

All choice sets request at most four earlier neighbours. Unrelated auxiliary
vertices may coincide. Every face used as a host triangle has three distinct
corners, because its three edges are edges of the loopless host.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset StructuralF3General TypedTransformer

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def octahedronTree (a b c : V) : ChoiceTree V 3 :=
  .step (guardedNeighbours p G {b, c} (p a)) fun A =>
    .step (guardedNeighbours p G {a, c, A} (p b)) fun B =>
      .step (guardedNeighbours p G {a, b, A, B} (p c)) fun _ => .leaf

noncomputable def prismTree (a b c d : V) : ChoiceTree V 2 :=
  .step (guardedNeighbours p G {b, c, d} (p a)) fun A =>
    .step (guardedNeighbours p G {a, c, d, A} (p b)) fun _ => .leaf

theorem octahedronTree_lower (Allowed : Fin t → Fin t → Prop)
    (hsymm : Std.Symm Allowed) (s : ℝ)
    (hs : GuardedSupply p G Allowed 4 s) (a b c : V)
    (hab : Allowed (p a) (p b)) (hac : Allowed (p a) (p c))
    (hbc : Allowed (p b) (p c)) : ChoiceTree.Lower s (octahedronTree p G a b c) := by
  change s ≤ (guardedNeighbours p G {b, c} (p a)).card ∧ _
  refine ⟨hs _ (card_le_two.trans (by omega)) _ ?_, ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hsymm.symm _ _ hab
    · exact hsymm.symm _ _ hac
  · intro A hA
    have hpa := (mem_filter.mp hA).2.1
    change s ≤ (guardedNeighbours p G {a, c, A} (p b)).card ∧ _
    refine ⟨hs _ (card_le_three.trans (by omega)) _ ?_, ?_⟩
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hab
      · exact hsymm.symm _ _ hbc
      · simpa only [hpa] using hab
    · intro B hB
      have hpb := (mem_filter.mp hB).2.1
      change s ≤ (guardedNeighbours p G {a, b, A, B} (p c)).card ∧ _
      refine ⟨hs _ card_le_four _ ?_, fun _ _ => trivial⟩
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hac
      · exact hbc
      · simpa only [hpa] using hac
      · simpa only [hpb] using hbc

theorem prismTree_lower (Allowed : Fin t → Fin t → Prop)
    (hsymm : Std.Symm Allowed) (s : ℝ)
    (hs : GuardedSupply p G Allowed 4 s) (a b c d : V)
    (hab : Allowed (p a) (p b)) (hac : Allowed (p a) (p c))
    (had : Allowed (p a) (p d)) (hbc : Allowed (p b) (p c))
    (hbd : Allowed (p b) (p d)) : ChoiceTree.Lower s (prismTree p G a b c d) := by
  change s ≤ (guardedNeighbours p G {b, c, d} (p a)).card ∧ _
  refine ⟨hs _ (card_le_three.trans (by omega)) _ ?_, ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hsymm.symm _ _ hab
    · exact hsymm.symm _ _ hac
    · exact hsymm.symm _ _ had
  · intro A hA
    have hpa := (mem_filter.mp hA).2.1
    change s ≤ (guardedNeighbours p G {a, c, d, A} (p b)).card ∧ _
    refine ⟨hs _ card_le_four _ ?_, fun _ _ => trivial⟩
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hab
    · exact hsymm.symm _ _ hbc
    · exact hsymm.symm _ _ hbd
    · simpa only [hpa] using hab

structure OctahedronRealization (a b c A B C : V) : Prop where
  classA : p A = p a
  classB : p B = p b
  classC : p C = p c
  bA : G.Adj b A
  cA : G.Adj c A
  aB : G.Adj a B
  cB : G.Adj c B
  AB : G.Adj A B
  aC : G.Adj a C
  bC : G.Adj b C
  AC : G.Adj A C
  BC : G.Adj B C

theorem octahedronTree_realizes (a b c : V) (f : Fin 3 → V)
    (hf : ChoiceTree.Supports (octahedronTree p G a b c) f) :
    OctahedronRealization p G a b c (f 0) (f 1) (f 2) := by
  obtain ⟨hA, hB, hC, -⟩ := hf
  obtain ⟨hpa, hAe⟩ := (mem_filter.mp hA).2
  obtain ⟨hpb, hBe⟩ := (mem_filter.mp hB).2
  obtain ⟨hpc, hCe⟩ := (mem_filter.mp hC).2
  exact ⟨hpa, hpb, hpc, hAe _ (by simp), hAe _ (by simp),
    hBe _ (by simp), hBe _ (by simp), hBe _ (by simp),
    hCe _ (by simp), hCe _ (by simp), hCe _ (by simp), hCe _ (by simp)⟩

structure PrismRealization (a b c d A B : V) : Prop where
  classA : p A = p a
  classB : p B = p b
  bA : G.Adj b A
  cA : G.Adj c A
  dA : G.Adj d A
  aB : G.Adj a B
  cB : G.Adj c B
  dB : G.Adj d B
  AB : G.Adj A B

theorem prismTree_realizes (a b c d : V) (f : Fin 2 → V)
    (hf : ChoiceTree.Supports (prismTree p G a b c d) f) :
    PrismRealization p G a b c d (f 0) (f 1) := by
  obtain ⟨hA, hB, -⟩ := hf
  obtain ⟨hpa, hAe⟩ := (mem_filter.mp hA).2
  obtain ⟨hpb, hBe⟩ := (mem_filter.mp hB).2
  exact ⟨hpa, hpb, hAe _ (by simp), hAe _ (by simp), hAe _ (by simp),
    hBe _ (by simp), hBe _ (by simp), hBe _ (by simp), hBe _ (by simp)⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem isCopy_of_three_adj (F : Finset (Multiset (Fin t))) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (ht : Link F (p a) (p b) (p c)) : IsCopy p F G {a, b, c} := by
  have hneab := hab.ne
  have hneac := hac.ne
  have hnebc := hbc.ne
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isNClique_iff]
    constructor
    · rw [show ({a, b, c} : Finset V) = insert a (insert b {c}) by rfl]
      simp only [coe_insert, coe_singleton, SimpleGraph.isClique_insert,
        SimpleGraph.isClique_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
        true_and]
      exact ⟨fun x hx _ => by subst x; exact hbc,
        fun x hx _ => by rcases hx with rfl | rfl; exact hab; exact hac⟩
    · simp [hneab, hneac, hnebc]
  · rw [map_three p hneab hneac hnebc]
    exact ht

omit [Fintype V] [DecidableRel G.Adj] in
theorem OctahedronRealization.host_faces {a b c A B C : V}
    (h : OctahedronRealization p G a b c A B C)
    (F : Finset (Multiset (Fin t))) (ht : Link F (p a) (p b) (p c)) :
    IsCopy p F G {A, B, c} ∧ IsCopy p F G {A, b, C} ∧
    IsCopy p F G {a, B, C} ∧ IsCopy p F G {A, B, C} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isCopy_of_three_adj p G F h.AB h.cA.symm h.cB.symm
      (by simpa only [h.classA, h.classB] using ht)
  · exact isCopy_of_three_adj p G F h.bA.symm h.AC h.bC
      (by simpa only [h.classA, h.classC] using ht)
  · exact isCopy_of_three_adj p G F h.aB h.aC h.BC
      (by simpa only [h.classB, h.classC] using ht)
  · exact isCopy_of_three_adj p G F h.AB h.AC h.BC
      (by simpa only [h.classA, h.classB, h.classC] using ht)

omit [Fintype V] [DecidableRel G.Adj] in
theorem OctahedronRealization.residual_faces {a b c A B C : V}
    (h : OctahedronRealization p G a b c A B C)
    (F : Finset (Multiset (Fin t))) (ht : Link F (p a) (p b) (p c)) :
    (G.Adj b c → IsCopy p F G {A, b, c}) ∧
    (G.Adj a c → IsCopy p F G {a, B, c}) ∧
    (G.Adj a b → IsCopy p F G {a, b, C}) := by
  refine ⟨fun hbc => ?_, fun hac => ?_, fun hab => ?_⟩
  · exact isCopy_of_three_adj p G F h.bA.symm h.cA.symm hbc
      (by simpa only [h.classA] using ht)
  · exact isCopy_of_three_adj p G F h.aB hac h.cB.symm
      (by simpa only [h.classB] using ht)
  · exact isCopy_of_three_adj p G F hab h.aC h.bC
      (by simpa only [h.classC] using ht)

omit [Fintype V] [DecidableRel G.Adj] in
theorem PrismRealization.host_faces {a b c d A B : V}
    (h : PrismRealization p G a b c d A B)
    (F : Finset (Multiset (Fin t)))
    (htc : Link F (p a) (p b) (p c)) (htd : Link F (p a) (p b) (p d))
    (hac : G.Adj a c) (hbc : G.Adj b c) (had : G.Adj a d) (hbd : G.Adj b d) :
    IsCopy p F G {a, B, c} ∧ IsCopy p F G {A, b, c} ∧
    IsCopy p F G {A, B, d} ∧ IsCopy p F G {a, B, d} ∧
    IsCopy p F G {A, b, d} ∧ IsCopy p F G {A, B, c} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCopy_of_three_adj p G F h.aB hac h.cB.symm
      (by simpa only [h.classB] using htc)
  · exact isCopy_of_three_adj p G F h.bA.symm h.cA.symm hbc
      (by simpa only [h.classA] using htc)
  · exact isCopy_of_three_adj p G F h.AB h.dA.symm h.dB.symm
      (by simpa only [h.classA, h.classB] using htd)
  · exact isCopy_of_three_adj p G F h.aB had h.dB.symm
      (by simpa only [h.classB] using htd)
  · exact isCopy_of_three_adj p G F h.bA.symm h.dA.symm hbd
      (by simpa only [h.classA] using htd)
  · exact isCopy_of_three_adj p G F h.AB h.cA.symm h.cB.symm
      (by simpa only [h.classA, h.classB] using htc)

#print axioms octahedronTree_lower
#print axioms prismTree_lower
#print axioms octahedronTree_realizes
#print axioms prismTree_realizes
#print axioms OctahedronRealization.host_faces
#print axioms OctahedronRealization.residual_faces
#print axioms PrismRealization.host_faces

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

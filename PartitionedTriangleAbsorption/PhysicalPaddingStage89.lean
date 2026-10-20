/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleRootedEmbeddingStage87
public import PartitionedTriangleAbsorption.TypedBoundedCoefficients

/-! # Selecting signed-lattice padding inside the actual host

Stage35 supplies an abstract finite extension and a uniform coefficient bound
for bounded pieces. Here the negative triangles are actually selected in G,
avoiding all prohibited edges and specified vertices. The bound is uniform in
pieces of bounded size, not a claimed linear Smith bound in the piece size.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalPaddingStage89

open Finset TypedTransformer PairMoveSelectionStage85 PrivateTemplate

variable {t : ℕ}

/-- Distinct corners of an allowed type are link-compatible, even when their
labels coincide. -/
theorem corners_compatible (F : Finset (Multiset (Fin t))) (σ : Fin 3 → Fin t)
    (hσ : ({σ 0, σ 1, σ 2} : Multiset (Fin t)) ∈ F)
    (i j : Fin 3) (hij : i ≠ j) : ∃ k, Link F (σ i) (σ j) k := by
  have h01 : Link F (σ 0) (σ 1) (σ 2) := hσ
  have h02 := (link_swap F (σ 0) (σ 1) (σ 2)).mp h01
  have h10 := (link_root_swap F (σ 0) (σ 1) (σ 2)).mp h01
  have h12 := (link_swap F (σ 1) (σ 0) (σ 2)).mp h10
  have h20 := (link_root_swap F (σ 0) (σ 2) (σ 1)).mp h02
  have h21 := (link_root_swap F (σ 1) (σ 2) (σ 0)).mp h12
  fin_cases i <;> fin_cases j <;> first
    | contradiction | exact ⟨_, h01⟩ | exact ⟨_, h02⟩ | exact ⟨_, h10⟩
    | exact ⟨_, h12⟩ | exact ⟨_, h20⟩ | exact ⟨_, h21⟩

/-- A prescribed finite family of allowed triangles has a vertex-disjoint,
label-preserving embedding outside the complete exclusion set. -/
theorem select_triangles {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (σ : I → Fin 3 → Fin t)
    (hσ : ∀ i, ({σ i 0, σ i 1, σ i 2} : Multiset (Fin t)) ∈ F)
    (a d : ℝ) (hs : CompatibleSupply p F G a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : 3 * (Fintype.card I : ℝ) + Z.card + 4 * d < a) :
    ∃ f : I × Fin 3 ↪ V, (∀ i j, p (f (i,j)) = σ i j) ∧
      (∀ x, f x ∉ Z) ∧
      ∀ i j k, j ≠ k → G.Adj (f (i,j)) (f (i,k)) ∧ s(f (i,j),f (i,k)) ∉ B := by
  classical
  let m := Fintype.card (I × Fin 3)
  let e : Fin m ≃ I × Fin 3 := (Fintype.equivFin (I × Fin 3)).symm
  let T : SimpleGraph (Fin m) := {
    Adj := fun u v => (e u).1 = (e v).1 ∧ (e u).2 ≠ (e v).2
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }
  let label : Fin m → Fin t := fun u => σ (e u).1 (e u).2
  have hbudget : (m : ℝ) + Z.card + 4 * d < a := by
    simpa [m, Fintype.card_prod, mul_comm] using hb
  have ha : 0 < a := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hz : (0 : ℝ) ≤ Z.card := Nat.cast_nonneg _
    linarith
  have hv : ∀ u : Fin m, ∃ v : V, True := by
    intro u
    have hcount := hs ∅ (by simp) (label u) (by simp [Compatible])
    have hpos : 0 < (TypedEmbeddingSelection.typedNeighbours p G ∅ (label u)).card := by
      exact_mod_cast (lt_of_lt_of_le ha hcount)
    obtain ⟨v, _⟩ := card_pos.mp hpos
    exact ⟨v, trivial⟩
  choose root hroot using hv
  have horder : ∀ v : Fin m, 0 ≤ v.val →
      (univ.filter (fun u : Fin m => u.val < v.val ∧ T.Adj u v)).card ≤ 4 := by
    intro v _
    have hsub : univ.filter (fun u : Fin m => u.val < v.val ∧ T.Adj u v) ⊆
        univ.image (fun j : Fin 3 => e.symm ((e v).1,j)) := by
      intro u hu
      have hu' := (mem_filter.mp hu).2.2
      change (e u).1 = (e v).1 ∧ (e u).2 ≠ (e v).2 at hu'
      refine mem_image.mpr ⟨(e u).2, mem_univ _, ?_⟩
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext hu'.1.symm rfl
    have hc := (card_le_card hsub).trans card_image_le
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  have hcompat : ∀ v : Fin m, 0 ≤ v.val → ∀ u : Fin m, u.val < v.val →
      T.Adj u v → ∃ k, Link F (label v) (label u) k := by
    intro v _ u _ huv
    change (e u).1 = (e v).1 ∧ (e u).2 ≠ (e v).2 at huv
    dsimp [label]
    rw [huv.1]
    exact corners_compatible F (σ (e v).1) (hσ _) _ _ huv.2.symm
  obtain ⟨f, hf, hp, _, havoid⟩ := CompatibleRootedEmbeddingStage87.exists_embedding
    T G p F label a d hs B Z hB hd hbudget 0 (by omega) root
    ⟨by intros; omega, by intros; omega⟩ (by intros; omega) horder hcompat
  let g : I × Fin 3 ↪ V := ⟨fun x => f (e.symm x), by
    intro x y hxy
    exact e.symm.injective (hf.injective _ _ (Fin.isLt _) (Fin.isLt _) hxy)⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i j
    change p (f (e.symm (i,j))) = σ i j
    simpa only [label, e.apply_symm_apply] using hp (e.symm (i,j))
  · intro x
    exact havoid _ (Nat.zero_le _)
  · intro i j k hjk
    exact hf.edges _ _ (Fin.isLt _) (Fin.isLt _) (by simpa [T] using hjk)

/-- Globally distinct vertices give edge-disjoint triangle blocks. -/
theorem good_blocks {I V : Type*} [DecidableEq V]
    (f : I × Fin 3 ↪ V) :
    GoodLabels (fun i => f (i,0)) (fun i => f (i,1)) (fun i => f (i,2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h; have := f.injective h; simp at this
  · intro i h; have := f.injective h; simp at this
  · intro i h; have := f.injective h; simp at this
  · intro i j e he he'
    rw [mem_tri3] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h <;>
      simp only [Sym2.eq_iff] at h
    all_goals rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;>
      exact congrArg Prod.fst (f.injective h)

/-- Select the negative coefficient triangles physically, with their exact
type vector. No absorber or terminal decomposition of the padded piece is
assumed. -/
theorem physical_padding {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (c : Multiset (Fin t) → ℤ) (a d : ℝ) (hs : CompatibleSupply p F G a)
    (B U : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : 3 * (TypedBoundedCoefficients.negativeMass F c : ℝ) + Z.card +
      4 * (d + U.card) < a) :
    ∃ Q : Finset (Sym2 V), Q ⊆ G.edgeFinset ∧ Disjoint Q (B ∪ U) ∧
      HasDecomp p F Q ∧ Q.card = 3 * TypedBoundedCoefficients.negativeMass F c ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
      edgeVec p Q = ∑ τ ∈ F, (max (-c τ) 0) • typeEdgeVec τ := by
  classical
  let I := TypedPaddingProducer.Index F c
  let σ := TypedPaddingProducer.labels F hF c
  have hσ : ∀ i : I, ({σ i 0, σ i 1, σ i 2} : Multiset (Fin t)) ∈ F :=
    TypedPaddingProducer.labels_allowed F hF c
  have hc : Fintype.card I = TypedBoundedCoefficients.negativeMass F c :=
    TypedPaddingProducer.index_card F c
  have hb' : 3 * (Fintype.card I : ℝ) + Z.card + 4 * (d+U.card) < a := by
    rw [hc]
    exact hb
  obtain ⟨f, hp, hz, he⟩ := select_triangles G p F σ hσ a (d+U.card) hs
    (B ∪ U) Z (blocked_union_degree B U d hB) (by positivity) hb'
  let Q := labelEdges (fun i => f (i,0)) (fun i => f (i,1)) (fun i => f (i,2))
  have hg := good_blocks f
  refine ⟨Q, ?_, ?_, ⟨_, goodLabels_typed hg p F ?_⟩, ?_, ?_, ?_⟩
  · intro e heQ
    obtain ⟨i, hi⟩ := mem_labelEdges.mp heQ
    rw [mem_tri3] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact G.mem_edgeFinset.mpr (he i _ _ (by decide)).1
  · rw [disjoint_left]
    intro e heQ heB
    obtain ⟨i, hi⟩ := mem_labelEdges.mp heQ
    rw [mem_tri3] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (he i _ _ (by decide)).2 heB
  · intro i
    simpa only [hp, Link] using hσ i
  · exact hg.card_labelEdges.trans (congrArg (3 * ·) hc)
  · intro e heQ v hv
    obtain ⟨i, hi⟩ := mem_labelEdges.mp heQ
    rw [mem_tri3] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp only [Sym2.mem_iff] at hv <;>
      rcases hv with rfl | rfl <;> exact hz _
  · have hdis : ((univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => tri3 (f (i,0)) (f (i,1)) (f (i,2))) := by
      intro i _ j _ hij
      exact disjoint_left.mpr (fun e hi hj => hij (hg.sep i j e hi hj))
    have hvec : edgeVec p Q = ∑ i : I, typeEdgeVec (TypedLatticePadding.padType σ i) := by
      change edgeVec p (labelEdges (fun i => f (i,0)) (fun i => f (i,1))
        (fun i => f (i,2))) = _
      rw [edgeVec, labelEdges, sum_biUnion hdis]
      apply sum_congr rfl
      intro i _
      rw [tri3, ← triEdges_three (hg.hab i) (hg.hac i) (hg.hbc i), ← edgeVec,
        edgeVec_three p (hg.hab i) (hg.hac i) (hg.hbc i)]
      simp only [hp]
      rfl
    rw [hvec]
    change (∑ i : TypedPaddingProducer.Index F c,
      typeEdgeVec (TypedLatticePadding.padType (TypedPaddingProducer.labels F hF c) i)) = _
    simp only [TypedPaddingProducer.labels_type, Fintype.sum_sigma, sum_const,
      card_univ, Fintype.card_fin]
    rw [← F.sum_coe_sort]
    apply sum_congr rfl
    intro τ _
    rw [← natCast_zsmul, Int.toNat_eq_max]

end PartitionedTriangleAbsorption.PhysicalPaddingStage89

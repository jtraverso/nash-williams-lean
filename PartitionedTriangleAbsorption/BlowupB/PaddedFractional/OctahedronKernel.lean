/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.OctahedronChain

@[expose] public section

/-!
# An octahedral kernel for each complete allowed triangle

The kernel consists of four host faces and three distributions, one over
each original edge. Its boundary is the original physical triangle, and
its four-face part has the stated pointwise coefficient bound.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj]

theorem typed_octahedron_lower (s : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) :
    ChoiceTree.Lower s (octahedronTree p G a b c) := by
  have hsym : Std.Symm (fun i j => ∃ k, Link F i j k) := ⟨by
    intro i j h
    obtain ⟨k, hk⟩ := h
    exact ⟨k, (link_root_swap F _ _ _).mp hk⟩⟩
  exact octahedronTree_lower p G _ hsym s hs a b c
    ⟨p c, ht⟩ ⟨p b, (link_swap F _ _ _).mp ht⟩
    ⟨p a, (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mp ht)⟩

noncomputable def octThirdAB (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) : ThirdDistribution p F G a b s where
  law := ChoiceTree.marginal (octahedronTree p G a b c) 2 s hpos
    (typed_octahedron_lower p F G s hs a b c ht)
  completion := p c
  typed := ht
  support v hv := ChoiceTree.coordinateMass_support _ 2
    (fun v => p v = p c ∧ G.Adj a v ∧ G.Adj b v)
    (fun f hf => by
      have h := octahedronTree_realizes p G a b c f hf
      exact ⟨h.classC, h.aC, h.bC⟩) v hv
  cap v := ChoiceTree.coordinateMass_le _ 2 v s hpos
    (typed_octahedron_lower p F G s hs a b c ht)

noncomputable def octThirdAC (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) : ThirdDistribution p F G a c s where
  law := ChoiceTree.marginal (octahedronTree p G a b c) 1 s hpos
    (typed_octahedron_lower p F G s hs a b c ht)
  completion := p b
  typed := (link_swap F _ _ _).mp ht
  support v hv := ChoiceTree.coordinateMass_support _ 1
    (fun v => p v = p b ∧ G.Adj a v ∧ G.Adj c v)
    (fun f hf => by
      have h := octahedronTree_realizes p G a b c f hf
      exact ⟨h.classB, h.aB, h.cB⟩) v hv
  cap v := ChoiceTree.coordinateMass_le _ 1 v s hpos
    (typed_octahedron_lower p F G s hs a b c ht)

noncomputable def octThirdBC (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) : ThirdDistribution p F G b c s where
  law := ChoiceTree.marginal (octahedronTree p G a b c) 0 s hpos
    (typed_octahedron_lower p F G s hs a b c ht)
  completion := p a
  typed := (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mp ht)
  support v hv := ChoiceTree.coordinateMass_support _ 0
    (fun v => p v = p a ∧ G.Adj b v ∧ G.Adj c v)
    (fun f hf => by
      have h := octahedronTree_realizes p G a b c f hf
      exact ⟨h.classA, h.bA, h.cA⟩) v hv
  cap v := ChoiceTree.coordinateMass_le _ 0 v s hpos
    (typed_octahedron_lower p F G s hs a b c ht)

theorem octThirdAB_chain (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) (Q : Finset V) :
    (octThirdAB p F G s hpos hs a b c ht).chain Q =
      ChoiceTree.mean (octahedronTree p G a b c) (fun f => triangleBasis {a, b, f 2} Q) :=
  ChoiceTree.marginal_average _ 2 s hpos (typed_octahedron_lower p F G s hs a b c ht) _

theorem octThirdAC_chain (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) (Q : Finset V) :
    (octThirdAC p F G s hpos hs a b c ht).chain Q =
      ChoiceTree.mean (octahedronTree p G a b c) (fun f => triangleBasis {a, f 1, c} Q) := by
  rw [ThirdDistribution.chain]
  change (ChoiceTree.marginal (octahedronTree p G a b c) 1 s hpos
    (typed_octahedron_lower p F G s hs a b c ht)).average _ = _
  rw [ChoiceTree.marginal_average]
  apply ChoiceTree.mean_congr
  intro f hf
  congr 1
  ext v
  simp [or_comm]

theorem octThirdBC_chain (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (ht : Link F (p a) (p b) (p c)) (Q : Finset V) :
    (octThirdBC p F G s hpos hs a b c ht).chain Q =
      ChoiceTree.mean (octahedronTree p G a b c) (fun f => triangleBasis {f 0, b, c} Q) := by
  rw [ThirdDistribution.chain]
  change (ChoiceTree.marginal (octahedronTree p G a b c) 0 s hpos
    (typed_octahedron_lower p F G s hs a b c ht)).average _ = _
  rw [ChoiceTree.marginal_average]
  apply ChoiceTree.mean_congr
  intro f hf
  congr 1
  ext v
  simp [or_comm, or_assoc]

structure RootedSide (s : ℝ) where
  left : V
  right : V
  distinct : left ≠ right
  distribution : ThirdDistribution p F G left right s

def RootedSide.edge {s : ℝ} (R : RootedSide p F G s) : Sym2 V := s(R.left, R.right)

structure OctKernel (s : ℝ) (T : Finset V) where
  side : Fin 3 → RootedSide p F G s
  side_injective : Function.Injective (fun i => (side i).edge p F G)
  side_edges : univ.image (fun i => (side i).edge p F G) = triEdges T
  base : TriangleChain V
  base_supported : CopySupported p F G base
  boundary_identity : ∀ e, boundary (triangleBasis T) e =
    boundary base e + ∑ i, boundary (side i).distribution.chain e
  base_bound : ∀ Q : Finset V, Q.card = 3 → |base Q| ≤
    (3 / s) ^ 3 + (∑ v ∈ T, vertexIndicator Q v) * (3 / s) ^ 2

theorem exists_octKernel_three (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : Link F (p a) (p b) (p c)) : Nonempty (OctKernel p F G s {a, b, c}) := by
  classical
  let A := octThirdAB p F G s hpos hs a b c ht
  let B := octThirdAC p F G s hpos hs a b c ht
  let C := octThirdBC p F G s hpos hs a b c ht
  let sides : Fin 3 → RootedSide p F G s :=
    ![⟨a, b, hab, A⟩, ⟨a, c, hac, B⟩, ⟨b, c, hbc, C⟩]
  let tree := octahedronTree p G a b c
  let base : TriangleChain V := fun Q => ChoiceTree.mean tree (fun f => octBase a b c f Q)
  have hlower : ChoiceTree.Lower s tree := typed_octahedron_lower p F G s hs a b c ht
  refine ⟨⟨sides, ?_, ?_, base, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sides, RootedSide.edge, hab.symm, hac.symm, hbc.symm]
  · rw [triEdges_three hab hac hbc]
    ext e
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    simp only [Fin.exists_fin_succ, sides, Matrix.cons_val_zero, RootedSide.edge]
    aesop
  · exact CopySupported.mean tree (fun f => octBase a b c f)
      (fun f hf => octBase_supported p F G a b c f ht (octahedronTree_realizes p G a b c f hf))
  · intro e
    have hAB : boundary A.chain e = ChoiceTree.mean tree
        (fun f => boundary (triangleBasis {a, b, f 2}) e) := by
      simp_rw [show A.chain = (fun Q => ChoiceTree.mean tree
        (fun f => triangleBasis {a, b, f 2} Q)) from funext (octThirdAB_chain p F G s hpos hs a b c ht)]
      exact boundary_mean tree _ e
    have hAC : boundary B.chain e = ChoiceTree.mean tree
        (fun f => boundary (triangleBasis {a, f 1, c}) e) := by
      simp_rw [show B.chain = (fun Q => ChoiceTree.mean tree
        (fun f => triangleBasis {a, f 1, c} Q)) from funext (octThirdAC_chain p F G s hpos hs a b c ht)]
      exact boundary_mean tree _ e
    have hBC : boundary C.chain e = ChoiceTree.mean tree
        (fun f => boundary (triangleBasis {f 0, b, c}) e) := by
      simp_rw [show C.chain = (fun Q => ChoiceTree.mean tree
        (fun f => triangleBasis {f 0, b, c} Q)) from funext (octThirdBC_chain p F G s hpos hs a b c ht)]
      exact boundary_mean tree _ e
    have hmean := ChoiceTree.mean_congr tree (fun _ => boundary (triangleBasis {a, b, c}) e)
      (fun f => boundary (octBase a b c f) e + boundary (triangleBasis {a, b, f 2}) e +
        boundary (triangleBasis {a, f 1, c}) e + boundary (triangleBasis {f 0, b, c}) e)
      (fun f hf => octBase_boundary p G a b c f hab hac hbc
        (octahedronTree_realizes p G a b c f hf) e)
    rw [ChoiceTree.mean_const tree s hpos hlower] at hmean
    simp only [ChoiceTree.mean_add, ← hAB, ← hAC, ← hBC] at hmean
    have hb : boundary base e = ChoiceTree.mean tree (fun f => boundary (octBase a b c f) e) :=
      boundary_mean tree _ e
    rw [← hb] at hmean
    simpa [sides, Fin.sum_univ_succ, add_assoc] using hmean
  · intro Q hQ
    have h := ChoiceTree.mean_octBase_bound tree s hpos hlower a b c Q hQ
    have hsum : (∑ v ∈ ({a, b, c} : Finset V), vertexIndicator Q v) =
        vertexIndicator Q a + vertexIndicator Q b + vertexIndicator Q c := by
      simp [hab, hac, hbc, add_assoc]
    rw [hsum]
    exact h

theorem exists_octKernel (s : ℝ) (hpos : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (T : Finset V) (hT : IsCopy p F (activeCompleteGraph p F) T) :
    Nonempty (OctKernel p F G s T) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hT.1.card_eq
  apply exists_octKernel_three p F G s hpos hs a b c hab hac hbc
  simpa only [Link, map_three p hab hac hbc] using hT.2

#print axioms typed_octahedron_lower
#print axioms octThirdAB_chain
#print axioms octThirdAC_chain
#print axioms octThirdBC_chain
#print axioms exists_octKernel_three
#print axioms exists_octKernel

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case127.Fixer
import RequestProject.NW18.Case126.FixerEdges

/-!
# The fixer triangle pairs (proof of Theorem 12.7)

`FixQ` — the properties of a fixer triangle pair (`fixQA` or `fixQB`, the paper's `Q₁`, `Q₂`)
used in the proof of Theorem 12.7, with `F₂` in place of `F₁`: an edge-disjoint pair of cross
triangles inside the fixer edges `W` covering every edge of `W` at `A`, the remaining two edges
being (cross, hence `F₂`-allowed) edges between normal vertices.  The edge set `fixW`, the pairs
`fixQA`, `fixQB` and the swap lemma `parity_swap` are those of Theorem 12.6.
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The properties of a fixer triangle pair `Q` used in the proof of Theorem 12.6. -/
structure FixQ (G : SimpleGraph V) (p : V → Fin 4) (A : Finset V) (q : V → Fin 2)
    (W : Finset (Sym2 V)) (Q : Finset (Finset V)) : Prop where
  pack : IsTrianglePacking G Q
  sub : Q.biUnion triEdges ⊆ W
  cross : ∀ t ∈ Q, ¬ IsInteriorTri q t
  covA : ∀ x y, s(x, y) ∈ W → (x ∈ A ∨ y ∈ A) → s(x, y) ∈ Q.biUnion triEdges
  rest : ∀ x y, s(x, y) ∈ W → s(x, y) ∉ Q.biUnion triEdges →
    x ∉ A ∧ y ∉ A ∧ AllowedT F2 (p x) (p y)

section

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V}
  {v w0 w1 w2 w3 : V}

omit [Fintype V] [DecidableRel G.Adj] in
lemma fixQA_good (hF : Fixer126 G p A v w0 w1 w2 w3) (q : V → Fin 2)
    (hq0 : q w0 = 0) (hq1 : q w1 = 0) (hq2 : q w2 = 1) (hq3 : q w3 = 1) :
    FixQ G p A q (fixW v w0 w1 w2 w3) (fixQA v w0 w1 w2 w3) := by
  obtain ⟨n0, n1, n2, n3, h01, h02, h03, h12, h13, h23⟩ := hF.ne
  have hE : (fixQA v w0 w1 w2 w3).biUnion triEdges =
      {s(v, w0), s(v, w2), s(w0, w2), s(v, w1), s(v, w3), s(w1, w3)} := by
    rw [fixQA, biUnion_insert, singleton_biUnion, NashWilliams18.triEdges_three n0 n2 h02,
      NashWilliams18.triEdges_three n1 n3 h13]
    ext e; simp only [mem_union, mem_insert, mem_singleton]; tauto
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [fixQA, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hF.a0, hF.a2, hF.e02⟩
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hF.a1, hF.a3, hF.e13⟩
  · intro t ht t' ht' htt'
    simp only [fixQA, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ht ht'
    rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact absurd rfl htt'
    · rw [Function.onFun, NashWilliams18.triEdges_three n0 n2 h02,
        NashWilliams18.triEdges_three n1 n3 h13]
      simp [disjoint_left, *, Ne.symm h12]
    · rw [Function.onFun, NashWilliams18.triEdges_three n0 n2 h02,
        NashWilliams18.triEdges_three n1 n3 h13]
      simp [disjoint_left, *, Ne.symm h01, Ne.symm h03, Ne.symm h23]
    · exact absurd rfl htt'
  · rw [hE]
    intro e he
    simp only [mem_insert, mem_singleton] at he
    simp only [fixW, mem_insert, mem_singleton]
    tauto
  · intro t ht hint
    simp only [fixQA, mem_insert, mem_singleton] at ht
    obtain ⟨i, hi⟩ := hint
    rcases ht with rfl | rfl
    · have a := hi w0 (by simp)
      have b := hi w2 (by simp)
      rw [hq0] at a; rw [hq2] at b; rw [← a] at b; exact absurd b (by decide)
    · have a := hi w1 (by simp)
      have b := hi w3 (by simp)
      rw [hq1] at a; rw [hq3] at b; rw [← a] at b; exact absurd b (by decide)
  · intro x y hxy hA
    rw [hE]
    simp only [fixW, mem_insert, mem_singleton] at hxy ⊢
    rcases hxy with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl h))
    · exfalso
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA with hA | hA <;>
        first | exact hF.n0 hA | exact hF.n3 hA
    · exfalso
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA with hA | hA <;>
        first | exact hF.n1 hA | exact hF.n2 hA
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · intro x y hxy hnot
    rw [hE] at hnot
    simp only [fixW, mem_insert, mem_singleton] at hxy hnot
    rcases hxy with h | h | h | h | h | h | h | h
    · exact absurd (Or.inl h) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hnot
    · exact absurd (Or.inr (Or.inl h)) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hnot
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hF.n0, hF.n3, by rw [hF.c0, hF.c3]; decide⟩
      · exact ⟨hF.n3, hF.n0, by rw [hF.c0, hF.c3]; decide⟩
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hF.n1, hF.n2, by rw [hF.c1, hF.c2]; decide⟩
      · exact ⟨hF.n2, hF.n1, by rw [hF.c1, hF.c2]; decide⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hnot

omit [Fintype V] [DecidableRel G.Adj] in
lemma fixQB_good (hF : Fixer126 G p A v w0 w1 w2 w3) (q : V → Fin 2)
    (hq0 : q w0 = 0) (hq1 : q w1 = 0) (hq2 : q w2 = 1) (hq3 : q w3 = 1) :
    FixQ G p A q (fixW v w0 w1 w2 w3) (fixQB v w0 w1 w2 w3) := by
  obtain ⟨n0, n1, n2, n3, h01, h02, h03, h12, h13, h23⟩ := hF.ne
  have hE : (fixQB v w0 w1 w2 w3).biUnion triEdges =
      {s(v, w0), s(v, w3), s(w0, w3), s(v, w1), s(v, w2), s(w1, w2)} := by
    rw [fixQB, biUnion_insert, singleton_biUnion, NashWilliams18.triEdges_three n0 n3 h03,
      NashWilliams18.triEdges_three n1 n2 h12]
    ext e; simp only [mem_union, mem_insert, mem_singleton]; tauto
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [fixQB, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hF.a0, hF.a3, hF.e03⟩
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hF.a1, hF.a2, hF.e12⟩
  · intro t ht t' ht' htt'
    simp only [fixQB, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ht ht'
    rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact absurd rfl htt'
    · rw [Function.onFun, NashWilliams18.triEdges_three n0 n3 h03,
        NashWilliams18.triEdges_three n1 n2 h12]
      simp [disjoint_left, *, Ne.symm h13, Ne.symm h23]
    · rw [Function.onFun, NashWilliams18.triEdges_three n0 n3 h03,
        NashWilliams18.triEdges_three n1 n2 h12]
      simp [disjoint_left, *, Ne.symm h01, Ne.symm h02]
    · exact absurd rfl htt'
  · rw [hE]
    intro e he
    simp only [mem_insert, mem_singleton] at he
    simp only [fixW, mem_insert, mem_singleton]
    tauto
  · intro t ht hint
    simp only [fixQB, mem_insert, mem_singleton] at ht
    obtain ⟨i, hi⟩ := hint
    rcases ht with rfl | rfl
    · have a := hi w0 (by simp)
      have b := hi w3 (by simp)
      rw [hq0] at a; rw [hq3] at b; rw [← a] at b; exact absurd b (by decide)
    · have a := hi w1 (by simp)
      have b := hi w2 (by simp)
      rw [hq1] at a; rw [hq2] at b; rw [← a] at b; exact absurd b (by decide)
  · intro x y hxy hA
    rw [hE]
    simp only [fixW, mem_insert, mem_singleton] at hxy ⊢
    rcases hxy with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inl h)
    · exfalso
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA with hA | hA <;>
        first | exact hF.n0 hA | exact hF.n2 hA
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exfalso
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA with hA | hA <;>
        first | exact hF.n1 hA | exact hF.n3 hA
  · intro x y hxy hnot
    rw [hE] at hnot
    simp only [fixW, mem_insert, mem_singleton] at hxy hnot
    rcases hxy with h | h | h | h | h | h | h | h
    · exact absurd (Or.inl h) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hnot
    · exact absurd (Or.inr (Or.inl h)) hnot
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hF.n0, hF.n2, by rw [hF.c0, hF.c2]; decide⟩
      · exact ⟨hF.n2, hF.n0, by rw [hF.c0, hF.c2]; decide⟩
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hnot
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hF.n1, hF.n3, by rw [hF.c1, hF.c3]; decide⟩
      · exact ⟨hF.n3, hF.n1, by rw [hF.c1, hF.c3]; decide⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Swapping `fixQA` for `fixQB` keeps `E₀₀` and changes `E₀₂` by `+1` and `E₀₃` by `-1`. -/
lemma parity_swap_F2 (hF : Fixer126 G p A v w0 w1 w2 w3) (E : Finset (Sym2 V))
    (hE : fixW v w0 w1 w2 w3 ⊆ E) :
    edgeVec p (E \ (fixQB v w0 w1 w2 w3).biUnion triEdges) 0 0 =
        edgeVec p (E \ (fixQA v w0 w1 w2 w3).biUnion triEdges) 0 0 ∧
      edgeVec p (E \ (fixQB v w0 w1 w2 w3).biUnion triEdges) 0 2 =
        edgeVec p (E \ (fixQA v w0 w1 w2 w3).biUnion triEdges) 0 2 + 1 ∧
      edgeVec p (E \ (fixQB v w0 w1 w2 w3).biUnion triEdges) 0 3 + 1 =
        edgeVec p (E \ (fixQA v w0 w1 w2 w3).biUnion triEdges) 0 3 := by
  obtain ⟨n0, n1, n2, n3, h01, h02, h03, h12, h13, h23⟩ := hF.ne
  set S : Finset (Sym2 V) := {s(v, w0), s(v, w1), s(v, w2), s(v, w3)} with hS
  set MA : Finset (Sym2 V) := {s(w0, w2), s(w1, w3)} with hMA
  set MB : Finset (Sym2 V) := {s(w0, w3), s(w1, w2)} with hMB
  have hQA : (fixQA v w0 w1 w2 w3).biUnion triEdges = S ∪ MA := by
    rw [fixQA, biUnion_insert, singleton_biUnion, NashWilliams18.triEdges_three n0 n2 h02,
      NashWilliams18.triEdges_three n1 n3 h13]
    ext e; simp only [hS, hMA, mem_union, mem_insert, mem_singleton]; tauto
  have hQB : (fixQB v w0 w1 w2 w3).biUnion triEdges = S ∪ MB := by
    rw [fixQB, biUnion_insert, singleton_biUnion, NashWilliams18.triEdges_three n0 n3 h03,
      NashWilliams18.triEdges_three n1 n2 h12]
    ext e; simp only [hS, hMB, mem_union, mem_insert, mem_singleton]; tauto
  have hdA : Disjoint S MA := by
    rw [disjoint_left]
    intro e he1 he2
    simp only [hS, hMA, mem_insert, mem_singleton] at he1 he2
    rcases he1 with rfl | rfl | rfl | rfl <;> rcases he2 with h | h <;> rw [Sym2.eq_iff] at h <;>
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  have hdB : Disjoint S MB := by
    rw [disjoint_left]
    intro e he1 he2
    simp only [hS, hMB, mem_insert, mem_singleton] at he1 he2
    rcases he1 with rfl | rfl | rfl | rfl <;> rcases he2 with h | h <;> rw [Sym2.eq_iff] at h <;>
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  have hMAE : MA ⊆ E := fun e he => hE (by
    simp only [hMA, mem_insert, mem_singleton] at he
    simp only [fixW, mem_insert, mem_singleton]; tauto)
  have hMBE : MB ⊆ E := fun e he => hE (by
    simp only [hMB, mem_insert, mem_singleton] at he
    simp only [fixW, mem_insert, mem_singleton]; tauto)
  have key : ∀ M : Finset (Sym2 V), Disjoint S M → M ⊆ E →
      edgeVec p (E \ S) = edgeVec p (E \ (S ∪ M)) + edgeVec p M := by
    intro M hd hM
    rw [← edgeVec_union p (disjoint_left.mpr fun e he heM => (mem_sdiff.mp he).2
      (mem_union_right _ heM))]
    congr 1
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨heE, heS⟩
      by_cases heM : e ∈ M
      · exact Or.inr heM
      · exact Or.inl ⟨heE, by tauto⟩
    · rintro (⟨heE, h⟩ | heM)
      · exact ⟨heE, fun h' => h (Or.inl h')⟩
      · exact ⟨hM heM, fun h' => disjoint_left.mp hd h' heM⟩
  have kA := key MA hdA hMAE
  have kB := key MB hdB hMBE
  rw [hQA, hQB]
  have hne1 : s(w0, w2) ≠ s(w1, w3) := by simp [h01, h03]
  have hne2 : s(w0, w3) ≠ s(w1, w2) := by simp [h01, h02]
  have vA : ∀ i j, edgeVec p MA i j = pairVec p s(w0, w2) i j + pairVec p s(w1, w3) i j := by
    intro i j; simp only [hMA, edgeVec, sum_pair hne1, Pi.add_apply]
  have vB : ∀ i j, edgeVec p MB i j = pairVec p s(w0, w3) i j + pairVec p s(w1, w2) i j := by
    intro i j; simp only [hMB, edgeVec, sum_pair hne2, Pi.add_apply]
  have e1 := fun i j => (congrFun (congrFun kA i) j).symm.trans (congrFun (congrFun kB i) j)
  simp only [Pi.add_apply, vA, vB, pairVec, Sym2.lift_mk, hF.c0, hF.c1, hF.c2, hF.c3] at e1
  refine ⟨?_, ?_, ?_⟩
  · have := e1 0 0; simp at this; linarith
  · have := e1 0 2; simp at this; linarith
  · have := e1 0 3; simp at this; linarith

end

end NashWilliams18.C127

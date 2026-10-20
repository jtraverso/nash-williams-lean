/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.PuncturedLoadF1
import PartitionedTriangleAbsorption.TypedNearConsumer

/-!
# The ported typed near-load nibble, relative to a vertex SET `W`

`TypedNearConsumer.typed_nibble_packing_near` measures weights, degrees and the residual against
`n = |V|`, the whole vertex type.  A vortex level lives on a finite set `W ⊆ V` of a fixed host.
`typed_nibble_on_set` (proved) transports the nibble to the subtype `{v // v ∈ W}`: for a graph `J`
whose edges lie inside `W`, weights `≤ b/|W|`, degree gap `(1 - ξ)|W|` and loads within the
nibble tolerance `δ`, it produces an actual `F`-decomposable `Q ⊆ E(J)` whose residual has maximum
degree `≤ η |W|`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption

/-- **Typed near-load nibble on a vertex set** (proved, by transport of the ported nibble). -/
theorem typed_nibble_on_set (b η ξ : ℝ) (hb : 0 < b) (hη : 0 < η) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Finset V),
      N ≤ W.card → ∀ (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (J : SimpleGraph V)
        [DecidableRel J.Adj] (φ : Finset V → ℝ),
      (∀ x y, J.Adj x y → x ∈ W) →
      (∀ s, 0 ≤ φ s ∧ φ s ≤ b / W.card) →
      (∀ v, ((J.edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤ (1 - ξ) * W.card) →
      (∀ e ∈ J.edgeFinset, |(∑ s ∈ copies p F J with e ∈ triEdges s, φ s) - 1| ≤ δ) →
      ∃ D : Finset (Finset V), ∃ Q : Finset (Sym2 V), Q ⊆ J.edgeFinset ∧ IsDecomp p F Q D ∧
        ∀ v, (((J.edgeFinset \ Q).filter fun e => v ∈ e).card : ℝ) ≤ η * W.card := by
  obtain ⟨δ, hδ, -, N, hN⟩ := TypedNearConsumer.typed_nibble_packing_near b η ξ hb hη hξ
  refine ⟨δ, hδ, N, ?_⟩
  intro V _ _ W hNW p F J _ φ hJW hφ hdeg hload
  classical
  let V' := {v // v ∈ W}
  let e : V' ↪ V := Function.Embedding.subtype _
  let J' : SimpleGraph V' := J.comap e
  let p' : V' → Fin 4 := fun x => p x.1
  let φ' : Finset V' → ℝ := fun s => φ (s.map e)
  have hcard : Fintype.card V' = W.card := Fintype.card_coe W
  have hJW' : ∀ x y, J.Adj x y → y ∈ W := fun x y h => hJW y x h.symm
  -- degrees
  have hdeg' : DegBounded J'.edgeFinset ((1 - ξ) * Fintype.card V') := by
    intro x
    rw [hcard, ← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
    have h1 := hdeg x.1
    rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree] at h1
    have hle : J'.degree x ≤ J.degree x.1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      rw [← card_map e]
      apply card_le_card
      intro z hz
      obtain ⟨z', hz', rfl⟩ := mem_map.mp hz
      rw [SimpleGraph.mem_neighborFinset] at hz' ⊢
      exact hz'
    exact le_trans (by exact_mod_cast hle) h1
  -- loads
  have hload' : ∀ e' ∈ J'.edgeFinset,
      |(∑ s ∈ copies p' F J' with e' ∈ triEdges s, φ' s) - 1| ≤ δ := by
    intro e' he'
    induction e' using Sym2.ind with
    | _ x y =>
    have hxy' : J'.Adj x y := SimpleGraph.mem_edgeFinset.mp he'
    have hxy : J.Adj x.1 y.1 := hxy'
    have h := hload s(x.1, y.1) (SimpleGraph.mem_edgeFinset.mpr hxy)
    rw [sum_copies_through p' F J' hxy' φ']
    rw [sum_copies_through p F J hxy φ] at h
    have hset : (univ.filter fun w => J.Adj x.1 w ∧ J.Adj w y.1 ∧
        ({p x.1, p y.1, p w} : Multiset (Fin 4)) ∈ F) =
        (univ.filter fun w : V' => J'.Adj x w ∧ J'.Adj w y ∧
          ({p' x, p' y, p' w} : Multiset (Fin 4)) ∈ F).map e := by
      ext z
      simp only [mem_filter, mem_univ, true_and, mem_map]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨z, hJW' _ _ h1⟩, ⟨h1, h2, h3⟩, rfl⟩
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        exact ⟨h1, h2, h3⟩
    have key : ∑ w ∈ univ.filter (fun w : V' => J'.Adj x w ∧ J'.Adj w y ∧
          ({p' x, p' y, p' w} : Multiset (Fin 4)) ∈ F), φ' {x, y, w} =
        ∑ z ∈ univ.filter (fun w => J.Adj x.1 w ∧ J.Adj w y.1 ∧
          ({p x.1, p y.1, p w} : Multiset (Fin 4)) ∈ F), φ {x.1, y.1, z} := by
      rw [hset, sum_map]
      refine sum_congr rfl fun w _ => ?_
      simp only [φ', map_insert, map_singleton]
      rfl
    rw [key]; exact h
  obtain ⟨D', Q', -, hQD', hQ'J, hD', -, hres⟩ := hN V' (hcard ▸ hNW) 4 p' F J' φ'
    (fun s _ => ⟨(hφ _).1, by rw [hcard]; exact (hφ _).2⟩) hdeg' hload'
  refine ⟨D'.map (NashWilliams18.finsetMapEmb e), Q'.map e.sym2Map, ?_,
    NashWilliams18.isDecomp_map_typed e (fun _ => rfl) hD', ?_⟩
  · intro f hf
    obtain ⟨f', hf', rfl⟩ := mem_map.mp hf
    have := hQ'J hf'
    induction f' using Sym2.ind with
    | _ x y =>
    have hxy : J'.Adj x y := SimpleGraph.mem_edgeFinset.mp this
    have hxyJ : J.Adj (e x) (e y) := hxy
    simpa [Function.Embedding.sym2Map_apply] using hxyJ
  · intro v
    by_cases hv : v ∈ W
    · have hsub : (J.edgeFinset \ Q'.map e.sym2Map).filter (fun f => v ∈ f) ⊆
          ((J'.edgeFinset \ Q').filter (fun f => (⟨v, hv⟩ : V') ∈ f)).map e.sym2Map := by
        intro f hf
        obtain ⟨hf1, hvf⟩ := mem_filter.mp hf
        obtain ⟨hfJ, hfQ⟩ := mem_sdiff.mp hf1
        induction f using Sym2.ind with
        | _ a c =>
        have hac : J.Adj a c := SimpleGraph.mem_edgeFinset.mp hfJ
        have ha := hJW a c hac
        have hc := hJW' a c hac
        refine mem_map.mpr ⟨s(⟨a, ha⟩, ⟨c, hc⟩), ?_, by simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk]; rfl⟩
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hac, fun hQ => ?_⟩, ?_⟩
        · exact hfQ (mem_map.mpr ⟨_, hQ, by simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk]; rfl⟩)
        · rcases Sym2.mem_iff.mp hvf with rfl | rfl
          · exact Sym2.mem_mk_left _ _
          · exact Sym2.mem_mk_right _ _
      have h1 := card_le_card hsub
      rw [card_map] at h1
      have h2 := hres ⟨v, hv⟩
      rw [hcard] at h2
      exact le_trans (by exact_mod_cast h1) h2
    · have hempty : (J.edgeFinset \ Q'.map e.sym2Map).filter (fun f => v ∈ f) = ∅ := by
        rw [filter_eq_empty_iff]
        intro f hf hvf
        induction f using Sym2.ind with
        | _ a c =>
        have hac : J.Adj a c := SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp hf).1
        rcases Sym2.mem_iff.mp hvf with rfl | rfl
        · exact hv (hJW _ _ hac)
        · exact hv (hJW' _ _ hac)
      rw [hempty, card_empty, Nat.cast_zero]
      positivity

end NashWilliams18.SpreadF1

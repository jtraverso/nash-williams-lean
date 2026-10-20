/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.QuantitativeTransportStage264
public import PartitionedTriangleAbsorption.BlowupB.CompleteBlowup
public import PartitionedTriangleAbsorption.OnePartDivisibility

/-! # Signed physical transport in the nonextremal branch

Each step between opposite edges of a physical K4 costs four signed triangles.
Composing the previously constructed paths gives cost at most 116. This is an
integer certificate, not a nonnegative packing or a simultaneous absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedTransportStage265

open Finset BlowupB OnePart OppositeEdgeTransportStage259

variable {V : Type*} [DecidableEq V]

theorem triangle_cost (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    PhysCostZ part1 triFam G (indZ (triEdges {u, v, w})) 1 := by
  apply physCostZ_of_isCopy
  refine ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩, ?_⟩
  rw [map_three part1 huv.ne huw.ne hvw.ne]
  simp [part1, triFam]

theorem k4_transport_cost (G : SimpleGraph V) {u v a b : V}
    (huv : G.Adj u v) (hab : G.Adj a b)
    (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) :
    PhysCostZ part1 triFam G ((2 : ℤ) • (ind1 s(u, v) - ind1 s(a, b))) 4 := by
  have h := ((triangle_cost G huv hua hva).add (triangle_cost G huv hub hvb)).sub
    ((triangle_cost G hua hub hab).add (triangle_cost G hva hvb hab))
  apply h.congr
  rw [indZ_triEdges_three huv.ne hua.ne hva.ne,
    indZ_triEdges_three huv.ne hub.ne hvb.ne,
    indZ_triEdges_three hua.ne hub.ne hab.ne,
    indZ_triEdges_three hva.ne hvb.ne hab.ne]
  funext e
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem opposite_transport_cost (G : SimpleGraph V) {f g : G.edgeSet}
    (h : (oppositeEdgeGraph G).Adj f g) :
    PhysCostZ part1 triFam G ((2 : ℤ) • (ind1 f.val - ind1 g.val)) 4 := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  induction f using Sym2.ind with
  | _ u v =>
    induction g using Sym2.ind with
    | _ a b =>
      exact k4_transport_cost G hf hg
        (h.2 u (by simp) a (by simp)) (h.2 u (by simp) b (by simp))
        (h.2 v (by simp) a (by simp)) (h.2 v (by simp) b (by simp))

theorem walk_transport_cost (G : SimpleGraph V) {f g : G.edgeSet}
    (p : (oppositeEdgeGraph G).Walk f g) :
    PhysCostZ part1 triFam G ((2 : ℤ) • (ind1 f.val - ind1 g.val))
      (4 * (p.length : ℤ)) := by
  induction p with
  | nil => simpa using PhysCostZ.zero part1 triFam G
  | @cons f h g hfh p ih =>
    have hc := (opposite_transport_cost G hfh).add ih
    have hv : (2 : ℤ) • (ind1 f.val - ind1 h.val) +
        (2 : ℤ) • (ind1 h.val - ind1 g.val) =
        (2 : ℤ) • (ind1 f.val - ind1 g.val) := by
      funext e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simpa [SimpleGraph.Walk.length_cons, Nat.cast_add, mul_add, add_comm] using hc.congr hv

variable [Fintype V]

open scoped Classical in
/-- Every doubled edge difference has a physical signed certificate of cost
at most 116, obtained from the graph hypotheses rather than assumed. -/
theorem nonextremal_transport_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ w, (Fintype.card V : ℝ) ≤ G.degree w + (1 / 4 + e) * Fintype.card V)
    (hnot : ¬ ((1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    {u v x y : V} (huv : G.Adj u v) (hxy : G.Adj x y) :
    PhysCostZ part1 triFam G ((2 : ℤ) • (ind1 s(u, v) - ind1 s(x, y))) 116 := by
  obtain ⟨p, _, hp⟩ := QuantitativeTransportStage264.nonextremal_walk_lt_thirty
    G a e ha ha1 he hn hsmall hdeg hnot huv hxy
  exact (walk_transport_cost G p).mono (by omega)

end PartitionedTriangleAbsorption.SignedTransportStage265

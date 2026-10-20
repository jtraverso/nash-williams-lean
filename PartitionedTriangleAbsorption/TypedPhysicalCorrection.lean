/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedCorrectionFamily
public import PartitionedTriangleAbsorption.TypedLinkObstructions
public import PartitionedTriangleAbsorption.ReserveCoverDown

/-! # Physical repair of prescribed link defects

The correction is a sparse typed triangle packing, disjoint from the input.
At a defective vertex its designated triangle is separated from the others
before adding natural link certificates. Thus processing order is irrelevant.
This is a correction for a supplied input, not a universal refiner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedPhysicalCorrection

open Finset TypedLinkCoefficients TypedCorrectionFamily

variable {V : Type*} [DecidableEq V] {t : ℕ}

theorem realizable_of_decomp {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 V)} (h : HasDecomp p F E) (v : V) :
    Realizable F (p v) (degVec p E v) := by
  classical
  obtain ⟨D, hD⟩ := h
  exact ⟨fun τ => (D.filter (fun s => v ∈ s ∧ triType p s = τ)).card, hD.degVec_eq v⟩

theorem edges_decomp (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    {u a b : V} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (ht : ({p u, p a, p b} : Multiset (Fin t)) ∈ F) :
    HasDecomp p F (edges u a b) := by
  rw [show edges u a b = triEdges {u, a, b} from (triEdges_three hua hub hab).symm]
  apply ReserveCoverDown.hasDecomp_triEdges
  refine ⟨by simp [hua, hub, hab], ?_⟩
  simpa only [map_three p hua hub hab] using ht

/-- Repair any prescribed collection of defects admitting a permitted pair. -/
theorem exists_correction [Fintype V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (α d : ℝ) (hanti : AntiEdgeful p F G α)
    (P : Finset (Sym2 V)) (hP : DegBounded P d)
    (anchor : V → V) (central branch : V → Fin t) (s : Finset V)
    (hanchor : ∀ u ∈ s, u ≠ anchor u ∧ p (anchor u) = branch u)
    (htype : ∀ u ∈ s, ({p u, central u, branch u} : Multiset (Fin t)) ∈ F)
    (hgood : ∀ u, u ∉ s → Realizable F (p u) (degVec p P u))
    (hrepair : ∀ u ∈ s,
      Realizable F (p u) (degVec p P u + (basis (central u) + basis (branch u))))
    (q : ℕ) (hq : 0 < q)
    (hbudget : 2 * (s.card : ℝ) / q + 2 * (d + 2 * (q + 1)) <
      α * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint P R ∧ DegBounded R (2 * (q + 1)) ∧
      HasDecomp p F R ∧ ∀ u, Realizable F (p u) (degVec p (P ∪ R) u) := by
  classical
  obtain ⟨a, b, hab, hdis, haux⟩ :=
    exists_family p F G α d hanti P hP anchor central branch s hanchor htype q hq hbudget
  have hdec : ∀ u ∈ s, HasDecomp p F (edges u (a u) (b u)) := by
    intro u hu
    obtain ⟨hua, hub, hab', hpa, hpb, _⟩ := hab u hu
    apply edges_decomp p F hua.ne hub.ne hab'.ne
    rw [hpa, hpb]
    exact htype u hu
  have havoid : Disjoint P (unionEdges s a b) := by
    rw [unionEdges, disjoint_biUnion_right]
    exact fun u hu => (hab u hu).2.2.2.2.2.symm
  have hdecomp : HasDecomp p F (unionEdges s a b) :=
    RefinerAssembly.hasDecomp_biUnion s _ hdec hdis
  refine ⟨unionEdges s a b, ?_, havoid, ?_, hdecomp, ?_⟩
  · intro e he
    obtain ⟨u, hu, he⟩ := mem_biUnion.mp he
    obtain ⟨hua, hub, hab', _⟩ := hab u hu
    rcases mem_insert.mp he with rfl | he
    · exact G.mem_edgeFinset.mpr hua
    · rcases mem_insert.mp he with rfl | he
      · exact G.mem_edgeFinset.mpr hub
      · rw [mem_singleton.mp he]
        exact G.mem_edgeFinset.mpr hab'
  · have hzero : DegBounded (∅ : Finset (Sym2 V)) (0 : ℝ) := by
      intro x
      simp
    simpa using union_degree_bound s a b ∅ 0 q hzero haux
  · intro u
    rw [degVec_union p havoid]
    by_cases hu : u ∈ s
    · let rest := unionEdges (s.erase u) a b
      have hrest : HasDecomp p F rest := RefinerAssembly.hasDecomp_biUnion
        (s.erase u) _ (fun i hi => hdec i (mem_erase.mp hi).2)
        (hdis.subset (by intro i hi; exact (mem_erase.mp hi).2))
      have heq : unionEdges s a b = edges u (a u) (b u) ∪ rest := by
        conv_lhs => rw [← insert_erase hu]
        exact biUnion_insert
      have hdr : Disjoint (edges u (a u) (b u)) rest := by
        rw [show rest = (s.erase u).biUnion (fun i => edges i (a i) (b i)) from rfl,
          disjoint_biUnion_right]
        intro i hi
        exact hdis hu (mem_erase.mp hi).2 (mem_erase.mp hi).1.symm
      obtain ⟨hua, hub, hab', hpa, hpb, _⟩ := hab u hu
      have hroot : degVec p (edges u (a u) (b u)) u =
          basis (central u) + basis (branch u) := by
        rw [show edges u (a u) (b u) = triEdges {u, a u, b u} from
          (triEdges_three hua.ne hub.ne hab'.ne).symm,
          degVec_three_self p hua.ne hub.ne hab'.ne, hpa, hpb, triple_link]
      rw [heq, degVec_union p hdr, hroot, ← add_assoc]
      exact (hrepair u hu).add (realizable_of_decomp hrest u)
    · exact (hgood u hu).add (realizable_of_decomp hdecomp u)

/-- The uniform quota and sparse-input hypotheses imply the strict greedy budget. -/
theorem correction_budget (α n : ℝ) (q : ℕ) (s : ℕ)
    (hn : 0 ≤ n) (hs : (s : ℝ) ≤ n) (hq : 0 < q)
    (hscale : 8 ≤ α * q) (hsize : 16 * ((q : ℝ) + 1) ≤ α * n) :
    2 * (s : ℝ) / q + 2 * (α * n / 8 + 2 * (q + 1)) < α * n := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmass : 2 * (s : ℝ) / q ≤ α * n / 4 := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hscale)]
  nlinarith

end PartitionedTriangleAbsorption.TypedPhysicalCorrection

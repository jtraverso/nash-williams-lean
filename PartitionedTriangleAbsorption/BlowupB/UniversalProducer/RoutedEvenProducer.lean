/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.VirtualRefiner
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.WeightedRouting

/-!
# The shared even refiner by weighted physical path routing (no common-link classes)

`evenRefinerProducer_routed`: for every family of card-three types on `Fin t`, `t ≥ 1`,

    EvenRefinerProducer F (Fin t × HeapIdx) 2 (42 * (t + 1)) (7 * (4096 * t)) (routedC t)

with `routedC t = min (1 / 2²⁴) (1 / (1024 · (4096 t) · (t + 1)))`, i.e. `K = 4096 t`,
`Lmax = t + 1`, `Sref = 2`, `m = 42 Lmax`, `K0 = 7 K`.  All constants depend only on `t`.

Construction (for given host, scales and reserve `X`):
1. `virtual_even_refiner`: the heap refiner run on the VIRTUAL complete graph of each component
   class of the allowed-label graph gives one virtual remainder `R` and one library.
2. Weights `w(e) = #{j ∈ lib : e ∈ P j}` counted in the WHOLE library; `w ≥ 1` on `R` from the
   `L = ∅` selection.
3. `weighted_routing` replaces each virtual edge once by a short simple physical path (label
   walks from `exists_labelWalk`), edge-disjoint and avoiding `X`.
4. `subdividePredRefiner` transports all selections; `SubdivisionLoad` bounds the
   whole-library incidence by original load plus weighted auxiliary load.

Composed with the proved charge/torsion reduction this gives `RefinerProducer` and the
universal-absorber target for every card-three family with `ThreeStepLinks`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedTransformer UniversalRefiner

variable {t : ℕ}

/-- The host-independent constant `c = min (2⁻²⁴) (1 / (1024 K Lmax))`, `K = 4096 t`,
`Lmax = t + 1`. -/
noncomputable def routedC (t : ℕ) : ℝ :=
  min (1 / 2 ^ 24) (1 / (1024 * (4096 * (t : ℝ)) * ((t : ℝ) + 1)))

theorem routedC_pos {t : ℕ} (ht : 1 ≤ t) : 0 < routedC t := by
  unfold routedC
  refine lt_min (by norm_num) ?_
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have : (0 : ℝ) < 1024 * (4096 * (t : ℝ)) * ((t : ℝ) + 1) := by positivity
  positivity

/-- **The shared even refiner, without common-link classes.** -/
theorem evenRefinerProducer_routed (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (ht : 1 ≤ t) :
    EvenRefinerProducer F (Fin t × HeapIdx) 2 (42 * (t + 1)) (7 * (4096 * t)) (routedC t) := by
  classical
  intro V _ _ p G _ ω lam rho hω hω1 hact hsup hlam hlamc hrho hrhoc hrn hcn X hXG hXdeg
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set K : ℝ := 4096 * (t : ℝ) with hKdef
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hc := routedC_pos ht
  have hc24 : routedC t ≤ 1 / 2 ^ 24 := min_le_left _ _
  have hcK : 1024 * K * ((t : ℝ) + 1) * routedC t ≤ 1 := by
    have h1 : routedC t ≤ 1 / (1024 * K * ((t : ℝ) + 1)) := min_le_right _ _
    have hpos : 0 < 1024 * K * ((t : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hpos] at h1
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · exfalso
      have : n = 0 := by rw [hndef, h]; simp
      rw [this] at hrn; simp at hrn; linarith
    · exact h
  obtain ⟨h64K, h128, hrl, hord⟩ := weighted_routing_scales K ((t : ℝ) + 1) (routedC t) lam rho
    ω n hK1 (by linarith) hc hcK hω hω1 hlam hlamc hrho.le hrhoc hcn
  -- the ordinary hypotheses for the virtual heap refiners
  have h64 : 64 * lam ≤ ω := by nlinarith
  have hscale : 2 ^ 24 * rho ≤ lam ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc24 (sq_nonneg lam)
    linarith
  have hn2 : 256 ≤ lam * n := by
    have hln : 0 ≤ lam * n := by positivity
    have := mul_le_mul_of_nonneg_right hc24 hln
    have e1 : routedC t * lam * n = routedC t * (lam * n) := by ring
    linarith
  have h4 : 4 ≤ ω * n := by nlinarith
  obtain ⟨E, hET, hEcls, hEm, hEdeg, hEcard, hEload⟩ := virtual_even_refiner F hF3 p G ω lam rho
    hact hsup hlam h64 hrho hscale hrn hn2 h4 X hXG hXdeg
  -- whole-library weights
  set w : Sym2 V → ℕ := libraryMultiplicity E.lib E.P with hwdef
  have hw1 : ∀ e ∈ E.R0, 1 ≤ w e := by
    intro e he
    obtain ⟨s, hs, -, hcov⟩ := E.refines ∅ (empty_subset _) RefinerAssembly.empty_isIntDiv
    have : e ∈ s.biUnion E.P := by rw [hcov, union_empty]; exact he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp this
    exact card_pos.mpr ⟨j, mem_filter.mpr ⟨hs hj, hej⟩⟩
  have hwv : ∀ v, ((∑ e ∈ E.R0.filter (fun e => v ∈ e), w e : ℕ) : ℝ) ≤ K * lam * n := by
    intro v
    have h1 := weighted_root_load_le E.lib E.P E.R0 v
    have h1' : ((∑ e ∈ E.R0.filter (fun e => v ∈ e), w e : ℕ) : ℝ) ≤
        ((∑ j ∈ E.lib, incidentLoad (E.P j) v : ℕ) : ℝ) := by exact_mod_cast h1
    have := hEload v
    rw [hKdef]
    linarith
  have hwtot : ((∑ e ∈ E.R0, w e : ℕ) : ℝ) ≤ 42 * K * rho * n ^ 2 := by
    have h1 := sum_libraryMultiplicity_le E.lib E.P E.R0 42 hEm
    have h1' : ((∑ e ∈ E.R0, w e : ℕ) : ℝ) ≤ (E.lib.card : ℝ) * 42 := by exact_mod_cast h1
    rw [hKdef]
    nlinarith
  -- label walks for the virtual edges
  have hwalk : ∀ e ∈ E.R0, ∃ x y, e = s(x, y) ∧ x ≠ y ∧ ∃ (m : ℕ) (lab : ℕ → Fin t), 2 ≤ m ∧
      m ≤ t + 1 ∧ lab 0 = p x ∧ lab m = p y ∧ ∀ k < m, AllowedF F (lab k) (lab (k + 1)) := by
    intro e he
    obtain ⟨r, hr⟩ := hEcls e he
    have heT := hET he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at heT
      have hx := hr x (Sym2.mem_mk_left x y)
      have hy := hr y (Sym2.mem_mk_right x y)
      rw [mem_classVerts, mem_classParts] at hx hy
      have hreach := reach_of_compMap_eq (hx.2.trans hy.2.symm)
      obtain ⟨m, lab, h1, h2, h3, h4, h5⟩ := exists_labelWalk hx.1 hreach
      exact ⟨x, y, rfl, heT, m, lab, h1, h2, h3, h4, h5⟩
  -- the single weighted physical routing
  obtain ⟨f0, aux, hf0, hdisj0, hauxload⟩ := weighted_routing p G (AllowedF F)
    (fun i j h => allowedF_symm h) K lam rho ω (t + 1) hK1 hlam hrho.le hnpos h64K
    (by push_cast; exact h128) hrl (by push_cast; exact hord) hsup X hXdeg E.R0 w hw1 hwv hwtot
    hwalk
  -- the fixed substitution: paths on `R`, identity on `X`
  set f : Sym2 V → Finset (Sym2 V) := fun e => if e ∈ E.R0 then f0 e else {e} with hfdef
  have hfR : ∀ e ∈ E.R0, f e = f0 e := fun e he => if_pos he
  have hfix : ∀ e ∈ X, f e = {e} := fun e he =>
    if_neg (fun h => disjoint_left.mp E.disjRX h he)
  have hf : ((E.R0 ∪ X : Finset (Sym2 V)) : Set (Sym2 V)).PairwiseDisjoint f := by
    intro a ha b hb hab
    simp only [coe_union, Set.mem_union, mem_coe] at ha hb
    have hRX : ∀ a ∈ E.R0, ∀ b ∈ X, Disjoint (f a) (f b) := by
      intro a ha b hb
      rw [hfR a ha, hfix b hb, disjoint_singleton_right]
      exact fun h => disjoint_left.mp (hf0 a ha).2.2.1 h hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · change Disjoint (f a) (f b)
      rw [hfR a ha, hfR b hb]
      exact hdisj0 ha hb hab
    · exact hRX a ha b hb
    · exact (hRX b hb a ha).symm
    · change Disjoint (f a) (f b)
      rw [hfix a ha, hfix b hb, disjoint_singleton]
      exact hab
  have hloop : ∀ e ∈ E.R0 ∪ X, ∀ a ∈ f e, ¬ a.IsDiag := by
    intro e he a ha
    rcases mem_union.mp he with he | he
    · rw [hfR e he] at ha
      exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp ((hf0 e he).1 ha))
    · rw [hfix e he, mem_singleton] at ha
      subst ha
      exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))
  have hpar : ∀ e ∈ E.R0 ∪ X, ∀ v, (incidentLoad (f e) v : ZMod 2) = symInd e v := by
    intro e he v
    rcases mem_union.mp he with he | he
    · rw [hfR e he]; exact (hf0 e he).2.2.2.2 v
    · rw [hfix e he, symInd]
      unfold incidentLoad
      rw [filter_singleton]
      split_ifs <;> simp
  let E' := subdividePredRefiner E f hf hfix hloop hpar
  have hinc : ∀ e ∈ E.R0, ∀ v, incidentLoad (f e) v = (if v ∈ e then 1 else 0) + aux e v := by
    intro e he v
    rw [hfR e he]; exact (hf0 e he).2.2.2.1 v
  refine ⟨E', ?_, ?_, ?_, ?_, ?_⟩
  · -- the physical remainder lies in the host
    intro a ha
    obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
    rw [hfR e he] at hae
    exact (hf0 e he).1 hae
  · -- piece size
    intro j hj
    have hfc : ∀ e ∈ E.R0 ∪ X, (f e).card ≤ t + 1 := by
      intro e he
      rcases mem_union.mp he with he | he
      · rw [hfR e he]; exact (hf0 e he).2.1
      · rw [hfix e he, card_singleton]; omega
    have h1 := subdivide_card_le f (t + 1) hfc (E.subP j hj)
    have h2 := hEm j hj
    calc (E'.P j).card = (subdivideEdges f (E.P j)).card := rfl
      _ ≤ (E.P j).card * (t + 1) := h1
      _ ≤ 42 * (t + 1) := Nat.mul_le_mul_right _ h2
  · -- degree of the physical remainder
    intro v
    change ((incidentLoad (E.R0.biUnion f) v : ℕ) : ℝ) ≤ _
    have h1 := routed_degree_le E.R0 E.R0 subset_rfl w hw1 f aux hinc v
    have h1' : ((incidentLoad (E.R0.biUnion f) v : ℕ) : ℝ) ≤
        ((∑ e ∈ E.R0.filter (fun e => v ∈ e), w e : ℕ) : ℝ) +
          ((∑ e ∈ E.R0, w e * aux e v : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := hwv v
    have h3 := hauxload v
    rw [hKdef] at h2 h3
    linarith
  · -- number of pieces (unchanged)
    change (E.lib.card : ℝ) ≤ _
    have : (0 : ℝ) ≤ 4096 * t * rho * n ^ 2 := by positivity
    linarith
  · -- whole-library incidence: original load plus weighted auxiliary load
    intro v
    change ((∑ j ∈ E.lib, incidentLoad (subdivideEdges f (E.P j)) v : ℕ) : ℝ) ≤ _
    set aux' : Sym2 V → ℕ := fun e => if e ∈ E.R0 then aux e v else 0 with haux'
    have ha : ∀ e ∈ E.R0 ∪ X, incidentLoad (f e) v ≤ (if v ∈ e then 1 else 0) + aux' e := by
      intro e he
      rcases mem_union.mp he with he | he
      · rw [hinc e he v, haux']; simp [he]
      · have hne : e ∉ E.R0 := fun h => disjoint_left.mp E.disjRX h he
        rw [hfix e he, haux']
        simp only [hne, if_false, add_zero]
        unfold incidentLoad
        rw [filter_singleton]
        split_ifs <;> simp
    have h1 := subdivide_library_load_le E.lib E.P (E.R0 ∪ X) (fun j hj => E.subP j hj) f hf v
      aux' ha
    have hsplit : ∑ e ∈ E.R0 ∪ X, libraryMultiplicity E.lib E.P e * aux' e =
        ∑ e ∈ E.R0, w e * aux e v := by
      rw [sum_union E.disjRX]
      have hX0 : ∑ e ∈ X, libraryMultiplicity E.lib E.P e * aux' e = 0 := by
        refine sum_eq_zero fun e he => ?_
        have hne : e ∉ E.R0 := fun h => disjoint_left.mp E.disjRX h he
        simp [haux', hne]
      rw [hX0, add_zero]
      refine sum_congr rfl fun e he => ?_
      simp [haux', he, hwdef]
    rw [hsplit] at h1
    have h1' : ((∑ j ∈ E.lib, incidentLoad (subdivideEdges f (E.P j)) v : ℕ) : ℝ) ≤
        ((∑ j ∈ E.lib, incidentLoad (E.P j) v : ℕ) : ℝ) +
          ((∑ e ∈ E.R0, w e * aux e v : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := hEload v
    have h3 := hauxload v
    rw [hKdef] at h3 ⊢
    linarith

/-- **`RefinerProducer` for every card-three family with `ThreeStepLinks`** (`t ≥ 1`), by the
proved charge/torsion reduction applied to the routed even refiner. -/
theorem refinerProducer_of_threeStepLinks (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F) (ht : 1 ≤ t) :
    ∃ (Sref m : ℕ) (K c : ℝ), 0 ≤ K ∧ 0 < c ∧
      RefinerProducer F (LIdx (genList F (42 * (t + 1)) (2 * (42 * (t + 1)))).length
        (Fin t × HeapIdx)) Sref m K c :=
  refinerProducer_of_evenRefinerProducer F hthree (Fin t × HeapIdx) 2 (42 * (t + 1))
    (7 * (4096 * t)) (routedC t) (routedC_pos ht) (evenRefinerProducer_routed F hF3 ht)

/-- **The universal-absorber target for every card-three family on four parts with
`ThreeStepLinks`** (no common-link hypothesis). -/
theorem producerTarget_of_threeStepLinks (F : Finset (Multiset (Fin 4)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F) :
    ∃ S : ℕ, 4 ≤ S ∧ ProducerTarget F S :=
  producerTarget_of_evenRefinerProducer F hF3 hthree (Fin 4 × HeapIdx) 2 (42 * (4 + 1))
    (7 * (4096 * 4)) (routedC 4) (routedC_pos (by norm_num)) (evenRefinerProducer_routed F hF3 (by norm_num))

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQueryReserveStage59

/-! # Marker and cross-edge lower tails for one physical edge sampling

All statements use one measure `μ` on `Sym2 V → Bool` with mutually independent
coordinate events of probability `ρ`.

* `marker_lower_tail`: for a candidate set `C` disjoint from a root set `R`, a candidate `c`
  is *marked* when every edge `s(r, c)`, `r ∈ R`, is sampled. The blocks
  `starEdges R c` are pairwise disjoint (every block edge has exactly one non-root endpoint,
  namely `c`), so the marker events are mutually independent; this geometry is proved, via
  `RootQueryReserveStage59.starEdges_disjoint`, not assumed.
* `cross_lower_tail`: for disjoint vertex sets `A`, `B`, the pairs `(a, b) ∈ A × B` give
  distinct physical coordinates `s(a, b)`, so the number of sampled cross pairs is a sum of
  `|A||B|` independent Bernoulli(`ρ`) indicators.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks RootQueryReserveStage59

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Candidates of `C` all of whose root edges `s(r, c)`, `r ∈ R`, are sampled. -/
def marked (C R : Finset V) (ω : Sym2 V → Bool) : Finset V :=
  C.filter (fun c => ∀ r ∈ R, ω s(r, c) = true)

/-- Sampled cross pairs between `A` and `B`. -/
def crossSampled (A B : Finset V) (ω : Sym2 V → Bool) : Finset (V × V) :=
  (A ×ˢ B).filter (fun q => ω s(q.1, q.2) = true)

omit [Fintype V] in
theorem mem_blockEvent_star (R : Finset V) (c : V) (ω : Sym2 V → Bool) :
    ω ∈ blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true}) (starEdges R c) ↔
      ∀ r ∈ R, ω s(r, c) = true := by
  simp only [blockEvent, starEdges, Set.mem_iInter, Set.mem_ofPred_eq, mem_image]
  constructor
  · intro h r hr
    exact h _ ⟨r, hr, rfl⟩
  · rintro h e ⟨r, hr, rfl⟩
    exact h r hr

theorem marked_card_eq_sum (C R : Finset V) (ω : Sym2 V → Bool) :
    ((marked C R ω).card : ℝ) =
      ∑ c : C, (blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
        (starEdges R c.val)).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp only [Set.indicator_apply, mem_blockEvent_star]
  rw [Finset.sum_coe_sort C (fun c : V => if ∀ r ∈ R, ω s(r, c) = true then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  rfl

/-- **Marker lower tail.** -/
theorem marker_lower_tail (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ) (ρ : ℝ) (hρ : 0 < ρ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ)
    (C R : Finset V) (hCR : Disjoint C R) (hC : C.Nonempty) :
    μ.real {ω | ((marked C R ω).card : ℝ) ≤ ρ ^ R.card * C.card / 2} ≤
      Real.exp (-(ρ ^ R.card) ^ 2 * C.card / 2) := by
  classical
  have : Nonempty C := hC.to_subtype
  let A := fun c : C => blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
    (starEdges R c.val)
  have hdis : Pairwise (fun a b : C => Disjoint (starEdges R a.val) (starEdges R b.val)) := by
    intro a b hab
    exact starEdges_disjoint R a.val b.val (disjoint_left.mp hCR a.property)
      (fun h => hab (Subtype.ext h))
  have hblocks : iIndepSet A μ := independent_blocks _ μ
    (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) hind _ hdis
  have hreal : ∀ c : C, μ.real (A c) = ρ ^ R.card := by
    intro c
    rw [measureReal_def, block_probability _ μ hind _ hmarg, starEdges_card,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le]
  have hb := FiniteBernoulliTail.lower_half_mean μ A
    (fun c => blockEvent_measurable _
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) _) hblocks
    (ρ ^ R.card) (pow_nonneg hρ.le _) hreal
  have hcard : (Fintype.card C : ℝ) = C.card := by simp
  rw [hcard] at hb
  refine le_trans (measureReal_mono ?_) hb
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [marked_card_eq_sum] at hω
  exact hω

omit [Fintype V] [DecidableEq V] in
theorem crossSampled_card_eq_sum (A B : Finset V) (ω : Sym2 V → Bool) :
    ((crossSampled A B ω).card : ℝ) =
      ∑ q : (A ×ˢ B : Finset (V × V)),
        ({ω : Sym2 V → Bool | ω s(q.val.1, q.val.2) = true}).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_coe_sort (A ×ˢ B)
    (fun q : V × V => if ω s(q.1, q.2) = true then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  rfl

omit [Fintype V] [DecidableEq V] in
theorem cross_injective (A B : Finset V) (hAB : Disjoint A B) :
    Function.Injective (fun q : (A ×ˢ B : Finset (V × V)) => s(q.val.1, q.val.2)) := by
  rintro ⟨⟨a, b⟩, hq⟩ ⟨⟨a', b'⟩, hq'⟩ h
  simp only [mem_product] at hq hq'
  simp only at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; rfl
  · exact absurd (h1 ▸ hq'.2) (disjoint_left.mp hAB hq.1)

omit [Fintype V] [DecidableEq V] in
/-- **Cross-edge lower tail** between two disjoint vertex sets. -/
theorem cross_lower_tail (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ) (ρ : ℝ) (hρ : 0 < ρ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal ρ)
    (A B : Finset V) (hAB : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    μ.real {ω | ((crossSampled A B ω).card : ℝ) ≤ ρ * (A.card * B.card) / 2} ≤
      Real.exp (-ρ ^ 2 * (A.card * B.card) / 2) := by
  classical
  have : Nonempty (A ×ˢ B : Finset (V × V)) := (hA.product hB).to_subtype
  let E := fun q : (A ×ˢ B : Finset (V × V)) => {ω : Sym2 V → Bool | ω s(q.val.1, q.val.2) = true}
  have hE : iIndepSet E μ := hind.precomp (cross_injective A B hAB)
  have hreal : ∀ q, μ.real (E q) = ρ := by
    intro q
    simp [E, measureReal_def, hmarg, ENNReal.toReal_ofReal hρ.le]
  have hb := FiniteBernoulliTail.lower_half_mean μ E
    (fun q => show MeasurableSet {ω : Sym2 V → Bool | ω s(q.val.1, q.val.2) = true} from
      (measurable_pi_apply s(q.val.1, q.val.2) : Measurable (fun ω : Sym2 V → Bool =>
        ω s(q.val.1, q.val.2))) (measurableSet_singleton true)) hE ρ hρ.le hreal
  have hcard : (Fintype.card (A ×ˢ B : Finset (V × V)) : ℝ) = A.card * B.card := by
    simp
  rw [hcard] at hb
  refine le_trans (measureReal_mono ?_) hb
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [crossSampled_card_eq_sum] at hω
  exact hω

end PartitionedTriangleAbsorption.ClassReserveStage65

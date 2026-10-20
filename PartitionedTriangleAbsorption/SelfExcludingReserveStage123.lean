/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveQueryGeometryStage123
public import PartitionedTriangleAbsorption.SignedTrialsStage123

/-! # Simultaneous thinning with connector self-exclusion

The input packing is explicit. This theorem constructs the thinning before
any residual is chosen, for all supplied queries at once. It does not assert
existence of the input packing in an arbitrary host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SelfExcludingReserveStage123

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks
open DisjointQueriesStage123 SignedTrialsStage123

variable {I : Type*} [DecidableEq I]

def good (s : Finset I) (B : I → Finset I) (ω : I → Bool) : Finset I :=
  s.filter fun i => ω i = true ∧ ∀ j ∈ B i, j ≠ i → ω j = false

theorem mem_good (s : Finset I) (B : I → Finset I) (ω : I → Bool) (i : I) :
    i ∈ good s B ω ↔ i ∈ s ∧ ω i = true ∧ ∀ j ∈ B i, j ≠ i → ω j = false := by
  simp only [good, mem_filter]

theorem good_mono {s t : Finset I} (h : s ⊆ t) (B : I → Finset I) (ω : I → Bool) :
    good s B ω ⊆ good t B ω := by
  intro i hi
  rw [mem_good] at hi ⊢
  exact ⟨h hi.1, hi.2⟩

theorem good_tail (s : Finset I) (B : I → Finset I)
    (hself : ∀ i ∈ s, i ∈ B i) (hsize : ∀ i ∈ s, (B i).card ≤ 3)
    (hread : ∀ j, (s.filter fun i => j ∈ B i).card ≤ 4)
    (a : ℝ) (ha : 0 < a) (hcard : a ≤ (s.card : ℝ))
    (μ : Measure (I → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun i => {ω | ω i = true}) μ)
    (hmarg : ∀ i, μ {ω | ω i = true} = ENNReal.ofReal (1 / 2)) :
    μ.real {ω | ((good s B ω).card : ℝ) ≤ a / 192} ≤ Real.exp (-a / 1536) := by
  classical
  obtain ⟨W, hWs, hd, hc⟩ := exists_disjoint_of_read s B 3 4
    (fun i hi => ⟨i, hself i hi⟩) hsize hread
  have hwc : a ≤ 12 * (W.card : ℝ) := by exact hcard.trans (by exact_mod_cast hc)
  have hwpos : 0 < W.card := by exact_mod_cast (by linarith : (0 : ℝ) < W.card)
  let J := {i // i ∈ W}
  have : Nonempty J := by
    obtain ⟨i, hi⟩ := card_pos.mp hwpos
    exact ⟨⟨i, hi⟩⟩
  let sign : I → Bool := fun i => decide (i ∈ W)
  let A : J → Set (I → Bool) := fun i => blockEvent
    (fun j => if sign j then {ω | ω j = true} else {ω | ω j = true}ᶜ) (B i.val)
  have hiff : ∀ (i : J) (ω : I → Bool), ω ∈ A i ↔
      ω i.val = true ∧ ∀ j ∈ B i.val, j ≠ i.val → ω j = false := by
    intro i ω
    have honly : ∀ j ∈ B i.val, j ∈ W ↔ j = i.val := by
      intro j hj
      constructor
      · intro hjW
        by_contra hn
        exact disjoint_left.mp (hd i.property hjW (Ne.symm hn)) hj (hself j (hWs hjW))
      · rintro rfl
        exact i.property
    simp only [A, blockEvent, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · simpa [sign, i.property] using h i.val (hself i.val (hWs i.property))
      · intro j hj hn
        have hjn : j ∉ W := fun hw => hn ((honly j hj).mp hw)
        simpa [sign, hjn] using h j hj
    · rintro ⟨hon, hoff⟩ j hj
      by_cases he : j = i.val
      · subst j
        simpa [sign, i.property] using hon
      · have hjn : j ∉ W := fun hw => he ((honly j hj).mp hw)
        simpa [sign, hjn] using hoff j hj he
  have ht := signed_blocks_tail μ hind hmarg sign (fun i : J => B i.val)
    (fun i j hij => hd i.property j.property (fun h => hij (Subtype.ext h)))
    (fun i => hsize i.val (hWs i.property))
  have hsum : ∀ ω, (∑ i : J, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
      ((good s B ω).card : ℝ) := by
    intro ω
    have heq : (∑ i : J, (A i).indicator (fun _ => (1 : ℝ)) ω) =
        ((good W B ω).card : ℝ) := by
      calc
        _ = ∑ i ∈ W, if ω i = true ∧ ∀ j ∈ B i, j ≠ i → ω j = false
            then (1 : ℝ) else 0 := by
          apply sum_bij (fun i _ => i.val)
          · intro i _; exact i.property
          · intro i _ j _ h; exact Subtype.ext h
          · intro i hi; exact ⟨⟨i, hi⟩, mem_univ _, rfl⟩
          · intro i _; simp only [Set.indicator_apply, hiff]
        _ = _ := by simp only [sum_boole, good]
    rw [heq]
    exact_mod_cast card_le_card (good_mono hWs B ω)
  have hset : {ω | ((good s B ω).card : ℝ) ≤ a / 192} ⊆
      {ω | (∑ i : J, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
        (Fintype.card J : ℝ) / 16} := by
    intro ω hω
    change _ ≤ _ at hω ⊢
    have hh := hsum ω
    have hj : Fintype.card J = W.card := Fintype.card_coe _
    rw [hj]
    linarith
  apply (measureReal_mono hset).trans (ht.trans (Real.exp_le_exp.mpr ?_))
  have hj : Fintype.card J = W.card := Fintype.card_coe _
  rw [hj]
  linarith

theorem exists_simultaneous [Finite I] {Q : Type*} [Fintype Q]
    (s : Q → Finset I) (B : Q → I → Finset I)
    (hself : ∀ q i, i ∈ s q → i ∈ B q i)
    (hsize : ∀ q i, i ∈ s q → (B q i).card ≤ 3)
    (hread : ∀ q j, ((s q).filter fun i => j ∈ B q i).card ≤ 4)
    (a : ℝ) (ha : 0 < a) (hcard : ∀ q, a ≤ ((s q).card : ℝ))
    (hbudget : (Fintype.card Q : ℝ) * Real.exp (-a / 1536) < 1) :
    ∃ ω : I → Bool, ∀ q, a / 192 < ((good (s q) (B q) ω).card : ℝ) := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := I) (1 / 2)
    (by norm_num) (by norm_num)
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ
    (fun q => {ω | ((good (s q) (B q) ω).card : ℝ) ≤ a / 192})
    (fun _ => Real.exp (-a / 1536))
    (fun q => good_tail (s q) (B q) (hself q) (hsize q) (hread q) a ha (hcard q)
      μ hind hmarg)
    (by simpa only [sum_const, card_univ, nsmul_eq_mul] using hbudget)
  exact ⟨ω, fun q => not_le.mp (hω q)⟩

end PartitionedTriangleAbsorption.SelfExcludingReserveStage123

namespace PartitionedTriangleAbsorption.ReserveQueryGeometryStage123

open Finset CoverDownStage105 SelfExcludingReserveStage123

/-- One subpacking serves every query simultaneously, with both connector
edges outside the whole subpacking. The base packing and raw richness remain
explicit inputs; no residual-dependent choice is made. -/
theorem exists_physical_thinning {V Q : Type*} [Finite V] [DecidableEq V] [Fintype Q]
    (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (S : Q → Finset (V × V × V)) (x y z : Q → V)
    (hST : ∀ q, S q ⊆ T) (hroot : ∀ q r, r ∈ S q → r.1 = x q)
    (hself : ∀ q r, r ∈ S q → Disjoint (connectors (y q) (z q) r) (resTri r))
    (a : ℝ) (ha : 0 < a) (hcard : ∀ q, a ≤ ((S q).card : ℝ))
    (hbudget : (Fintype.card Q : ℝ) * Real.exp (-a / 1536) < 1) :
    ∃ T' ⊆ T, (T' : Set (V × V × V)).PairwiseDisjoint resTri ∧
      ∀ q, a / 192 < ((T'.filter fun r => r ∈ S q ∧
        Disjoint (connectors (y q) (z q) r) (resEdges T')).card : ℝ) := by
  classical
  obtain ⟨ω, hω⟩ := exists_simultaneous S (fun q => queryBlock T (y q) (z q))
    (fun _ r _ => mem_insert_self _ _)
    (fun q r _ => queryBlock_card_le T hd (y q) (z q) r)
    (fun q => queryBlock_read_le T (S q) hd (hST q) (x q) (y q) (z q) (hroot q))
    a ha hcard hbudget
  let T' := T.filter fun r => ω r = true
  have ht : T' ⊆ T := filter_subset _ _
  refine ⟨T', ht, hd.subset ht, ?_⟩
  intro q
  apply (hω q).trans_le
  apply Nat.cast_le.mpr
  apply card_le_card
  intro r hr
  obtain ⟨hrs, hon, hoff⟩ := (mem_good _ _ _ _).mp hr
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hST q hrs, hon⟩, hrs,
    clean_connectors T (y q) (z q) r ω (hself q r hrs) hoff⟩

end PartitionedTriangleAbsorption.ReserveQueryGeometryStage123

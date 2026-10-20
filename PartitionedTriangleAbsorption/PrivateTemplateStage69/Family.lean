/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplateStage69.LedgerStep

/-! # Simultaneous private absorbers for a preselected bounded family

`family_private_absorbers`: a family `P 0, …, P (K-1)` of bounded structural
`F3`-divisible pieces of the four-class host is fixed **first**, together with a forbidden
ledger `R` (source and refiner edges) of maximum degree `ρ`. Pieces are processed in order;
piece `k` receives its private absorber from `ledger_step` against the ledger
`R ∪ A 0 ∪ … ∪ A (k-1)`. The output satisfies

* each `A i ⊆ E(G₀)`, `A i ∩ R = ∅`, `|A i|, |V(A i)| ≤ C(m)`, `A i` has no edge between
  two roots of `P i`, and both modes `A i`, `A i ∪ P i` have structural `F3` decompositions;
* the `A i` are pairwise edge-disjoint;
* **explicit load accounting**: for every vertex `v`,
  `deg_{R ∪ ⋃ A}(v) ≤ max(deg_R(v), T + C(m)) + C(m) · λ(v)`, where `λ(v)` is the number of
  pieces having `v` as a root; hence the global ledger has maximum degree `≤ D`.

A host vertex may be reused by different absorbers; it is used as an auxiliary only while
its ledger degree is at most `T`, and every root use costs at most `C(m)`.
`family_universal`: if the pieces are pairwise edge-disjoint and lie in `R`, then for
**every** subfamily `S` chosen afterwards, `⋃ A ∪ ⋃_{i ∈ S} P i` has a structural `F3`
decomposition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks SignedHinge SparseReserveGeometry PhysicalHingeSupply
open ClassRepresentativesStage65 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of the first `k` pieces having `v` as a root. -/
def rootLoad (P : ℕ → Finset (Sym2 V)) (k : ℕ) (v : V) : ℕ :=
  ((range k).filter fun i => v ∈ vertSet (P i)).card

theorem rootLoad_succ (P : ℕ → Finset (Sym2 V)) (k : ℕ) (v : V) :
    rootLoad P (k + 1) v = rootLoad P k v + if v ∈ vertSet (P k) then 1 else 0 := by
  unfold rootLoad
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hk => notMem_range_self (mem_filter.mp hk).1)]
  · rfl

theorem rootLoad_mono (P : ℕ → Finset (Sym2 V)) {k K : ℕ} (hk : k ≤ K) (v : V) :
    rootLoad P k v ≤ rootLoad P K v :=
  card_le_card (filter_subset_filter _ (range_subset_range.mpr hk))

omit [Fintype V] in
theorem incidentLoad_union {E F : Finset (Sym2 V)} (h : Disjoint E F) (v : V) :
    incidentLoad (E ∪ F) v = incidentLoad E v + incidentLoad F v := by
  unfold incidentLoad
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

omit [Fintype V] in
theorem incidentLoad_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) (v : V) :
    incidentLoad E v ≤ incidentLoad F v :=
  card_le_card (filter_subset_filter _ h)

omit [Fintype V] in
/-- Union of decompositions of two disjoint edge sets, for any labelling and family. -/
theorem hasDecomp_union_any {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E₁ E₂ : Finset (Sym2 V)} (h₁ : HasDecomp p F E₁) (h₂ : HasDecomp p F E₂)
    (hd : Disjoint E₁ E₂) : HasDecomp p F (E₁ ∪ E₂) := by
  obtain ⟨D₁, hT₁, hP₁, hU₁⟩ := h₁
  obtain ⟨D₂, hT₂, hP₂, hU₂⟩ := h₂
  have hsub₁ : ∀ s ∈ D₁, triEdges s ⊆ E₁ := fun s hs => hU₁ ▸ subset_biUnion_of_mem _ hs
  have hsub₂ : ∀ s ∈ D₂, triEdges s ⊆ E₂ := fun s hs => hU₂ ▸ subset_biUnion_of_mem _ hs
  refine ⟨D₁ ∪ D₂, fun s hs => ?_, ?_, ?_⟩
  · rcases mem_union.mp hs with h | h
    · exact hT₁ s h
    · exact hT₂ s h
  · intro s hs u hu hsu
    rcases mem_union.mp (mem_coe.mp hs) with h | h <;>
      rcases mem_union.mp (mem_coe.mp hu) with h' | h'
    · exact hP₁ h h' hsu
    · exact disjoint_of_subset_left (hsub₁ s h) (disjoint_of_subset_right (hsub₂ u h') hd)
    · exact disjoint_of_subset_left (hsub₂ s h)
        (disjoint_of_subset_right (hsub₁ u h') hd.symm)
    · exact hP₂ h h' hsu
  · rw [union_biUnion, hU₁, hU₂]

omit [Fintype V] in
/-- Decompositions of pairwise edge-disjoint pieces combine. -/
theorem hasDecomp_biUnion_any {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 V))
    (hE : ∀ i ∈ s, HasDecomp p F (E i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j)) :
    HasDecomp p F (s.biUnion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine hasDecomp_union_any (hE a (mem_insert_self _ _))
      (ih (fun i hi => hE i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hd i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)) ?_
    refine (disjoint_biUnion_right _ _ _).mpr fun j hj => ?_
    exact hd a (mem_insert_self _ _) j (mem_insert_of_mem hj) (fun h => ha (h ▸ hj))

/-- The invariant maintained by the sequential placement. -/
def FamilyInv (cls : V → Fin 4) (G₀ : SimpleGraph V) [DecidableRel G₀.Adj] (m : ℕ)
    (T : ℝ) (R : Finset (Sym2 V)) (P : ℕ → Finset (Sym2 V)) (k : ℕ)
    (A : ℕ → Finset (Sym2 V)) : Prop :=
  (∀ i < k, A i ⊆ G₀.edgeFinset ∧ Disjoint (A i) R ∧ HasDecomp cls F3 (A i) ∧
      HasDecomp cls F3 (A i ∪ P i) ∧ (A i).card ≤ templateConst m ∧
      (vertSet (A i)).card ≤ templateConst m ∧
      ∀ a ∈ vertSet (P i), ∀ b ∈ vertSet (P i), s(a, b) ∉ A i) ∧
    (∀ i < k, ∀ j < k, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ v, (incidentLoad (R ∪ (range k).biUnion A) v : ℝ) ≤
      max (incidentLoad R v : ℝ) (T + templateConst m) + templateConst m * rootLoad P k v) ∧
    ((range k).biUnion A).card ≤ k * templateConst m

theorem familyInv_zero (cls : V → Fin 4) (G₀ : SimpleGraph V) [DecidableRel G₀.Adj]
    (m : ℕ) (T : ℝ) (R : Finset (Sym2 V)) (P : ℕ → Finset (Sym2 V)) :
    FamilyInv cls G₀ m T R P 0 (fun _ => ∅) := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _), fun v => ?_, by simp⟩
  simp only [range_zero, biUnion_empty, union_empty, rootLoad, filter_empty, card_empty,
    Nat.cast_zero, mul_zero, add_zero]
  exact le_max_left _ _

/-- The sequential placement, by induction on the number of processed pieces. -/
theorem familyInv_exists (m : ℕ) (cls : V → Fin 4) (G₀ : SimpleGraph V)
    [DecidableRel G₀.Adj] (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b)
    (γ T D Λ ρ : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (h1 : (2 * m + 3 : ℝ) * D < γ ^ 2 * Fintype.card V / 4)
    (h2 : 2 ≤ γ ^ 2 * Fintype.card V / 4)
    (h3 : 56 * D ≤ γ ^ 3 * Fintype.card V / 8)
    (h4 : 4 * D ≤ γ ^ 2 * Fintype.card V / 4)
    (h5 : (absorberBudget 6 (12 * m) : ℝ) < γ ^ 2 * Fintype.card V / 8)
    (h6 : (2 ^ 21 : ℝ) * absorberBudget 6 (12 * m) < γ ^ 3 * Fintype.card V / 64)
    (R : Finset (Sym2 V)) (hR : DegBounded R ρ)
    (hD : max ρ (T + templateConst m) + templateConst m * Λ + 2 * m ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V)) (hPG : ∀ i < K, P i ⊆ G₀.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv cls F3 (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * ((R.card : ℝ) + K * templateConst m) ≤ T * γ * Fintype.card V) :
    ∀ k ≤ K, ∃ A, FamilyInv cls G₀ m T R P k A := by
  classical
  set C : ℝ := (templateConst m : ℝ) with hC
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hdeg : ∀ k ≤ K, ∀ A, FamilyInv cls G₀ m T R P k A →
      ∀ v, (incidentLoad (R ∪ (range k).biUnion A) v : ℝ) + 2 * m ≤ D := by
    intro k hk A hA v
    have h := hA.2.2.1 v
    have hRv : (incidentLoad R v : ℝ) ≤ ρ := hR v
    have hl : (rootLoad P k v : ℝ) ≤ Λ :=
      le_trans (by exact_mod_cast rootLoad_mono P hk v) (hload v)
    have hmax : max (incidentLoad R v : ℝ) (T + C) ≤ max ρ (T + C) :=
      max_le_max hRv le_rfl
    have : C * rootLoad P k v ≤ C * Λ := mul_le_mul_of_nonneg_left hl hC0
    linarith
  have hD0 : 0 ≤ D := by
    have := le_max_right ρ (T + C)
    have : 0 ≤ C * Λ ∨ C * Λ < 0 := le_or_gt 0 (C * Λ)
    have h0 := hD
    have hn : (0 : ℝ) < Fintype.card V := by nlinarith [sq_nonneg γ]
    have : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    have hl : (0 : ℝ) ≤ Λ := le_trans (Nat.cast_nonneg _) (hload (Classical.arbitrary V))
    nlinarith [mul_nonneg hC0 hl]
  intro k
  induction k with
  | zero => exact fun _ => ⟨_, familyInv_zero cls G₀ m T R P⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, hA⟩ := ih (Nat.le_of_succ_le hk)
    have hkK : k < K := hk
    set L := R ∪ (range k).biUnion A with hL
    have hLdeg : ∀ v, (incidentLoad L v : ℝ) + 2 * m ≤ D := hdeg k hkK.le A hA
    have hLc : 4 * (L.card : ℝ) ≤ T * γ * Fintype.card V := by
      have h1' : L.card ≤ R.card + k * templateConst m :=
        (card_union_le _ _).trans (Nat.add_le_add_left hA.2.2.2 _)
      have h2' : (L.card : ℝ) ≤ R.card + k * C := by rw [hC]; exact_mod_cast h1'
      have h3' : (k : ℝ) * C ≤ K * C :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkK.le) hC0
      linarith
    obtain ⟨Ak, hAkG, hAkL, -, hdAk, hdAkP, hAkc, hVkc, hroot', hload'⟩ :=
      ledger_step m cls G₀ hG₀ γ T D hγ hT hsize hD0 h1 h2 h3 h4 h5 h6 L hLdeg hLc
        (P k) (hPG k hkK) (hm k hkK) (hdiv k hkK)
    let A' : ℕ → Finset (Sym2 V) := fun i => if i = k then Ak else A i
    have hA'k : A' k = Ak := by simp [A']
    have hA'i : ∀ i < k, A' i = A i := fun i hi => by simp [A', Nat.ne_of_lt hi]
    have hbig : (range (k + 1)).biUnion A' = (range k).biUnion A ∪ Ak := by
      rw [range_add_one, biUnion_insert, hA'k, union_comm]
      congr 1
      exact biUnion_congr rfl fun i hi => hA'i i (mem_range.mp hi)
    have hAkR : Disjoint Ak R := disjoint_of_subset_right subset_union_left hAkL
    have hAkA : ∀ j < k, Disjoint Ak (A j) := fun j hj =>
      disjoint_of_subset_right
        ((subset_biUnion_of_mem A (mem_range.mpr hj)).trans subset_union_right) hAkL
    refine ⟨A', ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun v => ?_, ?_⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hA'i i hi]
        exact hA.1 i hi
      · rw [hA'k]
        exact ⟨hAkG, hAkR, hdAk, hdAkP, hAkc, hVkc, hroot'⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hA'i i hi, hA'i j hj]
        exact hA.2.1 i hi j hj hij
      · rw [hA'i i hi, hA'k]
        exact (hAkA i hi).symm
      · rw [hA'i j hj, hA'k]
        exact hAkA j hj
      · exact absurd rfl hij
    · rw [hbig, ← union_assoc, incidentLoad_union (disjoint_comm.mp hAkL), rootLoad_succ]
      have hold := hA.2.2.1 v
      have hAkv : (incidentLoad Ak v : ℝ) ≤ C := by
        rw [hC]
        exact_mod_cast (incidentLoad_le_card Ak v).trans hAkc
      by_cases hvP : v ∈ vertSet (P k)
      · simp only [hvP, ↓reduceIte]
        push_cast
        linarith
      · simp only [hvP, ↓reduceIte, add_zero]
        push_cast
        by_cases hvA : v ∈ vertSet Ak
        · rcases hload' v hvA with h | h
          · exact absurd h hvP
          · have hm1 : T + C ≤ max (incidentLoad R v : ℝ) (T + C) := le_max_right _ _
            have hm2 : 0 ≤ C * (rootLoad P k v : ℝ) :=
              mul_nonneg hC0 (Nat.cast_nonneg _)
            linarith
        · rw [incidentLoad_eq_zero hvA]
          push_cast
          linarith
    · rw [hbig]
      refine (card_union_le _ _).trans ?_
      have := hA.2.2.2
      rw [Nat.succ_mul]
      omega

/-- **Simultaneous private absorbers for a preselected family, with explicit load
accounting.** -/
theorem family_private_absorbers (m : ℕ) (cls : V → Fin 4) (G₀ : SimpleGraph V)
    [DecidableRel G₀.Adj] (hG₀ : ∀ a b, G₀.Adj a b ↔ cls a ≠ cls b)
    (γ T D Λ ρ : ℝ) (hγ : 0 < γ) (hT : 0 < T)
    (hsize : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (h1 : (2 * m + 3 : ℝ) * D < γ ^ 2 * Fintype.card V / 4)
    (h2 : 2 ≤ γ ^ 2 * Fintype.card V / 4)
    (h3 : 56 * D ≤ γ ^ 3 * Fintype.card V / 8)
    (h4 : 4 * D ≤ γ ^ 2 * Fintype.card V / 4)
    (h5 : (absorberBudget 6 (12 * m) : ℝ) < γ ^ 2 * Fintype.card V / 8)
    (h6 : (2 ^ 21 : ℝ) * absorberBudget 6 (12 * m) < γ ^ 3 * Fintype.card V / 64)
    (R : Finset (Sym2 V)) (hR : DegBounded R ρ)
    (hD : max ρ (T + templateConst m) + templateConst m * Λ + 2 * m ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V)) (hPG : ∀ i < K, P i ⊆ G₀.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv cls F3 (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * ((R.card : ℝ) + K * templateConst m) ≤ T * γ * Fintype.card V) :
    ∃ A : ℕ → Finset (Sym2 V),
      (∀ i < K, A i ⊆ G₀.edgeFinset ∧ Disjoint (A i) R ∧ HasDecomp cls F3 (A i) ∧
        HasDecomp cls F3 (A i ∪ P i) ∧ (A i).card ≤ templateConst m ∧
        (vertSet (A i)).card ≤ templateConst m ∧
        ∀ a ∈ vertSet (P i), ∀ b ∈ vertSet (P i), s(a, b) ∉ A i) ∧
      (∀ i < K, ∀ j < K, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ v, (incidentLoad (R ∪ (range K).biUnion A) v : ℝ) ≤
        max (incidentLoad R v : ℝ) (T + templateConst m) +
          templateConst m * rootLoad P K v) ∧
      DegBounded (R ∪ (range K).biUnion A) D := by
  obtain ⟨A, hA⟩ := familyInv_exists m cls G₀ hG₀ γ T D Λ ρ hγ hT hsize h1 h2 h3 h4 h5 h6
    R hR hD K P hPG hm hdiv hload hcount K le_rfl
  refine ⟨A, hA.1, hA.2.1, hA.2.2.1, fun v => ?_⟩
  have h := hA.2.2.1 v
  have hRv : (incidentLoad R v : ℝ) ≤ ρ := hR v
  have hC0 : (0 : ℝ) ≤ templateConst m := Nat.cast_nonneg _
  have hmax : max (incidentLoad R v : ℝ) (T + templateConst m) ≤
      max ρ (T + templateConst m) := max_le_max hRv le_rfl
  have : (templateConst m : ℝ) * rootLoad P K v ≤ templateConst m * Λ :=
    mul_le_mul_of_nonneg_left (hload v) hC0
  have hm0 : (0 : ℝ) ≤ 2 * m := by positivity
  change (incidentLoad (R ∪ (range K).biUnion A) v : ℝ) ≤ D
  linarith

omit [Fintype V] in
/-- **Universality for the preselected family.** If the pieces are pairwise edge-disjoint
source edges (contained in `R`), then for every subfamily `S` selected *after* the
absorbers, `⋃ A ∪ ⋃_{i ∈ S} P i` has a structural `F3` decomposition. -/
theorem family_universal {cls : V → Fin 4} {R : Finset (Sym2 V)} {K : ℕ}
    {P A : ℕ → Finset (Sym2 V)}
    (hA : ∀ i < K, Disjoint (A i) R ∧ HasDecomp cls F3 (A i) ∧ HasDecomp cls F3 (A i ∪ P i))
    (hAA : ∀ i < K, ∀ j < K, i ≠ j → Disjoint (A i) (A j))
    (hPR : ∀ i < K, P i ⊆ R) (hPP : ∀ i < K, ∀ j < K, i ≠ j → Disjoint (P i) (P j))
    (S : Finset ℕ) (hS : S ⊆ range K) :
    HasDecomp cls F3 ((range K).biUnion A ∪ S.biUnion P) := by
  classical
  let E : ℕ → Finset (Sym2 V) := fun i => if i ∈ S then A i ∪ P i else A i
  have hEq : (range K).biUnion A ∪ S.biUnion P = (range K).biUnion E := by
    ext e
    simp only [mem_union, mem_biUnion, mem_range, E]
    constructor
    · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
      · refine ⟨i, hi, ?_⟩
        split_ifs
        · exact mem_union_left _ he
        · exact he
      · refine ⟨i, mem_range.mp (hS hi), ?_⟩
        simp only [hi, ↓reduceIte]
        exact mem_union_right _ he
    · rintro ⟨i, hi, he⟩
      split_ifs at he with hiS
      · rcases mem_union.mp he with h | h
        · exact Or.inl ⟨i, hi, h⟩
        · exact Or.inr ⟨i, hiS, h⟩
      · exact Or.inl ⟨i, hi, he⟩
  rw [hEq]
  apply hasDecomp_biUnion_any
  · intro i hi
    have hi' := mem_range.mp hi
    simp only [E]
    split_ifs
    · exact (hA i hi').2.2
    · exact (hA i hi').2.1
  · intro i hi j hj hij
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hAP : ∀ a < K, ∀ b < K, Disjoint (A a) (P b) := fun a ha b hb =>
      disjoint_of_subset_right (hPR b hb) (hA a ha).1
    have key : Disjoint (A i ∪ P i) (A j ∪ P j) := by
      refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hAA i hi' j hj' hij,
        hAP i hi' j hj'⟩, disjoint_union_right.mpr ⟨(hAP j hj' i hi').symm,
        hPP i hi' j hj' hij⟩⟩
    simp only [E]
    split_ifs
    · exact key
    · exact disjoint_of_subset_right subset_union_left key
    · exact disjoint_of_subset_left subset_union_left key
    · exact disjoint_of_subset_left subset_union_left
        (disjoint_of_subset_right subset_union_left key)

end PartitionedTriangleAbsorption.PrivateTemplateStage69

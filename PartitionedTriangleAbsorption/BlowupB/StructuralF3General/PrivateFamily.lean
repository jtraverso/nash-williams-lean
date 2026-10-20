/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply
public import PartitionedTriangleAbsorption.RefinerAssembly

/-! # Universal assembly with a guarded terminal placement step

This is the deterministic ledger induction from PrivateTemplateStage69.Family,
with the host-specific terminal call separated into `PrivateStep`.  The type
family is arbitrary.  The eventual guarded terminal theorem supplies this
step; no completeness hypothesis occurs in the induction or assembly.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily

open Finset AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def rootLoad (P : ℕ → Finset (Sym2 V)) (k : ℕ) (v : V) : ℕ :=
  ((range k).filter fun i => v ∈ vertSet (P i)).card

theorem rootLoad_succ (P : ℕ → Finset (Sym2 V)) (k : ℕ) (v : V) :
    rootLoad P (k + 1) v = rootLoad P k v + if v ∈ vertSet (P k) then 1 else 0 := by
  unfold rootLoad
  rw [range_add_one, filter_insert]
  split_ifs
  · rw [card_insert_of_notMem (fun hk => notMem_range_self (mem_filter.mp hk).1)]
  · rfl

theorem rootLoad_mono (P : ℕ → Finset (Sym2 V)) {k K : ℕ} (hk : k ≤ K) (v : V) :
    rootLoad P k v ≤ rootLoad P K v :=
  card_le_card (filter_subset_filter _ (range_subset_range.mpr hk))

theorem rootLoad_le_incidence_sum (P : ℕ → Finset (Sym2 V)) (K : ℕ) (v : V) :
    rootLoad P K v ≤ ∑ i ∈ range K, incidentLoad (P i) v := by
  classical
  unfold rootLoad
  rw [card_filter]
  apply sum_le_sum
  intro i _
  split_ifs with hv
  · obtain ⟨_, e, he, hve⟩ := mem_filter.mp hv
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hve⟩⟩
  · exact Nat.zero_le _

omit [Fintype V] in
theorem incidentLoad_union {E F : Finset (Sym2 V)} (h : Disjoint E F) (v : V) :
    incidentLoad (E ∪ F) v = incidentLoad E v + incidentLoad F v := by
  unfold incidentLoad
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

omit [Fintype V] in
theorem incidentLoad_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) (v : V) :
    incidentLoad E v ≤ incidentLoad F v := card_le_card (filter_subset_filter _ h)

omit [Fintype V] in
theorem incidentLoad_le_card (E : Finset (Sym2 V)) (v : V) : incidentLoad E v ≤ E.card :=
  card_filter_le _ _

theorem incidentLoad_eq_zero {E : Finset (Sym2 V)} {v : V} (hv : v ∉ vertSet E) :
    incidentLoad E v = 0 := by
  rw [incidentLoad, card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  exact hv (mem_filter.mpr ⟨mem_univ _, e, he, hve⟩)

/-- The precise placement contract used by the ledger induction. -/
def PrivateStep (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (m C : ℕ) (T D a : ℝ) : Prop :=
  ∀ L : Finset (Sym2 V), DegBounded L D → 4 * (L.card : ℝ) ≤ T * a →
    ∀ P : Finset (Sym2 V), P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A L ∧
        HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧ A.card ≤ C ∧
        ∀ v ∈ vertSet A, v ∈ vertSet P ∨ (incidentLoad L v : ℝ) ≤ T

def FamilyInv (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (T : ℝ) (R : Finset (Sym2 V)) (P : ℕ → Finset (Sym2 V)) (k : ℕ)
    (A : ℕ → Finset (Sym2 V)) : Prop :=
  (∀ i < k, A i ⊆ G.edgeFinset ∧ Disjoint (A i) R ∧ HasDecomp p F (A i) ∧
      HasDecomp p F (A i ∪ P i) ∧ (A i).card ≤ C) ∧
    (∀ i < k, ∀ j < k, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ v, (incidentLoad (R ∪ (range k).biUnion A) v : ℝ) ≤
      max (incidentLoad R v : ℝ) (T + C) + C * rootLoad P k v) ∧
    ((range k).biUnion A).card ≤ k * C

theorem familyInv_zero (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℕ)
    (T : ℝ) (R : Finset (Sym2 V)) (P : ℕ → Finset (Sym2 V)) :
    FamilyInv p F G C T R P 0 (fun _ => ∅) := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _), fun v => ?_, by simp⟩
  simp only [range_zero, biUnion_empty, union_empty, rootLoad, filter_empty, card_empty,
    Nat.cast_zero, mul_zero, add_zero]
  exact le_max_left _ _

theorem familyInv_exists (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (m Cnat : ℕ) (T D Λ ρ a : ℝ)
    (hstep : PrivateStep p F G m Cnat T D a)
    (R : Finset (Sym2 V)) (hR : DegBounded R ρ)
    (hD : max ρ (T + Cnat) + Cnat * Λ ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V)) (hPG : ∀ i < K, P i ⊆ G.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv p F (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * ((R.card : ℝ) + K * Cnat) ≤ T * a) :
    ∀ k ≤ K, ∃ A, FamilyInv p F G Cnat T R P k A := by
  classical
  set C : ℝ := (Cnat : ℝ) with hC
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hdeg : ∀ k ≤ K, ∀ A, FamilyInv p F G Cnat T R P k A →
      DegBounded (R ∪ (range k).biUnion A) D := by
    intro k hk A hA v
    have h := hA.2.2.1 v
    have hRv : (incidentLoad R v : ℝ) ≤ ρ := hR v
    have hl : (rootLoad P k v : ℝ) ≤ Λ :=
      le_trans (by exact_mod_cast rootLoad_mono P hk v) (hload v)
    have hmax : max (incidentLoad R v : ℝ) (T + C) ≤ max ρ (T + C) :=
      max_le_max hRv le_rfl
    have : C * rootLoad P k v ≤ C * Λ := mul_le_mul_of_nonneg_left hl hC0
    change (incidentLoad (R ∪ (range k).biUnion A) v : ℝ) ≤ D
    linarith
  intro k
  induction k with
  | zero => exact fun _ => ⟨_, familyInv_zero p F G Cnat T R P⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, hA⟩ := ih (Nat.le_of_succ_le hk)
    have hkK : k < K := hk
    set L := R ∪ (range k).biUnion A with hL
    have hLdeg : DegBounded L D := hdeg k hkK.le A hA
    have hLc : 4 * (L.card : ℝ) ≤ T * a := by
      have h1' : L.card ≤ R.card + k * Cnat :=
        (card_union_le _ _).trans (Nat.add_le_add_left hA.2.2.2 _)
      have h2' : (L.card : ℝ) ≤ R.card + k * C := by rw [hC]; exact_mod_cast h1'
      have h3' : (k : ℝ) * C ≤ K * C :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkK.le) hC0
      linarith
    obtain ⟨Ak, hAkG, hAkL, hdAk, hdAkP, hAkc, hload'⟩ :=
      hstep L hLdeg hLc (P k) (hPG k hkK) (hm k hkK) (hdiv k hkK)
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
        exact ⟨hAkG, hAkR, hdAk, hdAkP, hAkc⟩
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

theorem family_private_absorbers (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (m C : ℕ) (T D Λ ρ a : ℝ)
    (hstep : PrivateStep p F G m C T D a)
    (R : Finset (Sym2 V)) (hR : DegBounded R ρ)
    (hD : max ρ (T + C) + C * Λ ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V)) (hPG : ∀ i < K, P i ⊆ G.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv p F (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * ((R.card : ℝ) + K * C) ≤ T * a) :
    ∃ A : ℕ → Finset (Sym2 V),
      (∀ i < K, A i ⊆ G.edgeFinset ∧ Disjoint (A i) R ∧ HasDecomp p F (A i) ∧
        HasDecomp p F (A i ∪ P i) ∧ (A i).card ≤ C) ∧
      (∀ i < K, ∀ j < K, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ v, (incidentLoad (R ∪ (range K).biUnion A) v : ℝ) ≤
        max (incidentLoad R v : ℝ) (T + C) + C * rootLoad P K v) ∧
      DegBounded (R ∪ (range K).biUnion A) D := by
  obtain ⟨A, hA⟩ := familyInv_exists p F G m C T D Λ ρ a hstep
    R hR hD K P hPG hm hdiv hload hcount K le_rfl
  refine ⟨A, hA.1, hA.2.1, hA.2.2.1, fun v => ?_⟩
  have h := hA.2.2.1 v
  have hRv : (incidentLoad R v : ℝ) ≤ ρ := hR v
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hmax : max (incidentLoad R v : ℝ) (T + C) ≤ max ρ (T + C) :=
    max_le_max hRv le_rfl
  have : (C : ℝ) * rootLoad P K v ≤ C * Λ :=
    mul_le_mul_of_nonneg_left (hload v) hC0
  change (incidentLoad (R ∪ (range K).biUnion A) v : ℝ) ≤ D
  linarith

/-- A single absorber is chosen before every divisible leftover in `X`. -/
theorem universal_from_library (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (m C : ℕ) (T D Λ ρ a : ℝ)
    (hstep : PrivateStep p F G m C T D a)
    (X R : Finset (Sym2 V)) (hRX : Disjoint R X) (hRG : R ⊆ G.edgeFinset)
    (hledger : DegBounded (X ∪ R) ρ)
    (hD : max ρ (T + C) + C * Λ ≤ D)
    (K : ℕ) (P : ℕ → Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) (range K) P X R)
    (hpieces : ∀ i < K, P i ⊆ X ∪ R)
    (hPG : ∀ i < K, P i ⊆ G.edgeFinset)
    (hm : ∀ i < K, (P i).card ≤ m) (hdiv : ∀ i < K, IsIntDiv p F (P i))
    (hload : ∀ v, (rootLoad P K v : ℝ) ≤ Λ)
    (hcount : 4 * (((X ∪ R).card : ℝ) + K * C) ≤ T * a) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F A ∧ DegBounded A D ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L) := by
  obtain ⟨priv, hpriv, hdis, _, hdeg⟩ :=
    family_private_absorbers p F G m C T D Λ ρ a hstep
      (X ∪ R) hledger hD K P hPG hm hdiv hload hcount
  have hcompose := RefinerAssembly.universal_of_refiner (range K) priv P X R hRX href
    (fun i hi => (hpriv i (mem_range.mp hi)).2.2.1)
    (fun i hi => (hpriv i (mem_range.mp hi)).2.2.2.1)
    (fun i hi j hj hij => hdis i (mem_range.mp hi) j (mem_range.mp hj) hij)
    (fun i hi => (hpriv i (mem_range.mp hi)).2.1)
    (fun i hi => hpieces i (mem_range.mp hi))
  refine ⟨R ∪ (range K).biUnion priv, ?_, hcompose.1, hcompose.2.1, ?_, hcompose.2.2⟩
  · exact union_subset hRG (biUnion_subset.mpr fun i hi => (hpriv i (mem_range.mp hi)).1)
  · intro v
    have hmono : (incidentLoad (R ∪ (range K).biUnion priv) v : ℝ) ≤
        incidentLoad ((X ∪ R) ∪ (range K).biUnion priv) v := by
      exact_mod_cast incidentLoad_mono (by
        intro e he
        rcases mem_union.mp he with he | he
        · exact mem_union_left _ (mem_union_right _ he)
        · exact mem_union_right _ he) v
    exact hmono.trans (hdeg v)

#print axioms familyInv_exists
#print axioms family_private_absorbers
#print axioms universal_from_library

end PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily

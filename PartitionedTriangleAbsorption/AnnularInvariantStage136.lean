/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ProtectedSuccessorStage135
public import PartitionedTriangleAbsorption.BalanceDivisibilityStage134

/-! # One-layer memory for a protected vertex vortex

Separate the fixed reference graph from edges consumed by previous levels.
When old damage avoids the child and a new packing avoids the grandchild,
the next damage is exactly the new packing restricted to the child. It is
not the sum of all historical damage. This is a deterministic transition
identity, not an existence theorem for the required protected packing.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AnnularInvariantStage136

open Finset CoverDownStage105 AntiEdgeSelection TypedApplicationLinks ReserveAwareRecutStage120

variable {V : Type*}

noncomputable def inner (E : Finset (Sym2 V)) (U : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (IsInner U)

@[simp] theorem mem_inner (E : Finset (Sym2 V)) (U : Finset V) (e : Sym2 V) :
    e ∈ inner E U ↔ e ∈ E ∧ IsInner U e := by
  classical
  exact mem_filter

theorem inner_subset (E : Finset (Sym2 V)) (U : Finset V) : inner E U ⊆ E :=
  fun _ he => (mem_inner _ _ _).mp he |>.1

variable [DecidableEq V]

/-- Confinement and absence of old inner damage identify the next host. -/
theorem next_host (E D P : Finset (Sym2 V)) (U : Finset V)
    (hclean : Disjoint D (inner E U))
    (hconf : (E \ D) \ P ⊆ inner E U) :
    (E \ D) \ P = inner E U \ (P ∩ inner E U) := by
  ext e
  constructor
  · intro he
    have hi := hconf he
    exact mem_sdiff.mpr ⟨hi, fun hp => (mem_sdiff.mp he).2 (mem_inter.mp hp).1⟩
  · intro he
    obtain ⟨hi, hn⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨inner_subset E U hi, ?_⟩, ?_⟩
    · intro hd
      exact disjoint_left.mp hclean hd hi
    · intro hp
      exact hn (mem_inter.mpr ⟨hp, hi⟩)

/-- The new defect contains no accumulated contribution from `D`. -/
theorem next_damage (E D P : Finset (Sym2 V)) (U : Finset V)
    (hclean : Disjoint D (inner E U))
    (hconf : (E \ D) \ P ⊆ inner E U) :
    inner E U \ ((E \ D) \ P) = P ∩ inner E U := by
  rw [next_host E D P U hclean hconf]
  ext e
  simp only [mem_sdiff, mem_inter]
  tauto

/-- The complete deterministic transition: divisibility, load, and support.
The packing and its quantitative/protection guarantees are explicit inputs. -/
theorem annular_advance (p : V → Fin 4) (E D P : Finset (Sym2 V))
    (U K : Finset V) (hclean : Disjoint D (inner E U))
    (hconf : (E \ D) \ P ⊆ inner E U)
    (hdiv : IsIntDiv p F3 (E \ D)) (hdec : HasDecomp p F3 P) (hP : P ⊆ E \ D)
    (hprotect : Disjoint P (inner E K)) (load : ℝ)
    (hload : DegBounded (P ∩ inner E U) load) :
    let D' := inner E U \ ((E \ D) \ P)
    D' = P ∩ inner E U ∧ Disjoint D' (inner E K) ∧ DegBounded D' load ∧
      IsIntDiv p F3 (inner E U \ D') := by
  dsimp only
  have he := next_damage E D P U hclean hconf
  rw [he]
  refine ⟨rfl, ?_, hload, ?_⟩
  · exact disjoint_left.mpr fun _ hp hk =>
      disjoint_left.mp hprotect (mem_inter.mp hp).1 hk
  · rw [← next_host E D P U hclean hconf]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hdec hP

/-- The annular packet carries precisely the reference's type charge. -/
theorem charge_carried_by_damage (p : V → Fin 4) (E D : Finset (Sym2 V))
    (hD : D ⊆ E) (hdiv : IsIntDiv p F3 (E \ D)) (k : Fin 2) :
    bal p k D = bal p k E := by
  classical
  have h := BalanceDivisibilityStage134.bal_zero_of_isIntDiv p hdiv k
  rw [bal_sdiff p k hD] at h
  omega

/-- Fixed defects and dynamic damage are separate physical edge sets. -/
theorem missing_split (E0 E D : Finset (Sym2 V)) (hD : D ⊆ E0) :
    E0 \ (E \ D) = (E0 \ E) ∪ D := by
  ext e
  have hd : e ∈ D → e ∈ E0 := fun h => hD h
  simp only [mem_sdiff, mem_union]
  tauto

/-- The next total load is reference load plus THIS level's budget only. -/
theorem missing_load (E0 E D : Finset (Sym2 V)) (hD : D ⊆ E0)
    (base fresh : ℝ) (hbase : DegBounded (E0 \ E) base) (hfresh : DegBounded D fresh) :
    DegBounded (E0 \ (E \ D)) (base + fresh) := by
  rw [missing_split E0 E D hD]
  exact PairSupplyDeletionStage117.degree_union _ _ _ _ hbase hfresh

end PartitionedTriangleAbsorption.AnnularInvariantStage136

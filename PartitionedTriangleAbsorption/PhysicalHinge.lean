/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Sym.Sym2

/-! # Physical support of a triangle hinge

These results concern actual unordered edges, not part labels or sampled
templates. They do not construct an absorber or prove Theorem 13.16.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHinge

variable {V : Type*} [DecidableEq V]

/-- Every edge extends to a physical triangle using only edges of `E`. -/
def TriangleCovered (E : Finset (Sym2 V)) : Prop :=
  ∀ u v, s(u, v) ∈ E → ∃ w, u ≠ w ∧ v ≠ w ∧ s(u, w) ∈ E ∧ s(v, w) ∈ E

/-- The actual vertices incident with the edge set. -/
def support (H : Finset (Sym2 V)) : Finset V := H.biUnion Sym2.toFinset

/-- The same physical edge-set convention used in the returned definitions. -/
def triEdges (s : Finset V) : Finset (Sym2 V) :=
  s.sym2.filter (fun e => ¬ e.IsDiag)

/-- Exact triangle decompositions imply triangle coverage. Disjointness is
not needed for this weaker consequence, so no extra assumption is imposed. -/
theorem triangleCovered_of_decomposition (E : Finset (Sym2 V))
    (D : Finset (Finset V)) (hcard : ∀ s ∈ D, s.card = 3)
    (hunion : D.biUnion triEdges = E) : TriangleCovered E := by
  intro u v he
  rw [← hunion, Finset.mem_biUnion] at he
  obtain ⟨s, hs, he⟩ := he
  simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff] at he
  obtain ⟨⟨hu, hv⟩, _⟩ := he
  have hthird : ∃ w ∈ s, w ≠ u ∧ w ≠ v := by
    by_contra h
    have hsub : s ⊆ ({u, v} : Finset V) := by
      intro x hx
      by_cases hxu : x = u
      · simp [hxu]
      by_cases hxv : x = v
      · simp [hxv]
      exact False.elim (h ⟨x, hx, hxu, hxv⟩)
    have hpair : ({u, v} : Finset V).card ≤ 2 := by
      by_cases huv : u = v <;> simp [huv]
    have hle := (Finset.card_le_card hsub).trans hpair
    simp only [hcard s hs] at hle
    contradiction
  obtain ⟨w, hw, hwu, hwv⟩ := hthird
  have hsub : triEdges s ⊆ E := hunion ▸ Finset.subset_biUnion_of_mem triEdges hs
  refine ⟨w, hwu.symm, hwv.symm, hsub ?_, hsub ?_⟩ <;>
    simp [triEdges, hu, hv, hw, hwu.symm, hwv.symm]

/-- Covering the two nonshared edges forces all three vertices into the hinge. -/
theorem three_roots_forced (H : Finset (Sym2 V)) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hdis : Disjoint H ({s(u, v), s(u, w), s(v, w)} : Finset (Sym2 V)))
    (hcov : TriangleCovered (H ∪ {s(u, w), s(v, w)})) :
    u ∈ support H ∧ v ∈ support H ∧ w ∈ support H := by
  have hmissing : s(u, v) ∉ H ∪ {s(u, w), s(v, w)} := by
    have hnot : s(u, v) ∉ H := fun he =>
      Finset.disjoint_left.mp hdis he (by simp)
    simp [hnot, huv, huw, hvw]
  obtain ⟨x, hux, hwx, huxE, _⟩ := hcov u w (by simp)
  have huxH : s(u, x) ∈ H := by
    simpa [huw, huv, hwx.symm] using huxE
  obtain ⟨y, hvy, hwy, hvyE, hwyE⟩ := hcov v w (by simp)
  have hyu : y ≠ u := by
    intro h; subst y
    have he : s(u, v) ∈ H ∪ {s(u, w), s(v, w)} := by
      simpa only [Sym2.eq_swap] using hvyE
    exact hmissing he
  have hvyH : s(v, y) ∈ H := by
    simpa [huv.symm, hvw, hwy.symm] using hvyE
  have hwyH : s(w, y) ∈ H := by
    simpa [huw.symm, hvw.symm, hyu, hvy.symm] using hwyE
  refine ⟨Finset.mem_biUnion.mpr ⟨s(u, x), huxH, ?_⟩,
    Finset.mem_biUnion.mpr ⟨s(v, y), hvyH, ?_⟩,
    Finset.mem_biUnion.mpr ⟨s(w, y), hwyH, ?_⟩⟩ <;>
    simp [Sym2.mem_toFinset, Sym2.mem_iff]

/-- Both alternative triangle covers force the four prescribed roots. -/
theorem four_roots_forced (H : Finset (Sym2 V)) (u v w z : V)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z)
    (hdisW : Disjoint H ({s(u, v), s(u, w), s(v, w)} : Finset (Sym2 V)))
    (hdisZ : Disjoint H ({s(u, v), s(u, z), s(v, z)} : Finset (Sym2 V)))
    (hcovW : TriangleCovered (H ∪ {s(u, w), s(v, w)}))
    (hcovZ : TriangleCovered (H ∪ {s(u, z), s(v, z)})) :
    ({u, v, w, z} : Finset V) ⊆ support H := by
  obtain ⟨hu, hv, hw⟩ := three_roots_forced H u v w huv huw hvw hdisW hcovW
  obtain ⟨_, _, hz⟩ := three_roots_forced H u v z huv huz hvz hdisZ hcovZ
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [hu, hv, hw, hz]

theorem four_le_support_card (H : Finset (Sym2 V)) (u v w z : V)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hroots : ({u, v, w, z} : Finset V) ⊆ support H) :
    4 ≤ (support H).card := by
  have hcard : ({u, v, w, z} : Finset V).card = 4 := by
    simp [huv, huw, huz, hvw, hvz, hwz]
  have hle := Finset.card_le_card hroots
  simpa only [hcard] using hle

/-- A hinge of order `i` has precisely `i - 4` vertices outside its fixed roots. -/
theorem free_support_card (H : Finset (Sym2 V)) (u v w z : V)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hroots : ({u, v, w, z} : Finset V) ⊆ support H) :
    (support H \ {u, v, w, z}).card = (support H).card - 4 := by
  have hcard : ({u, v, w, z} : Finset V).card = 4 := by
    simp [huv, huw, huz, hvw, hvz, hwz]
  rw [Finset.card_sdiff_of_subset hroots, hcard]

/-- The free vertices determine a support once all prescribed roots are present. -/
theorem support_eq_of_free_support_eq (R S T : Finset V)
    (hRS : R ⊆ S) (hRT : R ⊆ T) (hfree : S \ R = T \ R) : S = T := by
  calc
    S = R ∪ (S \ R) := (Finset.union_sdiff_of_subset hRS).symm
    _ = R ∪ (T \ R) := by rw [hfree]
    _ = T := Finset.union_sdiff_of_subset hRT

/-- Exact number of possible order-`i` supports containing four fixed roots.
This counts supports, not edge sets or absorbers. -/
theorem rooted_support_choices [Fintype V] (u v w z : V) (i : ℕ)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) (hi : 4 ≤ i) :
    (((Finset.univ : Finset V).powersetCard i).filter
      (({u, v, w, z} : Finset V) ⊆ ·)).card =
      Nat.choose (Fintype.card V - 4) (i - 4) := by
  have hcard : ({u, v, w, z} : Finset V).card = 4 := by
    simp [huv, huw, huz, hvw, hvz, hwz]
  simpa only [hcard, Finset.card_univ] using
    Finset.card_filter_powersetCard_subset ({u, v, w, z} : Finset V) Finset.univ i
      (Finset.subset_univ _) (by simpa only [hcard] using hi)

end PartitionedTriangleAbsorption.PhysicalHinge

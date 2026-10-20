/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Integer combinations of physical F0 triangles

`Realizes p G f w` says that the integer edge function `f : Sym2 V → ℤ` is, at **every**
`e : Sym2 V`, the signed sum `∑ s, c s * [e ∈ triEdges s]` of a coefficient function
`c : Finset V → ℤ` supported on actual F0 copies of `G`, with `∑ s, |c s| ≤ w`.

The predicate is closed under sums, integer multiples and pointwise equality, contains every
actual F0 triangle with cost `1`, and for `f = ind P` it yields exactly a
`SignedCertificate.IsSignedCert` with `certWeight ≤ w` (`Realizes.signedCert`).
Every `Realizes` function has zero F0 charge `crossing - 2·internal` (`Realizes.charge_eq_zero`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

section Edges

variable {V : Type*} [DecidableEq V]

/-- Indicator of a single unordered pair. -/
def edgeOf (e : Sym2 V) : Sym2 V → ℤ := fun e' => if e' = e then 1 else 0

/-- Indicator of the pair `{x, y}`. -/
def edgeInd (x y : V) : Sym2 V → ℤ := edgeOf s(x, y)

theorem edgeInd_comm (x y : V) : edgeInd x y = edgeInd y x := by
  unfold edgeInd; rw [Sym2.eq_swap]

end Edges

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `f` is an integer combination of actual F0 triangles of `G` of total weight `≤ w`. -/
def Realizes (p : V → Fin 2) (G : SimpleGraph V) (f : Sym2 V → ℤ) (w : ℤ) : Prop :=
  ∃ c : Finset V → ℤ, (∀ s, c s ≠ 0 → IsCopy p F0 G s) ∧
    (∀ e, f e = ∑ s, c s * ind (triEdges s) e) ∧ ∑ s, |c s| ≤ w

variable {p : V → Fin 2} {G : SimpleGraph V}

namespace Realizes

theorem zero : Realizes p G 0 0 :=
  ⟨0, by simp, by simp, by simp⟩

theorem congr {f g : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) (hfg : f = g) :
    Realizes p G g w := hfg ▸ h

theorem mono {f : Sym2 V → ℤ} {w w' : ℤ} (h : Realizes p G f w) (hw : w ≤ w') :
    Realizes p G f w' := by
  obtain ⟨c, h1, h2, h3⟩ := h
  exact ⟨c, h1, h2, h3.trans hw⟩

theorem add {f g : Sym2 V → ℤ} {w w' : ℤ} (hf : Realizes p G f w) (hg : Realizes p G g w') :
    Realizes p G (f + g) (w + w') := by
  obtain ⟨c, h1, h2, h3⟩ := hf
  obtain ⟨d, k1, k2, k3⟩ := hg
  refine ⟨c + d, fun s hs => ?_, fun e => ?_, ?_⟩
  · by_cases hc : c s = 0
    · exact k1 s (by simpa [hc] using hs)
    · exact h1 s hc
  · simp only [Pi.add_apply, h2 e, k2 e, add_mul, sum_add_distrib]
  · calc ∑ s, |(c + d) s| ≤ ∑ s, (|c s| + |d s|) :=
          Finset.sum_le_sum fun s _ => abs_add_le _ _
      _ = ∑ s, |c s| + ∑ s, |d s| := sum_add_distrib
      _ ≤ w + w' := add_le_add h3 k3

theorem smul {f : Sym2 V → ℤ} {w : ℤ} (k : ℤ) (h : Realizes p G f w) :
    Realizes p G (k • f) (|k| * w) := by
  obtain ⟨c, h1, h2, h3⟩ := h
  refine ⟨k • c, fun s hs => h1 s ?_, fun e => ?_, ?_⟩
  · intro hc; apply hs; simp [hc]
  · simp only [Pi.smul_apply, smul_eq_mul, h2 e, mul_sum, mul_assoc]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg k)

theorem neg {f : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) : Realizes p G (-f) w := by
  have := h.smul (-1)
  simpa using this

theorem sub {f g : Sym2 V → ℤ} {w w' : ℤ} (hf : Realizes p G f w) (hg : Realizes p G g w') :
    Realizes p G (f - g) (w + w') := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem sum {α : Type*} (S : Finset α) (f : α → Sym2 V → ℤ) (w : α → ℤ)
    (h : ∀ i ∈ S, Realizes p G (f i) (w i)) :
    Realizes p G (∑ i ∈ S, f i) (∑ i ∈ S, w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero : Realizes p G 0 0)
  | insert a S ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a S)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem tri {s : Finset V} (hs : IsCopy p F0 G s) : Realizes p G (ind (triEdges s)) 1 := by
  refine ⟨fun t => if t = s then 1 else 0, fun t ht => ?_, fun e => ?_, ?_⟩
  · by_cases h : t = s
    · exact h ▸ hs
    · simp [h] at ht
  · simp
  · simp [apply_ite]

end Realizes

/-! ### Triangles in terms of edges -/

omit [Fintype V] in
theorem ind_triEdges_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ind (triEdges ({a, b, c} : Finset V)) = edgeInd a b + edgeInd a c + edgeInd b c := by
  funext e
  rw [triEdges_three hab hac hbc]
  have h1 : s(a, b) ≠ s(a, c) := by simp [hac, hbc]
  have h2 : s(a, b) ≠ s(b, c) := by simp [hab, hac, hbc]
  have h3 : s(a, c) ≠ s(b, c) := by simp [hab, hac]
  simp only [ind, edgeInd, edgeOf, mem_insert, mem_singleton, Pi.add_apply]
  by_cases e1 : e = s(a, b)
  · subst e1; simp [h1, h2]
  · by_cases e2 : e = s(a, c)
    · subst e2; simp [h1.symm, h3]
    · by_cases e3 : e = s(b, c)
      · subst e3; simp [h2.symm, h3.symm]
      · simp [e1, e2, e3]

theorem f0_of_not_mono : ∀ a b c : Fin 2, ¬ (a = b ∧ b = c) →
    ({a, b, c} : Multiset (Fin 2)) ∈ F0 := by decide

omit [Fintype V] in
/-- An actual triangle of `G` that is not monochromatic is an F0 copy. -/
theorem isCopy_of_adj {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hmono : ¬ (p a = p b ∧ p b = p c)) : IsCopy p F0 G {a, b, c} := by
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
  · rw [map_three p hab.ne hac.ne hbc.ne]
    exact f0_of_not_mono _ _ _ hmono

/-- **Triangle gadget**: an actual non-monochromatic triangle realizes its three edges. -/
theorem realizes_triangle {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hmono : ¬ (p a = p b ∧ p b = p c)) :
    Realizes p G (edgeInd a b + edgeInd a c + edgeInd b c) 1 :=
  (Realizes.tri (isCopy_of_adj hab hac hbc hmono)).congr
    (ind_triEdges_three hab.ne hac.ne hbc.ne)

/-! ### The F0 charge -/

/-- Charge weight of a pair: `1` on crossing pairs, `-2` on internal pairs. -/
def kappa (p : V → Fin 2) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => if p a = p b then -2 else 1, by
    intro a b; by_cases h : p a = p b <;> simp [h, eq_comm]⟩

/-- The F0 charge `crossing - 2·internal` of an integer edge function. -/
def charge (p : V → Fin 2) (f : Sym2 V → ℤ) : ℤ := ∑ e, f e * kappa p e

omit [DecidableEq V] in
theorem charge_add (f g : Sym2 V → ℤ) : charge p (f + g) = charge p f + charge p g := by
  simp [charge, add_mul, sum_add_distrib]

omit [DecidableEq V] in
theorem charge_smul (k : ℤ) (f : Sym2 V → ℤ) : charge p (k • f) = k * charge p f := by
  simp [charge, mul_sum, mul_assoc]

omit [DecidableEq V] in
theorem charge_sub (f g : Sym2 V → ℤ) : charge p (f - g) = charge p f - charge p g := by
  simp [charge, sub_mul, sum_sub_distrib]

theorem charge_edgeInd (x y : V) :
    charge p (edgeInd x y) = if p x = p y then -2 else 1 := by
  simp [charge, edgeInd, edgeOf, kappa]

omit [Fintype V] in
theorem kappa_tri_sum {s : Finset V} (hs : IsCopy p F0 G s) :
    ∑ e ∈ triEdges s, kappa p e = 0 := by
  obtain ⟨hcl, hF⟩ := hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcl.card_eq
  rw [sum_triEdges_three _ hab hac hbc]
  rw [map_three p hab hac hbc] at hF
  simp only [kappa, Sym2.lift_mk]
  revert hF
  generalize p a = x; generalize p b = y; generalize p c = z
  revert x y z; decide

/-- Every realizable edge function has zero F0 charge. -/
theorem Realizes.charge_eq_zero {f : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) :
    charge p f = 0 := by
  obtain ⟨c, h1, h2, -⟩ := h
  have hP : ∀ s, c s * ∑ e ∈ triEdges s, kappa p e = 0 := by
    intro s
    by_cases hc : c s = 0
    · simp [hc]
    · rw [kappa_tri_sum (h1 s hc), mul_zero]
  calc charge p f = ∑ e, ∑ s, c s * (ind (triEdges s) e * kappa p e) := by
        refine sum_congr rfl fun e _ => ?_
        rw [h2 e, sum_mul]
        exact sum_congr rfl fun s _ => by ring
    _ = ∑ s, ∑ e, c s * (ind (triEdges s) e * kappa p e) := sum_comm
    _ = ∑ s, c s * ∑ e ∈ triEdges s, kappa p e := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_eq_sum_ind (triEdges s) (kappa p), mul_sum]
        exact sum_congr rfl fun e _ => by ring
    _ = 0 := sum_eq_zero fun s _ => hP s

/-! ### From `Realizes (ind P)` to a signed certificate -/

/-- A realization of `ind P` is a signed physical certificate, indexed by the actual F0 copies
with nonzero coefficient. -/
theorem Realizes.signedCert {P : Finset (Sym2 V)} {w : ℤ} (h : Realizes p G (ind P) w) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert p G P t c ∧ certWeight c ≤ w := by
  classical
  obtain ⟨c, h1, h2, h3⟩ := h
  let S : Finset (Finset V) := univ.filter fun s => c s ≠ 0
  refine ⟨S, inferInstance, fun j => j.1, fun j => c j.1, ⟨fun j => h1 _ ?_, fun e => ?_⟩, ?_⟩
  · exact (mem_filter.mp j.2).2
  · rw [h2 e, sum_coe_sort S (fun s => c s * ind (triEdges s) e)]
    rw [sum_filter_of_ne]
    intro s _ hs hc; exact hs (by simp [hc])
  · unfold certWeight
    rw [sum_coe_sort S (fun s => |c s|)]
    refine le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ S) ?_) h3
    intro s _ _; exact abs_nonneg _

end PartitionedTriangleAbsorption.IntegerCertificate

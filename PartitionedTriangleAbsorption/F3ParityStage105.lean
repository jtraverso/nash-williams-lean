/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownStage105
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # Stage105: parity of outer stars from integral divisibility

For `F3`, every vertex degree of an integrally divisible loopless edge set is even.
Consequently the parity premise of the one-level cover-down is DERIVED from the
divisibility of the actual remaining edge set, not assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

theorem F3_typeDegVec_sum : ∀ τ ∈ F3, ∀ a : Fin 4, a ∈ τ → ∑ i, typeDegVec τ a i = 2 := by
  decide

theorem sum_degContrib (p : V → Fin 4) (v : V) {e : Sym2 V} (he : ¬ e.IsDiag) :
    ∑ i, degContrib p v e i = if v ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := fun h => he (by simp [h])
  simp only [degContrib, Sym2.lift_mk, sum_add_distrib, ite_and]
  simp only [Sym2.mem_iff]
  by_cases ha : a = v
  · subst ha
    have : b ≠ a := fun h => hab h.symm
    simp [this]
  · by_cases hb : b = v
    · subst hb; simp [ha, Ne.symm ha]
    · simp [ha, hb, Ne.symm ha, Ne.symm hb]

/-- **Even degrees.** Every vertex degree of an integrally `F3`-divisible loopless edge set
is even. -/
theorem even_incidentLoad_of_isIntDiv_F3 (p : V → Fin 4) {E : Finset (Sym2 V)}
    (hE : IsIntDiv p F3 E) (hloop : ∀ e ∈ E, ¬ e.IsDiag) (v : V) :
    Even (incidentLoad E v) := by
  obtain ⟨c, hc⟩ := hE.2 v
  have hL : ∑ i, degVec p E v i = (incidentLoad E v : ℤ) := by
    unfold degVec incidentLoad
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm, sum_congr rfl (fun e he => sum_degContrib p v (hloop e he)), sum_boole]
  have hR : ∑ i, (∑ τ ∈ F3 with p v ∈ τ, c τ • typeDegVec τ (p v)) i =
      2 * ∑ τ ∈ F3 with p v ∈ τ, c τ := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun τ hτ => ?_
    obtain ⟨hτF, hvτ⟩ := mem_filter.mp hτ
    rw [← mul_sum, F3_typeDegVec_sum τ hτF (p v) hvτ, mul_comm]
  have := hL.symm.trans ((congrArg (fun f => ∑ i, f i) hc).trans hR)
  have h2 : Even (incidentLoad E v : ℤ) := ⟨_, this.trans (two_mul _)⟩
  exact_mod_cast h2

end PartitionedTriangleAbsorption.CoverDownStage105

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- **One vortex level on an actual divisible remaining edge set.**
`E` is the current actual remaining edge set (integrally `F3`-divisible), `P` an actual
packing inside `E` with no edge inside `U` (e.g. a nibble packing of the non-protected
part), `R1, T2` the reserve fixed before `P`. The leftover `H` is exactly the rest of the
non-protected part. Parity is DERIVED. Output: an actual packing `Q` such that the new
remaining set `E \ (P ∪ Q)` lies inside `U`, is integrally divisible, and the new
internal edges have charged loads. -/
theorem cover_down_level (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ a b, s(a, b) ∈ E → p a ≠ p b) (hE : IsIntDiv p F3 E) (U : Finset V)
    (P H R1 B : Finset (Sym2 V)) (T2 : Finset (V × V × V)) (h m lam a1 a2 : ℕ)
    (hPE : P ⊆ E) (hP : HasDecomp p F3 P) (hPU : ∀ e ∈ P, ¬ IsInner U e)
    (hHE : H ⊆ E) (hHU : ∀ e ∈ H, ¬ IsInner U e)
    (hHcover : ∀ e ∈ E, e ∉ P → e ∉ R1 → e ∉ resEdges T2 → ¬ IsInner U e → e ∈ H)
    (hR1E : R1 ⊆ E) (hR1 : ∀ e ∈ R1, IsSpoke U e)
    (hT2 : ∀ r ∈ T2, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hT2disj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri)
    (hPH : Disjoint P (H ∪ R1 ∪ resEdges T2)) (hHRT : Disjoint (H ∪ R1) (resEdges T2))
    (hB : Disjoint B (H ∪ R1 ∪ resEdges T2))
    (hdegH : ∀ v, v ∉ U → incidentLoad H v ≤ h)
    (hrich1 : ∀ x y, s(x, y) ∈ H → x ∉ U → y ∉ U →
      a1 ≤ (U.filter fun z => s(x, z) ∈ R1 ∧ s(y, z) ∈ R1).card)
    (hb1 : 2 * h ≤ a1)
    (hdegM : ∀ x, x ∉ U → incidentLoad (H ∪ R1) x ≤ m)
    (hrich2 : ∀ x, x ∉ U → ∀ y₁ y₂, y₁ ≠ y₂ → s(x, y₁) ∈ H ∪ R1 → s(x, y₂) ∈ H ∪ R1 →
      y₁ ∈ U → y₂ ∈ U →
      a2 ≤ (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ E ∧ s(r.2.2, y₂) ∈ E ∧
        s(y₁, r.2.1) ∉ B ∪ resEdges T2 ∧ s(r.2.2, y₂) ∉ B ∪ resEdges T2).card)
    (hlam : ∀ y ∈ U, incidentLoad (H ∪ R1) y + incidentLoad (resEdges T2) y ≤ lam)
    (hb2 : m + 4 * lam ≤ 2 * a2) :
    ∃ Q : Finset (Sym2 V), Q ⊆ E ∧ Disjoint P Q ∧ HasDecomp p F3 (P ∪ Q) ∧ Disjoint Q B ∧
      (∀ e ∈ E \ (P ∪ Q), IsInner U e) ∧ IsIntDiv p F3 (E \ (P ∪ Q)) ∧
      (∀ e ∈ Q \ (H ∪ R1 ∪ resEdges T2), IsInner U e) ∧
      ∀ w, incidentLoad (Q \ (H ∪ R1 ∪ resEdges T2)) w ≤
        incidentLoad (H ∪ R1) w + incidentLoad (resEdges T2) w := by
  have hloop : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      intro hd
      have hab : a = b := Sym2.mk_isDiag_iff.mp hd
      subst hab
      exact hcross a a he rfl
  have hT2E : resEdges T2 ⊆ E := by
    intro e he
    obtain ⟨r, hr, her⟩ := mem_biUnion.mp he
    exact (hT2 r hr).2.2.2 her
  -- parity of the outer stars, derived from divisibility
  have hpar : ∀ x, x ∉ U → Even (incidentLoad (H ∪ R1) x) := by
    intro x hx
    have hEP := isIntDiv_sdiff_of_hasDecomp hE hP hPE
    have hevW := even_incidentLoad_of_isIntDiv_F3 p hEP
      (fun e he => hloop e (mem_sdiff.mp he).1) x
    have hT2dec : HasDecomp p F3 (resEdges T2) :=
      RefinerAssembly.hasDecomp_biUnion _ _
        (fun r hr => hasDecomp_resTri p E hcross (hT2 r hr).2.2.2) hT2disj
    have hevT := even_incidentLoad_of_isIntDiv_F3 p (isIntDiv_of_hasDecomp hT2dec)
      (fun e he => hloop e (hT2E he)) x
    have hTW : resEdges T2 ⊆ E \ P := by
      intro e he
      exact mem_sdiff.mpr ⟨hT2E he, fun hp =>
        disjoint_left.mp hPH hp (mem_union_right _ he)⟩
    have hsplit := incidentLoad_sdiff_add hTW x
    have hfilter : ((E \ P) \ resEdges T2).filter (fun e => x ∈ e) =
        (H ∪ R1).filter (fun e => x ∈ e) := by
      ext e
      simp only [mem_filter, mem_sdiff, mem_union]
      constructor
      · rintro ⟨⟨⟨heE, heP⟩, heT⟩, hxe⟩
        refine ⟨?_, hxe⟩
        by_cases heR : e ∈ R1
        · exact Or.inr heR
        · exact Or.inl (hHcover e heE heP heR heT (fun hin => hx (hin x hxe)))
      · rintro ⟨heHR, hxe⟩
        have heE : e ∈ E := by rcases heHR with h' | h'; exacts [hHE h', hR1E h']
        refine ⟨⟨⟨heE, fun hp => disjoint_left.mp hPH hp ?_⟩, fun ht =>
          disjoint_left.mp hHRT (mem_union.mpr heHR) ht⟩, hxe⟩
        rcases heHR with h' | h'
        · exact mem_union_left _ (mem_union_left _ h')
        · exact mem_union_left _ (mem_union_right _ h')
    have hL : incidentLoad ((E \ P) \ resEdges T2) x = incidentLoad (H ∪ R1) x := by
      unfold incidentLoad; rw [hfilter]
    rw [hL] at hsplit
    rw [Nat.even_iff] at hevW hevT ⊢
    omega
  obtain ⟨Q, hQE, hQdec, hQB, hHRQ, hTin, hnewin, hload⟩ :=
    one_level_cover_down p E hcross U H R1 B T2 h m lam a1 a2 hHE
      (fun e he => by
        have := hHU e he
        unfold IsInner at this
        push Not at this
        exact this)
      hR1E hR1 hT2 hT2disj hHRT hB hpar hdegH hrich1 hb1 hdegM hrich2 hlam hb2
  have hPQ : Disjoint P Q := by
    rw [disjoint_left]
    intro e heP heQ
    by_cases hold : e ∈ H ∪ R1 ∪ resEdges T2
    · exact disjoint_left.mp hPH heP hold
    · exact hPU e heP (hnewin e (mem_sdiff.mpr ⟨heQ, hold⟩))
  have hPQE : P ∪ Q ⊆ E := union_subset hPE hQE
  have hdec := hP.union hQdec hPQ
  refine ⟨Q, hQE, hPQ, hdec, hQB, ?_, isIntDiv_sdiff_of_hasDecomp hE hdec hPQE, hnewin, hload⟩
  intro e he
  obtain ⟨heE, hePQ⟩ := mem_sdiff.mp he
  simp only [mem_union, not_or] at hePQ
  by_contra hin
  by_cases heR : e ∈ R1
  · exact hePQ.2 (hHRQ (mem_union_right _ heR))
  by_cases heT : e ∈ resEdges T2
  · exact hin (hTin e (mem_sdiff.mpr ⟨heT, hePQ.2⟩))
  exact hePQ.2 (hHRQ (mem_union_left _ (hHcover e heE hePQ.1 heR heT hin)))

end PartitionedTriangleAbsorption.CoverDownStage105

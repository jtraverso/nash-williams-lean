/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownInnerStage105
public import PartitionedTriangleAbsorption.CoverDownPairingInductionStage105

/-! # Stage105: a physical one-level cover-down for F3

Host: an edge set `E` all of whose edges join distinct classes of `p : V → Fin 4`.
Data fixed BEFORE the leftover is known: the next vortex set `U`, reserve spokes
`R1` and edge-disjoint reserve triples `T2` (each an actual triangle `x z z'`
with `x ∉ U`, `z, z' ∈ U`). The leftover `H` (e.g. a nibble leftover) has no
edge inside `U`.

Conclusion: an actual packing `Q ⊆ E` avoiding the forbidden `B` that covers
ALL of `H ∪ R1`; uncovered reserve edges and all newly used edges lie inside `U`;
new edges are charged vertex by vertex. The only premises are explicit
inequalities: parity of the outer stars, leftover degree `h`, two-root reserve
richness `a1 ≥ 2h`, pair richness `a2` counted through edges outside `B` and the
reserve, the star bound `m`, the dynamic load `λ`, and `m + 4λ ≤ 2 a2`.
The forbidden set `B` may be dense (e.g. all edges inside the next-but-one
vortex set): it only enters through the richness count.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- **Pairing step, from scratch.** -/
theorem pairing_cover {p : V → Fin 4} {E : Finset (Sym2 V)} {U : Finset V}
    {T2 : Finset (V × V × V)} {B0 M0 : Finset (Sym2 V)} {m lam a2 : ℕ}
    (hD : PairingData p E U T2 B0 M0 m lam a2)
    (hpar : ∀ x, x ∉ U → Even (incidentLoad M0 x)) :
    ∃ A ⊆ T2, ∃ I : Finset (Sym2 V), I ⊆ E ∧ (∀ e ∈ I, IsInner U e) ∧ Disjoint I B0 ∧
      (∀ w, incidentLoad I w ≤ incidentLoad M0 w + incidentLoad (spokesOf A) w) ∧
      HasDecomp p F3 (M0 ∪ spokesOf A ∪ I) := by
  have h0 : PairingInv E U T2 B0 M0 M0 ∅ ∅ := by
    refine ⟨subset_rfl, empty_subset _, hpar, ?_, ?_, empty_subset _, by simp, by simp⟩
    · intro x _; simp
    · intro w; simp [OnePart.incidentLoad_empty]
  obtain ⟨A, I, -, -, hinv, hdec⟩ := pairing_aux hD _ M0 ∅ ∅ rfl h0
  refine ⟨A, hinv.resA, I, hinv.inE, hinv.inner, hinv.avoid, fun w => ?_, by simpa using hdec⟩
  have := hinv.load w
  rw [OnePart.incidentLoad_empty] at this
  omega

omit [DecidableEq V] in
theorem not_inner_of_outer {U : Finset V} {e : Sym2 V} (h : ∀ v ∈ e, v ∉ U) :
    ¬ IsInner U e := by
  induction e using Sym2.ind with
  | _ a b => exact fun hin => h a (Sym2.mem_mk_left a b) (hin a (Sym2.mem_mk_left a b))

/-- **One-level physical cover-down (F3).** -/
theorem one_level_cover_down (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ a b, s(a, b) ∈ E → p a ≠ p b) (U : Finset V)
    (H R1 B : Finset (Sym2 V)) (T2 : Finset (V × V × V)) (h m lam a1 a2 : ℕ)
    (hHE : H ⊆ E) (hHU : ∀ e ∈ H, ∃ v ∈ e, v ∉ U)
    (hR1E : R1 ⊆ E) (hR1 : ∀ e ∈ R1, IsSpoke U e)
    (hT2 : ∀ r ∈ T2, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hT2disj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri)
    (hHRT : Disjoint (H ∪ R1) (resEdges T2))
    (hB : Disjoint B (H ∪ R1 ∪ resEdges T2))
    (hpar : ∀ x, x ∉ U → Even (incidentLoad (H ∪ R1) x))
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
    ∃ Q : Finset (Sym2 V), Q ⊆ E ∧ HasDecomp p F3 Q ∧ Disjoint Q B ∧ H ∪ R1 ⊆ Q ∧
      (∀ e ∈ resEdges T2 \ Q, IsInner U e) ∧
      (∀ e ∈ Q \ (H ∪ R1 ∪ resEdges T2), IsInner U e) ∧
      ∀ w, incidentLoad (Q \ (H ∪ R1 ∪ resEdges T2)) w ≤
        incidentLoad (H ∪ R1) w + incidentLoad (resEdges T2) w := by
  classical
  set H1 := H.filter (fun e => ∀ v ∈ e, v ∉ U) with hH1def
  have hH1H : H1 ⊆ H := filter_subset _ _
  have hH1out : ∀ x y, s(x, y) ∈ H1 → x ∉ U ∧ y ∉ U := by
    intro x y hxy
    have := (mem_filter.mp hxy).2
    exact ⟨this x (Sym2.mem_mk_left x y), this y (Sym2.mem_mk_right x y)⟩
  obtain ⟨S, hSR, hdec1, hloadS⟩ := inner_cover p E hcross U H1 R1 h a1
    (hH1H.trans hHE) hR1E hH1out hR1
    (fun v hv => (incidentLoad_mono hH1H v).trans (hdegH v hv))
    (fun x y hxy => hrich1 x y (hH1H hxy) (hH1out x y hxy).1 (hH1out x y hxy).2) hb1
  have hP1 : H1 ∪ S ⊆ H ∪ R1 := union_subset_union hH1H hSR
  set M0 := (H ∪ R1) \ (H1 ∪ S) with hM0def
  have hM0sub : M0 ⊆ H ∪ R1 := sdiff_subset
  have hM0spoke : ∀ e ∈ M0, IsSpoke U e := by
    intro e he
    obtain ⟨heHR, heP⟩ := mem_sdiff.mp he
    rcases mem_union.mp heHR with heH | heR
    · obtain ⟨v, hve, hvU⟩ := hHU e heH
      have hnot : ¬ ∀ v ∈ e, v ∉ U := fun hall =>
        heP (mem_union_left _ (mem_filter.mpr ⟨heH, hall⟩))
      push Not at hnot
      obtain ⟨u, hue, huU⟩ := hnot
      induction e using Sym2.ind with
      | _ a b =>
      rcases Sym2.mem_iff.mp hve with rfl | rfl <;>
        rcases Sym2.mem_iff.mp hue with rfl | rfl
      · exact absurd huU hvU
      · exact ⟨v, u, hvU, huU, rfl⟩
      · exact ⟨v, u, hvU, huU, Sym2.eq_swap⟩
      · exact absurd huU hvU
    · exact hR1 e heR
  have hSspoke : ∀ e ∈ S, IsSpoke U e := fun e he => hR1 e (hSR he)
  have hH1S : Disjoint H1 S := by
    rw [disjoint_left]
    intro e he heS
    obtain ⟨a, b, -, hb, rfl⟩ := hSspoke e heS
    exact (hH1out a b he).2 hb
  have hparM0 : ∀ x, x ∉ U → Even (incidentLoad M0 x) := by
    intro x hx
    have h1 := incidentLoad_sdiff_add hP1 x
    rw [OnePart.incidentLoad_union hH1S, hloadS x hx, ← hM0def] at h1
    have h2 := hpar x hx
    rw [Nat.even_iff] at h2 ⊢
    omega
  set B0 := B ∪ resEdges T2 with hB0def
  have hD : PairingData p E U T2 B0 M0 m lam a2 := by
    refine ⟨hcross, hT2, hT2disj, hM0sub.trans (union_subset hHE hR1E), hM0spoke,
      hHRT.mono_left hM0sub, subset_union_right, ?_, ?_, ?_, hb2⟩
    · intro x hx y₁ y₂ hne h1 h2
      obtain ⟨u1, hu1, he1⟩ := spoke_eq_of_mem hx (hM0spoke _ h1) (Sym2.mem_mk_left _ _)
      obtain ⟨u2, hu2, he2⟩ := spoke_eq_of_mem hx (hM0spoke _ h2) (Sym2.mem_mk_left _ _)
      have hy1 : y₁ = u1 := by
        rcases Sym2.eq_iff.mp he1 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (h ▸ hu1) hx
      have hy2 : y₂ = u2 := by
        rcases Sym2.eq_iff.mp he2 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd (h ▸ hu2) hx
      subst hy1 hy2
      rw [hB0def]
      exact hrich2 x hx y₁ y₂ hne (hM0sub h1) (hM0sub h2) hu1 hu2
    · exact fun x hx => (incidentLoad_mono hM0sub x).trans (hdegM x hx)
    · intro y hy
      have h2 := incidentLoad_mono hM0sub y
      have h3 := hlam y hy
      omega
  obtain ⟨A, hAT, I, hIE, hIin, hIB0, hIload, hdec2⟩ := pairing_cover hD hparM0
  have hspA : spokesOf A ⊆ resEdges T2 := spokesOf_subset_resEdges hAT
  have hdec3 : HasDecomp p F3 (resEdges (T2 \ A)) :=
    RefinerAssembly.hasDecomp_biUnion _ _
      (fun r hr => hasDecomp_resTri p E hcross (hT2 r (mem_sdiff.mp hr).1).2.2.2)
      (hT2disj.subset (by intro r hr; exact (mem_sdiff.mp hr).1))
  have hP3 : resEdges (T2 \ A) ⊆ resEdges T2 := resEdges_mono sdiff_subset
  have hIT : Disjoint I (resEdges T2) := hIB0.mono_right subset_union_right
  have hIHR : Disjoint I (H ∪ R1) := by
    rw [disjoint_left]
    intro e heI heHR
    rcases mem_union.mp heHR with heH | heR
    · obtain ⟨v, hve, hvU⟩ := hHU e heH
      exact hvU (hIin e heI v hve)
    · exact spoke_not_inner (hR1 e heR) (hIin e heI)
  have d12 : Disjoint (H1 ∪ S) (M0 ∪ spokesOf A ∪ I) := by
    refine disjoint_union_right.mpr ⟨disjoint_union_right.mpr ⟨?_, ?_⟩, ?_⟩
    · exact disjoint_sdiff
    · exact (hHRT.mono hP1 hspA)
    · exact (hIHR.mono_right hP1).symm
  have d3 : Disjoint ((H1 ∪ S) ∪ (M0 ∪ spokesOf A ∪ I)) (resEdges (T2 \ A)) := by
    refine disjoint_union_left.mpr ⟨hHRT.mono hP1 hP3, disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hHRT.mono hM0sub hP3, ?_⟩, hIT.mono_right hP3⟩⟩
    rw [disjoint_left]
    intro e heA heT
    obtain ⟨r, hrA, her⟩ := mem_biUnion.mp heA
    obtain ⟨q, hq, heq⟩ := mem_biUnion.mp heT
    obtain ⟨hqT, hqA⟩ := mem_sdiff.mp hq
    have hne : r ≠ q := fun h => hqA (h ▸ hrA)
    exact disjoint_left.mp (hT2disj (hAT hrA) hqT hne) (resSpokes_subset_resTri r her) heq
  set Q := (H1 ∪ S) ∪ (M0 ∪ spokesOf A ∪ I) ∪ resEdges (T2 \ A) with hQdef
  have hT2E : resEdges T2 ⊆ E := by
    intro e he
    obtain ⟨r, hr, her⟩ := mem_biUnion.mp he
    exact (hT2 r hr).2.2.2 her
  have hHRQ : H ∪ R1 ⊆ Q := by
    intro e he
    by_cases hP : e ∈ H1 ∪ S
    · exact mem_union_left _ (mem_union_left _ hP)
    · exact mem_union_left _ (mem_union_right _
        (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨he, hP⟩))))
  have hQnew : Q \ (H ∪ R1 ∪ resEdges T2) ⊆ I := by
    intro e he
    obtain ⟨heQ, hen⟩ := mem_sdiff.mp he
    simp only [mem_union, not_or] at hen
    rcases mem_union.mp heQ with he12 | he3
    · rcases mem_union.mp he12 with he1 | he2
      · exact absurd (hP1 he1) (by simp [hen.1.1, hen.1.2])
      · rcases mem_union.mp he2 with heMS | heI
        · rcases mem_union.mp heMS with heM | heS
          · exact absurd (hM0sub heM) (by simp [hen.1.1, hen.1.2])
          · exact absurd (hspA heS) hen.2
        · exact heI
    · exact absurd (hP3 he3) hen.2
  refine ⟨Q, ?_, ?_, ?_, hHRQ, ?_, ?_, ?_⟩
  · refine union_subset (union_subset (hP1.trans (union_subset hHE hR1E))
      (union_subset (union_subset (hM0sub.trans (union_subset hHE hR1E))
        (hspA.trans hT2E)) hIE)) (hP3.trans hT2E)
  · exact ((hdec1.union hdec2 d12).union hdec3 d3)
  · rw [disjoint_left]
    intro e heQ heB
    have hB' := disjoint_left.mp hB heB
    simp only [mem_union, not_or] at hB'
    rcases mem_union.mp heQ with he12 | he3
    · rcases mem_union.mp he12 with he1 | he2
      · rcases mem_union.mp (hP1 he1) with h' | h'
        exacts [hB'.1.1 h', hB'.1.2 h']
      · rcases mem_union.mp he2 with heMS | heI
        · rcases mem_union.mp heMS with heM | heS
          · rcases mem_union.mp (hM0sub heM) with h' | h'
            exacts [hB'.1.1 h', hB'.1.2 h']
          · exact hB'.2 (hspA heS)
        · exact disjoint_left.mp hIB0 heI (mem_union_left _ heB)
    · exact hB'.2 (hP3 he3)
  · intro e he
    obtain ⟨heT, heQ⟩ := mem_sdiff.mp he
    obtain ⟨r, hr, her⟩ := mem_biUnion.mp heT
    by_cases hrA : r ∈ A
    · simp only [resTri, mem_insert, mem_singleton] at her
      rcases her with rfl | rfl | rfl
      · exact absurd (mem_union_left _ (mem_union_right _ (mem_union_left _
          (mem_union_right _ (mem_biUnion.mpr ⟨r, hrA, by simp [resSpokes]⟩))))) heQ
      · exact absurd (mem_union_left _ (mem_union_right _ (mem_union_left _
          (mem_union_right _ (mem_biUnion.mpr ⟨r, hrA, by simp [resSpokes]⟩))))) heQ
      · intro v hv
        obtain ⟨-, h1, h2, -⟩ := hT2 r hr
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        exacts [h1, h2]
    · exact absurd (mem_union_right _ (mem_biUnion.mpr ⟨r, mem_sdiff.mpr ⟨hr, hrA⟩, her⟩)) heQ
  · exact fun e he => hIin e (hQnew he)
  · intro w
    have h1 := incidentLoad_mono hQnew w
    have h2 := hIload w
    have h3 := incidentLoad_mono hM0sub w
    have h4 := incidentLoad_mono hspA w
    omega

end PartitionedTriangleAbsorption.CoverDownStage105

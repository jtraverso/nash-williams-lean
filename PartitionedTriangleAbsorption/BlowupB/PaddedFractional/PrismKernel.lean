/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ThirdDistributions
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveWindow

/-!
# A bounded physical prism kernel

Two distributions over the third vertex of the same physical edge are
coupled by a separate adaptive prism for each pair of third vertices.
The six host faces preserve their exact difference of boundaries.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def prismChain (a b c d : V) (f : Fin 2 → V) : TriangleChain V := fun Q =>
  triangleBasis {a, f 1, c} Q + triangleBasis {f 0, b, c} Q +
  triangleBasis {f 0, f 1, d} Q - triangleBasis {a, f 1, d} Q -
  triangleBasis {f 0, b, d} Q - triangleBasis {f 0, f 1, c} Q

theorem completingPairs_symm (F : Finset (Multiset (Fin t))) :
    Std.Symm (fun i j => ∃ k, Link F i j k) := by
  constructor
  intro i j h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, (link_root_swap F i j k).mp hk⟩

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
    [DecidableRel G.Adj] {a b : V} {s : ℝ}

theorem prism_lower_of_distributions
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (μ ν : ThirdDistribution p F G a b s) {c d : V}
    (hc : μ.law.mass c ≠ 0) (hd : ν.law.mass d ≠ 0) :
    ChoiceTree.Lower s (prismTree p G a b c d) := by
  have htc : Link F (p a) (p b) (p c) := by
    rw [(μ.support c hc).1]
    exact μ.typed
  have htd : Link F (p a) (p b) (p d) := by
    rw [(ν.support d hd).1]
    exact ν.typed
  apply prismTree_lower p G (fun i j => ∃ k, Link F i j k) (completingPairs_symm F)
    s hs a b c d
  · exact ⟨p c, htc⟩
  · exact ⟨p b, (link_swap F _ _ _).mp htc⟩
  · exact ⟨p b, (link_swap F _ _ _).mp htd⟩
  · exact ⟨p a, (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mp htc)⟩
  · exact ⟨p a, (link_swap F _ _ _).mp ((link_root_swap F _ _ _).mp htd)⟩

theorem prismChain_supported (μ ν : ThirdDistribution p F G a b s) {c d : V}
    (hc : μ.law.mass c ≠ 0) (hd : ν.law.mass d ≠ 0) (f : Fin 2 → V)
    (hf : ChoiceTree.Supports (prismTree p G a b c d) f) :
    CopySupported p F G (prismChain a b c d f) := by
  obtain ⟨hpc, hac, hbc⟩ := μ.support c hc
  obtain ⟨hpd, had, hbd⟩ := ν.support d hd
  have htc : Link F (p a) (p b) (p c) := by simpa only [hpc] using μ.typed
  have htd : Link F (p a) (p b) (p d) := by simpa only [hpd] using ν.typed
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    PrismRealization.host_faces p G (prismTree_realizes p G a b c d f hf)
      F htc htd hac hbc had hbd
  exact (((((triangleBasis_supported p F G h1).add (triangleBasis_supported p F G h2)).add
    (triangleBasis_supported p F G h3)).sub (triangleBasis_supported p F G h4)).sub
    (triangleBasis_supported p F G h5)).sub (triangleBasis_supported p F G h6)

theorem prismChain_boundary (hab : a ≠ b) {c d : V}
    (hac : G.Adj a c) (hbc : G.Adj b c) (had : G.Adj a d) (hbd : G.Adj b d)
    (f : Fin 2 → V) (hf : ChoiceTree.Supports (prismTree p G a b c d) f)
    (e : Sym2 V) :
    boundary (prismChain a b c d f) e =
      boundary (triangleBasis {a, b, c}) e - boundary (triangleBasis {a, b, d}) e := by
  have h := prismTree_realizes p G a b c d f hf
  unfold prismChain
  simp only [boundary_sub, boundary_add,
    boundary_face h.aB.ne hac.ne h.cB.symm.ne,
    boundary_face h.bA.symm.ne h.cA.symm.ne hbc.ne,
    boundary_face h.AB.ne h.dA.symm.ne h.dB.symm.ne,
    boundary_face h.aB.ne had.ne h.dB.symm.ne,
    boundary_face h.bA.symm.ne h.dA.symm.ne hbd.ne,
    boundary_face h.AB.ne h.cA.symm.ne h.cB.symm.ne,
    boundary_face hab hac.ne hbc.ne,
    boundary_face hab had.ne hbd.ne]
  exact (prism_boundary (fun u v => edgeBasis s(u, v) e) a b c d (f 0) (f 1)).symm

noncomputable def prismKernel (μ ν : ThirdDistribution p F G a b s) : TriangleChain V :=
  fun Q => μ.law.average fun c => ν.law.average fun d =>
    ChoiceTree.mean (prismTree p G a b c d) (fun f => prismChain a b c d f Q)

theorem prismKernel_supported (μ ν : ThirdDistribution p F G a b s) :
    CopySupported p F G (prismKernel μ ν) := by
  apply μ.law.copySupported_average
  intro c hc
  apply ν.law.copySupported_average
  intro d hd
  exact CopySupported.mean _ _ (fun f hf => prismChain_supported μ ν hc hd f hf)

theorem prismKernel_boundary (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (hab : a ≠ b) (μ ν : ThirdDistribution p F G a b s) (e : Sym2 V) :
    boundary (prismKernel μ ν) e = boundary μ.chain e - boundary ν.chain e := by
  unfold prismKernel
  rw [μ.law.boundary_average]
  simp_rw [ν.law.boundary_average, boundary_mean]
  rw [μ.chain_boundary, ν.chain_boundary]
  calc
    _ = μ.law.average (fun c => ν.law.average (fun d =>
        boundary (triangleBasis {a, b, c}) e - boundary (triangleBasis {a, b, d}) e)) := by
      apply μ.law.average_congr
      intro c hc
      apply ν.law.average_congr
      intro d hd
      calc
        _ = ChoiceTree.mean (prismTree p G a b c d) (fun _ =>
            boundary (triangleBasis {a, b, c}) e - boundary (triangleBasis {a, b, d}) e) := by
          apply ChoiceTree.mean_congr
          intro f hf
          exact prismChain_boundary hab (μ.support c hc).2.1 (μ.support c hc).2.2
            (ν.support d hd).2.1 (ν.support d hd).2.2 f hf e
        _ = _ := ChoiceTree.mean_const _ s hs0 (prism_lower_of_distributions hs μ ν hc hd) _
    _ = _ := by simp only [FiniteDistribution.average_sub, FiniteDistribution.average_const]

namespace PrismBounds

def memberIndicator (Q : Finset V) (v : V) : ℝ := if v ∈ Q then 1 else 0

omit [Fintype V] [DecidableRel G.Adj] in
theorem memberIndicator_nonneg (Q : Finset V) (v : V) : 0 ≤ memberIndicator Q v := by
  unfold memberIndicator
  split_ifs <;> norm_num

omit [Fintype V] [DecidableRel G.Adj] in
theorem first_basis_bound (T : ChoiceTree V 2) (hs0 : 0 < s)
    (hT : ChoiceTree.Lower s T) (Q : Finset V) (hQ : Q.card ≤ 3) (u v : V) :
    |ChoiceTree.mean T (fun f => triangleBasis {f 0, u, v} Q)| ≤
      memberIndicator Q u * memberIndicator Q v * (3 / s) := by
  classical
  have hc : 0 ≤ memberIndicator Q u * memberIndicator Q v :=
    mul_nonneg (memberIndicator_nonneg Q u) (memberIndicator_nonneg Q v)
  have hh := ChoiceTree.mean_window_bound Q T (.selected (.any .nil)) s 3 hs0
    (by norm_num) hT (by exact_mod_cast hQ)
    (fun f => triangleBasis {f 0, u, v} Q)
    (memberIndicator Q u * memberIndicator Q v) hc (by
      intro f _
      rw [abs_triangleBasis]
      by_cases he : Q = ({f 0, u, v} : Finset V)
      · simp [he, triangleBasis, memberIndicator, SelectionMask.Accepts]
      · rw [triangleBasis_eq_zero _ _ he]
        exact mul_nonneg hc (by split_ifs <;> norm_num))
  simpa only [SelectionMask.count, Nat.zero_add, pow_one] using hh

omit [Fintype V] [DecidableRel G.Adj] in
theorem second_basis_bound (T : ChoiceTree V 2) (hs0 : 0 < s)
    (hT : ChoiceTree.Lower s T) (Q : Finset V) (hQ : Q.card ≤ 3) (u v : V) :
    |ChoiceTree.mean T (fun f => triangleBasis {u, f 1, v} Q)| ≤
      memberIndicator Q u * memberIndicator Q v * (3 / s) := by
  classical
  have hc : 0 ≤ memberIndicator Q u * memberIndicator Q v :=
    mul_nonneg (memberIndicator_nonneg Q u) (memberIndicator_nonneg Q v)
  have hh := ChoiceTree.mean_window_bound Q T (.any (.selected .nil)) s 3 hs0
    (by norm_num) hT (by exact_mod_cast hQ)
    (fun f => triangleBasis {u, f 1, v} Q)
    (memberIndicator Q u * memberIndicator Q v) hc (by
      intro f _
      rw [abs_triangleBasis]
      by_cases he : Q = ({u, f 1, v} : Finset V)
      · simp [he, triangleBasis, memberIndicator, SelectionMask.Accepts]
      · rw [triangleBasis_eq_zero _ _ he]
        exact mul_nonneg hc (by split_ifs <;> norm_num))
  simpa only [SelectionMask.count, Nat.zero_add, pow_one] using hh

omit [Fintype V] [DecidableRel G.Adj] in
theorem both_basis_bound (T : ChoiceTree V 2) (hs0 : 0 < s)
    (hT : ChoiceTree.Lower s T) (Q : Finset V) (hQ : Q.card ≤ 3) (u : V) :
    |ChoiceTree.mean T (fun f => triangleBasis {f 0, f 1, u} Q)| ≤
      memberIndicator Q u * (3 / s) ^ 2 := by
  classical
  have hc : 0 ≤ memberIndicator Q u := memberIndicator_nonneg Q u
  have hh := ChoiceTree.mean_window_bound Q T (.selected (.selected .nil)) s 3 hs0
    (by norm_num) hT (by exact_mod_cast hQ)
    (fun f => triangleBasis {f 0, f 1, u} Q) (memberIndicator Q u) hc (by
      intro f _
      rw [abs_triangleBasis]
      by_cases he : Q = ({f 0, f 1, u} : Finset V)
      · simp [he, triangleBasis, memberIndicator, SelectionMask.Accepts]
      · rw [triangleBasis_eq_zero _ _ he]
        exact mul_nonneg hc (by split_ifs <;> norm_num))
  simpa only [SelectionMask.count] using hh

omit [Fintype V] [DecidableRel G.Adj] in
theorem prismChain_mean_bound (T : ChoiceTree V 2) (hs0 : 0 < s)
    (hT : ChoiceTree.Lower s T) (Q : Finset V) (hQ : Q.card ≤ 3) (a b c d : V) :
    |ChoiceTree.mean T (fun f => prismChain a b c d f Q)| ≤
      ((memberIndicator Q a + memberIndicator Q b) * (3 / s) + (3 / s) ^ 2) *
        (memberIndicator Q c + memberIndicator Q d) := by
  let m1 := ChoiceTree.mean T (fun f => triangleBasis {a, f 1, c} Q)
  let m2 := ChoiceTree.mean T (fun f => triangleBasis {f 0, b, c} Q)
  let m3 := ChoiceTree.mean T (fun f => triangleBasis {f 0, f 1, d} Q)
  let m4 := ChoiceTree.mean T (fun f => triangleBasis {a, f 1, d} Q)
  let m5 := ChoiceTree.mean T (fun f => triangleBasis {f 0, b, d} Q)
  let m6 := ChoiceTree.mean T (fun f => triangleBasis {f 0, f 1, c} Q)
  have hmean : ChoiceTree.mean T (fun f => prismChain a b c d f Q) =
      m1 + m2 + m3 - m4 - m5 - m6 := by
    simp only [prismChain, ChoiceTree.mean_add, ChoiceTree.mean_sub]
    rfl
  have h1 : |m1| ≤ memberIndicator Q a * memberIndicator Q c * (3 / s) :=
    second_basis_bound T hs0 hT Q hQ a c
  have h2 : |m2| ≤ memberIndicator Q b * memberIndicator Q c * (3 / s) :=
    first_basis_bound T hs0 hT Q hQ b c
  have h3 : |m3| ≤ memberIndicator Q d * (3 / s) ^ 2 :=
    both_basis_bound T hs0 hT Q hQ d
  have h4 : |m4| ≤ memberIndicator Q a * memberIndicator Q d * (3 / s) :=
    second_basis_bound T hs0 hT Q hQ a d
  have h5 : |m5| ≤ memberIndicator Q b * memberIndicator Q d * (3 / s) :=
    first_basis_bound T hs0 hT Q hQ b d
  have h6 : |m6| ≤ memberIndicator Q c * (3 / s) ^ 2 :=
    both_basis_bound T hs0 hT Q hQ c
  have htri : |m1 + m2 + m3 - m4 - m5 - m6| ≤
      |m1| + |m2| + |m3| + |m4| + |m5| + |m6| := by
    have h12 := abs_add_le m1 m2
    have h123 := abs_add_le (m1 + m2) m3
    have h1234 : |m1 + m2 + m3 - m4| ≤ |m1 + m2 + m3| + |m4| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (m1 + m2 + m3) (-m4)
    have h12345 : |m1 + m2 + m3 - m4 - m5| ≤ |m1 + m2 + m3 - m4| + |m5| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (m1 + m2 + m3 - m4) (-m5)
    have h123456 : |m1 + m2 + m3 - m4 - m5 - m6| ≤
        |m1 + m2 + m3 - m4 - m5| + |m6| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (m1 + m2 + m3 - m4 - m5) (-m6)
    linarith only [h12, h123, h1234, h12345, h123456]
  rw [hmean]
  calc
    _ ≤ |m1| + |m2| + |m3| + |m4| + |m5| + |m6| := htri
    _ ≤ memberIndicator Q a * memberIndicator Q c * (3 / s) +
        memberIndicator Q b * memberIndicator Q c * (3 / s) +
        memberIndicator Q d * (3 / s) ^ 2 +
        memberIndicator Q a * memberIndicator Q d * (3 / s) +
        memberIndicator Q b * memberIndicator Q d * (3 / s) +
        memberIndicator Q c * (3 / s) ^ 2 := by linarith only [h1, h2, h3, h4, h5, h6]
    _ = _ := by ring

end PrismBounds

/-- Each old root contributes at most two faces requiring one prism image
and one distributed third image; the other two faces require three images. -/
theorem prismKernel_bound (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (μ ν : ThirdDistribution p F G a b s) (Q : Finset V) (hQ : Q.card = 3) :
    |prismKernel μ ν Q| ≤
      2 * ((if a ∈ Q then (1 : ℝ) else 0) + (if b ∈ Q then (1 : ℝ) else 0)) *
        (3 / s) ^ 2 + 2 * (3 / s) ^ 3 := by
  classical
  let R : ℝ := 3 / s
  let w : V → ℝ := PrismBounds.memberIndicator Q
  let C : ℝ := (w a + w b) * R + R ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (add_nonneg (PrismBounds.memberIndicator_nonneg Q a)
      (PrismBounds.memberIndicator_nonneg Q b)) hR) (sq_nonneg R)
  have hμ : μ.law.average w ≤ R := by
    change μ.law.average (fun v => if v ∈ Q then 1 else 0) ≤ 3 / s
    simpa only [hQ, Nat.cast_ofNat] using
      μ.law.average_window Q s hs0 μ.cap
  have hν : ν.law.average w ≤ R := by
    change ν.law.average (fun v => if v ∈ Q then 1 else 0) ≤ 3 / s
    simpa only [hQ, Nat.cast_ofNat] using
      ν.law.average_window Q s hs0 ν.cap
  calc
    _ ≤ μ.law.average (fun c => |ν.law.average (fun d =>
        ChoiceTree.mean (prismTree p G a b c d) (fun f => prismChain a b c d f Q))|) :=
      μ.law.abs_average_le _
    _ ≤ μ.law.average (fun c => ν.law.average (fun d =>
        |ChoiceTree.mean (prismTree p G a b c d) (fun f => prismChain a b c d f Q)|)) := by
      apply μ.law.average_mono
      intro c _
      exact ν.law.abs_average_le _
    _ ≤ μ.law.average (fun c => ν.law.average (fun d => C * (w c + w d))) := by
      apply μ.law.average_mono
      intro c hc
      apply ν.law.average_mono
      intro d hd
      exact PrismBounds.prismChain_mean_bound _ hs0
        (prism_lower_of_distributions hs μ ν hc hd) Q hQ.le a b c d
    _ = C * (μ.law.average w + ν.law.average w) := by
      simp only [FiniteDistribution.average_smul, FiniteDistribution.average_add,
        FiniteDistribution.average_const]
    _ ≤ C * (2 * R) := mul_le_mul_of_nonneg_left (by linarith only [hμ, hν]) hC
    _ = _ := by dsimp [C, R, w, PrismBounds.memberIndicator]; ring

theorem exists_prismKernel (hs0 : 0 < s)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 s)
    (hab : a ≠ b) (μ ν : ThirdDistribution p F G a b s) :
    ∃ k : TriangleChain V, CopySupported p F G k ∧
      (∀ e, boundary k e = boundary μ.chain e - boundary ν.chain e) ∧
      ∀ Q : Finset V, Q.card = 3 → |k Q| ≤
        2 * ((if a ∈ Q then (1 : ℝ) else 0) + (if b ∈ Q then (1 : ℝ) else 0)) *
          (3 / s) ^ 2 + 2 * (3 / s) ^ 3 := by
  exact ⟨prismKernel μ ν, prismKernel_supported μ ν,
    prismKernel_boundary hs0 hs hab μ ν, prismKernel_bound hs0 hs μ ν⟩

#print axioms prismChain_supported
#print axioms prismChain_boundary
#print axioms prismKernel_supported
#print axioms prismKernel_boundary
#print axioms prismKernel_bound
#print axioms exists_prismKernel

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional

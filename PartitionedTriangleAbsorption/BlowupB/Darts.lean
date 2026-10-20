/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PhasedAbsorber

/-! # BlowupB.Darts — phased trail systems from vertex pairings, for every family

A **pairing** of a loopless edge set `P` is, at every vertex `v`, an involution `π v` without
fixed points of the neighbours of `v` in `P`. Following paired edges defines a permutation of the
darts of `P` (`dartNext`); reversing darts conjugates it to its inverse (`rev_zpow`), and no cycle
contains a dart together with its reverse (`not_sameCycle_rev`). Choosing, for every pair of
reverse cycles, the one containing the smaller dart (`Chosen`) gives a trail system using every
edge of `P` exactly once.

`phasedTrail_of_pairing`: if a phase `κD u v` and a centre class `ζ u v` of the darts advance by
`1`, resp. stay constant, along paired edges, darts of phase `0` start in the centre class, and
every two consecutive darts span a type of `F`, then `P` has a phased trail system — hence an
absorber (`phased_private_absorber`). No orientation of `P` has to be given in advance.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv

universe u

section Darts

variable {V : Type u} [Fintype V] [DecidableEq V] {P : Finset (Sym2 V)}

/-- Darts of `P`. -/
abbrev PDart (P : Finset (Sym2 V)) : Type u := {d : V × V // s(d.1, d.2) ∈ P}

/-- A pairing of the edges at every vertex. -/
structure Pairing (P : Finset (Sym2 V)) (π : V → V → V) : Prop where
  mem : ∀ v w, s(v, w) ∈ P → s(v, π v w) ∈ P
  invol : ∀ v w, s(v, w) ∈ P → π v (π v w) = w
  ne : ∀ v w, s(v, w) ∈ P → π v w ≠ w

variable {π : V → V → V}

theorem mem_swap' {u v : V} (h : s(u, v) ∈ P) : s(v, u) ∈ P := by rw [Sym2.eq_swap]; exact h

/-- Successor of a dart: continue along the paired edge. -/
def dartNext (hπ : Pairing P π) : Perm (PDart P) where
  toFun d := ⟨(d.1.2, π d.1.2 d.1.1), hπ.mem _ _ (mem_swap' d.2)⟩
  invFun d := ⟨(π d.1.1 d.1.2, d.1.1), mem_swap' (hπ.mem _ _ d.2)⟩
  left_inv d := by
    obtain ⟨⟨u, v⟩, h⟩ := d
    apply Subtype.ext
    simp only [Prod.mk.injEq, and_true]
    exact hπ.invol _ _ (mem_swap' h)
  right_inv d := by
    obtain ⟨⟨u, v⟩, h⟩ := d
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and]
    exact hπ.invol _ _ h

/-- Reversal of darts. -/
def dartRev (P : Finset (Sym2 V)) : Perm (PDart P) where
  toFun d := ⟨(d.1.2, d.1.1), mem_swap' d.2⟩
  invFun d := ⟨(d.1.2, d.1.1), mem_swap' d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (hπ : Pairing P π)

theorem dartNext_val (d : PDart P) : (dartNext hπ d).1 = (d.1.2, π d.1.2 d.1.1) := rfl

theorem rev_conj : dartRev P * dartNext hπ * (dartRev P)⁻¹ = (dartNext hπ)⁻¹ :=
  Equiv.ext fun _ => rfl

theorem rev_zpow (k : ℤ) (d : PDart P) :
    dartRev P ((dartNext hπ ^ k) d) = (dartNext hπ ^ (-k)) (dartRev P d) := by
  have h := conj_zpow (i := k) (a := dartRev P) (b := dartNext hπ)
  rw [rev_conj, inv_zpow'] at h
  have h2 := congrArg (fun f : Perm (PDart P) => f (dartRev P d)) h
  simp only [Perm.mul_apply] at h2
  exact h2.symm

theorem not_sameCycle_rev (hloop : ∀ e ∈ P, ¬ e.IsDiag) (d : PDart P) :
    ¬ (dartNext hπ).SameCycle d (dartRev P d) := by
  rintro ⟨k, hk⟩
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · have hx : dartRev P ((dartNext hπ ^ m) d) = (dartNext hπ ^ m) d := by
      rw [rev_zpow, ← hk, ← Perm.mul_apply, ← zpow_add, show -m + 2 * m = m by ring]
    have h1 := congrArg Subtype.val hx
    set x := (dartNext hπ ^ m) d
    have h2 : x.1.1 = x.1.2 := (Prod.ext_iff.mp h1).2
    exact hloop _ x.2 (Sym2.mk_isDiag_iff.mpr h2)
  · have hx : dartRev P ((dartNext hπ ^ m) d) = dartNext hπ ((dartNext hπ ^ m) d) := by
      rw [rev_zpow, ← hk, ← Perm.mul_apply, ← zpow_add, show -m + (2 * m + 1) = 1 + m by ring,
        zpow_one_add, Perm.mul_apply]
    have h1 := congrArg Subtype.val hx
    set x := (dartNext hπ ^ m) d
    rw [dartNext_val] at h1
    have h2 : x.1.1 = π x.1.2 x.1.1 := (Prod.ext_iff.mp h1).2
    exact hπ.ne _ _ (mem_swap' x.2) h2.symm

/-- The rank of a dart. -/
noncomputable def dartRank (d : PDart P) : ℕ := (Fintype.equivFin (PDart P) d : ℕ)

theorem dartRank_injective : Function.Injective (dartRank (P := P)) := by
  intro a b h
  exact (Fintype.equivFin (PDart P)).injective (Fin.ext h)

/-- The cycle of `d` contains the dart of smallest rank of the cycles of `d` and of its reverse. -/
def Chosen (d : PDart P) : Prop :=
  ∃ d', (dartNext hπ).SameCycle d d' ∧ ∀ d'', ((dartNext hπ).SameCycle d d'' ∨
    (dartNext hπ).SameCycle (dartRev P d) d'') → dartRank d' ≤ dartRank d''

theorem sameCycle_rev {d d₁ : PDart P} (h : (dartNext hπ).SameCycle d d₁) :
    (dartNext hπ).SameCycle (dartRev P d) (dartRev P d₁) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by rw [← rev_zpow, hk]⟩

theorem chosen_iff_of_sameCycle {d d₁ : PDart P} (h : (dartNext hπ).SameCycle d d₁) :
    Chosen hπ d ↔ Chosen hπ d₁ := by
  have hr := sameCycle_rev hπ h
  constructor
  · rintro ⟨d', h1, h2⟩
    refine ⟨d', h.symm.trans h1, fun d'' hd'' => h2 d'' ?_⟩
    rcases hd'' with h3 | h3
    · exact Or.inl (h.trans h3)
    · exact Or.inr (hr.trans h3)
  · rintro ⟨d', h1, h2⟩
    refine ⟨d', h.trans h1, fun d'' hd'' => h2 d'' ?_⟩
    rcases hd'' with h3 | h3
    · exact Or.inl (h.symm.trans h3)
    · exact Or.inr (hr.symm.trans h3)

theorem rev_rev (d : PDart P) : dartRev P (dartRev P d) = d := rfl

theorem chosen_iff_not_rev (hloop : ∀ e ∈ P, ¬ e.IsDiag) (d : PDart P) :
    Chosen hπ d ↔ ¬ Chosen hπ (dartRev P d) := by
  classical
  constructor
  · rintro ⟨a, ha, hamin⟩ ⟨b, hb, hbmin⟩
    have h1 := hamin b (Or.inr hb)
    have h2 := hbmin a (Or.inr (by rw [rev_rev]; exact ha))
    have hab : a = b := dartRank_injective (le_antisymm h1 h2)
    subst hab
    exact not_sameCycle_rev hπ hloop d (ha.trans hb.symm)
  · intro hn
    set U : Finset (PDart P) := univ.filter fun d'' => (dartNext hπ).SameCycle d d'' ∨
      (dartNext hπ).SameCycle (dartRev P d) d'' with hU
    have hne : U.Nonempty := ⟨d, mem_filter.mpr ⟨mem_univ _, Or.inl (Perm.SameCycle.refl _ _)⟩⟩
    obtain ⟨m, hm, hmin⟩ := exists_min_image U dartRank hne
    have hmin' : ∀ d'', ((dartNext hπ).SameCycle d d'' ∨
        (dartNext hπ).SameCycle (dartRev P d) d'') → dartRank m ≤ dartRank d'' :=
      fun d'' h => hmin d'' (mem_filter.mpr ⟨mem_univ _, h⟩)
    rcases (mem_filter.mp hm).2 with h | h
    · exact ⟨m, h, hmin'⟩
    · refine absurd ⟨m, h, fun d'' hd'' => hmin' d'' ?_⟩ hn
      rcases hd'' with h3 | h3
      · exact Or.inr h3
      · exact Or.inl (by rw [rev_rev] at h3; exact h3)

end Darts

/-- **Phased trail systems from a pairing.** -/
theorem phasedTrail_of_pairing {t : ℕ} {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 V)} {π : V → V → V}
    (hloop : ∀ e ∈ P, ¬ e.IsDiag) (hπ : Pairing P π)
    (κD : V → V → Fin 3) (hκD : ∀ u v, s(u, v) ∈ P → κD v (π v u) = κD u v + 1)
    (ζ : V → V → Fin t) (hζ : ∀ u v, s(u, v) ∈ P → ζ v (π v u) = ζ u v)
    (hcen : ∀ u v, s(u, v) ∈ P → κD u v = 0 → p u = ζ u v)
    (htrip : ∀ u v, s(u, v) ∈ P → ({p u, p v, p (π v u)} : Multiset (Fin t)) ∈ F) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I), Nonempty (PhasedTrail p F P I) := by
  classical
  set N := dartNext hπ with hN
  have hpres : ∀ d, Chosen hπ (N d) ↔ Chosen hπ d := fun d =>
    (chosen_iff_of_sameCycle hπ (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl N d))).symm
  set σ : Perm {d : PDart P // Chosen hπ d} := N.subtypePerm hpres with hσ
  have hσv : ∀ i, (σ i).1 = N i.1 := fun _ => rfl
  -- ζ is invariant along the dart permutation
  have hζN : ∀ d : PDart P, ζ (N d).1.1 (N d).1.2 = ζ d.1.1 d.1.2 := fun d =>
    hζ d.1.1 d.1.2 d.2
  have hζpow : ∀ (k : ℤ) (d : PDart P), ζ ((N ^ k) d).1.1 ((N ^ k) d).1.2 = ζ d.1.1 d.1.2 := by
    intro k
    induction k using Int.induction_on with
    | zero => intro d; rfl
    | succ n ih =>
      intro d
      rw [zpow_add_one, Perm.mul_apply, ih (N d), hζN]
    | pred n ih =>
      intro d
      have h := ih ((N ^ (-1 : ℤ)) d)
      rw [← Perm.mul_apply, ← zpow_add, show -(n : ℤ) + (-1) = -(n : ℤ) - 1 by ring] at h
      rw [h]
      have h2 := hζN ((N ^ (-1 : ℤ)) d)
      rw [← Perm.mul_apply, ← zpow_one_add, show (1 : ℤ) + -1 = 0 by ring, zpow_zero,
        Perm.one_apply] at h2
      exact h2.symm
  refine ⟨{d : PDart P // Chosen hπ d}, inferInstance, inferInstance, ⟨{
    σ := σ
    x := fun i => i.1.1.1
    κ := fun i => κD i.1.1.1 i.1.1.2
    hx := ?_
    hinj := ?_
    hsrc := ?_
    hκ := ?_
    hcen := ?_
    htrip := ?_ }⟩⟩
  · intro i h
    rw [hσv] at h
    exact hloop _ i.1.2 (Sym2.mk_isDiag_iff.mpr h)
  · intro i j h
    simp only [hσv] at h
    change s(i.1.1.1, i.1.1.2) = s(j.1.1.1, j.1.1.2) at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
    · exfalso
      have hrev : i.1 = dartRev P j.1 := Subtype.ext (Prod.ext h1 h2)
      have hi := i.2
      rw [hrev] at hi
      exact (chosen_iff_not_rev hπ hloop j.1).mp j.2 hi
  · ext e
    simp only [srcE, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hσv]
      exact i.1.2
    · intro he
      induction e using Sym2.ind with
      | _ a b =>
        by_cases hc : Chosen hπ (⟨(a, b), he⟩ : PDart P)
        · exact ⟨⟨⟨(a, b), he⟩, hc⟩, by simp only [hσv]; rfl⟩
        · have hc' : Chosen hπ (dartRev P ⟨(a, b), he⟩) :=
            (chosen_iff_not_rev hπ hloop (dartRev P ⟨(a, b), he⟩)).mpr hc
          refine ⟨⟨dartRev P ⟨(a, b), he⟩, hc'⟩, ?_⟩
          simp only [hσv]
          exact Sym2.eq_swap
  · intro i
    rw [hσv]
    exact hκD _ _ i.1.2
  · intro i j hij hi hj
    have hij' : N.SameCycle i.1 j.1 := Perm.sameCycle_subtypePerm.mp hij
    obtain ⟨k, hk⟩ := hij'
    rw [hcen _ _ i.1.2 hi, hcen _ _ j.1.2 hj, ← hk, hζpow]
  · intro i
    simp only [hσv]
    exact htrip _ _ i.1.2

end PartitionedTriangleAbsorption.BlowupB

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Cost
public import PartitionedTriangleAbsorption.TypedTransformerLabels

/-! # BlowupB.OddLinks — admissible transitions from integral divisibility, for every family

The tree's transformer needs, at every root class `r`, a walk of length exactly `3` in the link
of `r` between any two labels (`ThreeStepLinks`). Here only **odd** walks are used.

* `LinkWalk F r n a b`: a walk of length `n` from `a` to `b` in the link of `r`
  (`Link F r a b ↔ {r, a, b} ∈ F`); `OddR`, `EvenR`: odd / even reachability.
* `Balanced F r d`: for every class `a`, the `d`-weight of the classes at even distance from `a`
  equals the weight at odd distance, and the weight of the component of `a` is even.
* `balanced_of_lattice`: every vector of the degree lattice at `r` (Definition 13.5) is balanced.
* `exists_odd_pairing`: a nonnegative balanced vector splits into pairs `e_a + e_b` with an odd
  link walk between `a` and `b`.

Consequence (`exists_odd_pairing_of_isIntDiv`): for **every** family, at every vertex of an
integrally divisible edge set the incident edges can be paired into transitions `a → r → b`
joined by an odd walk in the link of `r`. These are exactly the transitions an odd-length
transformer can realize; for the rainbow type `{0,1,2}` they are the non-reversing transitions.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer

variable {t : ℕ}

/-! ### Walks in a link -/

/-- A walk of length `n` from `a` to `b` in the link of `r`. -/
inductive LinkWalk (F : Finset (Multiset (Fin t))) (r : Fin t) : ℕ → Fin t → Fin t → Prop
  | nil (a : Fin t) : LinkWalk F r 0 a a
  | cons {n : ℕ} {a b c : Fin t} : Link F r a b → LinkWalk F r n b c → LinkWalk F r (n + 1) a c

namespace LinkWalk

variable {F : Finset (Multiset (Fin t))} {r : Fin t}

theorem single {a b : Fin t} (h : Link F r a b) : LinkWalk F r 1 a b := cons h (nil b)

theorem append {m n : ℕ} {a b c : Fin t} (h₁ : LinkWalk F r m a b) (h₂ : LinkWalk F r n b c) :
    LinkWalk F r (m + n) a c := by
  induction h₁ with
  | nil _ => simpa using h₂
  | @cons k a' b' c' hl _ ih =>
    have := cons hl (ih h₂)
    rwa [show k + n + 1 = k + 1 + n by omega] at this

theorem reverse {n : ℕ} {a b : Fin t} (h : LinkWalk F r n a b) : LinkWalk F r n b a := by
  induction h with
  | nil a => exact nil a
  | @cons k a' b' c' hl _ ih => exact ih.append (single ((link_swap F r a' b').mp hl))

end LinkWalk

/-- `a` and `b` are joined by an odd walk in the link of `r`. -/
def OddR (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ∃ n, LinkWalk F r (2 * n + 1) a b

/-- `a` and `b` are joined by an even walk in the link of `r`. -/
def EvenR (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ∃ n, LinkWalk F r (2 * n) a b

section Reach

variable {F : Finset (Multiset (Fin t))} {r : Fin t} {a b c : Fin t}

theorem evenR_refl (a : Fin t) : EvenR F r a a := ⟨0, LinkWalk.nil a⟩

theorem oddR_of_link (h : Link F r a b) : OddR F r a b := ⟨0, LinkWalk.single h⟩

theorem OddR.symm (h : OddR F r a b) : OddR F r b a := by
  obtain ⟨n, w⟩ := h; exact ⟨n, w.reverse⟩

theorem EvenR.symm (h : EvenR F r a b) : EvenR F r b a := by
  obtain ⟨n, w⟩ := h; exact ⟨n, w.reverse⟩

theorem EvenR.trans_odd (h₁ : EvenR F r a b) (h₂ : OddR F r b c) : OddR F r a c := by
  obtain ⟨m, w₁⟩ := h₁; obtain ⟨n, w₂⟩ := h₂
  exact ⟨m + n, by have := w₁.append w₂; rwa [show 2 * m + (2 * n + 1) = 2 * (m + n) + 1 by omega] at this⟩

theorem OddR.trans_even (h₁ : OddR F r a b) (h₂ : EvenR F r b c) : OddR F r a c := by
  obtain ⟨m, w₁⟩ := h₁; obtain ⟨n, w₂⟩ := h₂
  exact ⟨m + n, by have := w₁.append w₂; rwa [show 2 * m + 1 + 2 * n = 2 * (m + n) + 1 by omega] at this⟩

theorem OddR.trans_odd (h₁ : OddR F r a b) (h₂ : OddR F r b c) : EvenR F r a c := by
  obtain ⟨m, w₁⟩ := h₁; obtain ⟨n, w₂⟩ := h₂
  exact ⟨m + n + 1, by have := w₁.append w₂; rwa [show 2 * m + 1 + (2 * n + 1) = 2 * (m + n + 1) by omega] at this⟩

theorem EvenR.trans_even (h₁ : EvenR F r a b) (h₂ : EvenR F r b c) : EvenR F r a c := by
  obtain ⟨m, w₁⟩ := h₁; obtain ⟨n, w₂⟩ := h₂
  exact ⟨m + n, by have := w₁.append w₂; rwa [show 2 * m + 2 * n = 2 * (m + n) by omega] at this⟩

/-- Across an odd pair, even and odd reachability are exchanged. -/
theorem evenR_iff_oddR_of_oddR (h : OddR F r a b) (c : Fin t) :
    EvenR F r c a ↔ OddR F r c b :=
  ⟨fun h' => h'.trans_odd h, fun h' => h'.trans_odd h.symm⟩

theorem oddR_iff_evenR_of_oddR (h : OddR F r a b) (c : Fin t) :
    OddR F r c a ↔ EvenR F r c b :=
  ⟨fun h' => h'.trans_odd h, fun h' => h'.trans_odd h.symm⟩

end Reach

/-! ### The balance invariants -/

open Classical in
/-- Weight at even distance from `a`. -/
noncomputable def evSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (EvenR F r a), d b

open Classical in
/-- Weight at odd distance from `a`. -/
noncomputable def odSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (OddR F r a), d b

open Classical in
/-- Weight of the link component of `a`. -/
noncomputable def compSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (fun b => EvenR F r a b ∨ OddR F r a b), d b

/-- The balance invariants of a vector at the root `r`. -/
def Balanced (F : Finset (Multiset (Fin t))) (r : Fin t) (d : Fin t → ℤ) : Prop :=
  ∀ a, evSum F r a d = odSum F r a d ∧ Even (compSum F r a d)

/-- The vector `e_a + e_b`. -/
def pairVecZ (a b : Fin t) : Fin t → ℤ := fun i => (if a = i then 1 else 0) + (if b = i then 1 else 0)

section Balance

variable {F : Finset (Multiset (Fin t))} {r : Fin t}

theorem sum_filter_pairVecZ (S : Finset (Fin t)) (a b : Fin t) :
    ∑ i ∈ S, pairVecZ a b i = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  simp only [pairVecZ, sum_add_distrib, Finset.sum_ite_eq]

theorem balanced_pair {a b : Fin t} (h : OddR F r a b) : Balanced F r (pairVecZ a b) := by
  classical
  intro c
  have e1 := evenR_iff_oddR_of_oddR h c
  have e2 := oddR_iff_evenR_of_oddR h c
  constructor
  · unfold evSum odSum
    rw [sum_filter_pairVecZ, sum_filter_pairVecZ]
    simp only [mem_filter, mem_univ, true_and]
    have h3 : OddR F r c a ↔ EvenR F r c b := e2
    have h4 : OddR F r c b ↔ EvenR F r c a := e1.symm
    simp only [h3, h4]
    exact add_comm _ _
  · unfold compSum
    rw [sum_filter_pairVecZ]
    simp only [mem_filter, mem_univ, true_and]
    have hiff : (EvenR F r c a ∨ OddR F r c a) ↔ (EvenR F r c b ∨ OddR F r c b) := by
      rw [e1, e2]; tauto
    by_cases hc : EvenR F r c a ∨ OddR F r c a
    · rw [if_pos hc, if_pos (hiff.mp hc)]; exact ⟨1, rfl⟩
    · rw [if_neg hc, if_neg (fun h' => hc (hiff.mpr h'))]; exact ⟨0, rfl⟩

theorem Balanced.zero : Balanced F r 0 := by
  intro a
  simp [evSum, odSum, compSum]

theorem Balanced.add {d₁ d₂ : Fin t → ℤ} (h₁ : Balanced F r d₁) (h₂ : Balanced F r d₂) :
    Balanced F r (d₁ + d₂) := by
  intro a
  obtain ⟨h₁a, h₁b⟩ := h₁ a
  obtain ⟨h₂a, h₂b⟩ := h₂ a
  refine ⟨?_, ?_⟩
  · simp only [evSum, odSum, Pi.add_apply, sum_add_distrib] at *
    rw [h₁a, h₂a]
  · simp only [compSum, Pi.add_apply, sum_add_distrib] at *
    exact h₁b.add h₂b

theorem Balanced.smul {d : Fin t → ℤ} (h : Balanced F r d) (k : ℤ) : Balanced F r (k • d) := by
  intro a
  obtain ⟨ha, hb⟩ := h a
  refine ⟨?_, ?_⟩
  · simp only [evSum, odSum, Pi.smul_apply, smul_eq_mul, ← mul_sum] at *
    rw [ha]
  · simp only [compSum, Pi.smul_apply, smul_eq_mul, ← mul_sum] at *
    exact hb.mul_left k

theorem Balanced.sub {d₁ d₂ : Fin t → ℤ} (h₁ : Balanced F r d₁) (h₂ : Balanced F r d₂) :
    Balanced F r (d₁ - d₂) := by
  have := h₁.add (h₂.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at this

theorem Balanced.sum {ι : Type*} (s : Finset ι) (f : ι → Fin t → ℤ)
    (h : ∀ i ∈ s, Balanced F r (f i)) : Balanced F r (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact Balanced.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem typeDegVec_cons (r a b : Fin t) :
    typeDegVec (r ::ₘ {a, b} : Multiset (Fin t)) r = pairVecZ a b := by
  funext i
  simp only [typeDegVec, pairVecZ, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  by_cases h1 : i = r <;> by_cases h2 : i = a <;> by_cases h3 : i = b <;>
    simp [h1, h2, h3, eq_comm] <;> omega

/-- **Every vector of the degree lattice at `r` is balanced.** -/
theorem balanced_of_lattice (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) {d : Fin t → ℤ}
    {c : Multiset (Fin t) → ℤ} (hd : d = ∑ τ ∈ F with r ∈ τ, c τ • typeDegVec τ r) :
    Balanced F r d := by
  subst hd
  refine Balanced.sum _ _ fun τ hτ => ?_
  obtain ⟨hτF, hrτ⟩ := mem_filter.mp hτ
  obtain ⟨τ', rfl⟩ := Multiset.exists_cons_of_mem hrτ
  have hc : Multiset.card τ' = 2 := by
    have := hF3 _ hτF; rw [Multiset.card_cons] at this; omega
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
  rw [typeDegVec_cons]
  exact (balanced_pair (oddR_of_link (show Link F r a b from hτF))).smul _

end Balance

/-! ### Pairing -/

section Pairing

variable {F : Finset (Multiset (Fin t))} {r : Fin t}

theorem sum_pairVecZ (a b : Fin t) : ∑ i, pairVecZ a b i = 2 := by
  rw [sum_filter_pairVecZ]; simp

/-- **Odd pairing.** A nonnegative balanced vector is a sum of pairs `e_a + e_b` joined by odd
link walks. -/
theorem exists_odd_pairing (d : Fin t → ℤ) (hd0 : ∀ i, 0 ≤ d i) (hb : Balanced F r d) :
    ∃ M : Multiset (Fin t × Fin t), (∀ ab ∈ M, OddR F r ab.1 ab.2) ∧
      d = (M.map fun ab => pairVecZ ab.1 ab.2).sum := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∑ i, d i) = N :=
    ⟨(∑ i, d i).toNat, (Int.toNat_of_nonneg (sum_nonneg fun i _ => hd0 i)).symm⟩
  induction N using Nat.strong_induction_on generalizing d with
  | _ N ih =>
    by_cases hz : ∀ i, d i = 0
    · exact ⟨0, by simp, by funext i; simp [hz i]⟩
    push Not at hz
    obtain ⟨a, ha⟩ := hz
    have ha1 : 1 ≤ d a := lt_of_le_of_ne (hd0 a) (Ne.symm ha)
    -- an odd partner
    have hev : 1 ≤ evSum F r a d := by
      unfold evSum
      exact ha1.trans (single_le_sum (f := d) (fun i _ => hd0 i)
        (mem_filter.mpr ⟨mem_univ _, evenR_refl a⟩))
    have hod : 1 ≤ odSum F r a d := (hb a).1 ▸ hev
    have hpart : ∃ b, OddR F r a b ∧ 1 ≤ d b ∧ (b ≠ a ∨ 2 ≤ d a) := by
      by_contra hno
      push Not at hno
      -- every odd partner other than `a` has weight `0`, and `d a ≤ 1` if `a` is one
      have hpos : ∃ b ∈ univ.filter (OddR F r a), 1 ≤ d b := by
        by_contra hc
        push Not at hc
        have : odSum F r a d ≤ 0 := by
          unfold odSum
          exact sum_nonpos fun b hb' => by have := hc b hb'; omega
        omega
      obtain ⟨b, hbm, hb1⟩ := hpos
      have hbo := (mem_filter.mp hbm).2
      have hba : b = a := by
        by_contra hne; exact absurd (hno b hbo hb1).1 hne
      subst hba
      have hda : d b = 1 := by have := (hno b hbo hb1).2; omega
      -- the component of `b` is its odd class, and only `b` carries weight there
      have hset : univ.filter (fun c => EvenR F r b c ∨ OddR F r b c) =
          univ.filter (OddR F r b) := by
        ext c
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.elim (fun he => hbo.trans_even he) id, Or.inr⟩
      have hcomp : compSum F r b d = 1 := by
        unfold compSum
        rw [hset, Finset.sum_eq_single b]
        · exact hda
        · intro c hc hcb
          have hco := (mem_filter.mp hc).2
          have := hd0 c
          by_contra hne
          have h1 : 1 ≤ d c := by omega
          exact hcb (hno c hco h1).1
        · intro h; exact absurd (mem_filter.mpr ⟨mem_univ _, hbo⟩) h
      have := (hb b).2
      rw [hcomp] at this
      exact absurd this (by decide)
    obtain ⟨b, hab, hb1, hcase⟩ := hpart
    set d' := d - pairVecZ a b with hd'
    have hd'0 : ∀ i, 0 ≤ d' i := by
      intro i
      simp only [hd', Pi.sub_apply, pairVecZ]
      have := hd0 i
      by_cases h1 : a = i <;> by_cases h2 : b = i
      · subst h1; subst h2; rcases hcase with h | h; exact absurd rfl h; simp; omega
      · subst h1; simp [h2]; omega
      · subst h2; simp [h1]; omega
      · simp [h1, h2]; omega
    have hbal : Balanced F r d' := hb.sub (balanced_pair hab)
    have h2 : ∑ i, d' i = ∑ i, d i - 2 := by
      simp only [hd', Pi.sub_apply, sum_sub_distrib, sum_pairVecZ]
    have hnn : 0 ≤ ∑ i, d' i := sum_nonneg fun i _ => hd'0 i
    have hN2 : 2 ≤ N := by
      have : (2 : ℤ) ≤ N := by rw [← hN]; linarith
      exact_mod_cast this
    have hsum : ∑ i, d' i = ((N - 2 : ℕ) : ℤ) := by
      rw [h2, hN, Nat.cast_sub hN2]; norm_num
    obtain ⟨M', hM'o, hM'⟩ := ih (N - 2) (by omega) d' hd'0 hbal hsum
    refine ⟨(a, b) ::ₘ M', ?_, ?_⟩
    · intro ab hm
      rcases Multiset.mem_cons.mp hm with rfl | hm
      · exact hab
      · exact hM'o ab hm
    · rw [Multiset.map_cons, Multiset.sum_cons, ← hM', hd']
      abel

/-- **Admissible transitions at every vertex, for every family.** -/
theorem exists_odd_pairing_of_isIntDiv {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) {E : Finset (Sym2 V)} (hdiv : IsIntDiv p F E) (v : V) :
    ∃ M : Multiset (Fin t × Fin t), (∀ ab ∈ M, OddR F (p v) ab.1 ab.2) ∧
      degVec p E v = (M.map fun ab => pairVecZ ab.1 ab.2).sum := by
  obtain ⟨c, hc⟩ := hdiv.2 v
  refine exists_odd_pairing _ (fun j => ?_) (balanced_of_lattice hF3 hc)
  unfold degVec
  rw [Finset.sum_apply]
  exact sum_nonneg fun e _ => degContrib_nonneg p v e j

end Pairing

/-! ### The rainbow type: odd transitions are the non-reversing ones -/

/-- In the link of `0` for the rainbow type, `1` and `2` are joined by an odd walk, while `1`
is never joined to itself by one (the reversing transition `1 → 0 → 1`). -/
theorem rainbow_oddR_one_two : OddR ({{0, 1, 2}} : Finset (Multiset (Fin 3))) 0 1 2 :=
  oddR_of_link (by unfold Link; decide)

end PartitionedTriangleAbsorption.BlowupB

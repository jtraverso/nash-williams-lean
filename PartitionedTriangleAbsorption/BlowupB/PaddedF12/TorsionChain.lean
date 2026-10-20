/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Std

/-!
# A fixed universal chain for one bit of torsion

There is one old piece at every row `i < N`, with torsion `eps i`. A library
index has one of two decisions (use or omit that old piece), and one of two
incoming carries. The library is fixed by `N`, `eps`, and the final bit `r`;
it does not depend on the later selection `choose`.

The atoms `wireA j`, `wireB j` are two private torsion-one tokens on each wire.
The atom `tail` is an additional token when `r = 1`. Physical realizations of
tokens are transported after this purely combinatorial theorem. In particular,
the theorem below proves an actual partition, rather than assuming a universal
matching or refiner as an input.
-/

namespace PaddedF12.TorsionChain

def bit (b : Bool) : Nat := if b then 1 else 0

theorem bit_lt (b : Bool) : bit b < 2 := by cases b <;> decide

theorem bit_injective {b c : Bool} (h : bit b = bit c) : b = c := by
  cases b <;> cases c <;> simp_all [bit]

structure Index where
  row : Nat
  useOld : Bool
  before : Nat
deriving DecidableEq, Repr

inductive Atom where
  | old : Nat → Atom
  | wireA : Nat → Atom
  | wireB : Nat → Atom
  | tail : Atom
deriving DecidableEq, Repr

def oldBit (eps : Nat → Bool) (i : Index) : Nat :=
  if i.useOld then bit (eps i.row) else 0

def after (eps : Nat → Bool) (i : Index) : Nat :=
  (i.before + oldBit eps i) % 2

theorem oldBit_lt (eps : Nat → Bool) (i : Index) : oldBit eps i < 2 := by
  unfold oldBit
  split
  · exact bit_lt _
  · omega

theorem after_lt (eps : Nat → Bool) (i : Index) : after eps i < 2 := by
  exact Nat.mod_lt _ (by decide)

/-- The finite library has at most four indices per row. -/
def Valid (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) : Prop :=
  i.row < N ∧ i.before < 2 ∧ (i.row = 0 → i.before = 0) ∧
    (i.row + 1 = N → after eps i = r)

/-- Membership of an abstract whole piece or a whole private token. -/
def Contains (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) : Atom → Prop
  | .old j => i.row = j ∧ i.useOld = true
  | .wireA j => i.row = j ∧ i.row + 1 < N
  | .wireB j => (i.row = j ∧ i.row + 1 < N ∧ after eps i = 0) ∨
      (i.row = j + 1 ∧ i.before = 1)
  | .tail => i.row + 1 = N ∧ r = 1

/-- Number of private token occurrences in a library piece. -/
def tokenCount (N : Nat) (eps : Nat → Bool) (r : Nat) (i : Index) : Nat :=
  (if 0 < i.row ∧ i.before = 1 then 1 else 0) +
  (if i.row + 1 < N then 1 + if after eps i = 0 then 1 else 0 else 0) +
  (if i.row + 1 = N ∧ r = 1 then 1 else 0)

theorem tokenCount_le_three {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) : tokenCount N eps r i ≤ 3 := by
  have hrow := hi.1
  by_cases hin : 0 < i.row ∧ i.before = 1 <;>
    by_cases hout : i.row + 1 < N <;>
    by_cases hc : after eps i = 0 <;>
    by_cases ht : i.row + 1 = N ∧ r = 1 <;>
    simp [tokenCount, hin, hout, hc, ht] <;> omega

/-- Every member of the fixed library has torsion zero. -/
theorem piece_even {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index}
    (hi : Valid N eps r i) :
    (oldBit eps i + tokenCount N eps r i) % 2 = 0 := by
  obtain ⟨hrow, hb, hfirst, hlast⟩ := hi
  have he := oldBit_lt eps i
  have hc := after_lt eps i
  have ha : after eps i = (i.before + oldBit eps i) % 2 := rfl
  by_cases hin : 0 < i.row ∧ i.before = 1 <;>
    by_cases hout : i.row + 1 < N <;>
    by_cases hz : after eps i = 0 <;>
    by_cases ht : i.row + 1 = N ∧ r = 1 <;>
    simp [tokenCount, hin, hout, hz, ht] <;> omega

def carry (eps choose : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => (carry eps choose j + if choose j then bit (eps j) else 0) % 2

theorem carry_lt (eps choose : Nat → Bool) (j : Nat) : carry eps choose j < 2 := by
  cases j with
  | zero => change (0 : Nat) < 2; decide
  | succ j => exact Nat.mod_lt _ (by decide)

def selected (eps choose : Nat → Bool) (j : Nat) : Index :=
  ⟨j, choose j, carry eps choose j⟩

theorem after_selected (eps choose : Nat → Bool) (j : Nat) :
    after eps (selected eps choose j) = carry eps choose (j + 1) := rfl

theorem selected_valid {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    (hfinal : carry eps choose N = r) {j : Nat} (hj : j < N) :
    Valid N eps r (selected eps choose j) := by
  refine ⟨hj, carry_lt eps choose j, ?_, ?_⟩
  · intro h
    change j = 0 at h
    subst j
    rfl
  · intro h
    rw [after_selected]
    change j + 1 = N at h
    rw [h, hfinal]

/-- The requested target consists of selected old pieces, every wire token,
and the fixed last token when `r = 1`. -/
def Target (N : Nat) (r : Nat) (choose : Nat → Bool) : Atom → Prop
  | .old j => j < N ∧ choose j = true
  | .wireA j => j + 1 < N
  | .wireB j => j + 1 < N
  | .tail => 0 < N ∧ r = 1

theorem selected_no_extra {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    {j : Nat} (hj : j < N) {a : Atom}
    (ha : Contains N eps r (selected eps choose j) a) : Target N r choose a := by
  cases a with
  | old k =>
    change j = k ∧ choose j = true at ha
    obtain ⟨rfl, hs⟩ := ha
    exact ⟨hj, hs⟩
  | wireA k =>
    change j = k ∧ j + 1 < N at ha
    change k + 1 < N
    omega
  | wireB k =>
    change (j = k ∧ j + 1 < N ∧ _) ∨ (j = k + 1 ∧ _) at ha
    change k + 1 < N
    omega
  | tail =>
    change j + 1 = N ∧ r = 1 at ha
    change 0 < N ∧ r = 1
    omega

theorem selected_covers {N : Nat} {eps choose : Nat → Bool} {r : Nat} {a : Atom}
    (ha : Target N r choose a) :
    ∃ j, j < N ∧ Contains N eps r (selected eps choose j) a := by
  cases a with
  | old k =>
    exact ⟨k, ha.1, rfl, ha.2⟩
  | wireA k =>
    change k + 1 < N at ha
    exact ⟨k, by omega, rfl, ha⟩
  | wireB k =>
    change k + 1 < N at ha
    by_cases hp : carry eps choose (k + 1) = 0
    · refine ⟨k, by omega, Or.inl ⟨rfl, ha, ?_⟩⟩
      exact (after_selected eps choose k).trans hp
    · have hp1 : carry eps choose (k + 1) = 1 := by
        have := carry_lt eps choose (k + 1)
        omega
      exact ⟨k + 1, ha, Or.inr ⟨rfl, hp1⟩⟩
  | tail =>
    obtain ⟨hN, hr⟩ := ha
    refine ⟨N - 1, by omega, ?_⟩
    change N - 1 + 1 = N ∧ r = 1
    omega

theorem selected_disjoint {N : Nat} {eps choose : Nat → Bool} {r : Nat}
    {j k : Nat} {a : Atom}
    (hj : Contains N eps r (selected eps choose j) a)
    (hk : Contains N eps r (selected eps choose k) a) : j = k := by
  cases a with
  | old l =>
    change j = l ∧ _ at hj
    change k = l ∧ _ at hk
    omega
  | wireA l =>
    change j = l ∧ _ at hj
    change k = l ∧ _ at hk
    omega
  | wireB l =>
    change (j = l ∧ j + 1 < N ∧ after eps (selected eps choose j) = 0) ∨
      (j = l + 1 ∧ carry eps choose j = 1) at hj
    change (k = l ∧ k + 1 < N ∧ after eps (selected eps choose k) = 0) ∨
      (k = l + 1 ∧ carry eps choose k = 1) at hk
    rw [after_selected] at hj hk
    rcases hj with ⟨hjl, -, hjp⟩ | ⟨hjl, hjp⟩ <;>
      rcases hk with ⟨hkl, -, hkp⟩ | ⟨hkl, hkp⟩
    · omega
    · subst j
      subst k
      omega
    · subst j
      subst k
      omega
    · omega
  | tail =>
    change j + 1 = N ∧ _ at hj
    change k + 1 = N ∧ _ at hk
    omega

/-- Full universal partition statement. The library predicate `Valid` and every
piece `Contains` are fixed before `choose` is quantified. -/
theorem fixed_chain_refines (N : Nat) (eps : Nat → Bool) (r : Nat) :
    (∀ i, Valid N eps r i →
      tokenCount N eps r i ≤ 3 ∧ (oldBit eps i + tokenCount N eps r i) % 2 = 0) ∧
    ∀ choose : Nat → Bool, carry eps choose N = r →
      (∀ j < N, Valid N eps r (selected eps choose j)) ∧
      (∀ a, Target N r choose a ↔
        ∃ j, j < N ∧ Contains N eps r (selected eps choose j) a) ∧
      (∀ j k a, Contains N eps r (selected eps choose j) a →
        Contains N eps r (selected eps choose k) a → j = k) := by
  refine ⟨fun _ hi => ⟨tokenCount_le_three hi, piece_even hi⟩, ?_⟩
  intro choose hfinal
  refine ⟨fun _ hj => selected_valid hfinal hj, ?_, fun _ _ _ => selected_disjoint⟩
  intro a
  exact ⟨selected_covers, fun ⟨_, hj, ha⟩ => selected_no_extra hj ha⟩

/-! ## Local incidence bounds, as explicit finite-slot injections -/

/-- A slot in a set of at most four elements identifies a library occurrence
of a token; an old piece has only the two incoming-carry slots. -/
def localSlot (a : Atom) (i : Index) : Nat :=
  match a with
  | .old _ => i.before
  | .wireA _ => 2 * bit i.useOld + i.before
  | .wireB j => if i.row = j then bit i.useOld else 2 + bit i.useOld
  | .tail => 2 * bit i.useOld + i.before

theorem localSlot_bound {N : Nat} {eps : Nat → Bool} {r : Nat} {i : Index} {a : Atom}
    (hi : Valid N eps r i) :
    localSlot a i < (match a with | .old _ => 2 | _ => 4) := by
  have hb := hi.2.1
  have hs := bit_lt i.useOld
  cases a <;> simp only [localSlot]
  · omega
  · omega
  · split <;> omega
  · omega

theorem localSlot_injective {N : Nat} {eps : Nat → Bool} {r : Nat}
    {i j : Index} {a : Atom} (hi : Valid N eps r i) (hj : Valid N eps r j)
    (hai : Contains N eps r i a) (haj : Contains N eps r j a)
    (heq : localSlot a i = localSlot a j) : i = j := by
  obtain ⟨ir, is, ib⟩ := i
  obtain ⟨jr, js, jb⟩ := j
  have hib : ib < 2 := hi.2.1
  have hjb : jb < 2 := hj.2.1
  cases a with
  | old k =>
    change ir = k ∧ is = true at hai
    change jr = k ∧ js = true at haj
    change ib = jb at heq
    obtain ⟨rfl, rfl⟩ := hai
    obtain ⟨rfl, rfl⟩ := haj
    cases heq
    rfl
  | wireA k =>
    change ir = k ∧ _ at hai
    change jr = k ∧ _ at haj
    change 2 * bit is + ib = 2 * bit js + jb at heq
    have hir : ir = jr := by omega
    have hbit1 := bit_lt is
    have hbit2 := bit_lt js
    have hbits : bit is = bit js := by omega
    have his : is = js := bit_injective hbits
    have hib' : ib = jb := by omega
    cases hir
    cases his
    cases hib'
    rfl
  | wireB k =>
    change (ir = k ∧ ir + 1 < N ∧ after eps ⟨ir, is, ib⟩ = 0) ∨
      (ir = k + 1 ∧ ib = 1) at hai
    change (jr = k ∧ jr + 1 < N ∧ after eps ⟨jr, js, jb⟩ = 0) ∨
      (jr = k + 1 ∧ jb = 1) at haj
    change (if ir = k then bit is else 2 + bit is) =
      (if jr = k then bit js else 2 + bit js) at heq
    have hbit1 := bit_lt is
    have hbit2 := bit_lt js
    rcases hai with ⟨hir, -, hia⟩ | ⟨hir, hib'⟩ <;>
      rcases haj with ⟨hjr, -, hja⟩ | ⟨hjr, hjb'⟩
    · subst ir
      subst jr
      simp at heq
      have his : is = js := bit_injective heq
      subst js
      have he := bit_lt (eps k)
      simp only [after, oldBit] at hia hja
      have hbe : ib = jb := by
        cases is <;> simp at hia hja <;> omega
      cases hbe
      rfl
    · subst ir
      subst jr
      simp at heq
      omega
    · subst ir
      subst jr
      simp at heq
      omega
    · subst ir
      subst jr
      simp at heq
      have his : is = js := bit_injective (by omega)
      subst js
      subst ib
      subst jb
      rfl
  | tail =>
    change ir + 1 = N ∧ _ at hai
    change jr + 1 = N ∧ _ at haj
    change 2 * bit is + ib = 2 * bit js + jb at heq
    have hir : ir = jr := by omega
    have hbit1 := bit_lt is
    have hbit2 := bit_lt js
    have hbits : bit is = bit js := by omega
    have his : is = js := bit_injective hbits
    have hib' : ib = jb := by omega
    cases hir
    cases his
    cases hib'
    rfl

#print axioms piece_even
#print axioms fixed_chain_refines
#print axioms localSlot_bound
#print axioms localSlot_injective

end PaddedF12.TorsionChain

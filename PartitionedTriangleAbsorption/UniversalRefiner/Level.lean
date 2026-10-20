/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Transport

/-!
# One hub level of the parity transport, on atoms

Fix a finite set `Λ` of non-degenerate links (unordered pairs) and a hub map `h`.
* every vertex `u` has an endpoint chain whose positions are the links at `u` (`vChain`), with
  wire paths `ep l u j b` between `u` and `h u`;
* every non-degenerate hub pair `σ` has a pair chain whose positions are the links projecting to
  `σ` (`pChain`), with wire paths `pr l σ j b`, and two terminal paths `tm l σ false/true`;
* the library has, for each link, the 16 alternatives `alt l π x ca cb cs` (selection bit and
  the three incoming carries), and the cycle pieces `cyc l σ`.

`level_transport` proves that this library performs one level of parity transport: every
zero-boundary selection `S ⊆ Λ` is refined by pairwise disjoint zero-boundary alternatives,
except for the zero-boundary selection of next-level links `tm l σ true` whose pair-chain carry
is one.  All absent / present-unselected / selected states are handled, since the library is
indexed by all bit patterns and only the active subfamily depends on `S`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset

variable {V : Type*} [DecidableEq V]

/-- Next-level links: the non-degenerate hub pairs of the current links. -/
def nextLinks (Λ : Finset (Sym2 V)) (h : V → V) : Finset (Sym2 V) :=
  (Λ.image (Sym2.map h)).filter fun σ => ¬ σ.IsDiag

/-- Positions of the endpoint chain of `u`. -/
def vChain (Λ : Finset (Sym2 V)) (u : V) : Finset (Sym2 V) := Λ.filter fun π => u ∈ π

/-- Positions of the pair chain of `σ`. -/
def pChain (Λ : Finset (Sym2 V)) (h : V → V) (σ : Sym2 V) : Finset (Sym2 V) :=
  Λ.filter fun π => Sym2.map h π = σ

/-- The atom carrying link `π` at level `l`: a reserve edge at level `0`, and the transmitted
terminal path of the previous level otherwise. -/
def linkAtom (l : ℕ) (π : Sym2 V) : Atom V :=
  if l = 0 then Sum.inr π else Sum.inl (Req.tm (l - 1) π true)

/-- Endpoint-chain wire atoms indexed by `(wire, path)`. -/
def epAtoms (l : ℕ) (u : V) (Q : Finset (ℕ × Bool)) : Finset (Atom V) :=
  Q.image fun q => Sum.inl (Req.ep l u q.1 q.2)

/-- Pair-chain wire atoms indexed by `(wire, path)`. -/
def prAtoms (l : ℕ) (σ : Sym2 V) (Q : Finset (ℕ × Bool)) : Finset (Atom V) :=
  Q.image fun q => Sum.inl (Req.pr l σ q.1 q.2)

/-- Received endpoint-chain atoms of link `π` in the chain of `u`. -/
noncomputable def vRecv (Λ : Finset (Sym2 V)) (l : ℕ) (u : V) (π : Sym2 V) (cp cur : Bool) :
    Finset (Atom V) :=
  epAtoms l u (recvLoc (vChain Λ u).card (pos (vChain Λ u) π) cp cur)

/-- Received pair-chain atoms of link `π`, with the terminal `f_σ` at the last position. -/
noncomputable def pRecv (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) (π : Sym2 V)
    (cp cur : Bool) : Finset (Atom V) :=
  prAtoms l (Sym2.map h π) (recvLoc (pChain Λ h (Sym2.map h π)).card
      (pos (pChain Λ h (Sym2.map h π)) π) cp cur) ∪
    (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧ cur = true
      then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅)

/-- The atoms of the alternative `alt l π x ca cb cs`. -/
noncomputable def altAtoms (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) (π : Sym2 V)
    (x ca cb cs : Bool) : Finset (Atom V) :=
  (if x then {linkAtom l π} else ∅) ∪ vRecv Λ l (endA π) π ca (xor ca x) ∪
    vRecv Λ l (endB π) π cb (xor cb x) ∪
    (if (Sym2.map h π).IsDiag then ∅ else pRecv Λ h l π cs (xor cs x))

/-- The atoms of the cycle piece `f_σ ∪ f'_σ`. -/
def cycAtoms (l : ℕ) (σ : Sym2 V) : Finset (Atom V) :=
  {Sum.inl (Req.tm l σ false), Sum.inl (Req.tm l σ true)}

/-- The library of one level: all 16 alternatives of every link, and all cycle pieces. -/
def levelLib (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) : Finset (LibIdx V) :=
  (Λ ×ˢ (univ : Finset (Bool × Bool × Bool × Bool))).image
      (fun q => LibIdx.alt l q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) ∪
    (nextLinks Λ h).image (LibIdx.cyc l)

/-- All atoms created at one level. -/
def levelAtoms [Fintype V] (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) : Finset (Atom V) :=
  ((univ : Finset V).biUnion fun u => epAtoms l u (range ((vChain Λ u).card - 1) ×ˢ univ)) ∪
    ((nextLinks Λ h).biUnion fun σ => prAtoms l σ (range ((pChain Λ h σ).card - 1) ×ˢ univ)) ∪
    (nextLinks Λ h).biUnion (cycAtoms l)

/-! ### The active subfamily of a selection -/

section Selection

variable (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) (S : Finset (Sym2 V))

/-- Selection bits of the endpoint chain of `u`. -/
noncomputable def xv (u : V) : ℕ → Bool := selBits (vChain Λ u) S

/-- Selection bits of the pair chain of `σ`. -/
noncomputable def xp (σ : Sym2 V) : ℕ → Bool := selBits (pChain Λ h σ) S

/-- The wire paths actually received by `π` in the chain of `u`. -/
noncomputable def vR (u : V) (π : Sym2 V) : Finset (ℕ × Bool) :=
  recvLoc (vChain Λ u).card (pos (vChain Λ u) π)
    (prevBit (xv Λ S u) (pos (vChain Λ u) π)) (curBit (xv Λ S u) (pos (vChain Λ u) π))

/-- The wire paths actually received by `π` in its pair chain. -/
noncomputable def pR (π : Sym2 V) : Finset (ℕ × Bool) :=
  recvLoc (pChain Λ h (Sym2.map h π)).card (pos (pChain Λ h (Sym2.map h π)) π)
    (prevBit (xp Λ h S (Sym2.map h π)) (pos (pChain Λ h (Sym2.map h π)) π))
    (curBit (xp Λ h S (Sym2.map h π)) (pos (pChain Λ h (Sym2.map h π)) π))

/-- Final carry of the pair chain of `σ`. -/
noncomputable def finP (σ : Sym2 V) : Bool :=
  curBit (xp Λ h S σ) ((pChain Λ h σ).card - 1)

/-- The active alternative of link `π`. -/
noncomputable def chosen (π : Sym2 V) : LibIdx V :=
  LibIdx.alt l π (decide (π ∈ S))
    (prevBit (xv Λ S (endA π)) (pos (vChain Λ (endA π)) π))
    (prevBit (xv Λ S (endB π)) (pos (vChain Λ (endB π)) π))
    (prevBit (xp Λ h S (Sym2.map h π)) (pos (pChain Λ h (Sym2.map h π)) π))

/-- The active subfamily. -/
noncomputable def chosenSet : Finset (LibIdx V) :=
  Λ.image (chosen Λ h l S) ∪
    ((nextLinks Λ h).filter fun σ => finP Λ h S σ = false).image (LibIdx.cyc l)

/-- The transmitted selection of next-level links. -/
noncomputable def nextSel : Finset (Sym2 V) :=
  (nextLinks Λ h).filter fun σ => finP Λ h S σ = true

end Selection

/-- Atoms of the library, as a function of the index (for one level). -/
noncomputable def levelPiece (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ) :
    LibIdx V → Finset (Atom V)
  | LibIdx.alt _ π x ca cb cs => altAtoms Λ h l π x ca cb cs
  | LibIdx.cyc _ σ => cycAtoms l σ
  | LibIdx.adj _ => ∅

/-! ### Membership bookkeeping -/

section Bookkeeping

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ}

theorem mem_vChain {u : V} {π : Sym2 V} : π ∈ vChain Λ u ↔ π ∈ Λ ∧ u ∈ π := by
  simp [vChain]

theorem mem_pChain {σ π : Sym2 V} : π ∈ pChain Λ h σ ↔ π ∈ Λ ∧ Sym2.map h π = σ := by
  simp [pChain]

theorem mem_nextLinks {σ : Sym2 V} :
    σ ∈ nextLinks Λ h ↔ (∃ π ∈ Λ, Sym2.map h π = σ) ∧ ¬ σ.IsDiag := by
  simp [nextLinks]

omit [DecidableEq V] in
theorem endA_mem (π : Sym2 V) : endA π ∈ π := mem_iff_endA_endB.mpr (Or.inl rfl)

omit [DecidableEq V] in
theorem endB_mem (π : Sym2 V) : endB π ∈ π := mem_iff_endA_endB.mpr (Or.inr rfl)

@[simp] theorem ep_mem_epAtoms {l' : ℕ} {u u' : V} {j : ℕ} {b : Bool} {Q : Finset (ℕ × Bool)} :
    (Sum.inl (Req.ep l' u' j b) : Atom V) ∈ epAtoms l u Q ↔ l' = l ∧ u' = u ∧ (j, b) ∈ Q := by
  unfold epAtoms
  constructor
  · intro hm
    obtain ⟨q, hq, he⟩ := mem_image.mp hm
    simp only [Sum.inl.injEq, Req.ep.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact ⟨rfl, rfl, hq⟩
  · rintro ⟨rfl, rfl, hq⟩
    exact mem_image.mpr ⟨(j, b), hq, rfl⟩

@[simp] theorem pr_mem_epAtoms {l' : ℕ} {u : V} {σ : Sym2 V} {j : ℕ} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.pr l' σ j b) : Atom V) ∉ epAtoms l u Q := by
  simp [epAtoms]

@[simp] theorem tm_mem_epAtoms {l' : ℕ} {u : V} {σ : Sym2 V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.tm l' σ b) : Atom V) ∉ epAtoms l u Q := by
  simp [epAtoms]

@[simp] theorem md_mem_epAtoms {k : ℕ} {c : Fin 3} {u : V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.md k c b) : Atom V) ∉ epAtoms l u Q := by
  simp [epAtoms]

@[simp] theorem adj_mem_epAtoms {k : ℕ} {u : V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.adj k b) : Atom V) ∉ epAtoms l u Q := by
  simp [epAtoms]

@[simp] theorem inr_mem_epAtoms {e : Sym2 V} {u : V}
    {Q : Finset (ℕ × Bool)} : (Sum.inr e : Atom V) ∉ epAtoms l u Q := by
  simp [epAtoms]

@[simp] theorem pr_mem_prAtoms {l' : ℕ} {σ σ' : Sym2 V} {j : ℕ} {b : Bool}
    {Q : Finset (ℕ × Bool)} :
    (Sum.inl (Req.pr l' σ' j b) : Atom V) ∈ prAtoms l σ Q ↔ l' = l ∧ σ' = σ ∧ (j, b) ∈ Q := by
  unfold prAtoms
  constructor
  · intro hm
    obtain ⟨q, hq, he⟩ := mem_image.mp hm
    simp only [Sum.inl.injEq, Req.pr.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact ⟨rfl, rfl, hq⟩
  · rintro ⟨rfl, rfl, hq⟩
    exact mem_image.mpr ⟨(j, b), hq, rfl⟩

@[simp] theorem ep_mem_prAtoms {l' : ℕ} {u : V} {σ : Sym2 V} {j : ℕ} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.ep l' u j b) : Atom V) ∉ prAtoms l σ Q := by
  simp [prAtoms]

@[simp] theorem tm_mem_prAtoms {l' : ℕ} {σ σ' : Sym2 V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.tm l' σ' b) : Atom V) ∉ prAtoms l σ Q := by
  simp [prAtoms]

@[simp] theorem md_mem_prAtoms {k : ℕ} {c : Fin 3} {σ : Sym2 V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.md k c b) : Atom V) ∉ prAtoms l σ Q := by
  simp [prAtoms]

@[simp] theorem adj_mem_prAtoms {k : ℕ} {σ : Sym2 V} {b : Bool}
    {Q : Finset (ℕ × Bool)} : (Sum.inl (Req.adj k b) : Atom V) ∉ prAtoms l σ Q := by
  simp [prAtoms]

@[simp] theorem inr_mem_prAtoms {e σ : Sym2 V}
    {Q : Finset (ℕ × Bool)} : (Sum.inr e : Atom V) ∉ prAtoms l σ Q := by
  simp [prAtoms]

omit [DecidableEq V] in
@[simp] theorem linkAtom_ne_ep {π : Sym2 V} {l' : ℕ} {u : V} {j : ℕ} {b : Bool} :
    linkAtom l π ≠ Sum.inl (Req.ep l' u j b) := by
  unfold linkAtom; split_ifs <;> simp

omit [DecidableEq V] in
@[simp] theorem linkAtom_ne_pr {π σ : Sym2 V} {l' : ℕ} {j : ℕ} {b : Bool} :
    linkAtom l π ≠ Sum.inl (Req.pr l' σ j b) := by
  unfold linkAtom; split_ifs <;> simp

omit [DecidableEq V] in
@[simp] theorem linkAtom_ne_md {π : Sym2 V} {k : ℕ} {c : Fin 3} {b : Bool} :
    linkAtom l π ≠ Sum.inl (Req.md k c b) := by
  unfold linkAtom; split_ifs <;> simp

omit [DecidableEq V] in
@[simp] theorem linkAtom_ne_adj {π : Sym2 V} {k : ℕ} {b : Bool} :
    linkAtom l π ≠ Sum.inl (Req.adj k b) := by
  unfold linkAtom; split_ifs <;> simp

omit [DecidableEq V] in
theorem linkAtom_eq_tm {π σ : Sym2 V} {l' : ℕ} {b : Bool} :
    linkAtom l π = Sum.inl (Req.tm l' σ b) ↔ l ≠ 0 ∧ l' = l - 1 ∧ σ = π ∧ b = true := by
  unfold linkAtom
  split_ifs with hl
  · simp [hl]
  · simp only [Sum.inl.injEq, Req.tm.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨hl, h1.symm, h2.symm, h3.symm⟩
    · rintro ⟨-, h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩

omit [DecidableEq V] in
theorem linkAtom_eq_inr {π e : Sym2 V} : linkAtom l π = Sum.inr e ↔ l = 0 ∧ e = π := by
  unfold linkAtom
  split_ifs with hl
  · simp only [Sum.inr.injEq]; exact ⟨fun h => ⟨hl, h.symm⟩, fun h => h.2.symm⟩
  · simp [hl]

omit [DecidableEq V] in
theorem linkAtom_injective (l : ℕ) : Function.Injective (linkAtom (V := V) l) := by
  intro π π' hπ
  unfold linkAtom at hπ
  split_ifs at hπ
  · simpa using hπ
  · simp only [Sum.inl.injEq, Req.tm.injEq] at hπ; exact hπ.2.1

theorem xor_prev_sel {α : Type*} [DecidableEq α] {C S : Finset α} {a : α} (ha : a ∈ C) :
    xor (prevBit (selBits C S) (pos C a)) (decide (a ∈ S)) = curBit (selBits C S) (pos C a) := by
  rw [curBit_eq, selBits_pos ha]

end Bookkeeping

section Chosen

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {S : Finset (Sym2 V)}

/-- The active alternative of `π` consists of the link (when selected) and of what `π` actually
receives in its three chains, plus `f_σ` at the last pair position when the final carry is one. -/
theorem altAtoms_chosen {π : Sym2 V} (hπ : π ∈ Λ) :
    levelPiece Λ h l (chosen Λ h l S π) =
      (if π ∈ S then {linkAtom l π} else ∅) ∪ epAtoms l (endA π) (vR Λ S (endA π) π) ∪
        epAtoms l (endB π) (vR Λ S (endB π) π) ∪
        (if (Sym2.map h π).IsDiag then ∅ else prAtoms l (Sym2.map h π) (pR Λ h S π) ∪
          (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
              finP Λ h S (Sym2.map h π) = true
            then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅)) := by
  have hA : π ∈ vChain Λ (endA π) := mem_vChain.mpr ⟨hπ, endA_mem π⟩
  have hB : π ∈ vChain Λ (endB π) := mem_vChain.mpr ⟨hπ, endB_mem π⟩
  have hP : π ∈ pChain Λ h (Sym2.map h π) := mem_pChain.mpr ⟨hπ, rfl⟩
  have hlast : (pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
      curBit (xp Λ h S (Sym2.map h π)) (pos (pChain Λ h (Sym2.map h π)) π) = true) ↔
      (pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
        finP Λ h S (Sym2.map h π) = true) := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      unfold finP
      rwa [show (pChain Λ h (Sym2.map h π)).card - 1 = pos (pChain Λ h (Sym2.map h π)) π by
        omega]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      unfold finP at h2
      rwa [show (pChain Λ h (Sym2.map h π)).card - 1 = pos (pChain Λ h (Sym2.map h π)) π by
        omega] at h2
  simp only [levelPiece, chosen, altAtoms, vRecv, pRecv, vR, pR, xv, xp]
  rw [xor_prev_sel hA, xor_prev_sel hB, xor_prev_sel hP]
  simp only [decide_eq_true_eq]
  simp only [xp] at hlast
  congr 2
  split_ifs <;> simp_all

end Chosen

section Disjointness

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {S : Finset (Sym2 V)}

theorem mem_ite_empty {β : Type*} {p : Prop} [Decidable p] {s : Finset β} {a : β} :
    a ∈ (if p then s else ∅) ↔ p ∧ a ∈ s := by
  split_ifs <;> simp_all

theorem mem_ite_empty_left {β : Type*} {p : Prop} [Decidable p] {s : Finset β} {a : β} :
    a ∈ (if p then ∅ else s) ↔ ¬ p ∧ a ∈ s := by
  split_ifs <;> simp_all

omit [DecidableEq V] in
@[simp] theorem ep_ne_linkAtom {π : Sym2 V} {l' : ℕ} {u : V} {j : ℕ} {b : Bool} :
    Sum.inl (Req.ep l' u j b) ≠ linkAtom l π := fun h => linkAtom_ne_ep h.symm

omit [DecidableEq V] in
@[simp] theorem pr_ne_linkAtom {π σ : Sym2 V} {l' : ℕ} {j : ℕ} {b : Bool} :
    Sum.inl (Req.pr l' σ j b) ≠ linkAtom l π := fun h => linkAtom_ne_pr h.symm

omit [DecidableEq V] in
@[simp] theorem md_ne_linkAtom {π : Sym2 V} {k : ℕ} {c : Fin 3} {b : Bool} :
    Sum.inl (Req.md k c b) ≠ linkAtom l π := fun h => linkAtom_ne_md h.symm

omit [DecidableEq V] in
@[simp] theorem adj_ne_linkAtom {π : Sym2 V} {k : ℕ} {b : Bool} :
    Sum.inl (Req.adj k b) ≠ linkAtom l π := fun h => linkAtom_ne_adj h.symm

omit [DecidableEq V] in
theorem tm_eq_linkAtom {π σ : Sym2 V} {l' : ℕ} {b : Bool} :
    Sum.inl (Req.tm l' σ b) = linkAtom l π ↔ l ≠ 0 ∧ l' = l - 1 ∧ σ = π ∧ b = true := by
  rw [eq_comm]; exact linkAtom_eq_tm

omit [DecidableEq V] in
theorem inr_eq_linkAtom {π e : Sym2 V} : Sum.inr e = linkAtom l π ↔ l = 0 ∧ e = π := by
  rw [eq_comm]; exact linkAtom_eq_inr

theorem vR_disjoint {u : V} {π π' : Sym2 V} (hπ : π ∈ vChain Λ u) (hπ' : π' ∈ vChain Λ u)
    (hne : π ≠ π') : Disjoint (vR Λ S u π) (vR Λ S u π') :=
  recvLoc_disjoint _ _ (fun e => hne (pos_inj hπ hπ' e))

theorem pR_disjoint {π π' : Sym2 V} (hπ : π ∈ Λ) (hπ' : π' ∈ Λ)
    (hσ : Sym2.map h π = Sym2.map h π') (hne : π ≠ π') :
    Disjoint (pR Λ h S π) (pR Λ h S π') := by
  have h1 : π ∈ pChain Λ h (Sym2.map h π') := mem_pChain.mpr ⟨hπ, hσ⟩
  have h2 : π' ∈ pChain Λ h (Sym2.map h π') := mem_pChain.mpr ⟨hπ', rfl⟩
  unfold pR
  rw [hσ]
  exact recvLoc_disjoint _ _ (fun e => hne (pos_inj h1 h2 e))

theorem ep_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {l' : ℕ} {u : V} {j : ℕ} {b : Bool} :
    (Sum.inl (Req.ep l' u j b) : Atom V) ∈ levelPiece Λ h l (chosen Λ h l S π) ↔
      l' = l ∧ u ∈ π ∧ (j, b) ∈ vR Λ S u π := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, ep_mem_epAtoms,
    ep_mem_prAtoms, ep_ne_linkAtom, Sum.inl.injEq, reduceCtorEq, and_false, false_or, or_false]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> subst h2
    · exact ⟨h1, endA_mem π, h3⟩
    · exact ⟨h1, endB_mem π, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rcases mem_iff_endA_endB.mp h2 with h4 | h4 <;> subst h4
    · exact Or.inl ⟨h1, rfl, h3⟩
    · exact Or.inr ⟨h1, rfl, h3⟩

theorem pr_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {l' : ℕ} {σ : Sym2 V} {j : ℕ} {b : Bool} :
    (Sum.inl (Req.pr l' σ j b) : Atom V) ∈ levelPiece Λ h l (chosen Λ h l S π) ↔
      ¬ (Sym2.map h π).IsDiag ∧ l' = l ∧ σ = Sym2.map h π ∧ (j, b) ∈ pR Λ h S π := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, pr_mem_epAtoms,
    pr_mem_prAtoms, pr_ne_linkAtom, Sum.inl.injEq, reduceCtorEq, and_false, false_or,
    or_false]

theorem tm_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {l' : ℕ} {σ : Sym2 V} {b : Bool} :
    (Sum.inl (Req.tm l' σ b) : Atom V) ∈ levelPiece Λ h l (chosen Λ h l S π) ↔
      (π ∈ S ∧ l ≠ 0 ∧ l' = l - 1 ∧ σ = π ∧ b = true) ∨
      (¬ (Sym2.map h π).IsDiag ∧
        (pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
          finP Λ h S (Sym2.map h π) = true) ∧ l' = l ∧ σ = Sym2.map h π ∧ b = false) := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, tm_mem_epAtoms,
    tm_mem_prAtoms, tm_eq_linkAtom, Sum.inl.injEq, Req.tm.injEq, false_or, or_false]

theorem inr_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {e : Sym2 V} :
    (Sum.inr e : Atom V) ∈ levelPiece Λ h l (chosen Λ h l S π) ↔ π ∈ S ∧ l = 0 ∧ e = π := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, inr_mem_epAtoms,
    inr_mem_prAtoms, inr_eq_linkAtom, reduceCtorEq, and_false, or_false]

theorem md_not_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {k : ℕ} {c : Fin 3} {b : Bool} :
    (Sum.inl (Req.md k c b) : Atom V) ∉ levelPiece Λ h l (chosen Λ h l S π) := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, md_mem_epAtoms,
    md_mem_prAtoms, md_ne_linkAtom, Sum.inl.injEq, reduceCtorEq, and_false, or_false,
    not_false_eq_true]

theorem adj_not_mem_chosen {π : Sym2 V} (hπ : π ∈ Λ) {k : ℕ} {b : Bool} :
    (Sum.inl (Req.adj k b) : Atom V) ∉ levelPiece Λ h l (chosen Λ h l S π) := by
  rw [altAtoms_chosen hπ]
  simp only [mem_union, mem_ite_empty, mem_ite_empty_left, mem_singleton, adj_mem_epAtoms,
    adj_mem_prAtoms, adj_ne_linkAtom, Sum.inl.injEq, reduceCtorEq, and_false, or_false,
    not_false_eq_true]

/-- Active alternatives of distinct links are disjoint. -/
theorem chosen_disjoint {π π' : Sym2 V} (hπ : π ∈ Λ) (hπ' : π' ∈ Λ) (hne : π ≠ π') :
    Disjoint (levelPiece Λ h l (chosen Λ h l S π)) (levelPiece Λ h l (chosen Λ h l S π')) := by
  rw [disjoint_left]
  rintro (r | e) ha ha'
  · cases r with
    | ep l' u j b =>
      obtain ⟨-, hu, hq⟩ := (ep_mem_chosen hπ).mp ha
      obtain ⟨-, hu', hq'⟩ := (ep_mem_chosen hπ').mp ha'
      exact disjoint_left.mp (vR_disjoint (mem_vChain.mpr ⟨hπ, hu⟩)
        (mem_vChain.mpr ⟨hπ', hu'⟩) hne) hq hq'
    | pr l' σ j b =>
      obtain ⟨-, -, hσ, hq⟩ := (pr_mem_chosen hπ).mp ha
      obtain ⟨-, -, hσ', hq'⟩ := (pr_mem_chosen hπ').mp ha'
      exact disjoint_left.mp (pR_disjoint hπ hπ' (hσ.symm.trans hσ') hne) hq hq'
    | tm l' σ b =>
      rcases (tm_mem_chosen hπ).mp ha with ⟨-, hl0, h1, h2, -⟩ | ⟨-, ⟨hl1, -⟩, h1, h2, -⟩ <;>
      rcases (tm_mem_chosen hπ').mp ha' with
        ⟨-, hl0', h1', h2', -⟩ | ⟨-, ⟨hl1', -⟩, h1', h2', -⟩
      · exact hne (h2.symm.trans h2')
      · omega
      · omega
      · have hσ : Sym2.map h π = Sym2.map h π' := h2.symm.trans h2'
        apply hne
        refine pos_inj (mem_pChain.mpr ⟨hπ, hσ⟩) (mem_pChain.mpr ⟨hπ', rfl⟩) ?_
        rw [hσ] at hl1
        omega
    | md k c b => exact md_not_mem_chosen hπ ha
    | adj k b => exact adj_not_mem_chosen hπ ha
  · obtain ⟨-, -, h1⟩ := (inr_mem_chosen hπ).mp ha
    obtain ⟨-, -, h1'⟩ := (inr_mem_chosen hπ').mp ha'
    exact hne (h1.symm.trans h1')

end Disjointness

section Coverage

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {S : Finset (Sym2 V)}

theorem ep_mem_levelAtoms [Fintype V] {l' : ℕ} {u : V} {j : ℕ} {b : Bool} :
    (Sum.inl (Req.ep l' u j b) : Atom V) ∈ levelAtoms Λ h l ↔
      l' = l ∧ j + 1 < (vChain Λ u).card := by
  unfold levelAtoms
  simp only [mem_union, mem_biUnion, mem_univ, true_and, ep_mem_epAtoms, ep_mem_prAtoms,
    cycAtoms, mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_self, and_false,
    exists_false, or_false, mem_product, mem_range]
  constructor
  · rintro ⟨u', h1, rfl, h2, -⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨u, h1, rfl, by omega, trivial⟩

theorem pr_mem_levelAtoms [Fintype V] {l' : ℕ} {σ : Sym2 V} {j : ℕ} {b : Bool} :
    (Sum.inl (Req.pr l' σ j b) : Atom V) ∈ levelAtoms Λ h l ↔
      l' = l ∧ σ ∈ nextLinks Λ h ∧ j + 1 < (pChain Λ h σ).card := by
  unfold levelAtoms
  simp only [mem_union, mem_biUnion, mem_univ, pr_mem_epAtoms, pr_mem_prAtoms,
    cycAtoms, mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_self, and_false,
    exists_false, or_false, false_or, mem_product, mem_range]
  constructor
  · rintro ⟨σ', hσ', h1, rfl, h2, -⟩; exact ⟨h1, hσ', by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨σ, h2, h1, rfl, by omega, trivial⟩

theorem tm_mem_levelAtoms [Fintype V] {l' : ℕ} {σ : Sym2 V} {b : Bool} :
    (Sum.inl (Req.tm l' σ b) : Atom V) ∈ levelAtoms Λ h l ↔ l' = l ∧ σ ∈ nextLinks Λ h := by
  unfold levelAtoms
  simp only [mem_union, mem_biUnion, mem_univ, tm_mem_epAtoms, tm_mem_prAtoms,
    cycAtoms, mem_insert, mem_singleton, Sum.inl.injEq, Req.tm.injEq, and_false,
    exists_false, false_or]
  constructor
  · rintro ⟨σ', hσ', ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩⟩ <;> exact ⟨h1, hσ'⟩
  · rintro ⟨h1, h2⟩
    cases b
    · exact ⟨σ, h2, Or.inl ⟨h1, rfl, rfl⟩⟩
    · exact ⟨σ, h2, Or.inr ⟨h1, rfl, rfl⟩⟩

theorem md_not_mem_levelAtoms [Fintype V] {k : ℕ} {c : Fin 3} {b : Bool} :
    (Sum.inl (Req.md k c b) : Atom V) ∉ levelAtoms Λ h l := by
  unfold levelAtoms
  simp [cycAtoms]

theorem adj_not_mem_levelAtoms [Fintype V] {k : ℕ} {b : Bool} :
    (Sum.inl (Req.adj k b) : Atom V) ∉ levelAtoms Λ h l := by
  unfold levelAtoms
  simp [cycAtoms]

theorem inr_not_mem_levelAtoms [Fintype V] {e : Sym2 V} :
    (Sum.inr e : Atom V) ∉ levelAtoms Λ h l := by
  unfold levelAtoms
  simp [cycAtoms]

theorem mem_chosenSet_biUnion {a : Atom V} :
    a ∈ (chosenSet Λ h l S).biUnion (levelPiece Λ h l) ↔
      (∃ π ∈ Λ, a ∈ levelPiece Λ h l (chosen Λ h l S π)) ∨
      (∃ σ ∈ nextLinks Λ h, finP Λ h S σ = false ∧ a ∈ cycAtoms l σ) := by
  unfold chosenSet
  simp only [union_biUnion, mem_union, image_biUnion, mem_biUnion, mem_filter]
  constructor
  · rintro (⟨π, hπ, ha⟩ | ⟨σ, ⟨hσ, hf⟩, ha⟩)
    · exact Or.inl ⟨π, hπ, ha⟩
    · exact Or.inr ⟨σ, hσ, hf, ha⟩
  · rintro (⟨π, hπ, ha⟩ | ⟨σ, hσ, hf, ha⟩)
    · exact Or.inl ⟨π, hπ, ha⟩
    · exact Or.inr ⟨σ, ⟨hσ, hf⟩, ha⟩

theorem vR_cover {u : V} {j : ℕ} {b : Bool} (hj : j + 1 < (vChain Λ u).card) :
    ∃ π ∈ Λ, u ∈ π ∧ (j, b) ∈ vR Λ S u π := by
  obtain ⟨j₀, hj₀, hq⟩ := exists_recvLoc (vChain Λ u).card (xv Λ S u) (q := (j, b)) hj
  obtain ⟨π, hπ, rfl⟩ := exists_pos_eq hj₀
  exact ⟨π, (mem_vChain.mp hπ).1, (mem_vChain.mp hπ).2, hq⟩

theorem vR_wire_lt {u : V} {π : Sym2 V} {q : ℕ × Bool} (hπ : π ∈ Λ) (hu : u ∈ π)
    (hq : q ∈ vR Λ S u π) : q.1 + 1 < (vChain Λ u).card :=
  recvLoc_wire_lt (pos_lt (mem_vChain.mpr ⟨hπ, hu⟩)) hq

theorem pR_cover {σ : Sym2 V} {j : ℕ} {b : Bool} (hj : j + 1 < (pChain Λ h σ).card) :
    ∃ π ∈ Λ, Sym2.map h π = σ ∧ (j, b) ∈ pR Λ h S π := by
  obtain ⟨j₀, hj₀, hq⟩ := exists_recvLoc (pChain Λ h σ).card (xp Λ h S σ) (q := (j, b)) hj
  obtain ⟨π, hπ, rfl⟩ := exists_pos_eq hj₀
  obtain ⟨hπΛ, hσ⟩ := mem_pChain.mp hπ
  refine ⟨π, hπΛ, hσ, ?_⟩
  unfold pR
  rw [hσ]
  exact hq

theorem pR_wire_lt {π : Sym2 V} {q : ℕ × Bool} (hπ : π ∈ Λ)
    (hq : q ∈ pR Λ h S π) : q.1 + 1 < (pChain Λ h (Sym2.map h π)).card :=
  recvLoc_wire_lt (pos_lt (mem_pChain.mpr ⟨hπ, rfl⟩)) hq

omit [DecidableEq V] in
theorem linkAtom_succ (l : ℕ) (σ : Sym2 V) :
    linkAtom (l + 1) σ = Sum.inl (Req.tm l σ true) := by
  simp [linkAtom]

/-- **Coverage.** The active pieces together with the transmitted links are exactly the level
atoms together with the selected links: nothing is omitted and nothing is covered twice. -/
theorem chosen_cover [Fintype V] (hS : S ⊆ Λ) :
    (chosenSet Λ h l S).biUnion (levelPiece Λ h l) ∪ (nextSel Λ h S).image (linkAtom (l + 1)) =
      levelAtoms Λ h l ∪ S.image (linkAtom l) := by
  ext a
  rw [mem_union, mem_chosenSet_biUnion, mem_union]
  simp only [nextSel, mem_image, mem_filter, linkAtom_succ]
  rcases a with r | e
  · cases r with
    | ep l' u j b =>
      constructor
      · rintro ((⟨π, hπ, ha⟩ | ⟨σ, -, -, ha⟩) | ⟨σ, -, ha⟩)
        · obtain ⟨h1, hu, hq⟩ := (ep_mem_chosen hπ).mp ha
          exact Or.inl (ep_mem_levelAtoms.mpr ⟨h1, vR_wire_lt hπ hu hq⟩)
        · simp [cycAtoms] at ha
        · simp at ha
      · rintro (ha | ⟨π, -, ha⟩)
        · obtain ⟨h1, hj⟩ := ep_mem_levelAtoms.mp ha
          obtain ⟨π, hπ, hu, hq⟩ := vR_cover (S := S) hj
          exact Or.inl (Or.inl ⟨π, hπ, (ep_mem_chosen hπ).mpr ⟨h1, hu, hq⟩⟩)
        · exact absurd ha linkAtom_ne_ep
    | pr l' σ j b =>
      constructor
      · rintro ((⟨π, hπ, ha⟩ | ⟨σ', -, -, ha⟩) | ⟨σ', -, ha⟩)
        · obtain ⟨hd, h1, rfl, hq⟩ := (pr_mem_chosen hπ).mp ha
          exact Or.inl (pr_mem_levelAtoms.mpr ⟨h1, mem_nextLinks.mpr ⟨⟨π, hπ, rfl⟩, hd⟩,
            pR_wire_lt hπ hq⟩)
        · simp [cycAtoms] at ha
        · simp at ha
      · rintro (ha | ⟨π, -, ha⟩)
        · obtain ⟨h1, hσ, hj⟩ := pr_mem_levelAtoms.mp ha
          obtain ⟨π, hπ, rfl, hq⟩ := pR_cover (S := S) hj
          exact Or.inl (Or.inl ⟨π, hπ, (pr_mem_chosen hπ).mpr
            ⟨(mem_nextLinks.mp hσ).2, h1, rfl, hq⟩⟩)
        · exact absurd ha linkAtom_ne_pr
    | tm l' σ b =>
      constructor
      · rintro ((⟨π, hπ, ha⟩ | ⟨σ', hσ', -, ha⟩) | ⟨σ', ⟨hσ', -⟩, ha⟩)
        · rcases (tm_mem_chosen hπ).mp ha with ⟨hπS, hl0, h1, rfl, rfl⟩ | ⟨hd, -, h1, rfl, -⟩
          · exact Or.inr ⟨σ, hπS, linkAtom_eq_tm.mpr ⟨hl0, h1, rfl, rfl⟩⟩
          · exact Or.inl (tm_mem_levelAtoms.mpr ⟨h1, mem_nextLinks.mpr ⟨⟨π, hπ, rfl⟩, hd⟩⟩)
        · simp only [cycAtoms, mem_insert, mem_singleton, Sum.inl.injEq, Req.tm.injEq] at ha
          rcases ha with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ <;>
            exact Or.inl (tm_mem_levelAtoms.mpr ⟨h1, hσ'⟩)
        · simp only [Sum.inl.injEq, Req.tm.injEq] at ha
          obtain ⟨rfl, rfl, -⟩ := ha
          exact Or.inl (tm_mem_levelAtoms.mpr ⟨rfl, hσ'⟩)
      · rintro (ha | ⟨π, hπS, ha⟩)
        · obtain ⟨rfl, hσ⟩ := tm_mem_levelAtoms.mp ha
          cases hf : finP Λ h S σ
          · exact Or.inl (Or.inr ⟨σ, hσ, hf, by cases b <;> simp [cycAtoms]⟩)
          · cases b
            · obtain ⟨⟨π₀, hπ₀, hσ₀⟩, hd⟩ := mem_nextLinks.mp hσ
              have hpos : 0 < (pChain Λ h σ).card :=
                card_pos.mpr ⟨π₀, mem_pChain.mpr ⟨hπ₀, hσ₀⟩⟩
              obtain ⟨π, hπ, hπpos⟩ := exists_pos_eq (C := pChain Λ h σ)
                (j := (pChain Λ h σ).card - 1) (by omega)
              obtain ⟨hπΛ, rfl⟩ := mem_pChain.mp hπ
              refine Or.inl (Or.inl ⟨π, hπΛ, (tm_mem_chosen hπΛ).mpr (Or.inr ⟨hd, ⟨?_, hf⟩,
                rfl, rfl, rfl⟩)⟩)
              omega
            · exact Or.inr ⟨σ, ⟨hσ, hf⟩, rfl⟩
        · obtain ⟨hl0, h1, rfl, rfl⟩ := linkAtom_eq_tm.mp ha
          exact Or.inl (Or.inl ⟨σ, hS hπS, (tm_mem_chosen (hS hπS)).mpr
            (Or.inl ⟨hπS, hl0, h1, rfl, rfl⟩)⟩)
    | md k c b =>
      constructor
      · rintro ((⟨π, hπ, ha⟩ | ⟨σ', -, -, ha⟩) | ⟨σ', -, ha⟩)
        · exact absurd ha (md_not_mem_chosen hπ)
        · simp [cycAtoms] at ha
        · simp at ha
      · rintro (ha | ⟨π, -, ha⟩)
        · exact absurd ha md_not_mem_levelAtoms
        · exact absurd ha linkAtom_ne_md
    | adj k b =>
      constructor
      · rintro ((⟨π, hπ, ha⟩ | ⟨σ', -, -, ha⟩) | ⟨σ', -, ha⟩)
        · exact absurd ha (adj_not_mem_chosen hπ)
        · simp [cycAtoms] at ha
        · simp at ha
      · rintro (ha | ⟨π, -, ha⟩)
        · exact absurd ha adj_not_mem_levelAtoms
        · exact absurd ha linkAtom_ne_adj
  · constructor
    · rintro ((⟨π, hπ, ha⟩ | ⟨σ', -, -, ha⟩) | ⟨σ', -, ha⟩)
      · obtain ⟨hπS, hl0, rfl⟩ := (inr_mem_chosen hπ).mp ha
        exact Or.inr ⟨e, hπS, linkAtom_eq_inr.mpr ⟨hl0, rfl⟩⟩
      · simp [cycAtoms] at ha
      · simp at ha
    · rintro (ha | ⟨π, hπS, ha⟩)
      · exact absurd ha inr_not_mem_levelAtoms
      · obtain ⟨hl0, rfl⟩ := linkAtom_eq_inr.mp ha
        exact Or.inl (Or.inl ⟨e, hS hπS, (inr_mem_chosen (hS hπS)).mpr ⟨hπS, hl0, rfl⟩⟩)

end Coverage

section Parity

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {S : Finset (Sym2 V)}
variable {rb : Atom V → V → ZMod 2}

theorem sum_epAtoms (hep : ∀ u j b, rb (Sum.inl (Req.ep l u j b)) = ind u + ind (h u))
    (u : V) (Q : Finset (ℕ × Bool)) (w : V) :
    ∑ a ∈ epAtoms l u Q, rb a w = (Q.card : ZMod 2) * (ind u w + ind (h u) w) := by
  unfold epAtoms
  rw [sum_image (by
    intro q _ q' _ hq
    simp only [Sum.inl.injEq, Req.ep.injEq] at hq
    exact Prod.ext hq.2.2.1 hq.2.2.2)]
  simp [hep, sum_const, nsmul_eq_mul, mul_add]

theorem sum_prAtoms (hpr : ∀ σ j b, ¬ σ.IsDiag → rb (Sum.inl (Req.pr l σ j b)) = symInd σ)
    {σ : Sym2 V} (hσ : ¬ σ.IsDiag) (Q : Finset (ℕ × Bool)) (w : V) :
    ∑ a ∈ prAtoms l σ Q, rb a w = (Q.card : ZMod 2) * symInd σ w := by
  unfold prAtoms
  rw [sum_image (by
    intro q _ q' _ hq
    simp only [Sum.inl.injEq, Req.pr.injEq] at hq
    exact Prod.ext hq.2.2.1 hq.2.2.2)]
  simp [hpr _ _ _ hσ, sum_const, nsmul_eq_mul]

omit [DecidableEq V] in
theorem map_eq_ends (h : V → V) (π : Sym2 V) :
    Sym2.map h π = s(h (endA π), h (endB π)) := by
  conv_lhs => rw [← mk_endA_endB π]
  rfl

/-- For a zero-boundary selection the final carry of every endpoint chain vanishes. -/
theorem vertex_final_carry (hS : S ⊆ Λ) (hS0 : ∑ π ∈ S, symInd π = 0) (u : V)
    (hN : 0 < (vChain Λ u).card) : curBit (xv Λ S u) ((vChain Λ u).card - 1) = false := by
  rw [curBit_last _ _ hN]
  unfold xv
  rw [card_selBits]
  have h1 : vChain Λ u ∩ S = S.filter (fun π => u ∈ π) := by
    ext π
    simp only [vChain, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨-, hu⟩, hπ⟩; exact ⟨hπ, hu⟩
    · rintro ⟨hπ, hu⟩; exact ⟨⟨hS hπ, hu⟩, hπ⟩
  have h2 : ((S.filter (fun π => u ∈ π)).card : ZMod 2) = 0 := by
    have := congrFun hS0 u
    simp only [Finset.sum_apply, symInd, Pi.zero_apply] at this
    rwa [sum_boole] at this
  rw [h1]
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at h2
  simp [h2]

theorem vR_card_cast (hS : S ⊆ Λ) (hS0 : ∑ π ∈ S, symInd π = 0) {u : V} {π : Sym2 V}
    (hπ : π ∈ vChain Λ u) :
    ((vR Λ S u π).card : ZMod 2) = if π ∈ S then 1 else 0 := by
  have hpos := pos_lt hπ
  unfold vR
  rw [recvLoc_card_sel _ hpos]
  · unfold xv; rw [selBits_pos hπ]; simp
  · intro hl
    rw [show pos (vChain Λ u) π = (vChain Λ u).card - 1 by omega]
    exact vertex_final_carry hS hS0 u (by omega)

theorem pR_card_cast {π : Sym2 V} (hπ : π ∈ Λ) :
    ((pR Λ h S π).card : ZMod 2) +
      (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
          finP Λ h S (Sym2.map h π) = true then 1 else 0) = if π ∈ S then 1 else 0 := by
  have hP : π ∈ pChain Λ h (Sym2.map h π) := mem_pChain.mpr ⟨hπ, rfl⟩
  have hpos := pos_lt hP
  have hiff : (pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
      finP Λ h S (Sym2.map h π) = true) ↔
      (pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
      curBit (xp Λ h S (Sym2.map h π)) (pos (pChain Λ h (Sym2.map h π)) π) = true) := by
    unfold finP
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rwa [show pos (pChain Λ h (Sym2.map h π)) π = (pChain Λ h (Sym2.map h π)).card - 1 by
        omega]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rwa [show (pChain Λ h (Sym2.map h π)).card - 1 = pos (pChain Λ h (Sym2.map h π)) π by
        omega]
  rw [if_congr hiff rfl rfl]
  unfold pR
  rw [recvLoc_card_pair _ hpos]
  unfold xp; rw [selBits_pos hP]; simp

theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := by decide

/-- **Parity of the active alternatives.** -/
theorem chosen_even (hΛ : ∀ π ∈ Λ, ¬ π.IsDiag)
    (hep : ∀ u j b, rb (Sum.inl (Req.ep l u j b)) = ind u + ind (h u))
    (hpr : ∀ σ j b, ¬ σ.IsDiag → rb (Sum.inl (Req.pr l σ j b)) = symInd σ)
    (htm : ∀ σ b, ¬ σ.IsDiag → rb (Sum.inl (Req.tm l σ b)) = symInd σ)
    (hlink : ∀ π ∈ Λ, rb (linkAtom l π) = symInd π)
    (hS : S ⊆ Λ) (hS0 : ∑ π ∈ S, symInd π = 0) {π : Sym2 V} (hπ : π ∈ Λ) :
    ∑ a ∈ levelPiece Λ h l (chosen Λ h l S π), rb a = 0 := by
  rw [altAtoms_chosen hπ]
  have hab : endA π ≠ endB π := endA_ne_endB (hΛ π hπ)
  have d1 : Disjoint (if π ∈ S then {linkAtom l π} else ∅)
      (epAtoms l (endA π) (vR Λ S (endA π) π)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨-, hx⟩ := mem_ite_empty.mp hx
    rw [mem_singleton] at hx
    subst hx
    obtain ⟨q, -, hq⟩ := mem_image.mp hx'
    exact linkAtom_ne_ep hq.symm
  have d2 : Disjoint ((if π ∈ S then {linkAtom l π} else ∅) ∪
      epAtoms l (endA π) (vR Λ S (endA π) π)) (epAtoms l (endB π) (vR Λ S (endB π) π)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨q, -, rfl⟩ := mem_image.mp hx'
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨-, hx⟩ := mem_ite_empty.mp hx
      exact linkAtom_ne_ep (mem_singleton.mp hx).symm
    · obtain ⟨-, h1, -⟩ := ep_mem_epAtoms.mp hx
      exact hab h1.symm
  have d3 : Disjoint ((if π ∈ S then {linkAtom l π} else ∅) ∪
      epAtoms l (endA π) (vR Λ S (endA π) π) ∪ epAtoms l (endB π) (vR Λ S (endB π) π))
      (if (Sym2.map h π).IsDiag then ∅ else prAtoms l (Sym2.map h π) (pR Λ h S π) ∪
        (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
            finP Λ h S (Sym2.map h π) = true
          then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨-, hx'⟩ := mem_ite_empty_left.mp hx'
    rcases mem_union.mp hx' with hx' | hx'
    · obtain ⟨q, -, rfl⟩ := mem_image.mp hx'
      simp only [mem_union, mem_ite_empty, mem_singleton, pr_mem_epAtoms, or_false] at hx
      exact linkAtom_ne_pr hx.2.symm
    · obtain ⟨-, hx'⟩ := mem_ite_empty.mp hx'
      rw [mem_singleton] at hx'
      subst hx'
      simp only [mem_union, mem_ite_empty, mem_singleton, tm_mem_epAtoms, or_false,
        tm_eq_linkAtom] at hx
      exact Bool.noConfusion hx.2.2.2.2
  rw [sum_union d3, sum_union d2, sum_union d1]
  funext w
  simp only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply]
  rw [sum_epAtoms hep, sum_epAtoms hep,
    vR_card_cast hS hS0 (mem_vChain.mpr ⟨hπ, endA_mem π⟩),
    vR_card_cast hS hS0 (mem_vChain.mpr ⟨hπ, endB_mem π⟩)]
  have hL : ∑ x ∈ (if π ∈ S then {linkAtom l π} else ∅), rb x w =
      (if π ∈ S then 1 else 0) * (ind (endA π) w + ind (endB π) w) := by
    split_ifs
    · rw [sum_singleton, hlink π hπ, symInd_eq_ends (hΛ π hπ)]; simp
    · simp
  have hP : ∑ x ∈ (if (Sym2.map h π).IsDiag then ∅ else
      prAtoms l (Sym2.map h π) (pR Λ h S π) ∪
        (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
            finP Λ h S (Sym2.map h π) = true
          then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅)), rb x w =
      (if π ∈ S then 1 else 0) * (ind (h (endA π)) w + ind (h (endB π)) w) := by
    by_cases hd : (Sym2.map h π).IsDiag
    · rw [ite_eq_left hd, sum_empty]
      rw [map_eq_ends, Sym2.mk_isDiag_iff] at hd
      rw [hd, CharTwo.add_self_eq_zero, mul_zero]
    · rw [ite_eq_right hd]
      have hdis : Disjoint (prAtoms l (Sym2.map h π) (pR Λ h S π))
          (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
            finP Λ h S (Sym2.map h π) = true
          then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅) := by
        rw [disjoint_left]
        intro x hx hx'
        obtain ⟨-, hx'⟩ := mem_ite_empty.mp hx'
        rw [mem_singleton] at hx'
        subst hx'
        exact tm_mem_prAtoms hx
      rw [sum_union hdis, sum_prAtoms hpr hd]
      have hsym : symInd (Sym2.map h π) = ind (h (endA π)) + ind (h (endB π)) := by
        rw [map_eq_ends]
        rw [map_eq_ends, Sym2.mk_isDiag_iff] at hd
        exact symInd_mk hd
      have hlastsum : ∑ x ∈ (if pos (pChain Λ h (Sym2.map h π)) π + 1 =
            (pChain Λ h (Sym2.map h π)).card ∧ finP Λ h S (Sym2.map h π) = true
          then {Sum.inl (Req.tm l (Sym2.map h π) false)} else ∅), rb x w =
          (if pos (pChain Λ h (Sym2.map h π)) π + 1 = (pChain Λ h (Sym2.map h π)).card ∧
            finP Λ h S (Sym2.map h π) = true then 1 else 0) * symInd (Sym2.map h π) w := by
        split_ifs
        · rw [sum_singleton, htm _ _ hd]; simp
        · simp
      rw [hlastsum, ← add_mul, pR_card_cast hπ, hsym]
      rfl
  rw [hL, hP]
  linear_combination ((if π ∈ S then 1 else 0) * (ind (endA π) w + ind (endB π) w +
    ind (h (endA π)) w + ind (h (endB π)) w)) * two_eq_zero_zmod

theorem cyc_even (htm : ∀ σ b, ¬ σ.IsDiag → rb (Sum.inl (Req.tm l σ b)) = symInd σ)
    {σ : Sym2 V} (hσ : ¬ σ.IsDiag) : ∑ a ∈ cycAtoms l σ, rb a = 0 := by
  unfold cycAtoms
  rw [sum_pair (by simp), htm _ _ hσ, htm _ _ hσ]
  funext w
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

end Parity

section Assembly

variable {Λ : Finset (Sym2 V)} {h : V → V} {l : ℕ} {S : Finset (Sym2 V)}
variable {rb : Atom V → V → ZMod 2}

/-- Exchange the two paths of a wire (or of a terminal pair). -/
def flipAtom : Atom V → Atom V
  | Sum.inl (Req.ep l u j b) => Sum.inl (Req.ep l u j (!b))
  | Sum.inl (Req.pr l σ j b) => Sum.inl (Req.pr l σ j (!b))
  | Sum.inl (Req.tm l σ b) => Sum.inl (Req.tm l σ (!b))
  | a => a

/-- The level atoms come in pairs with equal boundary, so their total boundary vanishes. -/
theorem levelAtoms_sum_zero [Fintype V]
    (hep : ∀ u j b, rb (Sum.inl (Req.ep l u j b)) = ind u + ind (h u))
    (hpr : ∀ σ j b, ¬ σ.IsDiag → rb (Sum.inl (Req.pr l σ j b)) = symInd σ)
    (htm : ∀ σ b, ¬ σ.IsDiag → rb (Sum.inl (Req.tm l σ b)) = symInd σ) :
    ∑ a ∈ levelAtoms Λ h l, rb a = 0 := by
  have hflip : ∀ a ∈ levelAtoms Λ h l, flipAtom a ∈ levelAtoms Λ h l ∧
      rb (flipAtom a) = rb a ∧ flipAtom a ≠ a ∧ flipAtom (flipAtom a) = a := by
    rintro (r | e) ha
    · cases r with
      | ep l' u j b =>
        obtain ⟨rfl, hj⟩ := ep_mem_levelAtoms.mp ha
        refine ⟨ep_mem_levelAtoms.mpr ⟨rfl, hj⟩, by simp only [flipAtom, hep], ?_, ?_⟩ <;>
          cases b <;> simp [flipAtom]
      | pr l' σ j b =>
        obtain ⟨rfl, hσ, hj⟩ := pr_mem_levelAtoms.mp ha
        have hd := (mem_nextLinks.mp hσ).2
        refine ⟨pr_mem_levelAtoms.mpr ⟨rfl, hσ, hj⟩, by simp only [flipAtom, hpr _ _ _ hd], ?_,
          ?_⟩ <;> cases b <;> simp [flipAtom]
      | tm l' σ b =>
        obtain ⟨rfl, hσ⟩ := tm_mem_levelAtoms.mp ha
        have hd := (mem_nextLinks.mp hσ).2
        refine ⟨tm_mem_levelAtoms.mpr ⟨rfl, hσ⟩, by simp only [flipAtom, htm _ _ hd], ?_,
          ?_⟩ <;> cases b <;> simp [flipAtom]
      | md k c b => exact absurd ha md_not_mem_levelAtoms
      | adj k b => exact absurd ha adj_not_mem_levelAtoms
    · exact absurd ha inr_not_mem_levelAtoms
  refine sum_involution (fun a _ => flipAtom a) ?_ ?_ (fun a ha => (hflip a ha).1)
    (fun a ha => (hflip a ha).2.2.2)
  · intro a ha
    rw [(hflip a ha).2.1]
    funext w
    exact CharTwo.add_self_eq_zero _
  · intro a ha _
    exact (hflip a ha).2.2.1

theorem levelAtoms_disjoint_links [Fintype V] :
    Disjoint (levelAtoms Λ h l) (S.image (linkAtom l)) := by
  rw [disjoint_left]
  intro a ha ha'
  obtain ⟨π, -, rfl⟩ := mem_image.mp ha'
  unfold linkAtom at ha
  split_ifs at ha with hl
  · exact inr_not_mem_levelAtoms ha
  · obtain ⟨h1, -⟩ := tm_mem_levelAtoms.mp ha
    omega

theorem cyc_disjoint_chosen {π σ : Sym2 V} (hπ : π ∈ Λ) (hf : finP Λ h S σ = false) :
    Disjoint (levelPiece Λ h l (chosen Λ h l S π)) (cycAtoms l σ) := by
  rw [disjoint_left]
  intro a ha ha'
  simp only [cycAtoms, mem_insert, mem_singleton] at ha'
  rcases ha' with rfl | rfl
  · rcases (tm_mem_chosen hπ).mp ha with ⟨-, -, -, -, h⟩ | ⟨-, ⟨-, hfin⟩, -, rfl, -⟩
    · exact Bool.noConfusion h
    · rw [hf] at hfin; exact Bool.noConfusion hfin
  · rcases (tm_mem_chosen hπ).mp ha with ⟨-, hl0, h1, -, -⟩ | ⟨-, -, -, -, h⟩
    · omega
    · exact Bool.noConfusion h

theorem chosenSet_pairwiseDisjoint :
    ((chosenSet Λ h l S : Finset (LibIdx V)) : Set (LibIdx V)).PairwiseDisjoint
      (levelPiece Λ h l) := by
  intro i hi j hj hij
  simp only [chosenSet, coe_union, coe_image, coe_filter, Set.mem_union, Set.mem_image,
    mem_coe, Set.mem_ofPred_eq] at hi hj
  rcases hi with ⟨π, hπ, rfl⟩ | ⟨σ, ⟨hσ, hf⟩, rfl⟩ <;>
    rcases hj with ⟨π', hπ', rfl⟩ | ⟨σ', ⟨hσ', hf'⟩, rfl⟩
  · exact chosen_disjoint hπ hπ' (fun e => hij (by rw [e]))
  · exact cyc_disjoint_chosen hπ hf'
  · exact (cyc_disjoint_chosen hπ' hf).symm
  · change Disjoint (cycAtoms l σ) (cycAtoms l σ')
    have hne : σ ≠ σ' := fun e => hij (by rw [e])
    rw [disjoint_left]
    intro a ha ha'
    simp only [cycAtoms, mem_insert, mem_singleton] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with h' | h' <;>
      simp only [Sum.inl.injEq, Req.tm.injEq] at h' <;>
      exact hne h'.2.1

theorem chosenSet_subset : chosenSet Λ h l S ⊆ levelLib Λ h l := by
  intro i hi
  simp only [chosenSet, mem_union, mem_image, mem_filter] at hi
  simp only [levelLib, mem_union, mem_image, mem_product, mem_univ, and_true]
  rcases hi with ⟨π, hπ, rfl⟩ | ⟨σ, ⟨hσ, -⟩, rfl⟩
  · exact Or.inl ⟨(π, _, _, _, _), hπ, rfl⟩
  · exact Or.inr ⟨σ, hσ, rfl⟩

theorem chosen_sep :
    Disjoint ((chosenSet Λ h l S).biUnion (levelPiece Λ h l))
      ((nextSel Λ h S).image (linkAtom (l + 1))) := by
  rw [disjoint_left]
  intro a ha ha'
  obtain ⟨σ, hσ, rfl⟩ := mem_image.mp ha'
  rw [linkAtom_succ] at ha
  obtain ⟨-, hfin⟩ := mem_filter.mp hσ
  rcases mem_chosenSet_biUnion.mp ha with ⟨π, hπ, ha⟩ | ⟨σ', -, hf, ha⟩
  · rcases (tm_mem_chosen hπ).mp ha with ⟨-, hl0, h1, -, -⟩ | ⟨-, -, -, -, h⟩
    · omega
    · exact Bool.noConfusion h
  · simp only [cycAtoms, mem_insert, mem_singleton, Sum.inl.injEq, Req.tm.injEq] at ha
    rcases ha with ⟨-, -, h⟩ | ⟨-, rfl, -⟩
    · exact Bool.noConfusion h
    · rw [hf] at hfin; exact Bool.noConfusion hfin

end Assembly

/-- **One level of parity transport.** -/
theorem level_transport [Fintype V] (Λ : Finset (Sym2 V)) (h : V → V) (l : ℕ)
    (hΛ : ∀ π ∈ Λ, ¬ π.IsDiag)
    (A : LibIdx V → Finset (Atom V))
    (hAalt : ∀ π x ca cb cs, A (LibIdx.alt l π x ca cb cs) = altAtoms Λ h l π x ca cb cs)
    (hAcyc : ∀ σ, A (LibIdx.cyc l σ) = cycAtoms l σ)
    (rb : Atom V → V → ZMod 2)
    (hep : ∀ u j b, rb (Sum.inl (Req.ep l u j b)) = ind u + ind (h u))
    (hpr : ∀ σ j b, ¬ σ.IsDiag → rb (Sum.inl (Req.pr l σ j b)) = symInd σ)
    (htm : ∀ σ b, ¬ σ.IsDiag → rb (Sum.inl (Req.tm l σ b)) = symInd σ)
    (hlink : ∀ π ∈ Λ, rb (linkAtom l π) = symInd π) :
    Transport A rb Λ (linkAtom l) (nextLinks Λ h) (linkAtom (l + 1)) (levelLib Λ h l)
      (levelAtoms Λ h l) := by
  intro S hS hS0
  have hS0' : ∑ π ∈ S, symInd π = 0 := by
    rw [← hS0]; exact sum_congr rfl (fun π hπ => (hlink π (hS hπ)).symm)
  have hAT : ∀ i ∈ chosenSet Λ h l S, A i = levelPiece Λ h l i := by
    intro i hi
    simp only [chosenSet, mem_union, mem_image, mem_filter] at hi
    rcases hi with ⟨π, -, rfl⟩ | ⟨σ, -, rfl⟩
    · exact hAalt _ _ _ _ _
    · exact hAcyc _
  have hU : (chosenSet Λ h l S).biUnion A = (chosenSet Λ h l S).biUnion (levelPiece Λ h l) :=
    biUnion_congr rfl hAT
  have hdisj : ((chosenSet Λ h l S : Finset (LibIdx V)) : Set (LibIdx V)).PairwiseDisjoint A := by
    intro i hi j hj hij
    change Disjoint (A i) (A j)
    rw [hAT i hi, hAT j hj]
    exact chosenSet_pairwiseDisjoint hi hj hij
  have heven : ∀ i ∈ chosenSet Λ h l S, ∑ a ∈ A i, rb a = 0 := by
    intro i hi
    rw [hAT i hi]
    simp only [chosenSet, mem_union, mem_image, mem_filter] at hi
    rcases hi with ⟨π, hπ, rfl⟩ | ⟨σ, ⟨hσ, -⟩, rfl⟩
    · exact chosen_even hΛ hep hpr htm hlink hS hS0' hπ
    · exact cyc_even htm (mem_nextLinks.mp hσ).2
  have hsep := chosen_sep (Λ := Λ) (h := h) (l := l) (S := S)
  have hcov := chosen_cover (h := h) (l := l) hS
  rw [← hU] at hsep hcov
  refine ⟨nextSel Λ h S, filter_subset _ _, ?_, chosenSet Λ h l S, chosenSet_subset, hdisj,
    heven, hsep, hcov⟩
  have key : ∑ a ∈ (chosenSet Λ h l S).biUnion A ∪ (nextSel Λ h S).image (linkAtom (l + 1)),
      rb a = ∑ a ∈ levelAtoms Λ h l ∪ S.image (linkAtom l), rb a := by rw [hcov]
  rw [sum_union hsep, sum_union levelAtoms_disjoint_links, sum_biUnion hdisj,
    sum_eq_zero heven, levelAtoms_sum_zero hep hpr htm, sum_image (fun x _ y _ e =>
      linkAtom_injective l e), hS0, zero_add, zero_add,
    sum_image (fun x _ y _ e => linkAtom_injective (l + 1) e)] at key
  exact key

end PartitionedTriangleAbsorption.UniversalRefiner

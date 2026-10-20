/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeF0

/-! # Pieces made of a lifted edge set and a set of charge tokens

The charge layer works on the vertex type `W0 ⊕ (Tok κ × Fin 8)`: the old vertices `W0`
and eight fresh vertices for every token identity. A token is a copy of `gadget sign` on its
eight vertices. A piece is `liftE A ∪ tokU S` for an edge set `A` on `W0` and a finite set
`S` of token identities. Disjointness, unions, loads, evenness and charge of such pieces are
computed componentwise.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge

/-- Token identities: private plus tokens `pp i k` of negative pieces, variable minus slots
`vm j`, buffer plus tokens `bp x` and fixed buffer minus tokens `bm y`. -/
inductive Tok (κ : Type*) where
  | pp (i : κ) (k : ℕ)
  | vm (j : ℕ)
  | bp (x : ℕ)
  | bm (y : ℕ)
  deriving DecidableEq

/-- `true` for plus tokens. -/
def Tok.sign {κ : Type*} : Tok κ → Bool
  | Tok.pp _ _ => true
  | Tok.vm _ => false
  | Tok.bp _ => true
  | Tok.bm _ => false

/-- The extended vertex type. -/
abbrev W1 (W0 κ : Type*) := W0 ⊕ (Tok κ × Fin 8)

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

/-- The part function on the extended vertex type. -/
def pw1 (pw0 : W0 → Fin 2) : W1 W0 κ → Fin 2
  | Sum.inl w => pw0 w
  | Sum.inr (t, j) => gadgetPart t.sign j

/-- Lift of an old edge set. -/
def liftE (E : Finset (Sym2 W0)) : Finset (Sym2 (W1 W0 κ)) := mapE Sum.inl E

/-- The edges of one token. -/
def tokE (t : Tok κ) : Finset (Sym2 (W1 W0 κ)) :=
  mapE (fun j => (Sum.inr (t, j) : W1 W0 κ)) (gadget t.sign)

/-- The edges of a set of tokens. -/
def tokU (S : Finset (Tok κ)) : Finset (Sym2 (W1 W0 κ)) := S.biUnion tokE

/-- A piece: lifted old edges and tokens. -/
def piece (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) : Finset (Sym2 (W1 W0 κ)) :=
  liftE A ∪ tokU S

omit [DecidableEq W0] [DecidableEq κ] in
theorem tokEmb_inj (t : Tok κ) : Function.Injective (fun j => (Sum.inr (t, j) : W1 W0 κ)) := by
  intro a b h; simpa using h

theorem incidentLoad_union_eq {V : Type*} [DecidableEq V] {A B : Finset (Sym2 V)}
    (h : Disjoint A B) (v : V) :
    incidentLoad (A ∪ B) v = incidentLoad A v + incidentLoad B v := by
  unfold incidentLoad
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

/-- Every vertex of an edge of a token is a vertex of that token. -/
theorem mem_tokE_vertex {t : Tok κ} {e : Sym2 (W1 W0 κ)} (he : e ∈ tokE t) {v : W1 W0 κ}
    (hv : v ∈ e) : ∃ j, v = Sum.inr (t, j) := by
  obtain ⟨e', -, rfl⟩ := mem_mapE.mp he
  obtain ⟨j, -, rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨j, rfl⟩

theorem mem_liftE_vertex {A : Finset (Sym2 W0)} {e : Sym2 (W1 W0 κ)} (he : e ∈ liftE A)
    {v : W1 W0 κ} (hv : v ∈ e) : ∃ w, v = Sum.inl w := by
  obtain ⟨e', -, rfl⟩ := mem_mapE.mp he
  obtain ⟨w, -, rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w, rfl⟩

theorem disjoint_liftE_tokU (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) :
    Disjoint (liftE (κ := κ) A) (tokU S) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨t, -, ht⟩ := mem_biUnion.mp he'
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
    induction e using Sym2.ind with | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  obtain ⟨w, rfl⟩ := mem_liftE_vertex he hv
  obtain ⟨j, hj⟩ := mem_tokE_vertex ht hv
  simp at hj

theorem disjoint_tokE {t t' : Tok κ} (h : t ≠ t') :
    Disjoint (tokE (W0 := W0) t) (tokE t') := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e := by
    induction e using Sym2.ind with | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  obtain ⟨j, rfl⟩ := mem_tokE_vertex he hv
  obtain ⟨j', hj'⟩ := mem_tokE_vertex he' hv
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hj'
  exact h hj'.1

theorem disjoint_tokU {S S' : Finset (Tok κ)} (h : Disjoint S S') :
    Disjoint (tokU (W0 := W0) S) (tokU S') := by
  unfold tokU
  rw [disjoint_biUnion_left]
  intro t ht
  rw [disjoint_biUnion_right]
  intro t' ht'
  exact disjoint_tokE (fun e => disjoint_left.mp h ht (e ▸ ht'))

theorem disjoint_piece {A A' : Finset (Sym2 W0)} {S S' : Finset (Tok κ)}
    (hA : Disjoint A A') (hS : Disjoint S S') : Disjoint (piece A S) (piece A' S') := by
  unfold piece
  rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
  exact ⟨⟨disjoint_mapE Sum.inl_injective hA, disjoint_liftE_tokU _ _⟩,
    (disjoint_liftE_tokU _ _).symm, disjoint_tokU hS⟩

theorem biUnion_piece {ι : Type*} (s : Finset ι) (A : ι → Finset (Sym2 W0))
    (S : ι → Finset (Tok κ)) :
    s.biUnion (fun i => piece (A i) (S i)) = piece (s.biUnion A) (s.biUnion S) := by
  unfold piece liftE tokU
  rw [mapE_biUnion, biUnion_biUnion, biUnion_union]

theorem piece_union (A A' : Finset (Sym2 W0)) (S S' : Finset (Tok κ)) :
    piece A S ∪ piece A' S' = piece (A ∪ A') (S ∪ S') := by
  unfold piece liftE tokU
  rw [mapE_union, union_biUnion]
  ext e; simp only [mem_union]; tauto

theorem incidentLoad_tokE_inl (t : Tok κ) (w : W0) :
    incidentLoad (tokE t) (Sum.inl w : W1 W0 κ) = 0 :=
  incidentLoad_mapE_of_not_mem _ (fun j => by simp)

theorem incidentLoad_tokE_inr (t t' : Tok κ) (j : Fin 8) :
    incidentLoad (tokE t') (Sum.inr (t, j) : W1 W0 κ) =
      if t' = t then incidentLoad (gadget t.sign) j else 0 := by
  split_ifs with h
  · subst h
    exact incidentLoad_mapE_apply (tokEmb_inj t') _ j
  · exact incidentLoad_mapE_of_not_mem _ (fun j' => by simp [h])

theorem incidentLoad_tokU (S : Finset (Tok κ)) (v : W1 W0 κ) :
    incidentLoad (tokU S) v = ∑ t ∈ S, incidentLoad (tokE (W0 := W0) t) v := by
  unfold tokU
  exact ModThreeLayer.incidentLoad_biUnion_eq _ _
    (fun t _ t' _ h => disjoint_tokE h) v

theorem incidentLoad_piece_inl (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) (w : W0) :
    incidentLoad (piece A S) (Sum.inl w) = incidentLoad A w := by
  unfold piece
  rw [incidentLoad_union_eq (disjoint_liftE_tokU _ _), incidentLoad_tokU]
  simp only [incidentLoad_tokE_inl, sum_const_zero, add_zero]
  exact incidentLoad_mapE_apply Sum.inl_injective _ _

theorem incidentLoad_piece_inr (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) (t : Tok κ)
    (j : Fin 8) : incidentLoad (piece A S) (Sum.inr (t, j)) =
      if t ∈ S then incidentLoad (gadget t.sign) j else 0 := by
  unfold piece
  rw [incidentLoad_union_eq (disjoint_liftE_tokU _ _), incidentLoad_tokU]
  rw [show incidentLoad (liftE (κ := κ) A) (Sum.inr (t, j)) = 0 from
    incidentLoad_mapE_of_not_mem _ (fun w => by simp), zero_add]
  simp only [incidentLoad_tokE_inr]
  rw [sum_ite_eq']

theorem even_piece {A : Finset (Sym2 W0)} (hA : ∀ w, Even (incidentLoad A w))
    (S : Finset (Tok κ)) : ∀ v, Even (incidentLoad (piece A S) v) := by
  rintro (w | ⟨t, j⟩)
  · rw [incidentLoad_piece_inl]; exact hA w
  · rw [incidentLoad_piece_inr]
    split_ifs
    · exact gadget_even _ j
    · exact ⟨0, rfl⟩

theorem loopless_piece {A : Finset (Sym2 W0)} (hA : ∀ e ∈ A, ¬ e.IsDiag) (S : Finset (Tok κ)) :
    ∀ e ∈ piece A S, ¬ e.IsDiag := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact loopless_mapE Sum.inl_injective hA e he
  · obtain ⟨t, -, ht⟩ := mem_biUnion.mp he
    exact loopless_mapE (tokEmb_inj t) (gadget_loopless _) e ht

/-- The charge of one token. -/
def tokCharge (t : Tok κ) : ℤ := if t.sign then 4 else -4

theorem charge_tokE (pw0 : W0 → Fin 2) (t : Tok κ) :
    charge chi0 (pw1 pw0) (tokE t) = tokCharge t := by
  unfold tokE
  rw [charge_mapE _ (tokEmb_inj t)]
  have : (pw1 pw0 ∘ fun j => (Sum.inr (t, j) : W1 W0 κ)) = gadgetPart t.sign := by
    funext j; rfl
  rw [this, gadget_charge]
  rfl

theorem charge_piece (pw0 : W0 → Fin 2) (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) :
    charge chi0 (pw1 pw0) (piece A S) = charge chi0 pw0 A + ∑ t ∈ S, tokCharge t := by
  unfold piece
  rw [charge_union _ _ (disjoint_liftE_tokU _ _)]
  congr 1
  · unfold liftE
    rw [charge_mapE _ Sum.inl_injective]
    rfl
  · unfold tokU
    rw [charge_biUnion _ _ _ _ (fun t _ t' _ h => disjoint_tokE h)]
    exact sum_congr rfl fun t _ => charge_tokE pw0 t

theorem card_piece_le (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) :
    (piece A S).card ≤ A.card + 8 * S.card := by
  unfold piece
  refine (card_union_le _ _).trans ?_
  rw [liftE, card_mapE Sum.inl_injective]
  refine Nat.add_le_add_left ?_ _
  unfold tokU
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun t _ => ?_
  rw [tokE, card_mapE (tokEmb_inj t)]
  exact gadget_card_le _

/-- **Divisibility of a piece**: loopless even old part and zero total charge. -/
theorem isIntDiv_piece (pw0 : W0 → Fin 2) {A : Finset (Sym2 W0)} (hl : ∀ e ∈ A, ¬ e.IsDiag)
    (he : ∀ w, Even (incidentLoad A w)) (S : Finset (Tok κ))
    (hq : charge chi0 pw0 A + ∑ t ∈ S, tokCharge t = 0) :
    IsIntDiv (pw1 pw0) TypedApplicationLinks.F0 (piece A S) :=
  isIntDiv_of_charge _ (loopless_piece hl S) (even_piece he S)
    (by rw [charge_piece]; exact hq)

/-- Old edge sets inside the lift. -/
theorem exists_liftE_of_subset {X0 : Finset (Sym2 W0)} {L : Finset (Sym2 (W1 W0 κ))}
    (h : L ⊆ liftE X0) : ∃ L0 ⊆ X0, L = liftE L0 := by
  refine ⟨X0.filter fun e => Sym2.map Sum.inl e ∈ L, filter_subset _ _, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp (h he)
    exact mem_mapE.mpr ⟨e', mem_filter.mpr ⟨he', he⟩, rfl⟩
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
    exact (mem_filter.mp he').2

end PartitionedTriangleAbsorption.TypedRefinerF0

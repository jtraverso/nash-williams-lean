/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Level

/-!
# The hub hierarchy: telescoping of the levels, on atoms

Given the reserve links `X` and hub maps `hmap l` for every level `l`, the link families of the
hierarchy are `links X hmap 0 = X` and `links X hmap (l+1) = nextLinks (links X hmap l) (hmap l)`.
The global library `piece` gathers the level libraries; the adjustment cycles are always
active.  `parity_refiner` proves, on atoms, that the whole parity library refines every
zero-boundary selection of reserve edges, provided the last link family is empty.

The boundary of an atom is computed from the roots of the requests (`rootPair`): the realised
two-edge path of a request with distinct roots `u, v` has boundary `1_u + 1_v`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset

variable {V : Type*} [DecidableEq V]

/-- The link families of the hierarchy. -/
def links (X : Finset (Sym2 V)) (hmap : ℕ → V → V) : ℕ → Finset (Sym2 V)
  | 0 => X
  | l + 1 => nextLinks (links X hmap l) (hmap l)

/-- The two paths of adjustment cycle `k`. -/
def adjAtoms (k : ℕ) : Finset (Atom V) := {Sum.inl (Req.adj k false), Sum.inl (Req.adj k true)}

/-- The atoms of every library index of the hierarchy. -/
noncomputable def piece (X : Finset (Sym2 V)) (hmap : ℕ → V → V) : LibIdx V → Finset (Atom V)
  | LibIdx.alt l π x ca cb cs => altAtoms (links X hmap l) (hmap l) l π x ca cb cs
  | LibIdx.cyc l σ => cycAtoms l σ
  | LibIdx.adj k => adjAtoms k

/-- The parity library of the first `L` levels. -/
def parLib (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) : Finset (LibIdx V) :=
  (range L).biUnion fun l => levelLib (links X hmap l) (hmap l) l

/-- The atoms created by the first `L` levels. -/
def parRem [Fintype V] (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ) : Finset (Atom V) :=
  (range L).biUnion fun l => levelAtoms (links X hmap l) (hmap l) l

/-- The always-active adjustment pieces. -/
def adjLib (a : ℕ) : Finset (LibIdx V) := (range a).image LibIdx.adj

/-- The atoms of the adjustment cycles. -/
def adjRem (a : ℕ) : Finset (Atom V) := (range a).biUnion adjAtoms

/-- Roots of the requests. Mod-three wires and adjustment cycles get prescribed roots. -/
noncomputable def rootPair (hmap : ℕ → V → V) (mdr : ℕ → V × V) (adr : V × V) :
    Req V → V × V
  | Req.ep l u _ _ => (u, hmap l u)
  | Req.pr _ σ _ _ => (endA σ, endB σ)
  | Req.tm _ σ _ => (endA σ, endB σ)
  | Req.md k _ _ => mdr k
  | Req.adj _ _ => adr

/-- Boundary of an atom, computed from roots. -/
def rbOf (rt : Req V → V × V) : Atom V → V → ZMod 2
  | Sum.inl r => ind (rt r).1 + ind (rt r).2
  | Sum.inr e => symInd e

theorem links_not_diag {X : Finset (Sym2 V)} {hmap : ℕ → V → V} (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∀ l, ∀ π ∈ links X hmap l, ¬ π.IsDiag
  | 0 => hX
  | _ + 1 => fun _ hπ => (mem_nextLinks.mp hπ).2

omit [DecidableEq V] in
theorem linkAtom_zero : (linkAtom 0 : Sym2 V → Atom V) = Sum.inr := by
  funext π; simp [linkAtom]

theorem levelAtoms_disjoint_levels [Fintype V] {Λ Λ' Λ'' : Finset (Sym2 V)} {h h' : V → V} {l m : ℕ}
    (hlm : l < m) :
    Disjoint (levelAtoms Λ' h' m) (levelAtoms Λ h l ∪ Λ''.image (linkAtom l)) := by
  rw [disjoint_left]
  rintro (r | e) ha ha'
  · rcases mem_union.mp ha' with ha' | ha'
    · cases r with
      | ep l' u j b =>
        exact absurd ((ep_mem_levelAtoms.mp ha).1.symm.trans (ep_mem_levelAtoms.mp ha').1)
          (by omega)
      | pr l' σ j b =>
        exact absurd ((pr_mem_levelAtoms.mp ha).1.symm.trans (pr_mem_levelAtoms.mp ha').1)
          (by omega)
      | tm l' σ b =>
        exact absurd ((tm_mem_levelAtoms.mp ha).1.symm.trans (tm_mem_levelAtoms.mp ha').1)
          (by omega)
      | md k c b => exact md_not_mem_levelAtoms ha
      | adj k b => exact adj_not_mem_levelAtoms ha
    · obtain ⟨π, -, hπ⟩ := mem_image.mp ha'
      cases r with
      | ep l' u j b => exact linkAtom_ne_ep hπ
      | pr l' σ j b => exact linkAtom_ne_pr hπ
      | tm l' σ b =>
        obtain ⟨-, h1, -⟩ := linkAtom_eq_tm.mp hπ
        exact absurd ((tm_mem_levelAtoms.mp ha).1.symm.trans h1) (by omega)
      | md k c b => exact linkAtom_ne_md hπ
      | adj k b => exact linkAtom_ne_adj hπ
  · exact inr_not_mem_levelAtoms ha

/-- **The parity library of the hierarchy is a refiner** (on atoms). -/
theorem parity_refiner [Fintype V] (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (L : ℕ)
    (hX : ∀ e ∈ X, ¬ e.IsDiag) (hlast : links X hmap L = ∅)
    (mdr : ℕ → V × V) (adr : V × V) (a : ℕ) :
    Refiner (piece X hmap) (rbOf (rootPair hmap mdr adr)) X Sum.inr
      (parLib X hmap L ∪ adjLib a) (parRem X hmap L ∪ adjRem a) := by
  have hlev : Refiner (piece X hmap) (rbOf (rootPair hmap mdr adr)) (links X hmap 0)
      (linkAtom 0) ((range L).biUnion fun l => levelLib (links X hmap l) (hmap l) l)
      ((range L).biUnion fun l => levelAtoms (links X hmap l) (hmap l) l) := by
    refine refiner_of_levels (links X hmap) linkAtom
      (fun l => levelLib (links X hmap l) (hmap l) l)
      (fun l => levelAtoms (links X hmap l) (hmap l) l) L ?_ hlast ?_
    · intro l _
      refine level_transport (links X hmap l) (hmap l) l (links_not_diag hX l) (piece X hmap)
        (fun _ _ _ _ _ => rfl) (fun _ => rfl) _ (fun _ _ _ => rfl) ?_ ?_ ?_
      · intro σ _ _ hσ; exact (symInd_eq_ends hσ).symm
      · intro σ _ hσ; exact (symInd_eq_ends hσ).symm
      · intro π hπ
        rcases l with _ | k
        · simp [linkAtom, rbOf]
        · simp only [linkAtom, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, rbOf,
            rootPair]
          exact (symInd_eq_ends (links_not_diag hX _ π hπ)).symm
    · intro l _ m hlm _
      exact levelAtoms_disjoint_levels hlm
  have hadj := refiner_add_always (adjLib a) hlev ?_ ?_ ?_
  · rw [linkAtom_zero] at hadj
    have hC : (adjLib a).biUnion (piece X hmap) = adjRem a := by
      simp [adjLib, adjRem, image_biUnion, piece]
    rw [hC] at hadj
    exact hadj
  · intro i hi j hj hij
    obtain ⟨k, -, rfl⟩ := mem_image.mp (mem_coe.mp hi)
    obtain ⟨k', -, rfl⟩ := mem_image.mp (mem_coe.mp hj)
    have hne : k ≠ k' := fun e => hij (by rw [e])
    change Disjoint (adjAtoms k) (adjAtoms k')
    rw [disjoint_left]
    intro x hx hx'
    simp only [adjAtoms, mem_insert, mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;>
      simp only [Sum.inl.injEq, Req.adj.injEq] at h' <;>
      exact hne h'.1
  · intro i hi
    obtain ⟨k, -, rfl⟩ := mem_image.mp hi
    change Disjoint (adjAtoms k) _
    rw [disjoint_left]
    intro x hx hx'
    simp only [adjAtoms, mem_insert, mem_singleton] at hx
    rcases mem_union.mp hx' with hx' | hx'
    · obtain ⟨l, -, hl⟩ := mem_biUnion.mp hx'
      rcases hx with rfl | rfl <;> exact adj_not_mem_levelAtoms hl
    · obtain ⟨π, -, hπ⟩ := mem_image.mp hx'
      rcases hx with rfl | rfl <;> exact linkAtom_ne_adj hπ
  · intro i hi
    obtain ⟨k, -, rfl⟩ := mem_image.mp hi
    change ∑ x ∈ adjAtoms k, _ = 0
    rw [adjAtoms, sum_pair (by simp)]
    funext w
    simp only [rbOf, rootPair, Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

end PartitionedTriangleAbsorption.UniversalRefiner

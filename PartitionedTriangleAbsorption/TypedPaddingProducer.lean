/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLatticePadding
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fin.VecNotation

/-! # Constructing the lattice padding

The returned padding interface assumes that the fresh triangles of each type have already
been supplied. Here their index set and their labels are constructed from the negative
parts of the lattice coefficients. This is an abstract finite extension, not an embedding
in the original host. No absorber or universal refiner is asserted by this construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedPaddingProducer

open Finset TypedLatticePadding

variable {t : ℕ}

theorem exists_word {τ : Multiset (Fin t)} (hτ : τ.card = 3) :
    ∃ w : Fin 3 → Fin t, ({w 0, w 1, w 2} : Multiset (Fin t)) = τ := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < τ.card by omega)
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hs : s.card = 2 := by simpa using hτ
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < s.card by omega)
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hb
  have hs' : s'.card = 1 := by simpa using hs
  obtain ⟨d, rfl⟩ := Multiset.card_eq_one.mp hs'
  exact ⟨![a, b, d], rfl⟩

/-- One index for every unit of negative coefficient of an allowed type. -/
abbrev Index (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) :=
  (τ : {τ // τ ∈ F}) × Fin ((-c τ.val).toNat)

instance (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) :
    DecidableEq (Index F c) := inferInstanceAs (DecidableEq (Sigma _))

noncomputable def labels (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) (c : Multiset (Fin t) → ℤ) :
    Index F c → Fin 3 → Fin t :=
  fun x => (exists_word (hF x.1.val x.1.property)).choose

theorem labels_type (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) (c : Multiset (Fin t) → ℤ) (x : Index F c) :
    padType (labels F hF c) x = x.1.val :=
  (exists_word (hF x.1.val x.1.property)).choose_spec

theorem labels_allowed (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) (c : Multiset (Fin t) → ℤ) (x : Index F c) :
    padType (labels F hF c) x ∈ F := by
  rw [labels_type]
  exact x.1.property

theorem index_card (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) :
    Fintype.card (Index F c) = ∑ τ ∈ F, (-c τ).toNat := by
  classical
  simp only [Index, Fintype.card_sigma, Fintype.card_fin]
  exact F.sum_coe_sort (fun τ => (-c τ).toNat)

theorem padding_vector {W : Type*} [DecidableEq W]
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℤ) (p : W → Fin t) :
    edgeVec (extPart p (labels F hF c)) (padding (W := W) (T := Index F c)) =
      ∑ τ ∈ F, (max (-c τ) 0) • typeEdgeVec τ := by
  classical
  rw [edgeVec_padding]
  simp only [labels_type, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fin]
  rw [← F.sum_coe_sort]
  apply sum_congr rfl
  intro τ _
  rw [← natCast_zsmul, Int.toNat_eq_max]

/-- The producer removes the counting hypothesis from `padded_coefficients`. -/
theorem positive_padded_vector {W : Type*} [DecidableEq W]
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (c : Multiset (Fin t) → ℤ) (p : W → Fin t) (P : Finset (Sym2 W))
    (hc : edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ) :
    edgeVec (extPart p (labels F hF c))
      (liftE (T := Index F c) P ∪ padding (W := W) (T := Index F c)) =
        ∑ τ ∈ F, (max (c τ) 0) • typeEdgeVec τ := by
  classical
  rw [edgeVec_union _ (padding_disjoint_lift (T := Index F c) P),
    edgeVec_liftE, padding_vector, hc]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro τ _
  rw [← add_smul]
  congr 1
  omega

/-- Exact cost of the constructed padding; a separate choice of bounded coefficients
is needed before this becomes uniform over a bounded library of input pieces. -/
theorem padding_size {W : Type*} [DecidableEq W]
    (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) :
    (padding (W := W) (T := Index F c)).card = 3 * ∑ τ ∈ F, (-c τ).toNat := by
  classical
  rw [padding_card, index_card]

end PartitionedTriangleAbsorption.TypedPaddingProducer

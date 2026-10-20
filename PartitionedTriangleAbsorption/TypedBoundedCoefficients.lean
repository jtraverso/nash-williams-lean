/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPaddingProducer

/-! # Uniformly bounded choices of lattice coefficients

For fixed types and a bound on the number of edges, only finitely many edge vectors occur.
Choose one integral representation of each representable vector, then take the maximum of
their negative masses. The bound precedes the vertex type, partition, and input piece.
It does not bound every possible coefficient witness and supplies no explicit growth rate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedBoundedCoefficients

open Finset TypedLatticePadding TypedPaddingProducer

variable {t : ℕ}

def negativeMass (F : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) : ℕ :=
  ∑ τ ∈ F, (-c τ).toNat

/-- A finite family of representable vectors admits bounded choices of witnesses. -/
theorem finite_choice_bound {I : Type*} [Finite I]
    (F : Finset (Multiset (Fin t))) (v : I → Fin t → Fin t → ℤ) :
    ∃ B : ℕ, ∀ i, (∃ c : Multiset (Fin t) → ℤ, v i = ∑ τ ∈ F, c τ • typeEdgeVec τ) →
      ∃ c, v i = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B := by
  classical
  let _ := Fintype.ofFinite I
  have hchoice : ∀ i, ∃ c : Multiset (Fin t) → ℤ,
      (∃ d : Multiset (Fin t) → ℤ, v i = ∑ τ ∈ F, d τ • typeEdgeVec τ) →
        v i = ∑ τ ∈ F, c τ • typeEdgeVec τ := by
    intro i
    by_cases h : ∃ d : Multiset (Fin t) → ℤ, v i = ∑ τ ∈ F, d τ • typeEdgeVec τ
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨0, fun hd => (h hd).elim⟩
  choose c hc using hchoice
  refine ⟨univ.sup (fun i => negativeMass F (c i)), fun i hi => ?_⟩
  exact ⟨c i, hc i hi, le_sup (f := fun i => negativeMass F (c i)) (mem_univ i)⟩

theorem edgeVec_bounds {W : Type*} (p : W → Fin t) (P : Finset (Sym2 W))
    (i j : Fin t) : 0 ≤ edgeVec p P i j ∧ edgeVec p P i j ≤ 2 * (P.card : ℤ) := by
  have hp : ∀ e : Sym2 W, 0 ≤ pairVec p e i j ∧ pairVec p e i j ≤ 2 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [pairVec, Sym2.lift_mk]
      split_ifs <;> norm_num
  simp only [edgeVec, Finset.sum_apply]
  refine ⟨sum_nonneg (fun e _ => (hp e).1), ?_⟩
  calc _ ≤ ∑ _e ∈ P, (2 : ℤ) := sum_le_sum fun e _ => (hp e).2
    _ = _ := by simp [mul_comm]

/-- The bound depends only on `F` and `K`, not on the input graph or a supplied witness. -/
theorem bounded_coefficients (F : Finset (Multiset (Fin t))) (K : ℕ) :
    ∃ B : ℕ, ∀ {W : Type} (p : W → Fin t) (P : Finset (Sym2 W)), P.card ≤ K →
      (∃ c : Multiset (Fin t) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ) →
        ∃ c, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B := by
  obtain ⟨B, hB⟩ := finite_choice_bound F
    (fun v : Fin t → Fin t → Fin (2 * K + 1) => fun i j => (v i j : ℤ))
  refine ⟨B, fun {W} p P hK hc => ?_⟩
  let v : Fin t → Fin t → Fin (2 * K + 1) := fun i j =>
    ⟨(edgeVec p P i j).toNat, by have := edgeVec_bounds p P i j; omega⟩
  have hv : (fun i j => (v i j : ℤ)) = edgeVec p P := by
    funext i j
    exact Int.toNat_of_nonneg (edgeVec_bounds p P i j).1
  simpa only [hv] using hB v (by simpa only [hv] using hc)

/-- Signed lattice pieces of bounded size can be padded with uniformly bounded cost.
The padding is decomposable and avoids every original vertex by the producer lemmas. -/
theorem bounded_padding (F : Finset (Multiset (Fin t))) (K : ℕ) :
    ∃ B : ℕ, ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
      P.card ≤ K → (∃ c : Multiset (Fin t) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ) →
        ∃ c, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧
          (padding (W := W) (T := Index F c)).card ≤ 3 * B := by
  obtain ⟨B, hB⟩ := bounded_coefficients F K
  refine ⟨B, fun {W} _ p P hK hc => ?_⟩
  obtain ⟨c, hc, hmass⟩ := hB p P hK hc
  refine ⟨c, hc, ?_⟩
  rw [padding_size]
  exact Nat.mul_le_mul_left 3 hmass

/-- A complete padding producer: bounded cost, no old vertices, a decomposition of the
padding, and nonnegative global coefficients of the padded piece. This does not yet
construct an absorber of that piece. -/
theorem bounded_padding_package (F : Finset (Multiset (Fin t)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) (K : ℕ) :
    ∃ B : ℕ, ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
      P.card ≤ K → (∃ c : Multiset (Fin t) → ℤ, edgeVec p P =
        ∑ τ ∈ F, c τ • typeEdgeVec τ) →
      ∃ c : Multiset (Fin t) → ℤ,
        let σ := labels F hF c
        let Q := padding (W := W) (T := Index F c)
        Disjoint (liftE (T := Index F c) P) Q ∧
        HasDecomp (extPart p σ) F Q ∧ Q.card ≤ 3 * B ∧
        (∀ w : W, AntiEdgeSelection.incidentLoad Q (Sum.inl w) = 0) ∧
        edgeVec (extPart p σ) (liftE P ∪ Q) =
          ∑ τ ∈ F, (max (c τ) 0) • typeEdgeVec τ := by
  obtain ⟨B, hB⟩ := bounded_padding F K
  refine ⟨B, fun {W} _ p P hK hc => ?_⟩
  obtain ⟨c, hc, hsize⟩ := hB p P hK hc
  refine ⟨c, padding_disjoint_lift P,
    padding_hasDecomp p (labels F hF c) (labels_allowed F hF c), hsize,
    fun w => padding_avoids_original w, positive_padded_vector F hF c p P hc⟩

end PartitionedTriangleAbsorption.TypedBoundedCoefficients

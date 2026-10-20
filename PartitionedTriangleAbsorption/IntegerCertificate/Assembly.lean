/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Hubs
public import PartitionedTriangleAbsorption.IntegerCertificate.Divisibility

/-! # Assembling edge and vertex reductions

`hubReduces_ind`: if every edge `e = uv` of a loopless, even-degree source `P` satisfies
`[e] + D u + D v ≡ 0` (hub-reduction with cost `(wE, ME)`), and twice every vertex term
`2·D y` hub-reduces with cost `(wV, MV)`, then `ind P` hub-reduces with cost
`(|P|(wE + wV), |P|(ME + MV))`. The vertex terms cancel exactly because
`∑_{e ∈ P} ∑_{y ∈ e} D y = ∑_y deg_P(y) · D y` and each degree is even.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2} {G : SimpleGraph V}

omit [Fintype V] in
theorem ind_eq_sum_edgeOf (P : Finset (Sym2 V)) :
    ind P = ∑ e ∈ P, edgeOf e := by
  funext e'
  simp [ind, edgeOf, sum_apply]

theorem sum_endpoints (P : Finset (Sym2 V)) (D : V → Sym2 V → ℤ) :
    ∑ e ∈ P, ∑ y ∈ univ.filter (· ∈ e), D y = ∑ y, (deg P y : ℤ) • D y := by
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_filter, sum_const, deg, natCast_zsmul]

theorem filter_mem_mk {a b : V} : univ.filter (· ∈ s(a, b)) = ({a, b} : Finset V) := by
  ext y; simp [Sym2.mem_iff]

theorem card_filter_mem {e : Sym2 V} (he : ¬ e.IsDiag) : (univ.filter (· ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
  rw [filter_mem_mk, card_pair (by simpa using he)]

/-- Handshake: the degrees of a loopless edge set sum to `2|P|`. -/
theorem sum_deg {P : Finset (Sym2 V)} (hP : ∀ e ∈ P, ¬ e.IsDiag) :
    ∑ y, deg P y = 2 * P.card := by
  calc ∑ y, deg P y = ∑ y, ∑ e ∈ P, (if y ∈ e then 1 else 0) :=
        sum_congr rfl fun y _ => by rw [deg, card_filter]
    _ = ∑ e ∈ P, ∑ y, (if y ∈ e then 1 else 0) := sum_comm
    _ = ∑ e ∈ P, 2 := sum_congr rfl fun e he => by
        rw [← card_filter]; exact card_filter_mem (hP e he)
    _ = 2 * P.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **Assembly.** Edge reductions plus doubled vertex reductions give a hub reduction of the
whole even-degree source. -/
theorem hubReduces_ind {H : Hubs V} {P : Finset (Sym2 V)} (hP : ∀ e ∈ P, ¬ e.IsDiag)
    (hdeg : ∀ y, ∃ k : ℕ, deg P y = 2 * k) (D : V → Sym2 V → ℤ) {wE ME wV MV : ℤ}
    (hE : ∀ e ∈ P, HubReduces p G H (edgeOf e + ∑ y ∈ univ.filter (· ∈ e), D y) wE ME)
    (hV : ∀ y, 0 < deg P y → HubReduces p G H (2 • D y) wV MV) :
    HubReduces p G H (ind P) (P.card * (wE + wV)) (P.card * (ME + MV)) := by
  choose k hk using hdeg
  have hsumk : ∑ y, (k y : ℤ) = P.card := by
    have h := sum_deg hP
    simp only [hk, ← mul_sum] at h
    exact_mod_cast (by omega : ∑ y, k y = P.card)
  have key : ind P = ∑ e ∈ P, (edgeOf e + ∑ y ∈ univ.filter (· ∈ e), D y) -
      ∑ y, (k y : ℤ) • (2 • D y) := by
    rw [sum_add_distrib, sum_endpoints, ind_eq_sum_edgeOf]
    have : ∀ y, (deg P y : ℤ) • D y = (k y : ℤ) • (2 • D y) := by
      intro y; rw [hk y]; funext e
      simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
    simp only [this, add_sub_cancel_right]
  have h1 := HubReduces.sum P _ (fun _ => wE) (fun _ => ME) hE
  have h2 := HubReduces.sum univ (fun y => (k y : ℤ) • (2 • D y)) (fun y => k y * wV)
    (fun y => k y * MV) (fun y _ => by
      by_cases hk0 : k y = 0
      · refine (HubReduces.of_realizes (p := p) (G := G) (H := H) Realizes.zero).congr ?_
          |>.mono ?_ ?_
        all_goals simp [hk0]
      · have := (hV y (by rw [hk y]; omega)).smul (k y)
        simpa [abs_of_nonneg (Int.natCast_nonneg (k y))] using this)
  refine ((h1.sub h2).congr key.symm).mono ?_ ?_
  · simp only [sum_const, nsmul_eq_mul, ← sum_mul, hsumk]; ring_nf; rfl
  · simp only [sum_const, nsmul_eq_mul, ← sum_mul, hsumk]; ring_nf; rfl

/-- **Closing.** Combined with zero charge, the hub reduction of `ind P` is a signed physical
certificate of weight `≤ |P|(wE + wV) + 7|P|(ME + MV)`. -/
theorem signedCert_of_reductions {H : Hubs V} (hH : H.Good p G) {P : Finset (Sym2 V)}
    (hP : ∀ e ∈ P, ¬ e.IsDiag) (hdiv : IsIntDiv p F0 P) (D : V → Sym2 V → ℤ)
    {wE ME wV MV : ℤ}
    (hE : ∀ e ∈ P, HubReduces p G H (edgeOf e + ∑ y ∈ univ.filter (· ∈ e), D y) wE ME)
    (hV : ∀ y, 0 < deg P y → HubReduces p G H (2 • D y) wV MV) :
    Realizes p G (ind P) (P.card * (wE + wV) + 7 * (P.card * (ME + MV))) :=
  realizes_of_hubReduces hH
    (hubReduces_ind hP (even_degree_of_isIntDiv hdiv hP) D hE hV)
    (charge_ind_of_isIntDiv hdiv)

end PartitionedTriangleAbsorption.IntegerCertificate

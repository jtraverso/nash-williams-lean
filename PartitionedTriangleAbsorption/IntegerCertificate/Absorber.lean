/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Local
public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Consumer

/-! # Task 2 (candidate form) and Task 3: the certificate producer feeds the signed absorber

* `cn6_certificate_uniform` is the Stage 61 candidate verbatim: for `β > 0` and `m`, the
  constants `K = 137 m` and `N = 1` are fixed before `V, p, G, P`.
* `cn6_signed_absorber` removes the `IsSignedCert` premise of
  `PhysicalHingeSupply.signed_absorber_of_commonNbrRich` for **every** physical F0-divisible
  source with at most `m` edges in a `CN6` host. The constants `C, N` depend only on `β, m`
  and are chosen before the host and the source. The protected vertex set is `Z = V(P)`.
  The conclusion is the consumer's unchanged physical contract: the same physical `A, Q`,
  exact F0 decompositions and all three part-pair counts.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks F0Geometric SignedHinge

/-- **The Stage 61 candidate (Task 2).** For each `β > 0` and `m`, integers `K, N` chosen
before `V, p, G, P` such that `n ≥ N`, `CN6 p G β`, `P ⊆ E(G)`, `|P| ≤ m` and
`IsIntDiv p F0 P` give a signed physical integer certificate of weight `≤ K`. -/
theorem cn6_certificate_uniform (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ K N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Sym2 V)),
        CN6 p G β → P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F0 P →
        ∃ (ι : Type) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
          IsSignedCert p G P t c ∧ certWeight c ≤ K := by
  refine ⟨137 * m, 1, ?_⟩
  intro V _ _ hN p G _ P hG hPG hm hdiv
  have hpos : 0 < β * Fintype.card V :=
    mul_pos hβ (by exact_mod_cast (show 0 < Fintype.card V by omega))
  obtain ⟨ι, hι, t, c, hc, hw⟩ := cn6_certificate hG hpos hPG hdiv
  refine ⟨ι, hι, t, c, hc, hw.trans ?_⟩
  push_cast
  have : (P.card : ℤ) ≤ m := by exact_mod_cast hm
  linarith

/-- **Certificates on a remaining host.** If `G` satisfies `CN6(β)` and `J` misses at most
`d ≤ βn/12` edges of `G` at every vertex (for instance `J = G` minus a sparse deletion), then
every physical F0-divisible source inside `J` has a certificate of weight `≤ 137|P|` made of
actual F0 triangles **of `J`**. -/
theorem cn6_certificate_after_deletion {V : Type} [Fintype V] [DecidableEq V]
    {p : V → Fin 2} {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj] {β d : ℝ}
    (hG : CN6 p G β) (hpos : 0 < β * Fintype.card V) (hd : 0 ≤ d)
    (hdel : ∀ v, ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤ d)
    (hdβ : 12 * d ≤ β * Fintype.card V) {P : Finset (Sym2 V)} (hPJ : P ⊆ J.edgeFinset)
    (hdiv : IsIntDiv p F0 P) :
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
      IsSignedCert p J P t c ∧ certWeight c ≤ 137 * P.card := by
  have hJ : CN6 p J (β / 2) :=
    commonNbrRich_of_delete p G J hd hdel (by push_cast; linarith) hG
  exact cn6_certificate hJ (by linarith) hPJ hdiv

/-- **Task 3: certificate producer composed with the signed absorber.** For `β > 0` and `m`,
constants `C, N` (chosen before the host and the source) such that every `CN6 p G β` host of
order `≥ N` and every physical F0-divisible source `P ⊆ E(G)` with `|P| ≤ m` admit the
signed absorber of `signed_absorber_of_commonNbrRich`, with protected set `V(P)`. No
certificate is assumed. -/
theorem cn6_signed_absorber (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ C N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj], CN6 p G β →
      ∀ P : Finset (Sym2 V), P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F0 P →
        ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧
          Disjoint P A ∧ Disjoint P Q ∧ Disjoint A Q ∧ (∀ e ∈ Q, ∀ v ∈ e, v ∉ vertSet P) ∧
          (∃ D, IsDecomp p F0 Q D ∧ (D : Set (Finset V)).PairwiseDisjoint id) ∧
          HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧ HasDecomp p F0 (A ∪ Q) ∧
          A.card ≤ C * m ∧ Q.card ≤ C * m ∧ (vertSet (A ∪ Q)).card ≤ C * m ∧
          pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
          pairCount p Q 0 1 = pairCount p P 0 1 := by
  obtain ⟨C0, N0, habs⟩ := PhysicalHingeSupply.signed_absorber_of_commonNbrRich β hβ (137 * m)
  refine ⟨C0 * 137, max N0 1, ?_⟩
  intro V _ _ hN p G _ hG P hPG hm hdiv
  have hpos : 0 < β * Fintype.card V :=
    mul_pos hβ (by exact_mod_cast (show 0 < Fintype.card V by omega))
  obtain ⟨ι, hι, t, c, hc, hw⟩ := cn6_certificate hG hpos hPG hdiv
  have hK : certWeight c ≤ ((137 * m : ℕ) : ℤ) := by
    refine hw.trans ?_
    push_cast
    have : (P.card : ℤ) ≤ m := by exact_mod_cast hm
    linarith
  have hZ : (vertSet P).card ≤ 3 * (137 * m) := (card_vertSet_le P).trans (by omega)
  have hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ vertSet P := fun e he v hv =>
    mem_filter.mpr ⟨mem_univ _, e, he, hv⟩
  obtain ⟨A, Q, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
    habs V (le_of_max_le_left hN) p G (PhysicalHingeSupply.commonNbrRich_four_of_cn6 hG)
      P t c (vertSet P) hc hK hPZ hZ
  refine ⟨A, Q, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_, ?_, ?_, h14, h15, h16⟩ <;>
    simpa only [mul_assoc] using ‹_›

end PartitionedTriangleAbsorption.IntegerCertificate

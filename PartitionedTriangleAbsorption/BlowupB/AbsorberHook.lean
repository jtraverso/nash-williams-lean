/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.NearlyCompleteAbsorber
public import PartitionedTriangleAbsorption.UniformBoundedCoreStage104
public import PartitionedTriangleAbsorption.DivisiblePrivateAbsorberStage101

/-! # BlowupB.AbsorberHook — absorbers for every family in nearly complete blowups

The bounded-source absorbers of the tree for an arbitrary family (`ThreeStepLinks F`):
* `BoundedCoreStage104.exists_uniform_terminal_absorber` (terminal core),
* `PrivateAbsorberStage101.private_absorber_from_divisible` (private absorbers),
take the four-root supply `CompatibleSupply` as a hypothesis. The tree derives that supply from
the missing degree only for `F₃` (`AbsorberBootstrapStage138.compatible_supply_of_missing`).

Here (`compatibleSupply_of_missing`) it is derived for **every** family from the missing degree
and the class sizes, through `NearlyCompleteAbsorber.card_query_ge`. Consequently both
absorbers hold in every nearly complete blowup of every family with `ThreeStepLinks`
(`terminal_absorber_nearly`, `private_absorber_nearly`), in particular for `F₀, F₁, F₂, F₃`.

`ThreeStepLinks` is a genuine restriction: it fails for the single rainbow type `{0,1,2}`
(`not_threeStepLinks_rainbow`), although `BlowupB.Uniform` covers that family.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedTransformer PairMoveSelectionStage85 TypedEmbeddingSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem allowedPair_of_link {F : Finset (Multiset (Fin t))} {i j k : Fin t}
    (h : Link F i j k) : AllowedPair F j i :=
  (allowedPair_of_three h).1.symm

/-- **Four-root supply from the missing degree, for every family.** -/
theorem compatibleSupply_of_missing (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hmiss : ∀ v, missDeg p F G v ≤ d)
    (a : ℝ) (hcls : ∀ i, a + 4 * (d + 1) ≤ ((univ.filter fun v => p v = i).card : ℝ)) :
    CompatibleSupply p F G a := by
  intro S hS i hi
  have hq := NearlyCompleteAbsorber.card_query_ge p F G hmiss S i
    (fun u hu => by obtain ⟨k, hk⟩ := hi u hu; exact allowedPair_of_link hk)
  have hq' : ((univ.filter fun v => p v = i).card : ℝ) ≤
      (typedNeighbours p G S i).card + (S.card : ℝ) * (d + 1) := by
    exact_mod_cast hq
  have hS' : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have hloss : (S.card : ℝ) * (d + 1) ≤ 4 * (d + 1) :=
    mul_le_mul_of_nonneg_right hS' (by positivity)
  linarith [hcls i]

/-- The terminal-core absorption property of a family in nearly complete blowups: the
threshold precedes the host, the forbidden set and the core. -/
def TerminalAbsorberNearly (F : Finset (Multiset (Fin t))) (K : ℕ) (gamma eta : ℝ) : Prop :=
  ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin t) (d : ℕ), N ≤ Fintype.card V → (∀ v, missDeg p F G v ≤ d) →
    (∀ i, gamma * Fintype.card V + 4 * (d + 1) ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
    ∀ B X : Finset (Sym2 V), DegBounded B (gamma * Fintype.card V / 5) →
      X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
      ∃ C, C ⊆ G.edgeFinset ∧ Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
        DegBounded C (eta * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L)

/-- **Terminal-core absorber in nearly complete blowups, every family with three-step links.** -/
theorem terminal_absorber_nearly (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ) (gamma eta : ℝ)
    (hg : 0 < gamma) (he : 0 < eta) : TerminalAbsorberNearly F K gamma eta := by
  obtain ⟨N, hN⟩ :=
    BoundedCoreStage104.exists_uniform_terminal_absorber F hcard hF K gamma eta hg he
  refine ⟨N, ?_⟩
  intro V _ _ G _ p d hn hmiss hcls B X hB hXG hXB hK
  exact hN G p hn (compatibleSupply_of_missing p F G hmiss _ hcls) B X hB hXG hXB hK

/-- **Private absorbers in nearly complete blowups, every family with three-step links.** -/
theorem private_absorber_nearly (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ) :
    ∃ q : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (p : V → Fin t) (a d0 : ℝ) (d : ℕ), (∀ v, missDeg p F G v ≤ d) →
      (∀ i, a + 4 * (d + 1) ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
      ∀ (B P : Finset (Sym2 V)) (Z : Finset V), DegBounded B d0 → 0 ≤ d0 →
        P ⊆ G.edgeFinset → Disjoint P B → (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → P.card ≤ K →
        IsIntDiv p F P → (Z.card : ℝ) + 382 * K + 1164 * q + 4 * (d0 + P.card) < a →
        ∃ A, PairMoveAssemblyStage85.Absorbs (p := p) (F := F) A P ∧ Disjoint A B ∧
          A.card ≤ 93 * K + 282 * q ∧ A ⊆ G.edgeFinset := by
  obtain ⟨q, hq⟩ := PrivateAbsorberStage101.private_absorber_from_divisible F hcard hF K
  refine ⟨q, ?_⟩
  intro V _ _ G _ p a d0 d hmiss hcls B P Z hB hd0 hPG hPB hPZ hK hdiv hb
  exact hq G p a d0 (compatibleSupply_of_missing p F G hmiss a hcls) B P Z hB hd0 hPG hPB hPZ
    hK hdiv hb

/-! ### The Nash–Williams families -/

open TypedApplicationLinks in
theorem terminal_absorber_nearly_F1 (K : ℕ) (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    TerminalAbsorberNearly F1 K gamma eta :=
  terminal_absorber_nearly F1 card_F1 F1_three_step K gamma eta hg he

open TypedApplicationLinks in
theorem terminal_absorber_nearly_F2 (K : ℕ) (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    TerminalAbsorberNearly F2 K gamma eta :=
  terminal_absorber_nearly F2 card_F2 F2_three_step K gamma eta hg he

open TypedApplicationLinks in
theorem terminal_absorber_nearly_F0 (K : ℕ) (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    TerminalAbsorberNearly F0 K gamma eta :=
  terminal_absorber_nearly F0 card_F0 F0_three_step K gamma eta hg he

open TypedApplicationLinks in
theorem terminal_absorber_nearly_F3 (K : ℕ) (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    TerminalAbsorberNearly F3 K gamma eta :=
  terminal_absorber_nearly F3 card_F3 F3_three_step K gamma eta hg he

/-! ### The restriction -/

/-- `ThreeStepLinks` fails for the single rainbow type: the link of `0` is one edge `1 – 2`,
and no walk of length `3` returns from `1` to `1`. -/
theorem not_threeStepLinks_rainbow : ¬ ThreeStepLinks ({{0, 1, 2}} : Finset (Multiset (Fin 3))) := by
  unfold ThreeStepLinks Link
  decide

end PartitionedTriangleAbsorption.BlowupB

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.StarObstruction
public import PartitionedTriangleAbsorption.TypedApplicationLinks
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-! # A six-class host whose root has a bipartite F0-link

Vertices are `Fin 6 × Fin L`. Classes `0 = A`, `1 = X`, `2 = Y` form part `0`,
classes `3 = P`, `4 = Q`, `5 = Z` form part `1`. The classes `X`, `Y`, `Z`
are cliques and `A`, `P`, `Q` are independent. The class adjacencies are

  `A : X Y P Q`, `X : A X Y Q Z`, `Y : A X Y P Z`,
  `P : A Y Q Z`, `Q : A X P Z`, `Z : X Y P Q Z`.

Every vertex `v` of `A` has a bipartite F0-link with sides `P ∪ X`
and `Q ∪ Y`. Hence the star charge `χ_v` (`+1` towards `P ∪ X`, `-1`
towards `Q ∪ Y`) annihilates every F0 triangle of the host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost

open Finset TypedApplicationLinks

/-- Class-to-part map. -/
def part : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

/-- Class adjacency (diagonal entries `true` mean the class is a clique). -/
def R : Fin 6 → Fin 6 → Bool :=
  ![![false, true, true, true, true, false],
    ![true, true, true, false, true, true],
    ![true, true, true, true, false, true],
    ![true, false, true, false, true, true],
    ![true, true, false, true, false, true],
    ![false, true, true, true, true, true]]

theorem R_symm : ∀ a b : Fin 6, R a b = R b a := by decide

/-- Sign of the star charge at an `A`-vertex, by class of the other endpoint. -/
def sgn : Fin 6 → ℤ := ![0, 1, -1, 1, -1, 0]

/-- Class-level anti-edge witnesses: a third class outside both classes. -/
theorem anti_class : ∀ c d : Fin 6, ∀ k : Fin 2,
    ({part c, part d, k} : Multiset (Fin 2)) ∈ F0 →
      ∃ e : Fin 6, part e = k ∧ e ≠ c ∧ e ≠ d ∧ R c e = true ∧ R e d = true := by
  decide

/-- Class-level bipartite link of `A`. -/
theorem link_class : ∀ b c : Fin 6, R 0 b = true → R 0 c = true → R b c = true →
    ({0, part b, part c} : Multiset (Fin 2)) ∈ F0 → sgn b + sgn c = 0 := by
  decide

/-- Class-level clone witnesses for the four classes used by the roots. -/
theorem clone_class : ∀ c : Fin 6, (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 1) → ∀ j : Fin 2,
    ∃ e₁ e₂ : Fin 6, e₁ ≠ e₂ ∧ part e₁ = j ∧ part e₂ = j ∧ e₁ ≠ c ∧ e₂ ≠ c ∧
      R c e₁ = true ∧ R c e₂ = true := by
  decide

variable (L : ℕ)

/-- The host graph on `Fin 6 × Fin L`. -/
def host : SimpleGraph (Fin 6 × Fin L) where
  Adj a b := a ≠ b ∧ R a.1 b.1 = true
  symm := ⟨fun a b h => ⟨Ne.symm h.1, by rw [R_symm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel (host L).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ R a.1 b.1 = true))

/-- The partition `p`. -/
def hp : Fin 6 × Fin L → Fin 2 := fun v => part v.1

theorem card_host : Fintype.card (Fin 6 × Fin L) = 6 * L := by
  simp

/-- The block of one class. -/
def block (e : Fin 6) : Finset (Fin 6 × Fin L) :=
  univ.map ⟨fun m => (e, m), fun a b h => by simpa using h⟩

theorem card_block (e : Fin 6) : (block L e).card = L := by
  simp [block]

theorem mem_block {e : Fin 6} {w : Fin 6 × Fin L} : w ∈ block L e ↔ w.1 = e := by
  constructor
  · intro h
    simp only [block, mem_map, mem_univ, true_and] at h
    obtain ⟨m, rfl⟩ := h
    rfl
  · intro h
    simp only [block, mem_map, mem_univ, true_and]
    exact ⟨w.2, by subst h; rfl⟩

/-- **The host is F0-anti-edgeful with `α = 1/6`, for every `L`.** -/
theorem antiEdgeful : AntiEdgeful (hp L) F0 (host L) (1 / 6) := by
  intro τ hτ i j k hτeq u v _ hu hv
  subst hτeq
  have hτ' : ({part u.1, part v.1, k} : Multiset (Fin 2)) ∈ F0 := by
    simpa [hp, ← hu, ← hv] using hτ
  obtain ⟨e, hek, heu, hev, hue, hev'⟩ := anti_class u.1 v.1 k hτ'
  have hsub : block L e ⊆ univ.filter (fun w => (host L).Adj u w ∧ (host L).Adj w v ∧
      hp L w = k) := by
    intro w hw
    rw [mem_block] at hw
    rw [mem_filter]
    refine ⟨mem_univ _, ⟨?_, by rw [hw]; exact hue⟩, ⟨?_, by rw [hw]; exact hev'⟩,
      by change part w.1 = k; rw [hw]; exact hek⟩
    · intro h; apply heu; rw [← hw, ← h]
    · intro h; apply hev; rw [← hw, h]
  have h1 := card_le_card hsub
  rw [card_block] at h1
  rw [card_host]
  have h2 : (L : ℝ) ≤ ((univ.filter (fun w => (host L).Adj u w ∧ (host L).Adj w v ∧
      hp L w = k)).card : ℝ) := by exact_mod_cast h1
  push_cast
  linarith

/-! ### The star charge at an `A`-vertex -/

/-- The signing of the host: `+1` on `X ∪ P`, `-1` on `Y ∪ Q`, `0` on `A ∪ Z`. -/
def hostSign : Fin 6 × Fin L → ℤ := fun w => sgn w.1

/-- `χ_v(e)`: `sgn` of the other endpoint if `e` contains `v`, otherwise `0`. -/
def starCharge (v : Fin 6 × Fin L) : Sym2 (Fin 6 × Fin L) → ℤ :=
  starChargeOf v (hostSign L)

theorem starCharge_mk (v a b : Fin 6 × Fin L) :
    starCharge L v s(a, b) =
      (if a = v then sgn b.1 else 0) + (if b = v then sgn a.1 else 0) := rfl

theorem adj_class {a b : Fin 6 × Fin L} (h : (host L).Adj a b) : R a.1 b.1 = true := h.2

/-- **Every `A`-vertex has a bipartite F0-link**, signed by `hostSign`. -/
theorem linkSigned (v : Fin 6 × Fin L) (hv : v.1 = 0) :
    LinkSigned (hp L) F0 (host L) v (hostSign L) := by
  intro a b hva hvb hab hF
  have h1 := adj_class L hva
  have h2 := adj_class L hvb
  rw [hv] at h1 h2
  exact link_class a.1 b.1 h1 h2 (adj_class L hab)
    (by simpa [hp, hv, show part 0 = 0 from rfl] using hF)

/-- **The star charge at any `A`-vertex annihilates every F0 triangle of the host.** -/
theorem starCharge_annihilating (v : Fin 6 × Fin L) (hv : v.1 = 0) :
    TriangleAnnihilating (hp L) F0 (host L) (starCharge L v) :=
  starChargeOf_annihilating (linkSigned L v hv)

end PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost

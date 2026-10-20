/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.Ring

/-! # Integer identities for local same-part vertex transport

These identities hold at every edge coordinate over arbitrary vertex types.
They do not assert the global CN5 supply, cycle assembly or norm contract.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.LocalCycleTransportStage62

def tri {V : Type*} (e : V → V → ℤ) (a b c : V) : ℤ :=
  e a b + e a c + e b c

theorem double_spoke_transport {V : Type*} (e : V → V → ℤ) (v w u z t : V) :
    2 * e v z - 2 * e w z =
      tri e v u z + tri e v z t - tri e v u t -
      tri e w u z - tri e w z t + tri e w u t := by
  unfold tri
  ring

theorem two_star_transport {V : Type*} (e : V → V → ℤ) (a b v w u z t : V) :
    e a v + e b v - e a w - e b w =
      tri e a v z + tri e b v z - tri e a w z - tri e b w z -
      tri e v u z - tri e v z t + tri e v u t +
      tri e w u z + tri e w z t - tri e w u t := by
  unfold tri
  ring

def mixed (a b c : Bool) : Prop := a ≠ b ∨ b ≠ c

instance (a b c : Bool) : Decidable (mixed a b c) := by
  unfold mixed
  infer_instance

theorem circuits_mixed : ∀ a b s : Bool,
    mixed a s (!s) ∧ mixed b s (!s) ∧
    mixed s s (!s) ∧ mixed s (!s) (!s) := by
  decide

theorem transport_budget (m I B margin rect : ℤ)
    (hI : I ≤ m) (hB : B ≤ 2 * m)
    (hmargin : margin ≤ 6 * B) (hrect : rect ≤ 4 * B) :
    20 * m + I + margin + rect ≤ 41 * m := by
  omega

end PartitionedTriangleAbsorption.LocalCycleTransportStage62

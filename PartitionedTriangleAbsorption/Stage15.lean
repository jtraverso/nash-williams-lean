/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FiniteNibbleSchedule
public import PartitionedTriangleAbsorption.PrivateTemplate.Main

/-! # Stage 15: finite private templates and deterministic nibble budgets

The private template is constructed without assuming its existence. Its rank
still needs to be adapted to the physical rooted-embedding interface, and the
family/refiner is not constructed here. The schedule lemmas consume step bounds;
they do not formalize the written probabilistic nibble proof.
-/

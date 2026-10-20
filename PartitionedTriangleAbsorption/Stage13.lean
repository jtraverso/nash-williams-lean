/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage12
public import PartitionedTriangleAbsorption.FiniteBernoulliUpperTail
public import PartitionedTriangleAbsorption.PhysicalReserveTails
public import PartitionedTriangleAbsorption.PhysicalStarTail

/-! # Physical reserve tails and simultaneous-outcome selection

All common-neighbour queries now use a single supplied physical-edge measure.
Degree tails apply to the actual sampled graph. The finite union-bound selector
needs no independence between queries. Enumerating all required typed queries,
proving their cardinality bound and applying this selector to the full reserve
contract remain assembly obligations. The residual-nibble degree theorem is
not asserted here.
-/

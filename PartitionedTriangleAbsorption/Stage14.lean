/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage13
public import PartitionedTriangleAbsorption.BernoulliExposure
public import PartitionedTriangleAbsorption.TruncatedLinkCollisions

/-! # Finite exposure variance and truncated collision sensitivity

This checkpoint formalizes the probability-weighted one-coordinate variance
budget using actual future averages and the two-endpoint sensitivity bound.
The written one-round concentration proof and the iterative nibble are not
claimed as formalized by these imports.
-/

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.ProducerConsumer
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.RoutedEvenProducer

/-! The general three-step-link theorem, independent of the Nash-Williams adapters. -/

namespace PaddedGeneral.RealInverse

open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.BlowupB.UniversalProducer

/-- No universal absorber or external existence theorem remains as a premise. -/
theorem keevashTypedSpec_of_threeStepLinks
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hthree : ThreeStepLinks F) : KeevashTypedSpec F := by
  obtain ⟨S, hS, hP⟩ := producerTarget_of_threeStepLinks F hF.card_three hthree
  exact keevashTypedSpec_of_producer F hF S hS hP

end PaddedGeneral.RealInverse

#print axioms PaddedGeneral.RealInverse.keevashTypedSpec_of_threeStepLinks

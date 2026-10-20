/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.PaperIIAssembly
import Lean.Util.CollectAxioms

/-!
# Proof-term audit of the Paper II application

This checks dependencies of checked declarations, not just module imports.
The old final theorem and the alternative F1 vortex proof may be present in
the environment but must not occur in the dependency closure of the new proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `NashWilliams18.PaperI.nash_williams_via_paperII
  let mut todo := #[target]
  let mut visited : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if visited.contains name then continue
    visited := visited.insert name
    if let some info := env.checked.get.find? name then
      todo := todo ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        todo := todo ++ value.getUsedConstants
  for required in #[
      `NashWilliams18.PaperII.theorem146_F0,
      `NashWilliams18.theorem146Statement_holds,
      `PartitionedTriangleAbsorption.BlowupB.F0Direct.theorem146_ordered,
      `PartitionedTriangleAbsorption.BlowupB.F0Direct.statement,
      `NashWilliams18.PaperII.theorem147_F1,
      `NashWilliams18.PaperII.theorem147_F2,
      `PaddedGeneral.RealInverse.idealized_F12,
      `NashWilliams18.PaperII.margin_four_colour_decomposition,
      `PaddedGeneral.RealInverse.nearlyComplete_F123,
      `PaddedGeneral.RealInverse.keevashTypedSpec_of_producer,
      `PaddedGeneral.RealInverse.decomposition_of_producer,
      `PaddedGeneral.RealInverse.completeInverseCertLocalBound_general,
      `PartitionedTriangleAbsorption.BlowupB.UniversalProducer.producerTarget_of_threeStepLinks] do
    unless visited.contains required do
      throwError "Missing Paper II proof dependency: {required}"
  for forbidden in #[
      `nash_williams,
      `NashWilliams18.theorem_14_7_F1_of_vortex,
      `NashWilliams18.Theorem1316Statement,
      `PartitionedTriangleAbsorption.FourColourConsumerStage84.margin_four_colour_decomposition,
      `PartitionedTriangleAbsorption.BlowupB.theorem147_F1,
      `PartitionedTriangleAbsorption.BlowupB.theorem147_F2] do
    if visited.contains forbidden then
      throwError "Forbidden proof dependency: {forbidden}"
  for ax in (← Lean.collectAxioms target) do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Unexpected axiom: {ax}"
  logInfo "PASS_PAPERII_PROOF_DEPENDENCIES"

#print axioms NashWilliams18.PaperII.theorem146_F0
#print axioms NashWilliams18.PaperII.theorem147_F1
#print axioms NashWilliams18.PaperII.theorem147_F2
#print axioms NashWilliams18.PaperII.typed_inputs
#print axioms NashWilliams18.PaperI.nash_williams_of_paperII_inputs
#print axioms NashWilliams18.PaperI.nash_williams_via_paperII

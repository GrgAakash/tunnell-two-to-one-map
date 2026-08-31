import TunnellMap.N41Fibres

/-!
# Axiom audit of the `n = 41` end-to-end certification

Every principal `n = 41` theorem is checked here with `#print axioms`.  The
expected output for each is `[propext, Classical.choice, Quot.sound]` — the
three standard axioms of Lean's classical logic.  In particular no
`Lean.ofReduceBool` and no `Lean.trustCompiler` occurs, so no principal
`n = 41` theorem depends on `native_decide`.
-/

namespace TunnellMap
namespace Examples41

/-! ## Part 1: exhaustive representation data -/

#print axioms card_BRep_41
#print axioms card_ARep_41
#print axioms balance_41
#print axioms bEvenTriples_41
#print axioms bDirectTriples_41
#print axioms bResidualTriples_41
#print axioms bTriples_41_split
#print axioms aDirectTriples_41
#print axioms aResidualTriples_41
#print axioms aTriples_41_split
#print axioms sourceRosterExec_41
#print axioms sourceRosterExec_41_coords
#print axioms sourceRosterExec_41_lifts
#print axioms sourceRoster_41_orbit_unique
#print axioms sourceRoster_41_nodup
#print axioms targetRosterExec_41
#print axioms targetRosterExec_41_coords
#print axioms targetRosterExec_41_lifts
#print axioms targetRoster_41_orbit_unique
#print axioms targetRoster_41_nodup

/-! ## Part 2: complete generated preference data -/

#print axioms fullTrace_s1_41
#print axioms fullTrace_s2_41
#print axioms fullTrace_s3_41
#print axioms fullTrace_s4_41
#print axioms fullTrace_targets_41
#print axioms fullTrace_keys_41
#print axioms incidentStream_s1_targets_41
#print axioms incidentStream_s2_targets_41
#print axioms incidentStream_s3_targets_41
#print axioms incidentStream_s4_targets_41
#print axioms incidentStream_s2_keys_41

/-! ## Part 3: the actual deferred-acceptance trace -/

#print axioms TunnellMap.RecordDA.stepTrace_step
#print axioms TunnellMap.RecordDA.stepTrace_shape
#print axioms TunnellMap.RecordDA.stepTrace_generator_advance
#print axioms TunnellMap.RecordDA.stepTrace_accept_iff_free
#print axioms TunnellMap.RecordDA.runWithTrace_terminalRunExec
#print axioms fuelSuffices_41
#print axioms runWithTrace_terminalRun_41
#print axioms daTrace_41
#print axioms daTrace_41_manuscript
#print axioms daTrace_41_keys_signs
#print axioms daTrace_41_length

/-! ## Part 4: matching, signs, inverse and parking data -/

#print axioms terminalHeld_41
#print axioms terminalHolders_41
#print axioms residualMap_41
#print axioms residualMap_41_coords
#print axioms residualPairs_41
#print axioms inverseByRerun_41
#print axioms inverseByRerun_targets_41
#print axioms proposalCounts_41
#print axioms parkingSequence_41
#print axioms parkingTotal_41
#print axioms parkingBound_41
#print axioms parkingBound_41_literal
#print axioms costCounters_41

/-! ## Part 5: the complete fibres -/

#print axioms paperTunnellMapExec_41_exactly_two
#print axioms fibreCheck41_all
#print axioms fibre_direct_41
#print axioms fibre_residual_41
#print axioms fibre_direct_41_set
#print axioms fibre_residual_41_set
#print axioms fibres_41_two_distinct

end Examples41
end TunnellMap

import TunnellMap.Examples41Deterministic
import TunnellMap.FallbackFreeMap
import TunnellMap.PartialStableMatching

/-!
# Axiom audit of the deterministic frame, reduction, roster and pipeline

Every principal new correctness and equivalence theorem of this stage is
listed here with `#print axioms`.  Building this file prints the complete
axiom list of each declaration.
-/

namespace TunnellMap

/-! ## Stable partial matchings -/

#print axioms GloballyRanked.partialStable_isPerfect
#print axioms GloballyRanked.partialStable_unique
#print axioms GloballyRanked.existsUnique_partialStable

/-! ## A. Deterministic orthogonal frame -/

#print axioms orthogonalFrameExec
#print axioms orthogonalFrameExec_deterministic
#print axioms frame_orthogonal
#print axioms frame_linearIndependent
#print axioms frame_span_iff
#print axioms frame_span_unique
#print axioms frame_gram_det
#print axioms frame_change_unimodular
#print axioms frame_same_lattice
#print axioms orthogonalFrameExec_orthogonal
#print axioms orthogonalFrameExec_linearIndependent
#print axioms orthogonalFrameExec_span_iff
#print axioms orthogonalFrameExec_span_unique
#print axioms orthogonalFrameExec_gram_det

/-! ## B. Deterministic Lagrange–Gauss reduction -/

#print axioms lgReduce
#print axioms lgReduce_cross
#print axioms lgReduce_reduced
#print axioms lgReduce_deterministic
#print axioms reduceFrame
#print axioms isLagrangeGaussReduced_reduceFrame
#print axioms reduceFrame_alpha_square_bound
#print axioms reduceFrame_alpha_le_two_sqrt_div_three
#print axioms reduceFrame_unimodular
#print axioms reduceFrame_same_lattice
#print axioms reduceFrame_gram_det
#print axioms reduceFrame_deterministic

/-! ## C. Computable residual source roster -/

#print axioms sourceRosterExec
#print axioms mem_sourceRosterExec_iff
#print axioms mem_sourceRosterExec_iff_canonical
#print axioms sourceRosterExec_nodup
#print axioms sourceRosterExec_pairwise
#print axioms sourceRosterExec_orbit_unique
#print axioms sourceRosterExec_eq_sourceRoster

/-! ## D. Computable frame family and end-to-end pipeline -/

#print axioms RecordDA.frameExec
#print axioms RecordDA.framesExec
#print axioms RecordDA.isLagrangeGaussReduced_frameExec
#print axioms RecordDA.framesExec_deterministic
#print axioms RecordDA.canonicalIncidentStream_framesExec_eq_preferenceList
#print axioms RecordDA.terminalRunExec
#print axioms RecordDA.terminalRunExec_eq
#print axioms RecordDA.oneBlockAll_terminalRunExec
#print axioms RecordDA.runMatching_framesExec_eq
#print axioms RecordDA.terminalRunExec_queue_nil
#print axioms RecordDA.canonicalBExec_eq
#print axioms RecordDA.bResidualSignExec_eq
#print axioms RecordDA.aResidualOfTriple_residualTargetLift
#print axioms RecordDA.residualMapExec
#print axioms RecordDA.residualMapExec_eq
#print axioms RecordDA.inverseByRerunExec
#print axioms RecordDA.inverseByRerunExec_eq
#print axioms RecordDA.inverseByRerunExec_residualMapExec
#print axioms RecordDA.residualMapExec_inverseByRerunExec
#print axioms RecordDA.residualMapExec_bijective
#print axioms RecordDA.inverseByRerunExec_eq_residualEquiv_symm
#print axioms RecordDA.residualMapExec_eq_residualEquiv
#print axioms RecordDA.inverseByRerunExecOpt
#print axioms RecordDA.residualMapExecTotal
#print axioms RecordDA.residualMapExecTotal_eq_canonical
#print axioms RecordDA.inverseByRerunExecOpt_eq_some_value
#print axioms RecordDA.inverseByRerunExecOpt_isSome
#print axioms RecordDA.inverseByRerunExecTotal
#print axioms RecordDA.inverseByRerunExecTotal_eq_residualEquiv_symm
#print axioms RecordDA.inverseByRerunExecTotal_residualMapExecOpt
#print axioms RecordDA.residualMapExecOpt_inverseByRerunExecTotal
#print axioms RecordDA.inverseByRerunExecTotal_residualMapExecTotal
#print axioms RecordDA.residualMapExecTotal_inverseByRerunExecTotal

/-! ## The executable direct branch and full map -/

#print axioms directMapExec
#print axioms directMapExec_eq
#print axioms oddMapExec
#print axioms oddMapExec_eq
#print axioms paperTunnellMapExec
#print axioms paperTunnellMapExec_eq
#print axioms paperTunnellMapExec_exactly_two

end TunnellMap

import TunnellMap.KernelFullMap
import TunnellMap.N41Representations

/-!
# `n = 41`, part 2: the complete generated preference data

For each of the four residual source orbits `s1, s2, s3, s4` this file proves
that the *stateful arithmetic generator* emits exactly the four records of the
manuscript's preference row, in the displayed order, with the displayed keys,
targets and signs.

The frames are the ones the pipeline actually uses,
`RecordDA.framesExec squarefree41`; the equality is decided by the kernel
through the fuel-driven mirror `BlockGen.blocksFromK`, which
`BlockGen.blocksFromK_eq` identifies with `BlockGen.blocksFrom`, i.e. with
`BlockGen.fullTrace`.  Nothing is hard-coded: the four literal rows are the
*right-hand sides* of equalities whose left-hand sides are recomputed by the
kernel from the frame arithmetic.

The final section transports the four complete rows to the extensional
`OrderedGenerator.incidentStream`, so that the rows are the actual incident
streams and not merely four separately-checked candidates.
-/

namespace TunnellMap
namespace Examples41

open RecordDA BlockGen OrderedGenerator

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-- `0 < 41`, as an integer. -/
theorem pos41 : (0 : ℤ) < 41 := by norm_num

/-- `41` is odd. -/
theorem odd41 : Odd (41 : ℤ) := ⟨20, by norm_num⟩

/-! ## The four generated rows -/

/-- **The complete generated preference row of `s1`.** -/
theorem fullTrace_s1_41 :
    fullTrace s1 (framesExec squarefree41 s1) =
      [⟨key41 5 1 (-1) (-1), ⟨-4, -3, 0⟩, -1⟩,
       ⟨key41 5 1 1 (-1), ⟨0, -3, -4⟩, -1⟩,
       ⟨key41 20 1 (-4) (-1), ⟨-4, 3, 0⟩, -1⟩,
       ⟨key41 20 1 4 (-1), ⟨0, -3, 4⟩, 1⟩] := by
  rw [fullTrace, framesExec_apply, ← frameExecK_eq squarefree41,
    ← blocksFromK_eq (n := 41) (s := s1) (by norm_num) _ 21 1 (by norm_num)
      (by decide)]
  decide +kernel

/-- **The complete generated preference row of `s2`.** -/
theorem fullTrace_s2_41 :
    fullTrace s2 (framesExec squarefree41 s2) =
      [⟨key41 5 1 (-1) 1, ⟨-4, -3, 0⟩, -1⟩,
       ⟨key41 5 1 1 1, ⟨0, -3, 4⟩, -1⟩,
       ⟨key41 20 1 (-4) 1, ⟨-4, 3, 0⟩, -1⟩,
       ⟨key41 20 1 4 1, ⟨0, -3, -4⟩, 1⟩] := by
  rw [fullTrace, framesExec_apply, ← frameExecK_eq squarefree41,
    ← blocksFromK_eq (n := 41) (s := s2) (by norm_num) _ 21 1 (by norm_num)
      (by decide)]
  decide +kernel

/-- **The complete generated preference row of `s3`.** -/
theorem fullTrace_s3_41 :
    fullTrace s3 (framesExec squarefree41 s3) =
      [⟨key41 5 1 (-1) (-1), ⟨0, -3, 4⟩, 1⟩,
       ⟨key41 5 1 1 (-1), ⟨-4, 3, 0⟩, -1⟩,
       ⟨key41 20 1 (-4) (-1), ⟨0, -3, -4⟩, -1⟩,
       ⟨key41 20 1 4 (-1), ⟨-4, -3, 0⟩, -1⟩] := by
  rw [fullTrace, framesExec_apply, ← frameExecK_eq squarefree41,
    ← blocksFromK_eq (n := 41) (s := s3) (by norm_num) _ 21 1 (by norm_num)
      (by decide)]
  decide +kernel

/-- **The complete generated preference row of `s4`.** -/
theorem fullTrace_s4_41 :
    fullTrace s4 (framesExec squarefree41 s4) =
      [⟨key41 5 1 (-1) 1, ⟨0, -3, -4⟩, 1⟩,
       ⟨key41 5 1 1 1, ⟨-4, 3, 0⟩, -1⟩,
       ⟨key41 20 1 (-4) 1, ⟨0, -3, 4⟩, -1⟩,
       ⟨key41 20 1 4 1, ⟨-4, -3, 0⟩, -1⟩] := by
  rw [fullTrace, framesExec_apply, ← frameExecK_eq squarefree41,
    ← blocksFromK_eq (n := 41) (s := s4) (by norm_num) _ 21 1 (by norm_num)
      (by decide)]
  decide +kernel

/-! ## The rows in the manuscript's notation

Each emitted target is the lift of one of `t1, t2, t3, t4`, and each emitted
key is the corresponding representative edge key of
`TunnellMap.Examples41.residual_key_table`. -/

/-- The targets of the four generated rows, named by the manuscript's
`t1, …, t4`. -/
theorem fullTrace_targets_41 :
    (fullTrace s1 (framesExec squarefree41 s1)).map IncidentRecord.target =
        [residualTargetLift t1, residualTargetLift t3, residualTargetLift t2,
         residualTargetLift t4] ∧
      (fullTrace s2 (framesExec squarefree41 s2)).map IncidentRecord.target =
        [residualTargetLift t1, residualTargetLift t4, residualTargetLift t2,
         residualTargetLift t3] ∧
      (fullTrace s3 (framesExec squarefree41 s3)).map IncidentRecord.target =
        [residualTargetLift t4, residualTargetLift t2, residualTargetLift t3,
         residualTargetLift t1] ∧
      (fullTrace s4 (framesExec squarefree41 s4)).map IncidentRecord.target =
        [residualTargetLift t3, residualTargetLift t2, residualTargetLift t4,
         residualTargetLift t1] := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := residual_lifts
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fullTrace_s1_41, fullTrace_s2_41, fullTrace_s3_41, fullTrace_s4_41,
      List.map_cons, List.map_nil, h1, h2, h3, h4]

/-- The keys of the four generated rows, named by the manuscript's
representative edge keys. -/
theorem fullTrace_keys_41 :
    (fullTrace s1 (framesExec squarefree41 s1)).map IncidentRecord.key =
        [representativeEdgeKey s1 t1, representativeEdgeKey s1 t3,
         representativeEdgeKey s1 t2, representativeEdgeKey s1 t4] ∧
      (fullTrace s2 (framesExec squarefree41 s2)).map IncidentRecord.key =
        [representativeEdgeKey s2 t1, representativeEdgeKey s2 t4,
         representativeEdgeKey s2 t2, representativeEdgeKey s2 t3] ∧
      (fullTrace s3 (framesExec squarefree41 s3)).map IncidentRecord.key =
        [representativeEdgeKey s3 t4, representativeEdgeKey s3 t2,
         representativeEdgeKey s3 t3, representativeEdgeKey s3 t1] ∧
      (fullTrace s4 (framesExec squarefree41 s4)).map IncidentRecord.key =
        [representativeEdgeKey s4 t3, representativeEdgeKey s4 t2,
         representativeEdgeKey s4 t4, representativeEdgeKey s4 t1] := by
  obtain ⟨k11, k13, k12, k14, k21, k24, k22, k23, k34, k32, k33, k31,
    k43, k42, k44, k41'⟩ := residual_key_table
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fullTrace_s1_41, fullTrace_s2_41, fullTrace_s3_41, fullTrace_s4_41,
      List.map_cons, List.map_nil, k11, k13, k12, k14, k21, k24, k22, k23,
      k34, k32, k33, k31, k43, k42, k44, k41']

/-! ## The rows are the actual incident streams

`BlockGen.fullTrace_target_eq_incidentStream` and
`BlockGen.fullTrace_key_eq_incidentStream` identify the generated row with the
extensional `OrderedGenerator.incidentStream`.  Composing them with the four
computed rows shows that the manuscript's rows really are the incident
streams, not four independently valid candidates. -/

/-- **The complete generated `s2` row *is* the `s2` incident stream.** -/
theorem incidentStream_s2_targets_41 :
    (incidentStream pos41 s2 (framesExec squarefree41 s2)).map
        (orbitTargetLift pos41) =
      [residualTargetLift t1, residualTargetLift t4, residualTargetLift t2,
       residualTargetLift t3] := by
  rw [← fullTrace_target_eq_incidentStream pos41]
  exact fullTrace_targets_41.2.1

/-- The `s2` incident-stream edge keys. -/
theorem incidentStream_s2_keys_41 :
    (incidentStream pos41 s2 (framesExec squarefree41 s2)).map
        (orbitEdgeKey pos41 ((bResidualInvolution 41).orbit s2)) =
      [representativeEdgeKey s2 t1, representativeEdgeKey s2 t4,
       representativeEdgeKey s2 t2, representativeEdgeKey s2 t3] := by
  rw [← fullTrace_key_eq_incidentStream pos41]
  exact fullTrace_keys_41.2.1

/-- The `s1` incident stream. -/
theorem incidentStream_s1_targets_41 :
    (incidentStream pos41 s1 (framesExec squarefree41 s1)).map
        (orbitTargetLift pos41) =
      [residualTargetLift t1, residualTargetLift t3, residualTargetLift t2,
       residualTargetLift t4] := by
  rw [← fullTrace_target_eq_incidentStream pos41]
  exact fullTrace_targets_41.1

/-- The `s3` incident stream. -/
theorem incidentStream_s3_targets_41 :
    (incidentStream pos41 s3 (framesExec squarefree41 s3)).map
        (orbitTargetLift pos41) =
      [residualTargetLift t4, residualTargetLift t2, residualTargetLift t3,
       residualTargetLift t1] := by
  rw [← fullTrace_target_eq_incidentStream pos41]
  exact fullTrace_targets_41.2.2.1

/-- The `s4` incident stream. -/
theorem incidentStream_s4_targets_41 :
    (incidentStream pos41 s4 (framesExec squarefree41 s4)).map
        (orbitTargetLift pos41) =
      [residualTargetLift t3, residualTargetLift t2, residualTargetLift t4,
       residualTargetLift t1] := by
  rw [← fullTrace_target_eq_incidentStream pos41]
  exact fullTrace_targets_41.2.2.2

end Examples41
end TunnellMap

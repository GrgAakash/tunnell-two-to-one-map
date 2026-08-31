import TunnellMap.RecordTrace
import TunnellMap.N41Preferences

/-!
# `n = 41`, part 3: the actual deferred-acceptance trace

`RecordDA.runWithTrace` is the instrumented executable run of
`TunnellMap.RecordTrace`: its state transitions are literally those of
`RecordDA.step` (`RecordDA.stepTrace_step`), and each event records the
proposer, the target lift, the projective key, the sign `η` and the
accept/replace/reject outcome.

This file
* certifies that eight units of fuel exhaust the `n = 41` run;
* proves that erasing the trace gives `RecordDA.terminalRunExec`;
* computes the actual six-event trace by kernel evaluation of the real step
  sequence.
-/

namespace TunnellMap
namespace Examples41

open RecordDA BlockGen

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-- The kernel-reducible frame family of the `n = 41` run. -/
def framesK41 : FrameFamily 41 := framesExecK squarefree41

/-- The initial control state of the `n = 41` run. -/
def init41 : DARun 41 := DARun.initial (sourceRosterExec 41)

/-- **Eight units of fuel exhaust the run**: the state reached admits no
further `RecordDA.step`. -/
theorem fuelSuffices_41 : RecordDA.FuelSuffices squarefree41 8 := by
  show (stepK framesK41 (runK framesK41 8 init41)).isNone = true
  decide +kernel

/-- **Erasing the instrumentation gives the terminal executable run.** -/
theorem runWithTrace_terminalRun_41 :
    (runWithTrace framesK41 8 init41).1 = terminalRunExec (framesExec squarefree41) :=
  runWithTrace_terminalRunExec (by norm_num) squarefree41 8 fuelSuffices_41

/-- The list of proposal events of the actual `n = 41` run. -/
def daEvents41 : List (DAEvent 41) := (runWithTrace framesK41 8 init41).2

/-- **The actual `n = 41` deferred-acceptance trace.**  Six proposals, in the
order in which the machine makes them.  The left-hand side is the real
instrumented run; the right-hand side is the manuscript's displayed trace. -/
theorem daTrace_41 :
    daEvents41 =
      [⟨s1, ⟨-4, -3, 0⟩, key41 5 1 (-1) (-1), -1, DAOutcome.accept⟩,
       ⟨s2, ⟨-4, -3, 0⟩, key41 5 1 (-1) 1, -1, DAOutcome.reject⟩,
       ⟨s3, ⟨0, -3, 4⟩, key41 5 1 (-1) (-1), 1, DAOutcome.accept⟩,
       ⟨s4, ⟨0, -3, -4⟩, key41 5 1 (-1) 1, 1, DAOutcome.accept⟩,
       ⟨s2, ⟨0, -3, 4⟩, key41 5 1 1 1, -1, DAOutcome.reject⟩,
       ⟨s2, ⟨-4, 3, 0⟩, key41 20 1 (-4) 1, -1, DAOutcome.accept⟩] := by
  show (runWithTrace framesK41 8 init41).2 = _
  decide +kernel

/-- **The trace in the manuscript's notation:**
`s1 → t1`, `s2 → t1` (rejected), `s3 → t4`, `s4 → t3`, `s2 → t4` (rejected),
`s2 → t2`. -/
theorem daTrace_41_manuscript :
    daEvents41.map (fun e => (e.proposer, e.target, e.outcome)) =
      [(s1, residualTargetLift t1, DAOutcome.accept),
       (s2, residualTargetLift t1, DAOutcome.reject),
       (s3, residualTargetLift t4, DAOutcome.accept),
       (s4, residualTargetLift t3, DAOutcome.accept),
       (s2, residualTargetLift t4, DAOutcome.reject),
       (s2, residualTargetLift t2, DAOutcome.accept)] := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := residual_lifts
  rw [daTrace_41]
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4]

/-- The keys and signs carried by the six proposals, named by the
manuscript's representative edge keys. -/
theorem daTrace_41_keys_signs :
    daEvents41.map (fun e => (e.key, e.sign)) =
      [(representativeEdgeKey s1 t1, -1), (representativeEdgeKey s2 t1, -1),
       (representativeEdgeKey s3 t4, 1), (representativeEdgeKey s4 t3, 1),
       (representativeEdgeKey s2 t4, -1), (representativeEdgeKey s2 t2, -1)] := by
  obtain ⟨k11, -, -, -, k21, k24, k22, -, k34, -, -, -, k43, -, -, -⟩ :=
    residual_key_table
  rw [daTrace_41]
  simp only [List.map_cons, List.map_nil, k11, k21, k22, k24, k34, k43]

/-- The trace has exactly six events. -/
theorem daTrace_41_length : daEvents41.length = 6 := by
  rw [daTrace_41]
  rfl

end Examples41
end TunnellMap

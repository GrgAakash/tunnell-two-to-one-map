import TunnellMap.N41Trace

/-!
# `n = 41`, part 4: matching, signs, inverse and parking data

This file reads off the terminal state of the actual `n = 41` run.

* `terminalHeld_41` is the terminal held table, with the holder, the winning
  key and the sign of each of the four residual targets.
* `residualMap_41` and `residualPairs_41` give the executable matching,
  including signs: the four manuscript pairs
  `(-2,-5,-2) ↔ (4,3,0)`, `(-2,-5,2) ↔ (4,-3,0)`,
  `(-2,5,-2) ↔ (0,-3,4)`, `(-2,5,2) ↔ (0,-3,-4)`.
* `inverseByRerun_41` runs the inverse-by-rerun on the four forward values and
  recovers the four sources.
* The parking data: proposal counts `(1,3,1,1)`, sorted parking sequence
  `(1,1,1,3)`, total `6`, and the bound `6 ≤ 10`.

## The cost model

The manuscript speaks of "six generator advances and six proposal
comparisons".  In the formal cost model the three quantities are genuinely
different, and only two of them equal six:

* **proposal-processing steps** — the number of `RecordDA.stepTrace`
  transitions: `6`;
* **generator advances** — the number of `BlockGen.advanceK` calls; by
  `RecordDA.stepTrace_generator_advance` each processing step performs exactly
  one, so this is again `6`;
* **held-key comparisons** — the number of steps that compare the proposed key
  against a key already held; by `RecordDA.stepTrace_accept_iff_free` these are
  exactly the non-accepting steps, of which there are `2`.

So the manuscript's phrase is not correct for the third quantity.  The exact
correct replacement is:

> "six generator advances and six proposal-processing steps, of which exactly
> two involve a key comparison against a held record."

The model is *not* redefined to make the original phrase come out true.
-/

namespace TunnellMap
namespace Examples41

open RecordDA BlockGen

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! ## The terminal held table -/

/-- **The terminal held table of the `n = 41` run.**  Each residual target
lift is held by one source, together with the winning key and sign. -/
theorem terminalHeld_41 :
    (terminalRunExec (framesExec squarefree41)).held ⟨-4, -3, 0⟩ =
        some (s1, ⟨key41 5 1 (-1) (-1), ⟨-4, -3, 0⟩, -1⟩) ∧
      (terminalRunExec (framesExec squarefree41)).held ⟨-4, 3, 0⟩ =
        some (s2, ⟨key41 20 1 (-4) 1, ⟨-4, 3, 0⟩, -1⟩) ∧
      (terminalRunExec (framesExec squarefree41)).held ⟨0, -3, -4⟩ =
        some (s4, ⟨key41 5 1 (-1) 1, ⟨0, -3, -4⟩, 1⟩) ∧
      (terminalRunExec (framesExec squarefree41)).held ⟨0, -3, 4⟩ =
        some (s3, ⟨key41 5 1 (-1) (-1), ⟨0, -3, 4⟩, 1⟩) := by
  rw [← terminalRunK_eq (by norm_num) squarefree41 8 fuelSuffices_41]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The held table indexed by the manuscript's `t1, …, t4`: the matching is
`s1 ↔ t1`, `s2 ↔ t2`, `s3 ↔ t4`, `s4 ↔ t3`. -/
theorem terminalHolders_41 :
    ((terminalRunExec (framesExec squarefree41)).held
        (residualTargetLift t1)).map Prod.fst = some s1 ∧
      ((terminalRunExec (framesExec squarefree41)).held
        (residualTargetLift t2)).map Prod.fst = some s2 ∧
      ((terminalRunExec (framesExec squarefree41)).held
        (residualTargetLift t3)).map Prod.fst = some s4 ∧
      ((terminalRunExec (framesExec squarefree41)).held
        (residualTargetLift t4)).map Prod.fst = some s3 := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := residual_lifts
  obtain ⟨g1, g2, g3, g4⟩ := terminalHeld_41
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, g1]; rfl
  · rw [h2, g2]; rfl
  · rw [h3, g3]; rfl
  · rw [h4, g4]; rfl

/-! ## The executable matching, with signs -/

/-- **The executable residual matching at `n = 41`.**  The signed images are
`-t1, -t2, t4, t3`. -/
theorem residualMap_41 :
    residualMapExec41 s1 = negAResidual t1 ∧
      residualMapExec41 s2 = negAResidual t2 ∧
      residualMapExec41 s3 = t4 ∧
      residualMapExec41 s4 = t3 := by
  show residualMapExec pos41 squarefree41 t1 s1 = _ ∧
    residualMapExec pos41 squarefree41 t1 s2 = _ ∧
    residualMapExec pos41 squarefree41 t1 s3 = _ ∧
    residualMapExec pos41 squarefree41 t1 s4 = _
  rw [← residualMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41,
    ← residualMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41,
    ← residualMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41,
    ← residualMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The four manuscript residual pairs, in original coordinates.** -/
theorem residualMap_41_coords :
    (residualMapExec41 s1).1.1 = ⟨4, 3, 0⟩ ∧
      (residualMapExec41 s2).1.1 = ⟨4, -3, 0⟩ ∧
      (residualMapExec41 s3).1.1 = ⟨0, -3, 1⟩ ∧
      (residualMapExec41 s4).1.1 = ⟨0, -3, -1⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := residualMap_41
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · rw [h4]; rfl

/-- **The four manuscript residual pairs, with signs.**  In the manuscript's
lifted coordinates the matching is
`(-2,-5,-2) ↔ (4,3,0)`, `(-2,-5,2) ↔ (4,-3,0)`,
`(-2,5,-2) ↔ (0,-3,4)`, `(-2,5,2) ↔ (0,-3,-4)`. -/
theorem residualPairs_41 :
    (sourceRosterExec 41).map
        (fun s => (residualSourceLift s, residualTargetLift (residualMapExec41 s))) =
      [(⟨-2, -5, -2⟩, ⟨4, 3, 0⟩), (⟨-2, -5, 2⟩, ⟨4, -3, 0⟩),
       (⟨-2, 5, -2⟩, ⟨0, -3, 4⟩), (⟨-2, 5, 2⟩, ⟨0, -3, -4⟩)] := by
  obtain ⟨h1, h2, h3, h4, -⟩ := residual_lifts
  obtain ⟨m1, m2, m3, m4⟩ := residualMap_41
  rw [sourceRosterExec_41]
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4, m1, m2, m3, m4]
  rfl

/-! ## The inverse by rerun -/

/-- **Inverse by rerun.**  Rerunning the machine on each of the four forward
values recovers the source it came from. -/
theorem inverseByRerun_41 :
    inverseExec41 (residualMapExec41 s1) = s1 ∧
      inverseExec41 (residualMapExec41 s2) = s2 ∧
      inverseExec41 (residualMapExec41 s3) = s3 ∧
      inverseExec41 (residualMapExec41 s4) = s4 := by
  obtain ⟨m1, m2, m3, m4⟩ := residualMap_41
  show inverseByRerunExec squarefree41 s1 (residualMapExec41 s1) = _ ∧
    inverseByRerunExec squarefree41 s1 (residualMapExec41 s2) = _ ∧
    inverseByRerunExec squarefree41 s1 (residualMapExec41 s3) = _ ∧
    inverseByRerunExec squarefree41 s1 (residualMapExec41 s4) = _
  rw [m1, m2, m3, m4,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The inverse-by-rerun values of the four residual targets themselves. -/
theorem inverseByRerun_targets_41 :
    (targetRosterExec 41).map (fun t => residualSourceLift (inverseExec41 t)) =
      [⟨2, 5, 2⟩, ⟨2, 5, -2⟩, ⟨-2, 5, 2⟩, ⟨-2, 5, -2⟩] := by
  rw [targetRosterExec_41]
  show [residualSourceLift (inverseByRerunExec squarefree41 s1 t1),
    residualSourceLift (inverseByRerunExec squarefree41 s1 t2),
    residualSourceLift (inverseByRerunExec squarefree41 s1 t3),
    residualSourceLift (inverseByRerunExec squarefree41 s1 t4)] = _
  rw [← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41,
    ← inverseByRerunExecK_eq (by norm_num) squarefree41 s1 8 fuelSuffices_41]
  decide +kernel

/-! ## Parking data -/

/-- The number of proposals made by a given source during the actual run. -/
def proposalCount41 (s : BResidual 41) : ℕ :=
  daEvents41.countP fun e => decide (e.proposer = s)

/-- **The proposal counts of the four sources:** `(1, 3, 1, 1)`. -/
theorem proposalCounts_41 :
    (sourceRosterExec 41).map proposalCount41 = [1, 3, 1, 1] := by
  rw [sourceRosterExec_41]
  simp only [List.map_cons, List.map_nil, proposalCount41, daTrace_41]
  decide +kernel

/-- **The sorted parking sequence:** `(1, 1, 1, 3)`. -/
theorem parkingSequence_41 :
    List.insertionSort (· ≤ ·) ((sourceRosterExec 41).map proposalCount41) =
      [1, 1, 1, 3] := by
  rw [proposalCounts_41]
  decide

/-- **The total number of proposals is six.** -/
theorem parkingTotal_41 : ((sourceRosterExec 41).map proposalCount41).sum = 6 := by
  rw [proposalCounts_41]
  rfl

/-- **The triangular bound at `n = 41`:** with four sources the worst case is
`4 * 5 / 2 = 10`, and the actual total is `6 ≤ 10`. -/
theorem parkingBound_41 :
    ((sourceRosterExec 41).map proposalCount41).sum ≤
      (sourceRosterExec 41).length * ((sourceRosterExec 41).length + 1) / 2 := by
  rw [parkingTotal_41, sourceRosterExec_41]
  norm_num

/-- The bound is literally `6 ≤ 10`. -/
theorem parkingBound_41_literal :
    ((sourceRosterExec 41).map proposalCount41).sum = 6 ∧
      (sourceRosterExec 41).length * ((sourceRosterExec 41).length + 1) / 2 = 10 ∧
      (6 : ℕ) ≤ 10 := by
  refine ⟨parkingTotal_41, ?_, by norm_num⟩
  rw [sourceRosterExec_41]
  rfl

/-! ## The three cost counters -/

/-- The number of proposal-processing steps of the actual run. -/
def proposalSteps41 : ℕ := daEvents41.length

/-- The number of generator advances of the actual run.  By
`RecordDA.stepTrace_generator_advance` each processing step performs exactly
one generator advance, so this is the length of the event list. -/
def generatorAdvances41 : ℕ := daEvents41.length

/-- The number of held-key comparisons of the actual run.  By
`RecordDA.stepTrace_accept_iff_free` a comparison against a held key happens
exactly on the non-accepting steps. -/
def heldKeyComparisons41 : ℕ :=
  daEvents41.countP fun e => decide (e.outcome ≠ DAOutcome.accept)

/-- **The three cost counters of the actual `n = 41` run.**  Six
proposal-processing steps, six generator advances, and only *two* held-key
comparisons. -/
theorem costCounters_41 :
    proposalSteps41 = 6 ∧ generatorAdvances41 = 6 ∧ heldKeyComparisons41 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [proposalSteps41, generatorAdvances41, heldKeyComparisons41, daTrace_41] <;>
    decide +kernel

end Examples41
end TunnellMap

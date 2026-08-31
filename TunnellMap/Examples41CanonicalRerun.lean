import TunnellMap.Examples41GeneratorRun
import TunnellMap.InverseByRerun

/-!
# Executable tests for canonicalization, sign reconstruction and inverse rerunning

This file *runs* the canonical sign-lift machinery of
`TunnellMap.CanonicalSignLift`, `TunnellMap.RecordSign` and the reconstruction
step of `TunnellMap.RecordDA.inverseByRerun` on the concrete residual points
`s2`, `t1`, …, `t4` of the `n = 41` example.

Three kinds of behaviour are tested:

* *canonicalization* — `canonicalTargetLift` and `targetLiftSign` compute the
  lexicographically smaller point of an antipodal pair together with the sign
  that recovers the given point from it;
* *sign reconstruction* — the executable edge sign `etaPointExec` computes the
  manuscript's `η` for a signed pair, and agrees with the sign stored in the
  record actually emitted by the one-block generator;
* *inverse rerunning* — the reconstruction step used by `inverseByRerun`,
  applied to the held table produced by consuming a freshly generated record,
  returns the correctly *signed* residual source point, and flips that sign
  when the target point is replaced by its antipode.

All the checks are gathered into the single `IO` action `runCanonicalTests`,
which is evaluated once at the end of the file.  Every check recomputes its
value from the arithmetic of the concrete points, and raises an error —
breaking the build — if a computed value differs from the expected one.

These executions are *tests*: the facts they witness are established by the
evaluator, not by a kernel proof, and they concern single points.  They do
**not** prove the general theorems, which are
`TunnellMap.FreeInvolution.exists_unique_sign`,
`TunnellMap.canonicalResidualMapOf_signAct`,
`TunnellMap.canonicalResidualMapOf_eq_residualEquivOfOrbitCard`,
`TunnellMap.BlockGen.recordOf_sign_eq_etaPoint`,
`TunnellMap.RecordDA.inverseByRerun_canonicalResidualMap` and
`TunnellMap.RecordDA.canonicalResidualMap_inverseByRerun`.  They also do not
establish the complete `n = 41` theorem.
-/

namespace TunnellMap
namespace Examples41

open OrderedGenerator BlockGen RecordDA

set_option maxRecDepth 100000

/-! ## Executable comparisons -/

/-- Executable equality of triples. -/
def tripleEqExec (u w : Triple) : Bool :=
  decide (u.x = w.x) && decide (u.y = w.y) && decide (u.z = w.z)

theorem tripleEqExec_iff (u w : Triple) : tripleEqExec u w = true ↔ u = w := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨a', b', c'⟩ := w
  simp only [tripleEqExec, Bool.and_eq_true, decide_eq_true_eq, Triple.mk.injEq,
    and_assoc]

/-- Executable equality of residual source points, through their lifts. -/
def bResidualEqExec (u w : BResidual 41) : Bool :=
  tripleEqExec (residualSourceLift u) (residualSourceLift w)

/-- Executable equality of optional residual source points. -/
def optionBResidualEqExec : Option (BResidual 41) → BResidual 41 → Bool
  | none, _ => false
  | some u, w => bResidualEqExec u w

/-! ## The reconstruction step of `inverseByRerun`

`RecordDA.inverseByRerun` canonicalizes the target point, reruns the machine,
and then applies the *reconstruction step* below to the record held by the
canonical target lift.  The generator and the held table are executable, so the
reconstruction step can be run; the rerun itself needs the family of oriented
frames of *all* residual sources, which is not available computably here (the
deterministic frame construction is a separate task).  The tests therefore run
the generator, form the held table exactly as `RecordDA.step` does, and run the
reconstruction step on it. -/

/-- The reconstruction step used by `RecordDA.inverseByRerun`: canonicalize the
target point, read the record held at the canonical target lift, and rebuild
the signed source point from the stored proposer and sign. -/
def reconstructFromHeld (held : Triple → Option (BResidual 41 × IncidentRecord))
    (y : AResidual 41) : Option (BResidual 41) :=
  (held (canonicalTargetLift (residualTargetLift y))).map fun p =>
    signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1

/-- The reconstruction step is literally the tail of `inverseByRerun`. -/
theorem reconstructFromHeld_eq_inverseByRerun_body
    (held : Triple → Option (BResidual 41 × IncidentRecord))
    (fallback : BResidual 41) (y : AResidual 41) :
    (held (canonicalTargetLift (residualTargetLift y))).elim fallback
        (fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1) =
      (reconstructFromHeld held y).getD fallback := by
  unfold reconstructFromHeld
  cases held (canonicalTargetLift (residualTargetLift y)) <;> rfl

/-- The held table obtained by *running* the generator of `s2` once and storing
the emitted record exactly as `RecordDA.step` does. -/
def heldAfterFirstProposal : Triple → Option (BResidual 41 × IncidentRecord) :=
  match advance s2 frame41 GenState.initial with
  | none => (DARun.initial [s2]).held
  | some (r, _) => Function.update (DARun.initial [s2]).held r.target (some (s2, r))

/-! ## The executable test suite -/

/-- The executable test suite for canonicalization, sign reconstruction and
inverse rerunning. -/
def runCanonicalTests : IO Unit := do
  -- *Canonicalization.*  The canonical representative of an antipodal pair of
  -- target lifts is its lexicographically smaller point, and the sign recovers
  -- the given point from it.
  runCheck "canonical lift of t1"
    (tripleEqExec (canonicalTargetLift (residualTargetLift t1)) ⟨-4, -3, 0⟩)
  runCheck "canonical sign of t1"
    (decide (targetLiftSign (residualTargetLift t1) = 1))
  runCheck "canonical lift of -t1"
    (tripleEqExec (canonicalTargetLift (residualTargetLift (negAResidual t1)))
      ⟨-4, -3, 0⟩)
  runCheck "canonical sign of -t1"
    (decide (targetLiftSign (residualTargetLift (negAResidual t1)) = -1))
  -- The canonical representative is constant on each orbit, the signs of the
  -- two points of an orbit are opposite, and the decomposition
  -- `y = σ · canonical(orbit y)` holds at lift level.
  runCheck "canonicalization is orbit invariant"
    ([t1, t2, t3, t4].all fun t =>
      tripleEqExec (canonicalTargetLift (residualTargetLift t))
        (canonicalTargetLift (residualTargetLift (negAResidual t))))
  runCheck "opposite points have opposite signs"
    ([t1, t2, t3, t4].all fun t =>
      decide (targetLiftSign (residualTargetLift t) +
        targetLiftSign (residualTargetLift (negAResidual t)) = 0))
  runCheck "signed decomposition of target lifts"
    ([t1, t2, t3, t4].all fun t =>
      tripleEqExec
        (vsmul (targetLiftSign (residualTargetLift t))
          (canonicalTargetLift (residualTargetLift t)))
        (residualTargetLift t))
  -- *Sign reconstruction.*  The executable edge sign of a signed pair, and its
  -- behaviour under changing the sign of either point.
  runCheck "eta of (s2, t1)" (decide (etaPointExec s2 t1 = -1))
  runCheck "eta of (s2, -t1)" (decide (etaPointExec s2 (negAResidual t1) = 1))
  runCheck "eta of (-s2, t1)" (decide (etaPointExec (negBResidual s2) t1 = 1))
  runCheck "eta of (-s2, -t1)"
    (decide (etaPointExec (negBResidual s2) (negAResidual t1) = -1))
  -- The sign stored in each record generated for `s2` is the edge sign of the
  -- pair of signed points it connects.
  runCheck "record signs are edge signs"
    (decide (etaPointExec s2 t1 = genRecord1.sign) &&
      decide (etaPointExec s2 t4 = genRecord2.sign) &&
      decide (etaPointExec s2 t2 = genRecord3.sign) &&
      decide (etaPointExec s2 t3 = genRecord4.sign))
  -- *Inverse rerunning.*  The reconstruction step applied to the held table
  -- produced by consuming a freshly generated record returns the signed source
  -- point, and flips the sign with the target point.
  runCheck "reconstruction at t1 returns -s2"
    (optionBResidualEqExec (reconstructFromHeld heldAfterFirstProposal t1)
      (negBResidual s2))
  runCheck "reconstruction at -t1 returns s2"
    (optionBResidualEqExec
      (reconstructFromHeld heldAfterFirstProposal (negAResidual t1)) s2)
  -- The reconstructed point is the one whose edge sign with the target is `+1`,
  -- i.e. the pair actually emitted by the generator.
  runCheck "reconstructed pair is the emitted pair"
    (decide (etaPointExec (negBResidual s2) t1 = 1))
  -- Targets that hold no record are not reconstructed from.
  runCheck "no record held at t2"
    ((reconstructFromHeld heldAfterFirstProposal t2).isNone)
  IO.println "canonical sign lift and inverse rerunning: all executable tests passed"

#eval runCanonicalTests

end Examples41
end TunnellMap

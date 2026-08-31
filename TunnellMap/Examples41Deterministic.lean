import TunnellMap.Examples41CanonicalRerun
import TunnellMap.ComputableFullMap

/-!
# Executable tests for the deterministic frame, reduction, roster and pipeline

This file *runs* the deterministic constructions of
`TunnellMap.DeterministicFrame`, `TunnellMap.LagrangeGauss`,
`TunnellMap.ComputableRoster`, `TunnellMap.ComputablePipeline` and
`TunnellMap.ComputableFullMap` on the concrete arithmetic of `n = 41`:

* the extended-Euclidean orthogonal frame of a residual source lift;
* the Lagrange–Gauss reduction of a deliberately skew basis;
* the arithmetic enumeration of the residual source roster;
* the frame family attached to that roster;
* one forward and one inverse residual computation, run end to end by the
  block generators and the record-driven deferred-acceptance machine.

All checks are gathered into the single `IO` action `runDeterministicTests`,
which raises an error — breaking the build — as soon as a computed value
differs from the expected one.

These executions are *tests*: the facts they witness are produced by the
evaluator on single inputs, not by kernel proofs.  They do **not** establish
the separate complete `n = 41` execution-and-fibres theorem.
-/

namespace TunnellMap
namespace Examples41

open RecordDA

set_option maxRecDepth 100000

/-- `41` is squarefree. -/
theorem squarefree41 : Squarefree (41 : ℤ) :=
  (by norm_num : Prime (41 : ℤ)).squarefree

/-! ## The computed objects for `n = 41` -/

/-- The deterministic orthogonal frame of the source lift of `s2`. -/
def frameExec41 : OrthogonalFrame (tau (residualSourceLift s2)) :=
  frameExec squarefree41 s2

/-- The computable residual source roster for `n = 41`. -/
def rosterExec41 : List (BResidual 41) := sourceRosterExec 41

/-- The computable frame family for `n = 41`. -/
def framesExec41 : FrameFamily 41 := framesExec squarefree41

/-- The executable residual map for `n = 41`. -/
def residualMapExec41 : BResidual 41 → AResidual 41 :=
  residualMapExec (by norm_num) squarefree41 t1

/-- The executable inverse residual map for `n = 41`. -/
def inverseExec41 : AResidual 41 → BResidual 41 :=
  inverseByRerunExec squarefree41 s1

/-! ## Executable comparisons -/

/-- Executable equality of residual target points, through their lifts. -/
def aResidualEqExec (u w : AResidual 41) : Bool :=
  tripleEqExec (residualTargetLift u) (residualTargetLift w)

/-- Executable equality of lists of residual source points. -/
def bResidualListEqExec : List (BResidual 41) → List (BResidual 41) → Bool
  | [], [] => true
  | u :: us, w :: ws => bResidualEqExec u w && bResidualListEqExec us ws
  | _, _ => false

/-- The Lagrange–Gauss inequalities, as a Boolean test. -/
def isReducedPairExec (uv : Triple × Triple) : Bool :=
  decide (|2 * dot uv.1 uv.2| ≤ dot uv.1 uv.1) && decide (dot uv.1 uv.1 ≤ dot uv.2 uv.2)

/-- A deliberately skew input basis for the reduction test. -/
def skewU : Triple := ⟨10, 0, 0⟩

/-- The second vector of the skew input basis. -/
def skewV : Triple := ⟨1, 1, 0⟩

/-! ## The test suite -/

/-- The executable test suite for the deterministic frame, the Lagrange–Gauss
reduction, the roster enumeration, the frame family and the residual
pipeline. -/
def runDeterministicTests : IO Unit := do
  -- *Deterministic orthogonal frame.*  The extended-Euclidean construction on
  -- the source lift `τ(s₂) = (0,-5,-4)` returns the manuscript's frame.
  runCheck "frame e₁" (tripleEqExec frameExec41.e₁ ⟨1, 0, 0⟩)
  runCheck "frame e₂" (tripleEqExec frameExec41.e₂ ⟨0, -4, 5⟩)
  runCheck "frame z" (tripleEqExec frameExec41.z ⟨0, -1, 1⟩)
  -- The computed frame is the one used by the existing `n = 41` example.
  runCheck "frame agrees with frame41"
    (tripleEqExec frameExec41.e₁ frame41.e₁ &&
      tripleEqExec frameExec41.e₂ frame41.e₂)
  -- Its basis vectors really are orthogonal to the source lift, and their
  -- cross product is the source lift itself.
  runCheck "frame orthogonal"
    (decide (dot (tau (residualSourceLift s2)) frameExec41.e₁ = 0) &&
      decide (dot (tau (residualSourceLift s2)) frameExec41.e₂ = 0))
  runCheck "frame cross"
    (tripleEqExec (cross frameExec41.e₁ frameExec41.e₂)
      (tau (residualSourceLift s2)))
  -- *Lagrange–Gauss reduction.*  A skew basis of the plane `z = 0` is reduced
  -- to a short, sign-normalized basis of the same lattice.
  runCheck "reduction value"
    (tripleEqExec (lgReduce skewU skewV).1 ⟨1, 1, 0⟩ &&
      tripleEqExec (lgReduce skewU skewV).2 ⟨-5, 5, 0⟩)
  runCheck "reduction is reduced" (isReducedPairExec (lgReduce skewU skewV))
  runCheck "reduction preserves the lattice determinant"
    (tripleEqExec (cross (lgReduce skewU skewV).1 (lgReduce skewU skewV).2)
      (cross skewU skewV))
  -- The reduction of the already-reduced computed frame changes nothing.
  runCheck "frame already reduced"
    (isReducedPairExec (frameExec41.e₁, frameExec41.e₂))
  -- *Source-roster enumeration.*  Four canonical residual sources, in the
  -- manuscript's canonical order.
  runCheck "roster length" (decide (rosterExec41.length = 4))
  runCheck "roster contents" (bResidualListEqExec rosterExec41 [s1, s2, s3, s4])
  runCheck "roster is strictly increasing"
    (rosterExec41.zip rosterExec41.tail |>.all fun p =>
      tripleLexLtExec p.1.1.1 p.2.1.1)
  -- Every enumerated point is canonical in its antipodal orbit.
  runCheck "roster entries are canonical"
    (rosterExec41.all fun s => bResidualEqExec (canonicalBExec s) s)
  -- No antipode of an enumerated point is enumerated.
  runCheck "one representative per orbit"
    (rosterExec41.all fun s =>
      !(rosterExec41.any fun t => bResidualEqExec t (negBResidual s)))
  -- *Frame family.*  Every roster source carries an orthogonal reduced frame.
  runCheck "frame family orthogonal"
    (rosterExec41.all fun s =>
      decide (dot (tau (residualSourceLift s)) (framesExec41 s).e₁ = 0) &&
        decide (dot (tau (residualSourceLift s)) (framesExec41 s).e₂ = 0))
  runCheck "frame family cross"
    (rosterExec41.all fun s =>
      tripleEqExec (cross (framesExec41 s).e₁ (framesExec41 s).e₂)
        (tau (residualSourceLift s)))
  runCheck "frame family reduced"
    (rosterExec41.all fun s =>
      isReducedPairExec ((framesExec41 s).e₁, (framesExec41 s).e₂))
  -- *One forward residual computation.*  The whole pipeline — roster, frames,
  -- block generators, record-driven deferred acceptance, canonical sign lift —
  -- is run to compute the image of `s2`.
  runCheck "forward residual value"
    (tripleEqExec (residualMapExec41 s2).1.1 ⟨4, -3, 0⟩)
  -- The antipodal source gets the antipodal target: the sign lift is genuine.
  runCheck "forward residual sign"
    (aResidualEqExec (residualMapExec41 (negBResidual s2))
      (negAResidual (residualMapExec41 s2)))
  -- *One inverse residual computation*, by rerunning the same computation.
  runCheck "inverse residual value"
    (bResidualEqExec (inverseExec41 (residualMapExec41 s2)) s2)
  runCheck "inverse residual on the antipode"
    (bResidualEqExec (inverseExec41 (negAResidual (residualMapExec41 s2)))
      (negBResidual s2))
  -- The forward and inverse maps are mutually inverse on the whole roster.
  runCheck "round trip on the roster"
    (rosterExec41.all fun s =>
      bResidualEqExec (inverseExec41 (residualMapExec41 s)) s)
  IO.println "deterministic frame, reduction, roster and pipeline: all executable tests passed"

#eval runDeterministicTests

end Examples41
end TunnellMap

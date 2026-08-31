import TunnellMap.OrderedGenerator
import TunnellMap.ComputableDirection
import TunnellMap.ResidualTargetTest

/-!
# The stateful one-block arithmetic generator

`TunnellMap.OrderedGenerator.incidentStream` is an *extensional* description
of the manuscript's Algorithm 5.4: it materializes the whole set of retained
indices and sorts it.  This file implements the algorithm as the manuscript
actually states it — as a stateful generator that

* processes the outer parameter `h = 1, 2, …, (n-1)/2` in increasing order,
* holds exactly one sorted `h`-block together with the block cursor,
* emits `(key, target, sign)` records one at a time in strictly increasing
  key order,
* discards an exhausted block and deterministically advances to the next
  nonempty one.

Everything in this file is a plain `def`; no classical choice, no global sort
over `Finset.univ`, and no appeal to `incidentStream` occurs in the
implementation.
-/

namespace TunnellMap

namespace BlockGen

open OrderedGenerator

/-- One record of the manuscript's incident stream: the projective key of the
retained midpoint direction, the canonical representative of the target orbit
(as a lifted triple), and the sign `η` with `F = η F₀`. -/
structure IncidentRecord where
  key : DirectionKey
  target : Triple
  sign : ℤ
deriving DecidableEq

variable {n : ℤ} {p : Triple}

/-- The last block index of the outer loop. -/
def hMax (n : ℤ) : ℤ := (n - 1) / 2

/-! ## Steps 2–4: the candidate indices of one block -/

/-- The candidate indices of the single `h`-block.  Only the inner three
loops of Algorithm 5.4 are enumerated here; the outer `h`-loop is the
generator's state cursor. -/
def blockIndexList (n : ℤ) (F : OrthogonalFrame p) (h : ℤ) : List GeneratorIndex :=
  ((qValues n h).sort (· ≤ ·)).flatMap fun q =>
    ((bValues n F h q).sort (· ≤ ·)).flatMap fun b =>
      ((rootValues F h q b).sort (· ≤ ·)).map fun u => ⟨h, q, b, u⟩

/-! ## Steps 5–7: the retention tests and the emitted record -/

/-- The Boolean form of the retention tests of Algorithm 5.4.  Each
conjunct is an integer computation. -/
def Retained (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Prop :=
  InTauLattice (rValue F i) ∧
    tripleGcd (dValue F i) = 1 ∧
    FirstNonzeroPositive (dValue F i) ∧
    Odd (dValue F i).z ∧
    IsResidualTargetLift n (targetValue s F i) ∧
    primitiveKey (dValue F i) <
      directionKeyExec (vsub (residualSourceLift s) (targetValue s F i))

/-- The Boolean evaluation of the retention tests.  Each conjunct is an
integer computation, and the key comparison uses the executable
`keyLtExec`, so this function runs in compiled code. -/
def retainedB (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Bool :=
  decide (InTauLattice (rValue F i)) &&
  decide (tripleGcd (dValue F i) = 1) &&
  decide (FirstNonzeroPositive (dValue F i)) &&
  decide (Odd (dValue F i).z) &&
  decide (IsResidualTargetLift n (targetValue s F i)) &&
  keyLtExec (primitiveKey (dValue F i))
    (directionKeyExec (vsub (residualSourceLift s) (targetValue s F i)))

theorem retainedB_iff (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    retainedB s F i = true ↔ Retained s F i := by
  simp only [retainedB, Retained, Bool.and_eq_true, decide_eq_true_eq, keyLtExec_iff,
    and_assoc]

instance retainedDecidable (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    Decidable (Retained s F i) :=
  decidable_of_iff _ (retainedB_iff s F i)

/-- The record emitted for a retained index. -/
def recordOf (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : IncidentRecord :=
  ⟨primitiveKey (dValue F i), canonicalTargetLift (targetValue s F i),
    targetLiftSign (targetValue s F i)⟩

/-- Steps 5–7 as a partial emission function. -/
def emit (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Option IncidentRecord :=
  if Retained s F i then some (recordOf s F i) else none

/-- Comparison of two records by their projective keys. -/
def recordLe (r₁ r₂ : IncidentRecord) : Bool := keyLeExec r₁.key r₂.key

/-- The sorted `h`-block: the surviving records of the `h`-block, ordered by
projective key.  This is the only list the generator ever stores. -/
def blockRecords (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    List IncidentRecord :=
  ((blockIndexList n F h).filterMap (emit s F)).mergeSort recordLe

/-- The concatenation of all blocks from `h` onwards.  This is the
*specification* of the generator's remaining output, not its implementation:
the implementation below builds one block at a time. -/
def blocksFrom (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) :
    List IncidentRecord :=
  if h ≤ hMax n then blockRecords s F h ++ blocksFrom s F (h + 1) else []
termination_by (hMax n + 1 - h).toNat
decreasing_by omega

/-! ## The generator state -/

/-- The generator's entire storage: the next block index to be built, and the
not yet emitted tail of the current block. -/
structure GenState where
  nextBlock : ℤ
  pending : List IncidentRecord
deriving DecidableEq

/-- The generator is started before the first block. -/
def GenState.initial : GenState := ⟨1, []⟩

/-- One deterministic advance of the generator.  If the current block still
has records, the first one is emitted.  Otherwise the exhausted block is
discarded and the next block is built; the search continues until a nonempty
block is found or the outer loop is finished. -/
def advance (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : Option (IncidentRecord × GenState) :=
  match st with
  | ⟨h, r :: rest⟩ => some (r, ⟨h, rest⟩)
  | ⟨h, []⟩ =>
      if h ≤ hMax n then advance s F ⟨h + 1, blockRecords s F h⟩ else none
termination_by (hMax n + 1 - st.nextBlock).toNat
decreasing_by omega

/-- The records still to be emitted from a given state. -/
def remainingTrace (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState) :
    List IncidentRecord :=
  st.pending ++ blocksFrom s F st.nextBlock

/-- The complete trace of the generator. -/
def fullTrace (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : List IncidentRecord :=
  blocksFrom s F 1

@[simp] theorem remainingTrace_initial (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    remainingTrace s F GenState.initial = fullTrace s F := by
  simp [remainingTrace, fullTrace, GenState.initial]

end BlockGen

end TunnellMap

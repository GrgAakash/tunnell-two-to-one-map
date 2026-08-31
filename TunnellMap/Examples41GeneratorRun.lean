import TunnellMap.KernelGenerator
import TunnellMap.Examples41Generator
import TunnellMap.RecordDeferredAcceptance

/-!
# Executable tests for the one-block generator and record-driven DA

This file *runs* the executable machinery of `TunnellMap.BlockGenerator`,
`TunnellMap.BlockGeneratorState` and `TunnellMap.RecordDeferredAcceptance` on
the concrete source `s2` of the `n = 41` example, with the explicit oriented
frame `frame41`.

Three kinds of behaviour are tested:

* *generator advancement* — a single `BlockGen.advance` call produces the next
  record together with the successor state;
* *block disposal* — empty and exhausted blocks are discarded, the block
  cursor moves past them, and the generator stops when the outer loop ends;
* *deferred-acceptance consumption* — the record that `RecordDA.step` consumes
  is obtained from the generator, and the step then stores the whole record
  (hence the manuscript's sign `η`) together with the advanced generator
  state.

All the checks are gathered into the single `IO` action
`runGeneratorTests`, which is evaluated once at the end of the file.  Every
check evaluates the generator afresh from the arithmetic of `s2` and
`frame41`, and raises an error — breaking the build — if a computed value
differs from the expected one.  They are executions, not hard-coded traces.
Note that these executions are *tests*: the facts they witness are established
by the evaluator, not by a kernel proof.  The general soundness, completeness,
ordering, exact-once, trace-equality and storage theorems are proved elsewhere
(`TunnellMap.BlockGeneratorCorrect`, `TunnellMap.BlockGeneratorState`,
`TunnellMap.RecordDeferredAcceptanceCorrect`), and the emission, disposal and
exhaustion steps used below also have proved counterparts in this file.

These are focused tests on a single source.  They do **not** establish the
complete `n = 41` theorem.
-/

namespace TunnellMap
namespace Examples41

open OrderedGenerator BlockGen RecordDA

set_option maxRecDepth 100000

/-! ## Executable comparison of keys, records and generator states

The `DecidableEq` instance that `DirectionKey` inherits from its lexicographic
linear order is unusable in compiled code (see the comment in
`TunnellMap.ComputableDirection`), so the tests below compare keys through the
executable comparison `keyLtExec`. -/

/-- Executable equality of projective keys. -/
def keyEqExec (k₁ k₂ : DirectionKey) : Bool :=
  !keyLtExec k₁ k₂ && !keyLtExec k₂ k₁

theorem keyEqExec_iff (k₁ k₂ : DirectionKey) : keyEqExec k₁ k₂ = true ↔ k₁ = k₂ := by
  simp only [keyEqExec, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    ← Bool.not_eq_true, keyLtExec_iff, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- Executable equality of incident records. -/
def recordEqExec (a b : IncidentRecord) : Bool :=
  keyEqExec a.key b.key && decide (a.target = b.target) && decide (a.sign = b.sign)

theorem recordEqExec_iff (a b : IncidentRecord) : recordEqExec a b = true ↔ a = b := by
  obtain ⟨k₁, t₁, e₁⟩ := a
  obtain ⟨k₂, t₂, e₂⟩ := b
  simp only [recordEqExec, Bool.and_eq_true, decide_eq_true_eq, keyEqExec_iff,
    IncidentRecord.mk.injEq, and_assoc]

/-- Executable equality of record lists. -/
def recordListEqExec : List IncidentRecord → List IncidentRecord → Bool
  | [], [] => true
  | a :: as, b :: bs => recordEqExec a b && recordListEqExec as bs
  | _, _ => false

theorem recordListEqExec_iff :
    ∀ l m : List IncidentRecord, recordListEqExec l m = true ↔ l = m
  | [], [] => by simp [recordListEqExec]
  | [], _ :: _ => by simp [recordListEqExec]
  | _ :: _, [] => by simp [recordListEqExec]
  | a :: as, b :: bs => by
      simp only [recordListEqExec, Bool.and_eq_true, recordEqExec_iff,
        recordListEqExec_iff as bs, List.cons.injEq]

/-- Executable equality of generator states. -/
def genStateEqExec (st₁ st₂ : GenState) : Bool :=
  decide (st₁.nextBlock = st₂.nextBlock) && recordListEqExec st₁.pending st₂.pending

theorem genStateEqExec_iff (st₁ st₂ : GenState) :
    genStateEqExec st₁ st₂ = true ↔ st₁ = st₂ := by
  obtain ⟨h₁, p₁⟩ := st₁
  obtain ⟨h₂, p₂⟩ := st₂
  simp only [genStateEqExec, Bool.and_eq_true, decide_eq_true_eq, recordListEqExec_iff,
    GenState.mk.injEq]

/-- Executable equality for one emission step of the generator. -/
def emissionEqExec (o : Option (IncidentRecord × GenState))
    (r : IncidentRecord) (st : GenState) : Bool :=
  match o with
  | none => false
  | some (r', st') => recordEqExec r' r && genStateEqExec st' st

theorem emissionEqExec_iff (o : Option (IncidentRecord × GenState))
    (r : IncidentRecord) (st : GenState) :
    emissionEqExec o r st = true ↔ o = some (r, st) := by
  cases o with
  | none => simp [emissionEqExec]
  | some p =>
      obtain ⟨r', st'⟩ := p
      simp only [emissionEqExec, Bool.and_eq_true, recordEqExec_iff, genStateEqExec_iff,
        Option.some.injEq, Prod.mk.injEq]

/-- A named check that fails the build when the executed value is wrong. -/
def runCheck (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"executable generator test failed: {name}")

/-! ## The four records generated for the source `s2` -/

/-- First record emitted for `s2`: block `h = 5`, direction `(1,-1,1)`. -/
def genRecord1 : IncidentRecord := ⟨primitiveKey ⟨1, -1, 1⟩, ⟨-4, -3, 0⟩, -1⟩

/-- Second record emitted for `s2`: block `h = 5`, direction `(1,1,1)`. -/
def genRecord2 : IncidentRecord := ⟨primitiveKey ⟨1, 1, 1⟩, ⟨0, -3, 4⟩, -1⟩

/-- Third record emitted for `s2`: block `h = 20`, direction `(1,-4,1)`. -/
def genRecord3 : IncidentRecord := ⟨primitiveKey ⟨1, -4, 1⟩, ⟨-4, 3, 0⟩, -1⟩

/-- Fourth record emitted for `s2`: block `h = 20`, direction `(1,4,1)`. -/
def genRecord4 : IncidentRecord := ⟨primitiveKey ⟨1, 4, 1⟩, ⟨0, -3, -4⟩, 1⟩

/-- A record with a strictly smaller key, used to test rejection. -/
def betterRecord : IncidentRecord := ⟨primitiveKey ⟨1, 0, 0⟩, genRecord1.target, 1⟩

/-- The roster used by the deferred-acceptance statements below. -/
def daRun0 : DARun 41 := DARun.initial [s2]

/-- A control state in which the first target of `s2` already holds a better
proposal. -/
def contestedRun : DARun 41 where
  sources := [s2]
  queue := [s2]
  gen := fun _ => GenState.initial
  held := fun t => if t = genRecord1.target then some (s2, betterRecord) else none
  assigned := fun _ => none

/-- The outer loop of the generator for `n = 41` runs over `h = 1, …, 20`. -/
theorem hMax_41 : hMax 41 = 20 := by decide

/-! ## The executable test suite

All checks live in one `IO` action, executed by the single `#eval` at the end
of the file. -/

/-- The executable test suite for the one-block generator and the
record-driven deferred-acceptance step. -/
def runGeneratorTests : IO Unit := do
  -- *Block contents.*  The first four blocks of `s2` retain nothing at all.
  runCheck "block 1 empty" ((blockRecords s2 frame41 1).isEmpty)
  runCheck "block 2 empty" ((blockRecords s2 frame41 2).isEmpty)
  runCheck "block 3 empty" ((blockRecords s2 frame41 3).isEmpty)
  runCheck "block 4 empty" ((blockRecords s2 frame41 4).isEmpty)
  -- Block `h = 5` retains two records, sorted by projective key.
  runCheck "block 5 records"
    (recordListEqExec (blockRecords s2 frame41 5) [genRecord1, genRecord2])
  -- Block `h = 20` retains two records, sorted by projective key.
  runCheck "block 20 records"
    (recordListEqExec (blockRecords s2 frame41 20) [genRecord3, genRecord4])
  -- *Advancement and disposal.*  From the initial state the generator builds
  -- and discards the four empty blocks `h = 1,…,4`, builds block `h = 5`,
  -- emits its first record, and stores only the remainder of that single
  -- block, with the block cursor standing at `6`.
  runCheck "first advance"
    (emissionEqExec (advance s2 frame41 GenState.initial) genRecord1 ⟨6, [genRecord2]⟩)
  -- The next advance empties the stored block without moving the cursor.
  runCheck "second advance"
    (emissionEqExec (advance s2 frame41 ⟨6, [genRecord2]⟩) genRecord2 ⟨6, []⟩)
  -- Disposal of a run of empty blocks: with the stored block exhausted, the
  -- generator discards blocks `h = 6,…,19`, all of which are empty, and
  -- resumes emission at block `h = 20`.
  runCheck "skip empty blocks"
    (emissionEqExec (advance s2 frame41 ⟨6, []⟩) genRecord3 ⟨21, [genRecord4]⟩)
  -- After the last record the generator is exhausted.
  runCheck "exhaustion" ((advance s2 frame41 ⟨21, []⟩).isNone)
  -- *One-block storage.*  No state reached during the run ever stores more
  -- than the remainder of a single block, here at most one record.
  runCheck "one-block storage"
    (((advance s2 frame41 GenState.initial).map fun p => decide (p.2.pending.length ≤ 1)).getD false &&
      ((advance s2 frame41 ⟨6, []⟩).map fun p => decide (p.2.pending.length ≤ 1)).getD false)
  -- *The complete emitted trace* of `s2`: exactly the four records of the
  -- manuscript's preference row for `s2`.
  runCheck "full trace"
    (recordListEqExec (fullTrace s2 frame41) [genRecord1, genRecord2, genRecord3, genRecord4])
  -- The driver loop `drain` reproduces that trace.
  runCheck "drain"
    (recordListEqExec (drain s2 frame41 GenState.initial)
      [genRecord1, genRecord2, genRecord3, genRecord4])
  -- *Deferred-acceptance consumption.*  The record that the first
  -- deferred-acceptance step consumes, obtained by running the generator
  -- stored for `s2` in the initial control state.
  runCheck "DA consumes generated record"
    (emissionEqExec (advance s2 frame41 (daRun0.gen s2)) genRecord1 ⟨6, [genRecord2]⟩)
  -- The sign carried by that record is the manuscript's `η = -1`.
  runCheck "DA record sign" (decide (genRecord1.sign = -1))
  -- The generated proposal really does lose against `betterRecord`.
  runCheck "rejected proposal loses" (!keyLtExec genRecord1.key betterRecord.key)
  IO.println "one-block generator and record-driven DA: all executable tests passed"

#eval runGeneratorTests

/-! ## Proved counterparts of the executed steps

The emission, disposal and exhaustion steps are also proved.  The three
arithmetic facts about the concrete source `s2` are obtained by evaluating the
kernel-reducible generator mirrors of `TunnellMap.KernelGenerator` with
`decide +kernel`; every other statement below is derived from the generator
equations for arbitrary data. -/

/-- **Generator advancement.**  From its initial state the generator builds and
discards the four empty blocks `h = 1, …, 4`, builds block `h = 5`, emits the
first record of that block, and stores only the remainder of that single block
with the block cursor standing at `6`. -/
theorem generator_first_advance :
    advance s2 frame41 GenState.initial = some (genRecord1, ⟨6, [genRecord2]⟩) := by
  rw [← advanceK_eq (n := 41) (s := s2) (by norm_num) frame41 GenState.initial
    (by decide)]
  decide +kernel

/-- **Block disposal.**  With the stored block exhausted, the generator
discards the empty blocks `h = 6, …, 19` and resumes emission at block
`h = 20`. -/
theorem generator_skips_empty_blocks :
    advance s2 frame41 ⟨6, []⟩ = some (genRecord3, ⟨21, [genRecord4]⟩) := by
  rw [← advanceK_eq (n := 41) (s := s2) (by norm_num) frame41 ⟨6, []⟩ (by decide)]
  decide +kernel

/-- The complete trace emitted for `s2`: the four records of the manuscript's
preference row for `s2`. -/
theorem generator_full_trace :
    fullTrace s2 frame41 = [genRecord1, genRecord2, genRecord3, genRecord4] := by
  rw [fullTrace, ← blocksFromK_eq (n := 41) (s := s2) (by norm_num) frame41 21 1
    (by norm_num) (by decide)]
  decide +kernel

/-- The driver loop of the generator reproduces that trace. -/
theorem generator_drain :
    drain s2 frame41 GenState.initial =
      [genRecord1, genRecord2, genRecord3, genRecord4] := by
  rw [drain_initial]
  exact generator_full_trace

/-- Emission from a nonempty stored block leaves the block cursor fixed. -/
theorem generator_emission_step :
    advance s2 frame41 ⟨6, [genRecord2]⟩ = some (genRecord2, ⟨6, []⟩) :=
  advance_cons (s := s2) frame41 6 genRecord2 []

/-- Exhaustion, proved from the outer-loop bound. -/
theorem generator_exhausted : advance s2 frame41 ⟨21, []⟩ = none :=
  advance_nil_of_gt (s := s2) frame41 (by decide)

/-- The four keys of the executed trace are strictly increasing. -/
theorem trace_keys_strictly_increasing :
    genRecord1.key < genRecord2.key ∧ genRecord2.key < genRecord3.key ∧
      genRecord3.key < genRecord4.key := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [← keyLtExec_iff]
      rfl

/-- The state reached after the first advance satisfies the one-block
invariant: it stores a suffix of the single block it came from. -/
theorem oneBlock_after_first_advance :
    OneBlock s2 frame41 ⟨6, [genRecord2]⟩ :=
  oneBlock_advance frame41 (oneBlock_initial (s := s2) frame41) generator_first_advance

/-! ## Deferred acceptance consuming a generated record

`RecordDA.step` takes the family of oriented frames as data, and a computable
family for all sources of `n = 41` is not available here (the deterministic
frame construction is a separate task).  The tests above therefore execute the
generator call that the step consumes, and the effect of the step on the
control storage is proved for an arbitrary frame family whose value at `s2` is
`frame41`. -/

/-- **DA consumption.**  For any frame family whose value at `s2` is `frame41`,
one deferred-acceptance step consumes exactly one generated record: it stores
the advanced generator state for `s2`, holds the whole record — hence its sign
— at the record's target, and records it as the assignment of `s2`.  No
preference list is read. -/
theorem da_first_step_consumes_generated_record
    (frames : FrameFamily 41) (hf : frames s2 = frame41) :
    ∃ E : DARun 41, step frames daRun0 = some E ∧
      E.queue = [] ∧
      E.gen s2 = ⟨6, [genRecord2]⟩ ∧
      E.assigned s2 = some genRecord1 ∧
      E.held genRecord1.target = some (s2, genRecord1) := by
  have hadv' : BlockGen.advance s2 (frames s2) (daRun0.gen s2) =
      some (genRecord1, ⟨6, [genRecord2]⟩) := by
    rw [hf]; exact generator_first_advance
  refine ⟨_, step_accept (rest := []) rfl (by simp [daRun0, DARun.initial]) hadv' rfl,
    rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

/-- Once the queue is empty the integrated execution stops. -/
theorem da_step_none_of_queue_nil (frames : FrameFamily 41) (E : DARun 41)
    (hq : E.queue = []) : step frames E = none :=
  step_nil hq

/-- **Rejection.**  If the target already holds a better record the generated
proposal is rejected, the source is re-queued, and its generator cursor has
nevertheless advanced, so the next step proposes the following record. -/
theorem da_rejected_proposal_requeues
    (frames : FrameFamily 41) (hf : frames s2 = frame41) :
    ∃ E : DARun 41, step frames contestedRun = some E ∧
      E.queue = [s2] ∧
      E.gen s2 = ⟨6, [genRecord2]⟩ ∧
      E.assigned s2 = none ∧
      E.held genRecord1.target = some (s2, betterRecord) := by
  have hadv' : BlockGen.advance s2 (frames s2) (contestedRun.gen s2) =
      some (genRecord1, ⟨6, [genRecord2]⟩) := by
    rw [hf]; exact generator_first_advance
  have hheld : contestedRun.held genRecord1.target = some (s2, betterRecord) := by
    simp [contestedRun]
  have hlt : ¬ genRecord1.key < betterRecord.key := by
    rw [← keyLtExec_iff]
    simp only [Bool.not_eq_true]
    rfl
  refine ⟨_, step_reject (rest := []) rfl (by simp [contestedRun]) hadv' hheld hlt,
    rfl, ?_, rfl, hheld⟩
  simp

end Examples41
end TunnellMap

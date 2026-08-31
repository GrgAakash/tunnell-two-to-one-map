import TunnellMap.BlockGeneratorCorrect

/-!
# The stateful advance step and the one-block storage invariant

This file analyses the generator *as a state machine*.  It proves

* that one `advance` step emits exactly the next record of the remaining
  trace and leaves the state whose remaining trace is the tail,
* that repeatedly advancing terminates and produces exactly the full trace,
* and the manuscript's storage invariant: the generator's own storage is at
  every moment a suffix of a single `h`-block, so at most one block is ever
  retained.
-/

namespace TunnellMap

namespace BlockGen

open OrderedGenerator

variable {n : ℤ} {s : BResidual n}

/-! ## One advance step -/

theorem advance_step (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) :
    (∀ r st', advance s F st = some (r, st') →
        remainingTrace s F st = r :: remainingTrace s F st') ∧
      (advance s F st = none → remainingTrace s F st = []) := by
  suffices H : ∀ k : ℕ, ∀ st : GenState, (hMax n + 1 - st.nextBlock).toNat = k →
      (∀ r st', advance s F st = some (r, st') →
          remainingTrace s F st = r :: remainingTrace s F st') ∧
        (advance s F st = none → remainingTrace s F st = []) from H _ st rfl
  intro k
  induction k with
  | zero =>
      intro st hk
      obtain ⟨h, pending⟩ := st
      dsimp only at hk
      have hgt : ¬ h ≤ hMax n := by omega
      cases pending with
      | cons r rest =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            simp [remainingTrace]
          · intro hnone
            rw [advance] at hnone
            simp at hnone
      | nil =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance, if_neg hgt] at heq
            simp at heq
          · intro _
            simp only [remainingTrace, List.nil_append]
            rw [blocksFrom, if_neg hgt]
  | succ k ih =>
      intro st hk
      obtain ⟨h, pending⟩ := st
      dsimp only at hk
      cases pending with
      | cons r rest =>
          refine ⟨?_, ?_⟩
          · intro r' st' heq
            rw [advance] at heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            simp [remainingTrace]
          · intro hnone
            rw [advance] at hnone
            simp at hnone
      | nil =>
          have hle : h ≤ hMax n := by omega
          have hadv : advance s F ⟨h, []⟩ =
              advance s F ⟨h + 1, blockRecords s F h⟩ := by
            rw [advance, if_pos hle]
          have hrem : remainingTrace s F ⟨h, []⟩ =
              remainingTrace s F ⟨h + 1, blockRecords s F h⟩ := by
            simp only [remainingTrace, List.nil_append]
            rw [blocksFrom, if_pos hle]
          have hih := ih ⟨h + 1, blockRecords s F h⟩ (by dsimp only; omega)
          rw [hadv, hrem]
          exact hih

/-- Emission step: while the stored block still has records, the first one is
emitted and the block index does not move. -/
theorem advance_cons (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ)
    (r : IncidentRecord) (rest : List IncidentRecord) :
    advance s F ⟨h, r :: rest⟩ = some (r, ⟨h, rest⟩) := by
  rw [advance]

/-- Refill step: an exhausted block is discarded and the next block is built. -/
theorem advance_nil_of_le (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hle : h ≤ hMax n) :
    advance s F ⟨h, []⟩ = advance s F ⟨h + 1, blockRecords s F h⟩ := by
  rw [advance, if_pos hle]

/-- The generator stops exactly when the outer loop is finished. -/
theorem advance_nil_of_gt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hgt : ¬ h ≤ hMax n) : advance s F ⟨h, []⟩ = none := by
  rw [advance, if_neg hgt]

/-- **Block disposal.**  A block that survives no index is built, found empty,
and discarded without emitting anything; the generator moves on to the next
block index with empty storage. -/
theorem advance_dispose_empty_block (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hle : h ≤ hMax n) (hb : blockRecords s F h = []) :
    advance s F ⟨h, []⟩ = advance s F ⟨h + 1, []⟩ := by
  rw [advance_nil_of_le F hle, hb]

theorem advance_eq_some (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) :
    remainingTrace s F st = r :: remainingTrace s F st' :=
  (advance_step F st).1 r st' h

theorem advance_eq_none (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (h : advance s F st = none) :
    remainingTrace s F st = [] :=
  (advance_step F st).2 h

/-- The remaining trace strictly shrinks with every emitted record: this is
the termination certificate of the integrated execution. -/
theorem advance_length_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) :
    (remainingTrace s F st').length < (remainingTrace s F st).length := by
  rw [advance_eq_some F h]
  simp

/-! ## Draining the generator -/

/-- Run the generator to exhaustion, collecting the emitted records.  This is
the executable driver loop of Algorithm 5.4. -/
def drain (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : List IncidentRecord :=
  match _hadv : advance s F st with
  | none => []
  | some (r, st') => r :: drain s F st'
termination_by (remainingTrace s F st).length
decreasing_by exact advance_length_lt F _hadv

theorem drain_eq_remainingTrace (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : drain s F st = remainingTrace s F st := by
  induction st using drain.induct (s := s) (F := F) with
  | case1 st hst => rw [drain, hst, advance_eq_none F hst]
  | case2 st r st' hst ih =>
      rw [drain, hst]
      dsimp only
      rw [ih, advance_eq_some F hst]

/-- **Termination and total correctness of the executable run.**  Draining the
generator from its initial state produces exactly the complete trace. -/
theorem drain_initial (F : OrthogonalFrame (tau (residualSourceLift s))) :
    drain s F GenState.initial = fullTrace s F := by
  rw [drain_eq_remainingTrace, remainingTrace_initial]

/-! ## The one-block storage invariant -/

/-- The generator's own storage invariant: the pending list is always a suffix
of a *single* already built block, namely the one indexed by
`st.nextBlock - 1`.  No other block, and no part of any other block, is ever
retained. -/
def OneBlock (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : Prop :=
  st.pending <:+ blockRecords s F (st.nextBlock - 1)

theorem oneBlock_initial (F : OrthogonalFrame (tau (residualSourceLift s))) :
    OneBlock s F GenState.initial := by
  simp [OneBlock, GenState.initial]

/-- The invariant is preserved by every advance step. -/
theorem oneBlock_advance (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : OneBlock s F st) {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) : OneBlock s F st' := by
  suffices H : ∀ k : ℕ, ∀ st : GenState, (hMax n + 1 - st.nextBlock).toNat = k →
      OneBlock s F st → ∀ r st', advance s F st = some (r, st') → OneBlock s F st'
    from H _ st rfl hst r st' h
  intro k
  induction k with
  | zero =>
      intro st hk hinv r st' heq
      obtain ⟨hh, pending⟩ := st
      dsimp only at hk
      have hgt : ¬ hh ≤ hMax n := by omega
      cases pending with
      | cons a rest =>
          rw [advance] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact List.IsSuffix.trans (List.suffix_cons _ _) hinv
      | nil =>
          rw [advance, if_neg hgt] at heq
          simp at heq
  | succ k ih =>
      intro st hk hinv r st' heq
      obtain ⟨hh, pending⟩ := st
      dsimp only at hk
      cases pending with
      | cons a rest =>
          rw [advance] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact List.IsSuffix.trans (List.suffix_cons _ _) hinv
      | nil =>
          have hle : hh ≤ hMax n := by omega
          rw [advance, if_pos hle] at heq
          refine ih ⟨hh + 1, blockRecords s F hh⟩ (by dsimp only; omega) ?_ r st' heq
          show blockRecords s F hh <:+ blockRecords s F (hh + 1 - 1)
          rw [show hh + 1 - 1 = hh by ring]

/-- The storage bound implied by the invariant: the generator never holds more
records than a single block contains, and never more than the number of
candidate indices of that block. -/
theorem oneBlock_storage_bound (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : OneBlock s F st) :
    st.pending.length ≤ (blockIndexList n F (st.nextBlock - 1)).length := by
  refine le_trans (List.IsSuffix.length_le hst) ?_
  rw [blockRecords, List.length_mergeSort]
  exact List.length_filterMap_le _ _

end BlockGen

end TunnellMap

import TunnellMap.BlockGeneratorState
import TunnellMap.ResidualDeferredAcceptance

/-!
# Deferred acceptance driven directly by generated records

The deferred-acceptance machine of `TunnellMap.GloballyRanked.DAState` reads a
precomputed preference list.  This file replaces that interface by the
executable one-block generator of `TunnellMap.BlockGenerator`: the runtime
state carries one `GenState` per source, and every proposal is obtained by a
single `BlockGen.advance` step, so no preference list is ever materialized.

The two kinds of storage are kept apart:

* *generator-internal storage* is `DARun.gen`, whose one-block invariant is
  `BlockGen.OneBlock`;
* *deferred-acceptance control storage* is the roster, the FIFO queue, the
  held table and the assignment table.

Everything in this file is a plain `def`: the only classical input is the
family of oriented frames, which is supplied as data by the caller.
-/

namespace TunnellMap

namespace RecordDA

open OrderedGenerator BlockGen

instance bOddRepDecidableEq (n : ℤ) : DecidableEq (BOddRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n ∧ Odd p.z})

variable {n : ℤ}

/-- The oriented frames supplied to the executable run, one per source. -/
abbrev FrameFamily (n : ℤ) :=
  ∀ s : BResidual n, OrthogonalFrame (tau (residualSourceLift s))

/-- Runtime state of record-driven deferred acceptance.

`gen` is the generator-internal storage: one one-block generator state per
source.  `sources`, `queue`, `held` and `assigned` are the deferred-acceptance
control storage.  The held table stores the whole incident record, so the
manuscript's sign `η` of the accepted proposal is available at all times. -/
structure DARun (n : ℤ) where
  /-- The fixed roster of source representatives. -/
  sources : List (BResidual n)
  /-- The FIFO queue of currently unassigned sources. -/
  queue : List (BResidual n)
  /-- Generator-internal storage: one one-block generator state per source. -/
  gen : BResidual n → GenState
  /-- The record currently held at each target lift, with its proposer. -/
  held : Triple → Option (BResidual n × IncidentRecord)
  /-- The record currently accepted for each source. -/
  assigned : BResidual n → Option IncidentRecord

/-- The initial state: every generator is at the start of its first block, no
target is held, and every source is queued. -/
def DARun.initial (sources : List (BResidual n)) : DARun n where
  sources := sources
  queue := sources
  gen := fun _ => GenState.initial
  held := fun _ => none
  assigned := fun _ => none

/-- The number of records the generators still have to emit.  This is the
termination measure of the integrated execution. -/
def load (frames : FrameFamily n) (E : DARun n) : ℕ :=
  (E.sources.map fun s => (remainingTrace s (frames s) (E.gen s)).length).sum

/-- One deterministic step of record-driven deferred acceptance.  The head of
the queue asks its generator for exactly one further record; the record's key
is compared against the key of the record currently held by its target. -/
def step (frames : FrameFamily n) (E : DARun n) : Option (DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advance s (frames s) (E.gen s) with
        | none => none
        | some (r, g) =>
            match E.held r.target with
            | none =>
                some { E with
                  queue := rest
                  gen := Function.update E.gen s g
                  held := Function.update E.held r.target (some (s, r))
                  assigned := Function.update E.assigned s (some r) }
            | some (old, rold) =>
                if r.key < rold.key then
                  some { E with
                    queue := rest ++ [old]
                    gen := Function.update E.gen s g
                    held := Function.update E.held r.target (some (s, r))
                    assigned := Function.update
                      (Function.update E.assigned old none) s (some r) }
                else
                  some { E with
                    queue := rest ++ [s]
                    gen := Function.update E.gen s g }
      else none

/-! ## Equations for the six possible outcomes of a step -/

variable {frames : FrameFamily n} {E : DARun n} {s old : BResidual n}
  {rest : List (BResidual n)} {r rold : IncidentRecord} {g : GenState}

theorem step_nil (hq : E.queue = []) : step frames E = none := by
  unfold step; rw [hq]

theorem step_not_source (hq : E.queue = s :: rest) (hs : s ∉ E.sources) :
    step frames E = none := by
  unfold step; rw [hq]; dsimp only; rw [if_neg hs]

theorem step_exhausted (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = none) :
    step frames E = none := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]

theorem step_accept (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = none) :
    step frames E = some { E with
      queue := rest
      gen := Function.update E.gen s g
      held := Function.update E.held r.target (some (s, r))
      assigned := Function.update E.assigned s (some r) } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only; rw [hheld]

theorem step_replace (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = some (old, rold)) (hlt : r.key < rold.key) :
    step frames E = some { E with
      queue := rest ++ [old]
      gen := Function.update E.gen s g
      held := Function.update E.held r.target (some (s, r))
      assigned := Function.update
        (Function.update E.assigned old none) s (some r) } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only
  rw [hheld]; dsimp only; rw [if_pos hlt]

theorem step_reject (hq : E.queue = s :: rest) (hs : s ∈ E.sources)
    (hadv : BlockGen.advance s (frames s) (E.gen s) = some (r, g))
    (hheld : E.held r.target = some (old, rold)) (hlt : ¬ r.key < rold.key) :
    step frames E = some { E with
      queue := rest ++ [s]
      gen := Function.update E.gen s g } := by
  unfold step; rw [hq]; dsimp only; rw [if_pos hs, hadv]; dsimp only
  rw [hheld]; dsimp only; rw [if_neg hlt]

/-- Every successful step keeps the roster and updates exactly the generator
of the queue head. -/
theorem step_shape {E' : DARun n} (h : step frames E = some E') :
    ∃ (s : BResidual n) (rest : List (BResidual n)) (r : IncidentRecord)
      (g : GenState), E.queue = s :: rest ∧ s ∈ E.sources ∧
        BlockGen.advance s (frames s) (E.gen s) = some (r, g) ∧
        E'.sources = E.sources ∧ E'.gen = Function.update E.gen s g := by
  by_cases hq0 : E.queue = []
  · rw [step_nil hq0] at h; exact absurd h (by simp)
  · obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
    by_cases hs : s ∈ E.sources
    · cases hadv : BlockGen.advance s (frames s) (E.gen s) with
        | none => rw [step_exhausted hq hs hadv] at h; exact absurd h (by simp)
        | some rg =>
            obtain ⟨r, g⟩ := rg
            refine ⟨s, rest, r, g, hq, hs, hadv, ?_⟩
            cases hheld : E.held r.target with
            | none =>
                rw [step_accept hq hs hadv hheld] at h
                obtain rfl := Option.some.inj h
                exact ⟨rfl, rfl⟩
            | some p =>
                obtain ⟨o, ro⟩ := p
                by_cases hlt : r.key < ro.key
                · rw [step_replace hq hs hadv hheld hlt] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨rfl, rfl⟩
                · rw [step_reject hq hs hadv hheld hlt] at h
                  obtain rfl := Option.some.inj h
                  exact ⟨rfl, rfl⟩
    · rw [step_not_source hq hs] at h; exact absurd h (by simp)

/-! ## Termination -/

theorem sum_map_lt_of_mem {α : Type*} (l : List α) (f gf : α → ℕ) (a : α)
    (ha : a ∈ l) (hle : ∀ x, gf x ≤ f x) (hlt : gf a < f a) :
    (l.map gf).sum < (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
      rcases List.mem_cons.mp ha with rfl | hmem
      · have hsum : (t.map gf).sum ≤ (t.map f).sum := by
          clear ih ha
          induction t with
          | nil => simp
          | cons c u ihu => simpa using Nat.add_le_add (hle c) ihu
        simpa using Nat.add_lt_add_of_lt_of_le hlt hsum
      · exact Nat.add_lt_add_of_le_of_lt (hle b) (ih hmem)

/-- Every step of the executable machine consumes exactly one generated
record, so the total number of records still to be generated strictly
decreases. -/
theorem load_lt (frames : FrameFamily n) {E E' : DARun n}
    (h : step frames E = some E') : load frames E' < load frames E := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  unfold load
  rw [hsrc, hgen]
  refine sum_map_lt_of_mem _ _ _ s hs ?_ ?_
  · intro x
    by_cases hx : x = s
    · subst x
      rw [Function.update_self, advance_eq_some (frames s) hadv]
      simp
    · rw [Function.update_of_ne hx]
  · rw [Function.update_self, advance_eq_some (frames s) hadv]
    simp

/-- Run the integrated generator/deferred-acceptance machine to completion. -/
def run (frames : FrameFamily n) (E : DARun n) : DARun n :=
  match _hstep : step frames E with
  | none => E
  | some E' => run frames E'
termination_by load frames E
decreasing_by exact load_lt frames _hstep

theorem step_run_eq_none (frames : FrameFamily n) (E : DARun n) :
    step frames (run frames E) = none := by
  induction E using run.induct (frames := frames) with
  | case1 E hstep => rw [run, hstep]; dsimp only; exact hstep
  | case2 E E' hstep ih => rw [run, hstep]; dsimp only; exact ih

/-! ## The one-block storage invariant along a run -/

/-- Every generator in the state stores at most one `h`-block. -/
def OneBlockAll (frames : FrameFamily n) (E : DARun n) : Prop :=
  ∀ s : BResidual n, OneBlock s (frames s) (E.gen s)

theorem oneBlockAll_initial (frames : FrameFamily n)
    (sources : List (BResidual n)) :
    OneBlockAll frames (DARun.initial sources) :=
  fun s => oneBlock_initial (frames s)

theorem oneBlockAll_step (frames : FrameFamily n) {E E' : DARun n}
    (hE : OneBlockAll frames E) (h : step frames E = some E') :
    OneBlockAll frames E' := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  intro x
  rw [hgen]
  by_cases hx : x = s
  · subst x
    rw [Function.update_self]
    exact oneBlock_advance (frames s) (hE s) hadv
  · rw [Function.update_of_ne hx]
    exact hE x

/-- **The one-block storage invariant of the integrated execution.**  At every
moment of the run, each source's generator retains a suffix of a single
`h`-block. -/
theorem oneBlockAll_run (frames : FrameFamily n) :
    ∀ {E : DARun n}, OneBlockAll frames E → OneBlockAll frames (run frames E) := by
  intro E
  induction E using run.induct (frames := frames) with
  | case1 E hstep =>
      intro hE
      rw [run, hstep]
      dsimp only
      exact hE
  | case2 E E' hstep ih =>
      intro hE
      rw [run, hstep]
      dsimp only
      exact ih (oneBlockAll_step frames hE hstep)

end RecordDA

end TunnellMap

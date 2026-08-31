import TunnellMap.KernelPipeline

/-!
# An instrumented deferred-acceptance run

`RecordDA.stepTrace` performs exactly the state transition of `RecordDA.step`
and, in addition, reports the event that produced it: which source proposed,
to which target lift, with which projective key and which sign `η`, and
whether the proposal was accepted, rejected, or replaced a held record.

`RecordDA.runWithTrace` iterates `stepTrace` with an explicit fuel and returns
both the final state and the list of events, in the order in which they
happened.  `runWithTrace_fst` and `runWithTrace_run` prove that erasing the
trace gives exactly `RecordDA.run` — and hence `terminalRunExec`.
-/

namespace TunnellMap

namespace RecordDA

open OrderedGenerator BlockGen

variable {n : ℤ}

instance bRepDecidableEq (n : ℤ) : DecidableEq (BRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n})

instance bResidualDecidableEq (n : ℤ) : DecidableEq (BResidual n) :=
  inferInstanceAs (DecidableEq {p : BOddRep n // ¬ DirectSourceUsed p})

/-- What happened to a proposal. -/
inductive DAOutcome where
  /-- The target was free and the proposal was accepted. -/
  | accept : DAOutcome
  /-- The target was held by a worse record, which was displaced. -/
  | replace : DAOutcome
  /-- The target was held by a better record and the proposal was rejected. -/
  | reject : DAOutcome
  deriving DecidableEq, Repr

/-- One event of the instrumented run. -/
structure DAEvent (n : ℤ) where
  /-- The source that made the proposal. -/
  proposer : BResidual n
  /-- The lift of the target orbit representative that was proposed to. -/
  target : Triple
  /-- The projective key of the proposed edge. -/
  key : DirectionKey
  /-- The manuscript's sign `η` of the proposed edge. -/
  sign : ℤ
  /-- The outcome of the proposal. -/
  outcome : DAOutcome
  deriving DecidableEq

/-- **The instrumented step.**  The state transition is literally the one of
`RecordDA.step`; the extra output records the proposal. -/
def stepTrace (frames : FrameFamily n) (E : DARun n) :
    Option (DAEvent n × DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advanceK s (frames s) (E.gen s) with
        | none => none
        | some (r, g) =>
            match E.held r.target with
            | none =>
                some (⟨s, r.target, r.key, r.sign, DAOutcome.accept⟩,
                  { E with
                    queue := rest
                    gen := Function.update E.gen s g
                    held := Function.update E.held r.target (some (s, r))
                    assigned := Function.update E.assigned s (some r) })
            | some (old, rold) =>
                if r.key < rold.key then
                  some (⟨s, r.target, r.key, r.sign, DAOutcome.replace⟩,
                    { E with
                      queue := rest ++ [old]
                      gen := Function.update E.gen s g
                      held := Function.update E.held r.target (some (s, r))
                      assigned := Function.update
                        (Function.update E.assigned old none) s (some r) })
                else
                  some (⟨s, r.target, r.key, r.sign, DAOutcome.reject⟩,
                    { E with
                      queue := rest ++ [s]
                      gen := Function.update E.gen s g })
      else none

/-- **Erasing the instrumentation of one step gives `RecordDA.stepK`.** -/
theorem stepTrace_stepK (frames : FrameFamily n) (E : DARun n) :
    (stepTrace frames E).map Prod.snd = stepK frames E := by
  unfold stepTrace stepK
  cases hq : E.queue with
  | nil => rfl
  | cons s rest =>
      dsimp only
      by_cases hs : s ∈ E.sources
      · rw [if_pos hs, if_pos hs]
        cases hadv : BlockGen.advanceK s (frames s) (E.gen s) with
        | none => rfl
        | some rg =>
            obtain ⟨r, g⟩ := rg
            dsimp only
            cases hheld : E.held r.target with
            | none => rfl
            | some p =>
                obtain ⟨old, rold⟩ := p
                dsimp only
                by_cases hlt : r.key < rold.key
                · rw [if_pos hlt, if_pos hlt]; rfl
                · rw [if_neg hlt, if_neg hlt]; rfl
      · rw [if_neg hs, if_neg hs]; rfl

/-- **Erasing the instrumentation of one step gives `RecordDA.step`.** -/
theorem stepTrace_step (hn : 0 ≤ n) (frames : FrameFamily n) {E : DARun n}
    (hgen : GenStarted E) :
    (stepTrace frames E).map Prod.snd = step frames E := by
  rw [stepTrace_stepK, stepK_eq hn frames hgen]

/-! ## The shape of one instrumented step

These lemmas ground the cost accounting: every event of the trace is produced
by *exactly one* generator advance, and a held-key comparison is performed
exactly when the proposed target was not free. -/

theorem stepTrace_shape (frames : FrameFamily n) {E : DARun n} {ev : DAEvent n}
    {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ (s : BResidual n) (rest : List (BResidual n)) (g : GenState),
      E.queue = s :: rest ∧ s ∈ E.sources ∧
      BlockGen.advanceK s (frames s) (E.gen s) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      ev.proposer = s ∧ E'.gen = Function.update E.gen s g ∧
      (ev.outcome = DAOutcome.accept ↔ E.held ev.target = none) := by
  by_cases hq0 : E.queue = []
  · rw [stepTrace, hq0] at h; exact absurd h (by simp)
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  by_cases hs : s ∈ E.sources
  · cases hadv : BlockGen.advanceK s (frames s) (E.gen s) with
    | none => rw [stepTrace, hq] at h; simp only [hs, if_true, hadv] at h
              exact absurd h (by simp)
    | some rg =>
        obtain ⟨r, g⟩ := rg
        cases hheld : E.held r.target with
        | none =>
            rw [stepTrace, hq] at h
            simp only [hs, if_true, hadv, hheld] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            exact ⟨s, rest, g, hq, hs, hadv, rfl, rfl, by simp [hheld]⟩
        | some p =>
            obtain ⟨o, ro⟩ := p
            by_cases hlt : r.key < ro.key
            · rw [stepTrace, hq] at h
              simp only [hs, hadv, hheld, hlt, if_pos] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              refine ⟨s, rest, g, hq, hs, hadv, rfl, rfl, ?_⟩
              simp [hheld]
            · rw [stepTrace, hq] at h
              simp only [hs, if_true, hadv, hheld, hlt, if_false] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              refine ⟨s, rest, g, hq, hs, hadv, rfl, rfl, ?_⟩
              simp [hheld]
  · rw [stepTrace, hq] at h
    simp only [hs, if_false] at h
    exact absurd h (by simp)


/-- **One generator advance per event.**  The record carried by an event is
exactly the record the proposer's generator emitted on that step, and the
proposer's generator is the only one that moved. -/
theorem stepTrace_generator_advance (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ g, BlockGen.advanceK ev.proposer (frames ev.proposer) (E.gen ev.proposer) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      E'.gen = Function.update E.gen ev.proposer g := by
  obtain ⟨s, rest, g, -, -, hadv, hprop, hgen, -⟩ := stepTrace_shape frames h
  exact ⟨g, by rw [hprop]; exact hadv, by rw [hprop]; exact hgen⟩

/-- **A held-key comparison happens exactly on the non-accepting steps.**  The
step compares the proposed key with a held key precisely when the proposed
target was already occupied, that is, precisely when the outcome is not
`accept`. -/
theorem stepTrace_accept_iff_free (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ev.outcome = DAOutcome.accept ↔ E.held ev.target = none :=
  (stepTrace_shape frames h).choose_spec.choose_spec.choose_spec.2.2.2.2.2

/-- **The instrumented run.**  Returns the final state together with the
complete list of proposal events, in chronological order. -/
def runWithTrace (frames : FrameFamily n) :
    ℕ → DARun n → DARun n × List (DAEvent n)
  | 0, E => (E, [])
  | fuel + 1, E =>
      match stepTrace frames E with
      | none => (E, [])
      | some (ev, E') =>
          let p := runWithTrace frames fuel E'
          (p.1, ev :: p.2)

/-- **Erasing the trace gives the fuel-driven run.** -/
theorem runWithTrace_fst (frames : FrameFamily n) :
    ∀ (fuel : ℕ) (E : DARun n), (runWithTrace frames fuel E).1 = runK frames fuel E := by
  intro fuel
  induction fuel with
  | zero => intro E; rfl
  | succ fuel ih =>
      intro E
      have hmap := stepTrace_stepK frames E
      cases hst : stepTrace frames E with
      | none =>
          have : stepK frames E = none := by rw [← hmap, hst]; rfl
          rw [runWithTrace, hst, runK, this]
      | some p =>
          obtain ⟨ev, E'⟩ := p
          have : stepK frames E = some E' := by rw [← hmap, hst]; rfl
          rw [runWithTrace, hst, runK, this]
          exact ih E'

/-- **Erasing the trace gives `RecordDA.run`.** -/
theorem runWithTrace_run (hn : 0 ≤ n) (frames : FrameFamily n) (fuel : ℕ)
    (E : DARun n) (hgen : GenStarted E)
    (hstop : (stepK frames (runK frames fuel E)).isNone = true) :
    (runWithTrace frames fuel E).1 = run frames E := by
  rw [runWithTrace_fst, runK_eq hn frames fuel E hgen hstop]

/-- **Erasing the trace of the instrumented executable run gives
`terminalRunExec`.** -/
theorem runWithTrace_terminalRunExec (hn : 0 ≤ n) (hsq : Squarefree n)
    (fuel : ℕ)
    (hstop : (stepK (framesExecK hsq)
      (runK (framesExecK hsq) fuel
        (DARun.initial (sourceRosterExec n)))).isNone = true) :
    (runWithTrace (framesExecK hsq) fuel
        (DARun.initial (sourceRosterExec n))).1 =
      terminalRunExec (framesExec hsq) := by
  rw [runWithTrace_run hn _ fuel _ (genStarted_initial _) hstop, terminalRunExec,
    framesExecK_eq]

end RecordDA

end TunnellMap

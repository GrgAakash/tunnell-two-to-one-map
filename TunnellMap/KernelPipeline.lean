import TunnellMap.KernelGenerator
import TunnellMap.ComputablePipeline

/-!
# A kernel-reducible mirror of the integrated execution

`TunnellMap.RecordDA.step` calls `BlockGen.advance`, and
`TunnellMap.RecordDA.run` iterates `step` by well-founded recursion.  Neither
reduces in the kernel.  This file mirrors both by fuel-driven, structurally
recursive definitions and proves them equal to the originals:

* `RecordDA.frameExecK` / `RecordDA.framesExecK` — the computed frame family,
  with the kernel-reducible Lagrange–Gauss reduction;
* `RecordDA.stepK` — literally `RecordDA.step` with `BlockGen.advanceK` in
  place of `BlockGen.advance`;
* `RecordDA.runK` — the fuel-driven iteration of `stepK`.

`RecordDA.runK_eq` states that as soon as the fuel suffices — that is, as soon
as the state reached admits no further step — the mirror has computed exactly
`RecordDA.run`.
-/

namespace TunnellMap

namespace BlockGen

variable {n : ℤ} {s : BResidual n}

/-- The generator never moves its block cursor below its starting value. -/
theorem advance_nextBlock_pos (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : 1 ≤ st.nextBlock) {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) : 1 ≤ st'.nextBlock := by
  suffices H : ∀ k : ℕ, ∀ st : GenState, (hMax n + 1 - st.nextBlock).toNat = k →
      1 ≤ st.nextBlock → ∀ r st', advance s F st = some (r, st') → 1 ≤ st'.nextBlock
    from H _ st rfl hst r st' h
  intro k
  induction k with
  | zero =>
      intro st hk hinv r st' heq
      obtain ⟨hh, pending⟩ := st
      dsimp only at hk hinv
      have hgt : ¬ hh ≤ hMax n := by omega
      cases pending with
      | cons a rest =>
          rw [advance] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact hinv
      | nil =>
          rw [advance, if_neg hgt] at heq
          simp at heq
  | succ k ih =>
      intro st hk hinv r st' heq
      obtain ⟨hh, pending⟩ := st
      dsimp only at hk hinv
      cases pending with
      | cons a rest =>
          rw [advance] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact hinv
      | nil =>
          have hle : hh ≤ hMax n := by omega
          rw [advance, if_pos hle] at heq
          exact ih ⟨hh + 1, blockRecords s F hh⟩ (by dsimp only; omega)
            (by dsimp only; omega) r st' heq

end BlockGen

namespace RecordDA

open OrderedGenerator BlockGen

variable {n : ℤ}

/-! ## The kernel-reducible frame family -/

/-- Kernel-reducible form of `RecordDA.frameExec`. -/
def frameExecK (hsq : Squarefree n) (s : BResidual n) :
    OrthogonalFrame (tau (residualSourceLift s)) :=
  reduceFrameK (orthogonalFrameExec (tau (residualSourceLift s))
    (tripleGCD_tau_residualSourceLift hsq s))

/-- Kernel-reducible form of `RecordDA.framesExec`. -/
def framesExecK (hsq : Squarefree n) : FrameFamily n := frameExecK hsq

theorem frameExecK_eq (hsq : Squarefree n) (s : BResidual n) :
    frameExecK hsq s = frameExec hsq s := reduceFrameK_eq _

theorem framesExecK_eq (hsq : Squarefree n) : framesExecK hsq = framesExec hsq :=
  funext fun s => frameExecK_eq hsq s

/-! ## The kernel-reducible step -/

/-- Kernel-reducible form of `RecordDA.step`: literally the same control flow,
with `BlockGen.advanceK` in place of `BlockGen.advance`. -/
def stepK (frames : FrameFamily n) (E : DARun n) : Option (DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advanceK s (frames s) (E.gen s) with
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

/-- The invariant that every generator is at or beyond its first block. -/
def GenStarted (E : DARun n) : Prop := ∀ s : BResidual n, 1 ≤ (E.gen s).nextBlock

theorem genStarted_initial (sources : List (BResidual n)) :
    GenStarted (DARun.initial sources) := fun _ => by
  simp [DARun.initial, GenState.initial]

theorem genStarted_step {frames : FrameFamily n} {E E' : DARun n}
    (hE : GenStarted E) (h : step frames E = some E') : GenStarted E' := by
  obtain ⟨s, rest, r, g, hq, hs, hadv, hsrc, hgen⟩ := step_shape h
  intro x
  rw [hgen]
  by_cases hx : x = s
  · subst x
    rw [Function.update_self]
    exact advance_nextBlock_pos (frames s) (hE s) hadv
  · rw [Function.update_of_ne hx]
    exact hE x

theorem stepK_eq (hn : 0 ≤ n) (frames : FrameFamily n) {E : DARun n}
    (hgen : GenStarted E) : stepK frames E = step frames E := by
  unfold stepK step
  cases hq : E.queue with
  | nil => rfl
  | cons s rest =>
      dsimp only
      rw [advanceK_eq hn (frames s) (E.gen s) (hgen s)]
      rfl

/-! ## The kernel-reducible run -/

/-- Kernel-reducible form of `RecordDA.run`, driven by a fuel argument. -/
def runK (frames : FrameFamily n) : ℕ → DARun n → DARun n
  | 0, E => E
  | fuel + 1, E =>
      match stepK frames E with
      | none => E
      | some E' => runK frames fuel E'

/-- **The fuel-driven mirror computes the integrated run.**  As soon as the
state reached by `runK` admits no further step, it *is* the terminal state of
`RecordDA.run`. -/
theorem runK_eq (hn : 0 ≤ n) (frames : FrameFamily n) :
    ∀ (fuel : ℕ) (E : DARun n), GenStarted E →
      (stepK frames (runK frames fuel E)).isNone = true →
      runK frames fuel E = run frames E := by
  intro fuel
  induction fuel with
  | zero =>
      intro E hgen hstop
      rw [runK] at hstop ⊢
      have hs : step frames E = none := by
        rw [← stepK_eq hn frames hgen]
        exact Option.isNone_iff_eq_none.mp hstop
      rw [run, hs]
  | succ fuel ih =>
      intro E hgen hstop
      have hkeq : stepK frames E = step frames E := stepK_eq hn frames hgen
      cases hs : stepK frames E with
      | none =>
          have hs' : step frames E = none := by rw [← hkeq]; exact hs
          have hfix : runK frames (fuel + 1) E = E := by rw [runK, hs]
          rw [hfix, run, hs']
      | some E' =>
          have hs' : step frames E = some E' := by rw [← hkeq]; exact hs
          have hfix : runK frames (fuel + 1) E = runK frames fuel E' := by
            rw [runK, hs]
          rw [hfix] at hstop ⊢
          rw [run, hs']
          exact ih E' (genStarted_step hgen hs') hstop

end RecordDA

end TunnellMap

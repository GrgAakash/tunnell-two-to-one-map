import TunnellMap.DeferredAcceptanceAccounting

/-!
# Matching-phase operation counts

This is the explicit unit-cost model for Theorem 7.3.  It excludes arithmetic
inside an ordered-adjacency generator.  A successful proposal consumes one
generator record, compares at most one pair of held keys, changes the queue at
most twice, and writes at most three held/assignment slots.
-/

namespace TunnellMap

namespace GloballyRanked

structure ControlCost where
  generatorAdvances : ℕ
  keyComparisons : ℕ
  queueOperations : ℕ
  assignmentWrites : ℕ

namespace ControlCost

def zero : ControlCost := ⟨0, 0, 0, 0⟩

def add (a b : ControlCost) : ControlCost :=
  ⟨a.generatorAdvances + b.generatorAdvances,
    a.keyComparisons + b.keyComparisons,
    a.queueOperations + b.queueOperations,
    a.assignmentWrites + b.assignmentWrites⟩

end ControlCost

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

namespace DAState

variable (I : GloballyRanked K S T)

/-- Cost of the next proposal.  A zero cost means that `step` returns none. -/
noncomputable def oneStepCost (st : I.DAState) : ControlCost :=
  match st.queue with
  | [] => ControlCost.zero
  | s :: _rest =>
      if h : st.cursor s < Fintype.card T then
        let t := st.nextTarget I s h
        match st.held t with
        | none => ⟨1, 0, 1, 2⟩
        | some old =>
            if I.rank s t < I.rank old t then
              ⟨1, 1, 2, 3⟩
            else
              ⟨1, 1, 2, 0⟩
      else
        ControlCost.zero

theorem oneStepCost_bounds (st st' : I.DAState)
    (hstep : st.step I = some st') :
    (st.oneStepCost I).generatorAdvances = 1 ∧
      (st.oneStepCost I).keyComparisons ≤ 1 ∧
      (st.oneStepCost I).queueOperations ≤ 2 ∧
      (st.oneStepCost I).assignmentWrites ≤ 3 := by
  cases hqueue : st.queue with
  | nil => simp [step, oneStepCost, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp only [step, hqueue, hcur, dite_true] at hstep
        simp only [oneStepCost, hqueue, hcur, dite_true]
        split
        · simp
        · split <;> simp
      · simp [step, hqueue, hcur] at hstep

/-- Total control cost of the well-founded FIFO run. -/
noncomputable def runCost (st : I.DAState) : ControlCost :=
  match hstep : st.step I with
  | none => ControlCost.zero
  | some st' => ControlCost.add (st.oneStepCost I) (runCost st')
termination_by st.remaining I
decreasing_by exact remaining_step_lt I st st' hstep

theorem runCost_component_bounds (st : I.DAState) :
    (st.runCost I).keyComparisons ≤ (st.runCost I).generatorAdvances ∧
      (st.runCost I).queueOperations ≤
        2 * (st.runCost I).generatorAdvances ∧
      (st.runCost I).assignmentWrites ≤
        3 * (st.runCost I).generatorAdvances := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [runCost.eq_1, hstep]
      simp [ControlCost.zero]
  | case2 st st' hstep ih =>
      rw [runCost.eq_1, hstep]
      obtain ⟨hadvance, hkey, hqueue, hassign⟩ :=
        oneStepCost_bounds I st st' hstep
      simp only [ControlCost.add]
      omega

theorem runCost_advances_add_remaining (st : I.DAState) :
    (st.runCost I).generatorAdvances + (st.run I).remaining I =
      st.remaining I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [runCost.eq_1, run.eq_1, hstep]
      simp [ControlCost.zero]
  | case2 st st' hstep ih =>
      rw [runCost.eq_1, run.eq_1, hstep]
      have hadvance := (oneStepCost_bounds I st st' hstep).1
      have hremaining := remaining_step_add_one I st st' hstep
      simp only [ControlCost.add]
      omega

/-- Generator advances are exactly the successful proposal-step count. -/
theorem runCost_generatorAdvances_eq_proposalSteps (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I := by
  have haccount := runCost_advances_add_remaining I st
  have hle : (st.run I).remaining I ≤ st.remaining I := by omega
  unfold proposalSteps
  omega

/-- Exact constants implying the `O(N)` operation statement in Theorem 7.3. -/
theorem runCost_linear_bounds (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I ∧
      (st.runCost I).keyComparisons ≤ st.proposalSteps I ∧
      (st.runCost I).queueOperations ≤ 2 * st.proposalSteps I ∧
      (st.runCost I).assignmentWrites ≤ 3 * st.proposalSteps I := by
  have hcomponents := runCost_component_bounds I st
  have hadvances := runCost_generatorAdvances_eq_proposalSteps I st
  rw [hadvances] at hcomponents
  exact ⟨hadvances, hcomponents⟩

end DAState

end GloballyRanked

end TunnellMap

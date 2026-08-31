import TunnellMap.DeferredAcceptanceStability
import TunnellMap.PreferenceListPosition
import TunnellMap.MatchedOrder

/-!
# Proposal accounting for the FIFO run

Every successful machine step advances exactly one source generator.  The
invariant below records that an assigned source is held at its most recently
proposed target.  At termination this identifies each cursor with the
one-based preference position, hence with the manuscript's proposal count.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

namespace DAState

variable (I : GloballyRanked K S T)

/-- An assigned source is held at the last entry passed by its cursor. -/
def AssignedLast (st : I.DAState) : Prop :=
  ∀ s t, st.assigned s = some t →
    0 < st.cursor s ∧
      (I.preferenceList s)[st.cursor s - 1]? = some t

theorem initial_assignedLast (sourceOrder : List S) :
    (initial I sourceOrder).AssignedLast I := by
  intro s t h
  simp [initial] at h

theorem assignedLast_acceptEmpty (st : I.DAState)
    (hlast : st.AssignedLast I) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).AssignedLast I := by
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    have ht : st.nextTarget I s h = t := by
      simpa [acceptEmpty] using hassigned
    subst t
    constructor
    · simp [acceptEmpty, advancedCursor]
    · simpa [acceptEmpty, advancedCursor] using
        nextTarget_getElem? I st s h
  · have hold : st.assigned x = some t := by
      simpa [acceptEmpty, hxs] using hassigned
    have hlastOld := hlast x t hold
    simpa [acceptEmpty, advancedCursor, hxs] using hlastOld

theorem assignedLast_rejectProposal (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).AssignedLast I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    simp [rejectProposal, hsFree] at hassigned
  · have hlastOld := hlast x t hassigned
    simpa [rejectProposal, advancedCursor, hxs] using hlastOld

theorem assignedLast_replaceHeld (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).AssignedLast I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  have holdAssigned : st.assigned old = some (st.nextTarget I s h) :=
    (hv.held_iff_assigned old (st.nextTarget I s h)).mp hheld
  have hso : s ≠ old := by
    intro hEq
    have hEqAssigned : st.assigned s = st.assigned old :=
      congrArg st.assigned hEq
    have hSome : st.assigned s = some (st.nextTarget I s h) :=
      hEqAssigned.trans holdAssigned
    rw [hsFree] at hSome
    contradiction
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    have ht : st.nextTarget I s h = t := by
      simpa [replaceHeld, Ne.symm hso] using hassigned
    subst t
    constructor
    · simp [replaceHeld, advancedCursor]
    · simpa [replaceHeld, advancedCursor] using
        nextTarget_getElem? I st s h
  · by_cases hxo : x = old
    · subst x
      simp [replaceHeld, hxs] at hassigned
    · have hold : st.assigned x = some t := by
        simpa [replaceHeld, hxs, hxo] using hassigned
      have hlastOld := hlast x t hold
      simpa [replaceHeld, advancedCursor, hxs] using hlastOld

theorem assignedLast_advance (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).AssignedLast I := by
  simp only [advance]
  split
  · exact assignedLast_acceptEmpty I st hlast s rest h
  · split
    · apply assignedLast_replaceHeld I st hv hlast s rest hqueue h
      assumption
    · exact assignedLast_rejectProposal I st hv hlast s rest hqueue h

theorem assignedLast_step (st st' : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hstep : st.step I = some st') :
    st'.AssignedLast I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact assignedLast_advance I st hv hlast s rest hqueue hcur
      · simp [step, hqueue, hcur] at hstep

theorem assignedLast_run (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I) :
    (st.run I).AssignedLast I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hlast
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (valid_step I st st' hv hstep)
        (assignedLast_step I st st' hv hlast hstep)

/-- At a valid terminal state, every cursor is exactly the proposal count of
the extracted perfect matching. -/
theorem terminal_cursor_eq_proposalCount
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hqueue : st.queue = []) (s : S) :
    st.cursor s =
      I.proposalCount (matchingOfTerminal I hcard st hv hqueue) s := by
  let M := matchingOfTerminal I hcard st hv hqueue
  have hassigned : st.assigned s = some (M s) :=
    assigned_matchingOfTerminal I hcard st hv hqueue s
  obtain ⟨hpos, hlastGet⟩ := hlast s (M s) hassigned
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp hlastGet
  let j : Fin (I.preferenceList s).length := ⟨st.cursor s - 1, hidx⟩
  have hindex : I.preferenceIndex s (M s) = j := by
    apply (I.preferenceList_nodup s).injective_get
    calc
      (I.preferenceList s).get (I.preferenceIndex s (M s)) = M s :=
        I.get_preferenceIndex s (M s)
      _ = (I.preferenceList s).get j := hget.symm
  rw [I.proposalCount_eq_preferenceIndex_add_one M s, hindex]
  simp only [j]
  omega

/-- Total number of generator records already consumed by a state. -/
def cursorTotal (st : I.DAState) : ℕ :=
  ∑ s : S, st.cursor s

theorem cursorTotal_add_remaining (st : I.DAState) :
    st.cursorTotal I + st.remaining I =
      Fintype.card S * Fintype.card T := by
  unfold cursorTotal remaining
  rw [← Finset.sum_add_distrib]
  calc
    (∑ s : S, (st.cursor s + (Fintype.card T - st.cursor s))) =
        ∑ _s : S, Fintype.card T := by
          apply Finset.sum_congr rfl
          intro s _
          have hsle := st.cursor_le s
          omega
    _ = Fintype.card S * Fintype.card T := by simp

theorem remaining_step_add_one (st st' : I.DAState)
    (hstep : st.step I = some st') :
    st'.remaining I + 1 = st.remaining I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact remaining_advance_add_one I st s rest hcur
      · simp [step, hqueue, hcur] at hstep

/-- The successful-step count certified by the decreasing measure. -/
noncomputable def proposalSteps (st : I.DAState) : ℕ :=
  st.remaining I - (st.run I).remaining I

theorem proposalSteps_initial_eq_terminalCursorTotal
    (sourceOrder : List S) :
    (initial I sourceOrder).proposalSteps I =
      ((initial I sourceOrder).run I).cursorTotal I := by
  have hinitial := cursorTotal_add_remaining I (initial I sourceOrder)
  have hterminal := cursorTotal_add_remaining I ((initial I sourceOrder).run I)
  have hzero : (initial I sourceOrder).cursorTotal I = 0 := by
    simp [initial, cursorTotal]
  have hinitRemaining : (initial I sourceOrder).remaining I =
      Fintype.card S * Fintype.card T := by
    omega
  unfold proposalSteps
  rw [hinitRemaining]
  omega

/-- The actual terminal cursor sum equals the abstract proposal-count sum of
the output matching. -/
theorem terminal_cursorTotal_eq_proposalCount_sum
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hqueue : st.queue = []) :
    st.cursorTotal I =
      ∑ s : S, I.proposalCount
        (matchingOfTerminal I hcard st hv hqueue) s := by
  unfold cursorTotal
  apply Finset.sum_congr rfl
  intro s _
  exact terminal_cursor_eq_proposalCount I hcard st hv hlast hqueue s

/-- Exact proposal accounting and the paper's triangular upper bound for a
complete FIFO run. -/
theorem run_proposalSteps_le_triangular
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    (initial I sourceOrder).proposalSteps I ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let hl₀ : st₀.AssignedLast I := initial_assignedLast I sourceOrder
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hl : st.AssignedLast I := assignedLast_run I st₀ hv₀ hl₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  let M := matchingOfTerminal I hcard st hv hqueue
  have hsteps : st₀.proposalSteps I = st.cursorTotal I :=
    proposalSteps_initial_eq_terminalCursorTotal I sourceOrder
  have htotal : st.cursorTotal I = ∑ s : S, I.proposalCount M s :=
    terminal_cursorTotal_eq_proposalCount_sum I hcard st hv hl hqueue
  rw [hsteps, htotal]
  exact I.proposalCount_total_le_triangular M
    (matchingOfTerminal_stable I hcard st hv
      (proposalValid_run I st₀ (initial_proposalValid I sourceOrder)) hqueue)

/-- Array slots and queue entries retained by the control layer, excluding
all generator-internal state.  We count cursor and assignment slots
separately for each source, one held slot for each target, and the queue. -/
def auxiliaryRecordSlots (st : I.DAState) : ℕ :=
  2 * Fintype.card S + Fintype.card T + st.queue.length

/-- Under equal side cardinalities, a valid state uses at most `4m`
auxiliary control records. -/
theorem auxiliaryRecordSlots_le_four_mul
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.auxiliaryRecordSlots I ≤ 4 * Fintype.card S := by
  have hqueue : st.queue.length ≤ Fintype.card S :=
    hv.queue_nodup.length_le_card
  unfold auxiliaryRecordSlots
  omega

end DAState

end GloballyRanked

end TunnellMap

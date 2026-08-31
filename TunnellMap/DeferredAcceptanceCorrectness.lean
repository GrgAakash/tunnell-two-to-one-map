import TunnellMap.DeferredAcceptanceAlgorithm

/-!
# Correctness invariants for FIFO deferred acceptance

The invariant identifies the FIFO queue with the unassigned sources, records
that the two partial assignment maps are inverses, and says that every target
already passed by a source cursor remains occupied.  These are the four facts
used in the manuscript's termination and perfectness argument.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

namespace DAState

variable (I : GloballyRanked K S T)

def Occupied (st : I.DAState) (t : T) : Prop :=
  ∃ s, st.held t = some s

/-- The inductive state invariant of Algorithm 6.1. -/
structure Valid (st : I.DAState) : Prop where
  queue_nodup : st.queue.Nodup
  queued_iff_unassigned : ∀ s, s ∈ st.queue ↔ st.assigned s = none
  held_iff_assigned : ∀ s t, st.held t = some s ↔ st.assigned s = some t
  tried_occupied : ∀ s t,
    t ∈ (I.preferenceList s).take (st.cursor s) → st.Occupied I t

theorem initial_valid (sourceOrder : List S)
    (hnodup : sourceOrder.Nodup) (hcomplete : ∀ s, s ∈ sourceOrder) :
    (initial I sourceOrder).Valid I := by
  refine ⟨hnodup, ?_, ?_, ?_⟩
  · intro s
    simpa [initial] using hcomplete s
  · intro s t
    simp [initial]
  · intro s t ht
    simp [initial] at ht

/-- A valid queued source has a next untried target.  This is the finite
pigeonhole argument in the first paragraph of Theorem 6.3. -/
theorem queued_cursor_lt (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (s : S) (hs : s ∈ st.queue) :
    st.cursor s < Fintype.card T := by
  by_contra hnot
  have hcursor : st.cursor s = Fintype.card T := by
    have := st.cursor_le s
    omega
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hs
  have hoccupied : ∀ t : T, st.Occupied I t := by
    intro t
    apply hv.tried_occupied s t
    have ht := I.mem_preferenceList s t
    rw [hcursor, ← I.length_preferenceList s, List.take_length]
    exact ht
  classical
  let holder : T → S := fun t => Classical.choose (hoccupied t)
  have holder_spec (t : T) : st.held t = some (holder t) :=
    Classical.choose_spec (hoccupied t)
  have holder_ne (t : T) : holder t ≠ s := by
    intro heq
    have hassigned := (hv.held_iff_assigned (holder t) t).mp (holder_spec t)
    rw [heq, hsFree] at hassigned
    contradiction
  let f : T → {x : S // x ≠ s} := fun t => ⟨holder t, holder_ne t⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    have hholder : holder t₁ = holder t₂ := congrArg Subtype.val h
    have h₁ := (hv.held_iff_assigned (holder t₁) t₁).mp (holder_spec t₁)
    have h₂ := (hv.held_iff_assigned (holder t₂) t₂).mp (holder_spec t₂)
    rw [hholder] at h₁
    exact Option.some.inj (h₁.symm.trans h₂)
  have hle : Fintype.card T ≤ Fintype.card {x : S // x ≠ s} :=
    Fintype.card_le_of_injective f hf
  have hcompl : Fintype.card {x : S // x ≠ s} = Fintype.card S - 1 := by
    simp
  rw [hcompl, ← hcard] at hle
  have hSpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s⟩
  have hTpos : 0 < Fintype.card T := by omega
  omega

theorem step_eq_none_iff_queue_nil
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.step I = none ↔ st.queue = [] := by
  constructor
  · intro hstep
    cases hqueue : st.queue with
    | nil => rfl
    | cons s rest =>
        have hs : s ∈ st.queue := by simp [hqueue]
        have hcur := queued_cursor_lt I hcard st hv s hs
        simp [step, hqueue, hcur] at hstep
  · intro hqueue
    simp [step, hqueue]

theorem nextTarget_getElem? (st : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T) :
    (I.preferenceList s)[st.cursor s]? = some (st.nextTarget I s h) := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simpa using h, ?_⟩
  rfl

/-- The cursor/occupancy part of the invariant is common to all three
proposal outcomes. -/
theorem tried_occupied_after_cursor_advance
    (st st' : I.DAState) (hv : st.Valid I) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    (hmono : ∀ t, st.Occupied I t → st'.Occupied I t)
    (hnext : st'.Occupied I (st.nextTarget I s h)) :
    ∀ x t, t ∈ (I.preferenceList x).take (st'.cursor x) →
      st'.Occupied I t := by
  intro x t ht
  by_cases hx : x = s
  · subst x
    rw [hself, List.take_succ, nextTarget_getElem?] at ht
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact hmono t (hv.tried_occupied s t ht)
    · simpa only [ht] using hnext
  · rw [hother x hx] at ht
    exact hmono t (hv.tried_occupied x t ht)

theorem valid_acceptEmpty (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T)
    (hempty : st.held (st.nextTarget I s h) = none) :
    (st.acceptEmpty I s rest h).Valid I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  refine ⟨hn.2, ?_, ?_, ?_⟩
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    by_cases hx : x = s
    · subst x
      simp [acceptEmpty, hsNotRest]
    · simpa [acceptEmpty, hx] using hold
  · intro x u
    by_cases hu : u = st.nextTarget I s h
    · subst u
      by_cases hx : x = s
      · subst x
        simp [acceptEmpty]
      · constructor
        · intro hheld
          simp [acceptEmpty, hx] at hheld
          exact (hx hheld.symm).elim
        · intro hassigned
          have holdAssigned : st.assigned x =
              some (st.nextTarget I s h) := by
            simpa [acceptEmpty, hx] using hassigned
          have holdHeld :=
            (hv.held_iff_assigned x (st.nextTarget I s h)).mpr holdAssigned
          rw [hempty] at holdHeld
          contradiction
    · by_cases hx : x = s
      · subst x
        constructor
        · intro hheld
          have holdAssigned := (hv.held_iff_assigned s u).mp (by
            simpa [acceptEmpty, hu] using hheld)
          rw [hsFree] at holdAssigned
          contradiction
        · intro hassigned
          simp [acceptEmpty, hu] at hassigned
          exact (hu hassigned.symm).elim
      · simpa [acceptEmpty, hu, hx] using hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.acceptEmpty I s rest h) hv s h
    · simp [acceptEmpty, advancedCursor]
    · intro x hx
      simp [acceptEmpty, advancedCursor, hx]
    · intro u hu
      rcases hu with ⟨x, hx⟩
      by_cases hut : u = st.nextTarget I s h
      · subst u
        exact ⟨s, by simp [acceptEmpty]⟩
      · exact ⟨x, by simpa [acceptEmpty, hut] using hx⟩
    · exact ⟨s, by simp [acceptEmpty]⟩

theorem valid_rejectProposal (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T)
    {old : S} (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.rejectProposal I s rest h).Valid I := by
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (rest ++ [s]).Nodup
    rw [List.nodup_append]
    refine ⟨hn.2, by simp, ?_⟩
    intro a ha b hb
    have hbEq : b = s := by simpa using hb
    subst b
    exact fun has => hsNotRest (has ▸ ha)
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    simpa [rejectProposal, or_comm] using hold
  · intro x u
    simpa [rejectProposal] using hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.rejectProposal I s rest h) hv s h
    · simp [rejectProposal, advancedCursor]
    · intro x hx
      simp [rejectProposal, advancedCursor, hx]
    · intro u hu
      simpa [Occupied, rejectProposal] using hu
    · exact ⟨old, by simpa [rejectProposal] using hheld⟩

theorem valid_replaceHeld (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).Valid I := by
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
  have hn := hv.queue_nodup
  rw [hqueue, List.nodup_cons] at hn
  have hsNotRest : s ∉ rest := hn.1
  have holdNotQueue : old ∉ st.queue := by
    intro holdMem
    have holdFree := (hv.queued_iff_unassigned old).mp holdMem
    rw [holdAssigned] at holdFree
    contradiction
  have holdNotRest : old ∉ rest := by
    intro holdMem
    exact holdNotQueue (by simp [hqueue, holdMem])
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (rest ++ [old]).Nodup
    rw [List.nodup_append]
    refine ⟨hn.2, by simp, ?_⟩
    intro a ha b hb
    have hbEq : b = old := by simpa using hb
    subst b
    exact fun hao => holdNotRest (hao ▸ ha)
  · intro x
    have hold := hv.queued_iff_unassigned x
    rw [hqueue] at hold
    by_cases hxs : x = s
    · subst x
      simp [replaceHeld, hsNotRest, hso]
    · by_cases hxo : x = old
      · subst x
        simp [replaceHeld, Ne.symm hso]
      · simpa [replaceHeld, hxs, hxo] using hold
  · intro x u
    by_cases hu : u = st.nextTarget I s h
    · subst u
      by_cases hxs : x = s
      · subst x
        simp [replaceHeld]
      · constructor
        · intro hnewHeld
          simp [replaceHeld] at hnewHeld
          exact (hxs hnewHeld.symm).elim
        · intro hnewAssigned
          by_cases hxo : x = old
          · subst x
            simp [replaceHeld, Ne.symm hso] at hnewAssigned
          · have holdX : st.assigned x =
                some (st.nextTarget I s h) := by
              simpa [replaceHeld, hxs, hxo] using hnewAssigned
            have hheldX :=
              (hv.held_iff_assigned x (st.nextTarget I s h)).mpr holdX
            have hxOld : x = old := Option.some.inj (hheldX.symm.trans hheld)
            exact (hxo hxOld).elim
    · by_cases hxs : x = s
      · subst x
        constructor
        · intro hnewHeld
          have holdHeld : st.held u = some s := by
            simpa [replaceHeld, hu] using hnewHeld
          have holdSource := (hv.held_iff_assigned s u).mp holdHeld
          rw [hsFree] at holdSource
          contradiction
        · intro hnewAssigned
          have htargetEq : st.nextTarget I s h = u := by
            simpa [replaceHeld] using hnewAssigned
          exact (hu htargetEq.symm).elim
      · by_cases hxo : x = old
        · subst x
          constructor
          · intro hnewHeld
            have holdHeld : st.held u = some old := by
              simpa [replaceHeld, hu] using hnewHeld
            have holdSource := (hv.held_iff_assigned old u).mp holdHeld
            have huEq : u = st.nextTarget I s h :=
              Option.some.inj (holdSource.symm.trans holdAssigned)
            exact (hu huEq).elim
          · intro hnewAssigned
            simp [replaceHeld, Ne.symm hso] at hnewAssigned
        · simpa [replaceHeld, hu, hxs, hxo] using
            hv.held_iff_assigned x u
  · apply tried_occupied_after_cursor_advance I st
      (st.replaceHeld I s rest h old) hv s h
    · simp [replaceHeld, advancedCursor]
    · intro x hx
      simp [replaceHeld, advancedCursor, hx]
    · intro u hu
      rcases hu with ⟨x, hx⟩
      by_cases hut : u = st.nextTarget I s h
      · subst u
        exact ⟨s, by simp [replaceHeld]⟩
      · exact ⟨x, by simpa [replaceHeld, hut] using hx⟩
    · exact ⟨s, by simp [replaceHeld]⟩

theorem valid_advance (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).Valid I := by
  simp only [advance]
  split
  · apply valid_acceptEmpty I st hv s rest hqueue h
    assumption
  · split
    · apply valid_replaceHeld I st hv s rest hqueue h
      assumption
    · apply valid_rejectProposal I st hv s rest hqueue h
      assumption

theorem valid_step (st st' : I.DAState) (hv : st.Valid I)
    (hstep : st.step I = some st') : st'.Valid I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact valid_advance I st hv s rest hqueue hcur
      · simp [step, hqueue, hcur] at hstep

theorem valid_run (st : I.DAState) (hv : st.Valid I) :
    (st.run I).Valid I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hv
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (valid_step I st st' hv hstep)

/-- From a valid state on equal finite sides, `run` terminates with no free
source left in the FIFO queue. -/
theorem run_queue_nil (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    (st.run I).queue = [] := by
  have hvrun := valid_run I st hv
  exact (step_eq_none_iff_queue_nil I hcard (st.run I) hvrun).mp
    (step_run_eq_none I st)

end DAState

end GloballyRanked

end TunnellMap

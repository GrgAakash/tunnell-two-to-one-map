import TunnellMap.DeferredAcceptanceOutput

/-!
# Proposal-history invariants and stability

Besides the structural queue invariant, deferred acceptance uses two history
facts: an assigned edge has already been proposed, and a target's held key is
no larger than the key of any proposal it has received.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

namespace DAState

variable (I : GloballyRanked K S T)

structure ProposalValid (st : I.DAState) : Prop where
  assigned_tried : ∀ s t, st.assigned s = some t →
    t ∈ (I.preferenceList s).take (st.cursor s)
  held_dominates : ∀ s t,
    t ∈ (I.preferenceList s).take (st.cursor s) →
      ∃ holder, st.held t = some holder ∧
        I.rank holder t ≤ I.rank s t

theorem initial_proposalValid (sourceOrder : List S) :
    (initial I sourceOrder).ProposalValid I := by
  constructor
  · intro s t hassigned
    simp [initial] at hassigned
  · intro s t ht
    simp [initial] at ht

theorem old_mem_take_after_cursor_advance
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    {x : S} {t : T}
    (ht : t ∈ (I.preferenceList x).take (st.cursor x)) :
    t ∈ (I.preferenceList x).take (st'.cursor x) := by
  by_cases hx : x = s
  · subst x
    rw [hself, List.take_succ, nextTarget_getElem? I st s h]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton]
    exact Or.inl ht
  · rw [hother x hx]
    exact ht

theorem new_mem_take_after_cursor_advance
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1) :
    st.nextTarget I s h ∈
      (I.preferenceList s).take (st'.cursor s) := by
  rw [hself, List.take_succ, nextTarget_getElem? I st s h]
  simp

theorem mem_take_after_cursor_advance_cases
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    {x : S} {t : T}
    (ht : t ∈ (I.preferenceList x).take (st'.cursor x)) :
    t ∈ (I.preferenceList x).take (st.cursor x) ∨
      (x = s ∧ t = st.nextTarget I s h) := by
  by_cases hx : x = s
  · subst x
    rw [hself, List.take_succ, nextTarget_getElem? I st s h] at ht
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨rfl, ht⟩
  · rw [hother x hx] at ht
    exact Or.inl ht

theorem proposalValid_acceptEmpty
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    (hempty : st.held (st.nextTarget I s h) = none) :
    (st.acceptEmpty I s rest h).ProposalValid I := by
  let st' := st.acceptEmpty I s rest h
  have hself : st'.cursor s = st.cursor s + 1 := by
    simp [st', acceptEmpty, advancedCursor]
  have hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x := by
    intro x hx
    simp [st', acceptEmpty, advancedCursor, hx]
  constructor
  · intro x t hassigned
    by_cases hx : x = s
    · subst x
      have hsome : some (st.nextTarget I s h) = some t := by
        simpa [st', acceptEmpty] using hassigned
      have ht : t = st.nextTarget I s h := (Option.some.inj hsome).symm
      subst t
      exact new_mem_take_after_cursor_advance I st st' s h hself
    · have holdAssigned : st.assigned x = some t := by
        simpa [st', acceptEmpty, hx] using hassigned
      exact old_mem_take_after_cursor_advance I st st' s h hself hother
        (hv.assigned_tried x t holdAssigned)
  · intro x t ht
    rcases mem_take_after_cursor_advance_cases I st st' s h hself hother ht with
      hold | hnew
    · obtain ⟨holder, hheld, hkey⟩ := hv.held_dominates x t hold
      by_cases hut : t = st.nextTarget I s h
      · subst t
        rw [hempty] at hheld
        contradiction
      · exact ⟨holder, by simpa [st', acceptEmpty, hut] using hheld, hkey⟩
    · rcases hnew with ⟨hxs, htnew⟩
      subst x
      subst t
      exact ⟨s, by simp [st', acceptEmpty], le_rfl⟩

theorem proposalValid_rejectProposal
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    {old : S} (hheld : st.held (st.nextTarget I s h) = some old)
    (hnotbetter : ¬ I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    (st.rejectProposal I s rest h).ProposalValid I := by
  let st' := st.rejectProposal I s rest h
  have hself : st'.cursor s = st.cursor s + 1 := by
    simp [st', rejectProposal, advancedCursor]
  have hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x := by
    intro x hx
    simp [st', rejectProposal, advancedCursor, hx]
  constructor
  · intro x t hassigned
    have holdAssigned : st.assigned x = some t := by
      simpa [st', rejectProposal] using hassigned
    exact old_mem_take_after_cursor_advance I st st' s h hself hother
      (hv.assigned_tried x t holdAssigned)
  · intro x t ht
    rcases mem_take_after_cursor_advance_cases I st st' s h hself hother ht with
      hold | hnew
    · obtain ⟨holder, hholder, hkey⟩ := hv.held_dominates x t hold
      exact ⟨holder, by simpa [st', rejectProposal] using hholder, hkey⟩
    · rcases hnew with ⟨hxs, htnew⟩
      subst x
      subst t
      exact ⟨old, by simpa [st', rejectProposal] using hheld,
        le_of_not_gt hnotbetter⟩

theorem proposalValid_replaceHeld
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    (old : S) (hheld : st.held (st.nextTarget I s h) = some old)
    (hbetter : I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    (st.replaceHeld I s rest h old).ProposalValid I := by
  let st' := st.replaceHeld I s rest h old
  have hself : st'.cursor s = st.cursor s + 1 := by
    simp [st', replaceHeld, advancedCursor]
  have hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x := by
    intro x hx
    simp [st', replaceHeld, advancedCursor, hx]
  have hso : s ≠ old := by
    intro hEq
    subst old
    exact (lt_irrefl _ hbetter)
  constructor
  · intro x t hassigned
    by_cases hxs : x = s
    · subst x
      have hsome : some (st.nextTarget I s h) = some t := by
        simpa [st', replaceHeld] using hassigned
      have ht : t = st.nextTarget I s h := (Option.some.inj hsome).symm
      subst t
      exact new_mem_take_after_cursor_advance I st st' s h hself
    · by_cases hxo : x = old
      · subst x
        simp [st', replaceHeld, Ne.symm hso] at hassigned
      · have holdAssigned : st.assigned x = some t := by
          simpa [st', replaceHeld, hxs, hxo] using hassigned
        exact old_mem_take_after_cursor_advance I st st' s h hself hother
          (hv.assigned_tried x t holdAssigned)
  · intro x t ht
    rcases mem_take_after_cursor_advance_cases I st st' s h hself hother ht with
      hold | hnew
    · obtain ⟨holder, hholder, hkey⟩ := hv.held_dominates x t hold
      by_cases hut : t = st.nextTarget I s h
      · subst t
        have hholderOld : holder = old :=
          Option.some.inj (hholder.symm.trans hheld)
        subst holder
        exact ⟨s, by simp [st', replaceHeld], hbetter.le.trans hkey⟩
      · exact ⟨holder, by simpa [st', replaceHeld, hut] using hholder, hkey⟩
    · rcases hnew with ⟨hxs, htnew⟩
      subst x
      subst t
      exact ⟨s, by simp [st', replaceHeld], le_rfl⟩

theorem proposalValid_advance
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).ProposalValid I := by
  simp only [advance]
  split
  · apply proposalValid_acceptEmpty I st hv s rest h
    assumption
  · split
    · apply proposalValid_replaceHeld I st hv s rest h
      · assumption
      · assumption
    · apply proposalValid_rejectProposal I st hv s rest h
      · assumption
      · assumption

theorem proposalValid_step (st st' : I.DAState)
    (hv : st.ProposalValid I) (hstep : st.step I = some st') :
    st'.ProposalValid I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact proposalValid_advance I st hv s rest hcur
      · simp [step, hqueue, hcur] at hstep

theorem proposalValid_run (st : I.DAState) (hv : st.ProposalValid I) :
    (st.run I).ProposalValid I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hv
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (proposalValid_step I st st' hv hstep)

/-- In a source's sorted preference list, every target with smaller key than
an already tried target has also been tried. -/
theorem mem_take_of_rank_lt_of_mem_take (s : S) {t u : T} {k : ℕ}
    (hrank : I.rank s t < I.rank s u)
    (hu : u ∈ (I.preferenceList s).take k) :
    t ∈ (I.preferenceList s).take k := by
  let l := I.preferenceList s
  obtain ⟨j, hjMin, hjEq⟩ := List.mem_take_iff_getElem.mp hu
  have htMem : t ∈ l := I.mem_preferenceList s t
  obtain ⟨i, hiLen, hiEq⟩ := List.mem_iff_getElem.mp htMem
  have hjLen : j < l.length := lt_of_lt_of_le hjMin (Nat.min_le_right _ _)
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    rcases hji.eq_or_lt with hEq | hlt
    · subst i
      have htu : t = u := hiEq.symm.trans hjEq
      exact (ne_of_lt hrank) (congrArg (I.rank s) htu)
    · have hstrict := I.preferenceList_strict s
          (i := ⟨j, hjLen⟩) (j := ⟨i, hiLen⟩) hlt
      have hgetJ : l.get ⟨j, hjLen⟩ = u := hjEq
      have hgetI : l.get ⟨i, hiLen⟩ = t := hiEq
      rw [hgetJ, hgetI] at hstrict
      exact (not_lt_of_ge hrank.le) hstrict
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i, ?_, hiEq⟩
  exact lt_min (hij.trans (lt_of_lt_of_le hjMin (Nat.min_le_left _ _))) hiLen

/-- The matching encoded by a valid terminal state has the transcript-free
deferred-acceptance certificate. -/
theorem matchingOfTerminal_certificate
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.DeferredAcceptanceCertificate
      (matchingOfTerminal I hcard st hv hqueue) := by
  let M := matchingOfTerminal I hcard st hv hqueue
  intro s t hsource
  have hfinalAssigned : st.assigned s = some (M s) :=
    assigned_matchingOfTerminal I hcard st hv hqueue s
  have hfinalTried := hp.assigned_tried s (M s) hfinalAssigned
  have htTried := mem_take_of_rank_lt_of_mem_take I s hsource hfinalTried
  obtain ⟨holder, hheld, hle⟩ := hp.held_dominates s t htTried
  have hholder : M.symm t = holder :=
    matchingOfTerminal_symm_eq I hcard st hv hqueue holder t hheld
  rw [hholder]
  apply lt_of_le_of_ne hle
  intro heq
  have hholderEq : holder = s := I.target_injective t heq
  have hmatched : M s = t := by
    apply (held_iff_matchingOfTerminal I hcard st hv hqueue s t).mp
    simpa [hholderEq] using hheld
  rw [hmatched] at hsource
  exact (lt_irrefl _ hsource).elim

theorem matchingOfTerminal_stable
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.Stable (matchingOfTerminal I hcard st hv hqueue) :=
  I.stable_of_deferredAcceptanceCertificate _
    (matchingOfTerminal_certificate I hcard st hv hp hqueue)

theorem deferredAcceptanceMatching_stable
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    I.Stable (deferredAcceptanceMatching I hcard sourceOrder hnodup hcomplete) := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let hp₀ : st₀.ProposalValid I := initial_proposalValid I sourceOrder
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hp : st.ProposalValid I := proposalValid_run I st₀ hp₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  change I.Stable (matchingOfTerminal I hcard st hv hqueue)
  exact matchingOfTerminal_stable I hcard st hv hp hqueue

/-- The executable FIFO algorithm returns the unique stable matching already
characterized abstractly. -/
theorem deferredAcceptanceMatching_eq_unique
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    deferredAcceptanceMatching I hcard sourceOrder hnodup hcomplete =
      Classical.choose (I.exists_unique_stable hcard) := by
  classical
  exact (Classical.choose_spec (I.exists_unique_stable hcard)).2 _
    (deferredAcceptanceMatching_stable I hcard sourceOrder hnodup hcomplete)

/-- Changing the deterministic initial queue order cannot change the output in
a globally ranked instance, because the stable perfect matching is unique. -/
theorem deferredAcceptanceMatching_order_independent
    (hcard : Fintype.card S = Fintype.card T)
    (order₁ order₂ : List S)
    (hnodup₁ : order₁.Nodup) (hnodup₂ : order₂.Nodup)
    (hcomplete₁ : ∀ s, s ∈ order₁) (hcomplete₂ : ∀ s, s ∈ order₂) :
    deferredAcceptanceMatching I hcard order₁ hnodup₁ hcomplete₁ =
      deferredAcceptanceMatching I hcard order₂ hnodup₂ hcomplete₂ := by
  rw [deferredAcceptanceMatching_eq_unique I hcard order₁ hnodup₁ hcomplete₁,
    deferredAcceptanceMatching_eq_unique I hcard order₂ hnodup₂ hcomplete₂]

end DAState

end GloballyRanked

end TunnellMap

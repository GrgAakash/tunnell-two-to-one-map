import TunnellMap.DeferredAcceptanceCorrectness

/-!
# Extracting the perfect matching from the terminal queue state

An empty valid queue assigns every source.  The terminal assignment is
injective because the held and assigned maps are partial inverses; equal finite
cardinalities therefore make it bijective.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

namespace DAState

variable (I : GloballyRanked K S T)

theorem exists_assigned_of_queue_nil (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) : ∃ t, st.assigned s = some t := by
  cases hassigned : st.assigned s with
  | none =>
      have hsMem := (hv.queued_iff_unassigned s).mpr hassigned
      rw [hqueue] at hsMem
      contradiction
  | some t => exact ⟨t, rfl⟩

noncomputable def assignedTarget (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) : T :=
  Classical.choose (exists_assigned_of_queue_nil I st hv hqueue s)

theorem assignedTarget_spec (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) :
    st.assigned s = some (assignedTarget I st hv hqueue s) :=
  Classical.choose_spec (exists_assigned_of_queue_nil I st hv hqueue s)

theorem assignedTarget_injective (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) :
    Function.Injective (assignedTarget I st hv hqueue) := by
  intro s₁ s₂ ht
  have hheld₁ := (hv.held_iff_assigned s₁
    (assignedTarget I st hv hqueue s₁)).mpr
      (assignedTarget_spec I st hv hqueue s₁)
  have hheld₂ := (hv.held_iff_assigned s₂
    (assignedTarget I st hv hqueue s₂)).mpr
      (assignedTarget_spec I st hv hqueue s₂)
  rw [ht] at hheld₁
  exact Option.some.inj (hheld₁.symm.trans hheld₂)

/-- The perfect matching encoded by a valid terminal state. -/
noncomputable def matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) : S ≃ T :=
  Equiv.ofBijective (assignedTarget I st hv hqueue)
    ((Fintype.bijective_iff_injective_and_card
      (assignedTarget I st hv hqueue)).2
        ⟨assignedTarget_injective I st hv hqueue, hcard⟩)

@[simp] theorem matchingOfTerminal_apply
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) (s : S) :
    matchingOfTerminal I hcard st hv hqueue s =
      assignedTarget I st hv hqueue s := rfl

theorem assigned_matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) (s : S) :
    st.assigned s = some (matchingOfTerminal I hcard st hv hqueue s) := by
  simpa using assignedTarget_spec I st hv hqueue s

theorem held_iff_matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = [])
    (s : S) (t : T) :
    st.held t = some s ↔ matchingOfTerminal I hcard st hv hqueue s = t := by
  constructor
  · intro hheld
    have hassigned := (hv.held_iff_assigned s t).mp hheld
    have hfinal := assigned_matchingOfTerminal I hcard st hv hqueue s
    exact Option.some.inj (hfinal.symm.trans hassigned)
  · intro hmatch
    apply (hv.held_iff_assigned s t).mpr
    rw [← hmatch]
    exact assigned_matchingOfTerminal I hcard st hv hqueue s

theorem matchingOfTerminal_symm_eq
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = [])
    (s : S) (t : T) (hheld : st.held t = some s) :
    (matchingOfTerminal I hcard st hv hqueue).symm t = s := by
  rw [← (matchingOfTerminal I hcard st hv hqueue).injective.eq_iff]
  simp only [Equiv.apply_symm_apply]
  exact ((held_iff_matchingOfTerminal I hcard st hv hqueue s t).mp hheld).symm

/-- Run Algorithm 6.1 from any complete duplicate-free source order and
extract its perfect matching. -/
noncomputable def deferredAcceptanceMatching
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) : S ≃ T := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  exact matchingOfTerminal I hcard st hv hqueue

end DAState

end GloballyRanked

end TunnellMap

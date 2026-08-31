import TunnellMap.GloballyRanked

/-!
# Strict preference lists from a global edge ranking

At each source, sorting all targets by the global edge key gives the finite
strict preference list consumed by deferred acceptance.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

noncomputable def preferenceList (I : GloballyRanked K S T) (s : S) : List T :=
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  (Finset.univ : Finset T).sort (· ≤ ·)

theorem preferenceList_pairwise (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Pairwise fun t₁ t₂ => I.rank s t₁ ≤ I.rank s t₂ := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.pairwise_sort (Finset.univ : Finset T) (· ≤ ·)

theorem preferenceList_nodup (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Nodup := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.sort_nodup (Finset.univ : Finset T) (· ≤ ·)

@[simp] theorem mem_preferenceList (I : GloballyRanked K S T) (s : S) (t : T) :
    t ∈ I.preferenceList s := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : t ∈ (Finset.univ : Finset T).sort (α := T) (· ≤ ·) := by
    simp
  exact h

@[simp] theorem length_preferenceList (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).length = Fintype.card T := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : ((Finset.univ : Finset T).sort (α := T) (· ≤ ·)).length = Fintype.card T := by
    simp
  exact h

/-- Incident keys occur in strictly increasing order in the generated
preference list. -/
theorem preferenceList_strict (I : GloballyRanked K S T) (s : S)
    {i j : Fin (I.preferenceList s).length} (hij : i < j) :
    I.rank s ((I.preferenceList s).get i) <
      I.rank s ((I.preferenceList s).get j) := by
  have hle := (I.preferenceList_pairwise s).rel_get_of_lt hij
  have htne : (I.preferenceList s).get i ≠ (I.preferenceList s).get j := by
    intro h
    exact (ne_of_lt hij) ((I.preferenceList_nodup s).injective_get h)
  apply lt_of_le_of_ne hle
  intro hrank
  exact htne (I.source_injective s hrank)

end GloballyRanked

end TunnellMap

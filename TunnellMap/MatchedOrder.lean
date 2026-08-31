import TunnellMap.ParkingTotal
import Mathlib.Data.List.NodupEquivFin

/-!
# Ordering sources by their matched-edge keys

The parking theorem orders sources by nondecreasing key of their final
matched edge.  This file constructs that enumeration for every finite
globally ranked matching and removes the ordering parameter from the total
proposal bound.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

noncomputable def matchedSourceList (I : GloballyRanked K S T) (M : S ≃ T) : List S := by
  classical
  exact (Finset.univ : Finset S).toList.mergeSort fun s₁ s₂ =>
    I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂)

theorem matchedSourceList_pairwise (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).Pairwise fun s₁ s₂ =>
      I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂) := by
  classical
  let r : S → S → Prop := fun s₁ s₂ =>
    I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂)
  letI : Std.Total r := ⟨fun s₁ s₂ => le_total _ _⟩
  letI : IsTrans S r := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  simpa [matchedSourceList, r] using
    (List.pairwise_mergeSort' r (Finset.univ : Finset S).toList)

theorem matchedSourceList_nodup (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).Nodup := by
  classical
  unfold matchedSourceList
  exact (Finset.univ : Finset S).nodup_toList.mergeSort

@[simp] theorem mem_matchedSourceList (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : s ∈ I.matchedSourceList M := by
  classical
  simp [matchedSourceList]

@[simp] theorem length_matchedSourceList (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).length = Fintype.card S := by
  classical
  simp [matchedSourceList]

noncomputable def matchedKeyOrderEquiv (I : GloballyRanked K S T) (M : S ≃ T) :
    Fin (Fintype.card S) ≃ S := by
  classical
  let l := I.matchedSourceList M
  let cast : Fin (Fintype.card S) ≃ Fin l.length :=
    finCongr (I.length_matchedSourceList M).symm
  let get : Fin l.length ≃ S :=
    (I.matchedSourceList_nodup M).getEquivOfForallMemList l
      (I.mem_matchedSourceList M)
  exact cast.trans get

theorem matchedKeyOrderEquiv_spec (I : GloballyRanked K S T) (M : S ≃ T) :
    I.MatchedKeyOrder M (I.matchedKeyOrderEquiv M) := by
  classical
  intro i j hkey
  let l := I.matchedSourceList M
  let cast : Fin (Fintype.card S) ≃ Fin l.length :=
    finCongr (I.length_matchedSourceList M).symm
  have horderApply (k : Fin (Fintype.card S)) :
      I.matchedKeyOrderEquiv M k = l.get (cast k) := rfl
  by_contra hij
  have hji : j ≤ i := le_of_not_gt hij
  rcases hji.eq_or_lt with hEq | hlt
  · subst j
    exact (lt_irrefl _ hkey)
  · have hcast : cast j < cast i := by
      simpa [cast] using hlt
    have hle := (I.matchedSourceList_pairwise M).rel_get_of_lt hcast
    rw [horderApply, horderApply] at hkey
    exact (not_lt_of_ge hle) hkey

/-- The parameter-free triangular proposal bound of Theorem 7.1. -/
theorem proposalCount_total_le_triangular (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 :=
  I.proposalCount_total_le M hM (I.matchedKeyOrderEquiv M)
    (I.matchedKeyOrderEquiv_spec M)

end GloballyRanked

end TunnellMap

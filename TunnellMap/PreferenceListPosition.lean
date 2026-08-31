import TunnellMap.PreferenceList
import TunnellMap.Parking

/-!
# Preference-list positions and proposal counts

The proposal count of a source is the one-based position of its final partner
in the source's strict preference list.  This file proves that equivalence
from the global-rank injectivity hypotheses.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

/-- The unique position of a target in a source's complete preference list. -/
noncomputable def preferenceIndex (I : GloballyRanked K S T)
    (s : S) (t : T) : Fin (I.preferenceList s).length :=
  Classical.choose (List.get_of_mem (I.mem_preferenceList s t))

@[simp] theorem get_preferenceIndex (I : GloballyRanked K S T)
    (s : S) (t : T) :
    (I.preferenceList s).get (I.preferenceIndex s t) = t :=
  Classical.choose_spec (List.get_of_mem (I.mem_preferenceList s t))

theorem preferenceIndex_injective (I : GloballyRanked K S T) (s : S) :
    Function.Injective (I.preferenceIndex s) := by
  intro t₁ t₂ h
  have hget := congrArg (fun i => (I.preferenceList s).get i) h
  calc
    t₁ = (I.preferenceList s).get (I.preferenceIndex s t₁) :=
      (I.get_preferenceIndex s t₁).symm
    _ = (I.preferenceList s).get (I.preferenceIndex s t₂) := hget
    _ = t₂ := I.get_preferenceIndex s t₂

/-- Strict key order is exactly strict position order in a preference list. -/
theorem preferenceIndex_lt_iff_rank_lt (I : GloballyRanked K S T)
    (s : S) (t u : T) :
    I.preferenceIndex s t < I.preferenceIndex s u ↔
      I.rank s t < I.rank s u := by
  constructor
  · intro hidx
    have hstrict := I.preferenceList_strict s hidx
    rw [I.get_preferenceIndex s t, I.get_preferenceIndex s u] at hstrict
    exact hstrict
  · intro hrank
    by_contra hnot
    have hui : I.preferenceIndex s u ≤ I.preferenceIndex s t :=
      le_of_not_gt hnot
    rcases hui.eq_or_lt with heq | hlt
    · have htu : t = u := I.preferenceIndex_injective s heq.symm
      subst u
      exact (lt_irrefl _ hrank).elim
    · have hreverse := I.preferenceList_strict s hlt
      rw [I.get_preferenceIndex s u, I.get_preferenceIndex s t] at hreverse
      have : I.rank s u < I.rank s t := hreverse
      exact (not_lt_of_ge hrank.le) this

/-- The number of preferred targets is the zero-based position of the final
target. -/
theorem preferredTargets_card_eq_preferenceIndex
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    (I.preferredTargets M s).card = (I.preferenceIndex s (M s)).1 := by
  let i := I.preferenceIndex s (M s)
  let f : {t // t ∈ I.preferredTargets M s} → Fin i.1 := fun t =>
    ⟨(I.preferenceIndex s t.1).1, by
      have hrank : I.rank s t.1 < I.rank s (M s) := by
        simpa [preferredTargets] using (Finset.mem_filter.mp t.2).2
      exact (I.preferenceIndex_lt_iff_rank_lt s t.1 (M s)).2 hrank⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    have hval : (I.preferenceIndex s t₁.1).1 =
        (I.preferenceIndex s t₂.1).1 := by
      simpa [f] using congrArg Fin.val h
    apply Subtype.ext
    apply I.preferenceIndex_injective s
    apply Fin.ext
    exact hval
  let g : Fin i.1 → {t // t ∈ I.preferredTargets M s} := fun j =>
    ⟨(I.preferenceList s).get
        ⟨j.1, lt_trans j.2 i.2⟩, by
      simp only [preferredTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      have hstrict := I.preferenceList_strict s
        (i := ⟨j.1, lt_trans j.2 i.2⟩) (j := i) j.2
      rw [I.get_preferenceIndex s (M s)] at hstrict
      exact hstrict⟩
  have hg : Function.Injective g := by
    intro j₁ j₂ h
    have hind := (I.preferenceList_nodup s).injective_get
      (congrArg Subtype.val h)
    apply Fin.ext
    exact congrArg
      (fun k : Fin (I.preferenceList s).length => k.1) hind
  have hle : (I.preferredTargets M s).card ≤ i.1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hge : i.1 ≤ (I.preferredTargets M s).card := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective g hg
  exact Nat.le_antisymm hle hge

/-- The manuscript's equivalence between actual proposal count and one-based
preference-list position. -/
theorem proposalCount_eq_preferenceIndex_add_one
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    I.proposalCount M s = (I.preferenceIndex s (M s)).1 + 1 := by
  rw [proposalCount, I.preferredTargets_card_eq_preferenceIndex M s]

end GloballyRanked

end TunnellMap

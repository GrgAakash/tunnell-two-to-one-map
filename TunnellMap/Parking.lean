import TunnellMap.GloballyRankedExistence

/-!
# Proposal counts for globally ranked stable matchings

This file formalizes the injection at the heart of Theorem 7.1.  A target
preferred by a source to its stable partner is matched along an edge of
strictly smaller global key.  Consequently the number of proposals made by
that source is bounded by one plus the number of earlier matched edges.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

def preferredTargets (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : Finset T :=
  Finset.univ.filter fun t => I.rank s t < I.rank s (M s)

def earlierMatchedSources (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    Finset S :=
  Finset.univ.filter fun s' => I.rank s' (M s') < I.rank s (M s)

/-- The number of proposals made by a source whose final partner is `M s`:
all strictly preferred targets, followed by its final target. -/
def proposalCount (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : ℕ :=
  (I.preferredTargets M s).card + 1

omit [Fintype S] [DecidableEq S] [DecidableEq T] in
theorem preferred_target_has_earlier_match (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) (t : T)
    (ht : t ∈ I.preferredTargets M s) :
    I.rank (M.symm t) t < I.rank s (M s) := by
  have hpreferred : I.rank s t < I.rank s (M s) := by
    simpa [preferredTargets] using (Finset.mem_filter.mp ht).2
  have hmatched_le : I.rank (M.symm t) t ≤ I.rank s t := by
    apply le_of_not_gt
    intro hedge_lt
    exact hM s t ⟨hpreferred, hedge_lt⟩
  exact lt_of_le_of_lt hmatched_le hpreferred

noncomputable def preferredToEarlier (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    {t // t ∈ I.preferredTargets M s} → {s' // s' ∈ I.earlierMatchedSources M s} :=
  fun t => ⟨M.symm t.1, by
    simp only [earlierMatchedSources, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using I.preferred_target_has_earlier_match M hM s t.1 t.2⟩

omit [DecidableEq S] [DecidableEq T] in
theorem preferredToEarlier_injective (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    Function.Injective (I.preferredToEarlier M hM s) := by
  intro t₁ t₂ h
  apply Subtype.ext
  exact M.symm.injective (congrArg Subtype.val h)

omit [DecidableEq S] [DecidableEq T] in
/-- The pointwise estimate used in the parking-function proof. -/
theorem proposalCount_le_earlier_add_one (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    I.proposalCount M s ≤ (I.earlierMatchedSources M s).card + 1 := by
  have hcard : (I.preferredTargets M s).card ≤
      (I.earlierMatchedSources M s).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective (I.preferredToEarlier M hM s)
        (I.preferredToEarlier_injective M hM s)
  exact Nat.add_le_add_right hcard 1

/-- An enumeration is ordered by final edge key when every strict key
inequality points forward in the enumeration.  Ties may be broken arbitrarily. -/
def MatchedKeyOrder (I : GloballyRanked K S T) (M : S ≃ T)
    (order : Fin (Fintype.card S) ≃ S) : Prop :=
  ∀ i j,
    I.rank (order i) (M (order i)) < I.rank (order j) (M (order j)) → i < j

omit [Fintype T] [DecidableEq S] [DecidableEq T] in
theorem earlierMatchedSources_card_le_position (I : GloballyRanked K S T)
    (M : S ≃ T) (order : Fin (Fintype.card S) ≃ S)
    (horder : I.MatchedKeyOrder M order) (i : Fin (Fintype.card S)) :
    (I.earlierMatchedSources M (order i)).card ≤ i.1 := by
  let f : {s' // s' ∈ I.earlierMatchedSources M (order i)} → Fin i.1 :=
    fun s' => ⟨(order.symm s'.1).1, by
      apply horder (order.symm s'.1) i
      have hkey := (Finset.mem_filter.mp s'.2).2
      simpa only [Equiv.apply_symm_apply] using hkey⟩
  have hf : Function.Injective f := by
    intro s₁ s₂ h
    apply Subtype.ext
    apply order.symm.injective
    apply Fin.ext
    simpa [f] using congrArg Fin.val h
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

omit [DecidableEq S] [DecidableEq T] in
/-- The indexed form of Theorem 7.1, with zero-based indices. -/
theorem proposalCount_le_position (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order)
    (i : Fin (Fintype.card S)) :
    I.proposalCount M (order i) ≤ i.1 + 1 := by
  exact (I.proposalCount_le_earlier_add_one M hM (order i)).trans
    (Nat.add_le_add_right (I.earlierMatchedSources_card_le_position M order horder i) 1)

end GloballyRanked

end TunnellMap

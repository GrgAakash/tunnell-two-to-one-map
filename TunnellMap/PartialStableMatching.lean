import TunnellMap.GloballyRankedExistence

/-!
# Stable partial matchings are perfect

The manuscript allows a stable matching to leave vertices unmatched, with an
unmatched vertex ranking every available partner above being unmatched.  The
core `GloballyRanked` development represents a perfect matching by an `Equiv`.
This file closes that small interface gap using Mathlib's standard
`PartialEquiv`: on finite sides of equal cardinality, a stable partial matching
in the complete bipartite graph has no unmatched vertices.  Consequently the
unique stable perfect matching is also the unique stable partial matching.
-/

namespace TunnellMap
namespace GloballyRanked

variable {K S T : Type*}

/-- An edge blocks a partial matching when both endpoints prefer one another
to their current partners.  An unmatched endpoint prefers every partner. -/
def PartialBlocks [LT K] (I : GloballyRanked K S T) (M : PartialEquiv S T)
    (s : S) (t : T) : Prop :=
  (s ∉ M.source ∨ I.rank s t < I.rank s (M s)) ∧
    (t ∉ M.target ∨ I.rank s t < I.rank (M.symm t) t)

/-- Stability for a possibly nonperfect matching. -/
def PartialStable [LT K] (I : GloballyRanked K S T)
    (M : PartialEquiv S T) : Prop :=
  ∀ s t, ¬ I.PartialBlocks M s t

/-- A partial equivalence whose source and target are universal is an
ordinary equivalence. -/
def partialEquivToEquiv (M : PartialEquiv S T)
    (hsource : M.source = Set.univ) (htarget : M.target = Set.univ) : S ≃ T where
  toFun := M
  invFun := M.symm
  left_inv s := M.left_inv (by rw [hsource]; trivial)
  right_inv t := M.right_inv (by rw [htarget]; trivial)

/-- A stable perfect matching is stable when regarded as a partial matching. -/
theorem stable_to_partialStable [LT K] (I : GloballyRanked K S T) (M : S ≃ T)
    (hM : I.Stable M) : I.PartialStable M.toPartialEquiv := by
  intro s t hblock
  apply hM s t
  simpa [PartialBlocks] using hblock

/-- On finite sides of equal size, stability forces a partial matching to be
perfect.  Completeness of the bipartite graph is encoded by the fact that
`PartialBlocks` tests every pair `s, t`. -/
theorem partialStable_isPerfect [LT K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M : PartialEquiv S T) (hM : I.PartialStable M) :
    M.source = Set.univ ∧ M.target = Set.univ := by
  classical
  have hsource : M.source = Set.univ := by
    by_contra hne
    have hs_exists : ∃ s : S, s ∉ M.source := by
      simpa [Set.eq_univ_iff_forall] using hne
    obtain ⟨s, hs⟩ := hs_exists
    have hsource_lt : Fintype.card M.source < Fintype.card S :=
      Fintype.card_subtype_lt hs
    have hmatched_card : Fintype.card M.source = Fintype.card M.target :=
      Fintype.card_congr M.toEquiv
    have htarget_lt : Fintype.card M.target < Fintype.card T := by
      omega
    have htarget_ne : M.target ≠ Set.univ := by
      intro htarget
      have htarget_card : Fintype.card M.target = Fintype.card T :=
        (set_fintype_card_eq_univ_iff M.target).2 htarget
      omega
    have ht_exists : ∃ t : T, t ∉ M.target := by
      simpa [Set.eq_univ_iff_forall] using htarget_ne
    obtain ⟨t, ht⟩ := ht_exists
    exact hM s t ⟨Or.inl hs, Or.inl ht⟩
  have hmatched_card : Fintype.card M.source = Fintype.card M.target :=
    Fintype.card_congr M.toEquiv
  have hsource_card : Fintype.card M.source = Fintype.card S :=
    (set_fintype_card_eq_univ_iff M.source).2 hsource
  have htarget_card : Fintype.card M.target = Fintype.card T := by
    omega
  exact ⟨hsource, (set_fintype_card_eq_univ_iff M.target).1 htarget_card⟩

/-- Once a stable partial matching is known to be perfect, it gives a stable
ordinary equivalence. -/
theorem partialStable_to_stable [LT K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M : PartialEquiv S T) (hM : I.PartialStable M) :
    I.Stable (partialEquivToEquiv M
      (partialStable_isPerfect I hcard M hM).1
      (partialStable_isPerfect I hcard M hM).2) := by
  intro s t hblock
  apply hM s t
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  · simpa [partialEquivToEquiv] using hblock.1
  · simpa [partialEquivToEquiv] using hblock.2

/-- Any two stable partial matchings on finite equal sides coincide. -/
theorem partialStable_unique [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M N : PartialEquiv S T) (hM : I.PartialStable M)
    (hN : I.PartialStable N) : M = N := by
  classical
  let hMp := partialStable_isPerfect I hcard M hM
  let hNp := partialStable_isPerfect I hcard N hN
  let ME := partialEquivToEquiv M hMp.1 hMp.2
  let NE := partialEquivToEquiv N hNp.1 hNp.2
  have hME : I.Stable ME := partialStable_to_stable I hcard M hM
  have hNE : I.Stable NE := partialStable_to_stable I hcard N hN
  have heq : ME = NE := stable_unique I ME NE hME hNE
  apply PartialEquiv.ext
  · intro s
    exact congrArg (fun E : S ≃ T => E s) heq
  · intro t
    exact congrArg (fun E : S ≃ T => E.symm t) heq
  · exact hMp.1.trans hNp.1.symm

/-- Finite globally ranked complete bipartite instances with equal sides have
a unique stable matching even when partial matchings are admitted. -/
theorem existsUnique_partialStable [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃! M : PartialEquiv S T, I.PartialStable M := by
  classical
  obtain ⟨M, hM⟩ := stable_exists I hcard
  refine ⟨M.toPartialEquiv, stable_to_partialStable I M hM, ?_⟩
  intro N hN
  exact partialStable_unique I hcard N M.toPartialEquiv hN
    (stable_to_partialStable I M hM)

end GloballyRanked
end TunnellMap

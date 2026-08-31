import TunnellMap.GloballyRankedExistence
import TunnellMap.Parking

/-!
# Deferred-acceptance correctness contract

The source-proposing algorithm considers every target preceding a source's
final partner, and a target's held key can only decrease.  Its terminal
certificate therefore says that every such proposal is beaten by the final
held edge.  For globally ranked pairs this certificate is equivalent to
stability and hence identifies the unique stable perfect matching.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K]

/-- The transcript-free terminal certificate of source-proposing deferred
acceptance. -/
def DeferredAcceptanceCertificate (I : GloballyRanked K S T) (M : S ≃ T) : Prop :=
  ∀ s t, I.rank s t < I.rank s (M s) →
    I.rank (M.symm t) t < I.rank s t

theorem stable_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) : I.DeferredAcceptanceCertificate M := by
  intro s t hsource
  have htargetLe : I.rank (M.symm t) t ≤ I.rank s t := by
    apply le_of_not_gt
    intro htarget
    exact hM s t ⟨hsource, htarget⟩
  apply lt_of_le_of_ne htargetLe
  intro heq
  have hs : M.symm t = s := I.target_injective t heq
  have ht : t = M s := by
    rw [← hs]
    simp
  rw [ht] at hsource
  exact (lt_irrefl _) hsource

theorem stable_of_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) : I.Stable M := by
  intro s t hblock
  have hfinal := hM s t hblock.1
  exact (not_lt_of_ge hfinal.le) hblock.2

theorem stable_iff_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) :
    I.Stable M ↔ I.DeferredAcceptanceCertificate M :=
  ⟨I.stable_deferredAcceptanceCertificate M,
    I.stable_of_deferredAcceptanceCertificate M⟩

section Finite

variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- The targets to which source-proposing deferred acceptance sends a
proposal: all strictly preferred targets and then the final partner. -/
def proposalTargets (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : Finset T :=
  insert (M s) (I.preferredTargets M s)

@[simp] theorem finalPartner_mem_proposalTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∈ I.proposalTargets M s := by
  simp [proposalTargets]

theorem finalPartner_not_mem_preferredTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∉ I.preferredTargets M s := by
  simp [preferredTargets]

theorem proposalTargets_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) :
    (I.proposalTargets M s).card = I.proposalCount M s := by
  simp [proposalTargets, proposalCount, I.finalPartner_not_mem_preferredTargets M s]

/-- No source proposes twice to one target, and its total number of proposals
is at most the size of the target side. -/
theorem proposalCount_le_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : I.proposalCount M s ≤ Fintype.card T := by
  rw [← I.proposalTargets_card M s, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The elementary `m²` termination bound before the parking improvement. -/
theorem proposalCount_total_le_square (I : GloballyRanked K S T)
    (M : S ≃ T) :
    (∑ s : S, I.proposalCount M s) ≤ Fintype.card S * Fintype.card T := by
  calc
    (∑ s : S, I.proposalCount M s) ≤ ∑ _s : S, Fintype.card T :=
      Finset.sum_le_sum fun s _ => I.proposalCount_le_card M s
    _ = Fintype.card S * Fintype.card T := by simp

/-- Any perfect matching returned with the terminal deferred-acceptance
certificate is the unique stable matching. -/
theorem deferredAcceptance_output_unique (I : GloballyRanked K S T)
    (hcard : Fintype.card S = Fintype.card T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) :
    M = Classical.choose (I.exists_unique_stable hcard) := by
  classical
  exact (Classical.choose_spec (I.exists_unique_stable hcard)).2 M
    (I.stable_of_deferredAcceptanceCertificate M hM)

end Finite

end GloballyRanked

end TunnellMap

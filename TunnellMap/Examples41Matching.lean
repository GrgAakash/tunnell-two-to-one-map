import TunnellMap.Examples41Generator
import TunnellMap.Sharpness

/-!
# The finite matching runs in the worked examples

The `Fin 4` instance below is the manuscript's certified residual key table,
with rows `s1,...,s4` and columns `t1,...,t4`.  It is used to check the
six-proposal deferred-acceptance trace, the final matching, and the parking
function.
-/

namespace TunnellMap
namespace Examples41

open GloballyRanked

set_option maxRecDepth 10000

/-! ## The two-by-two introductory run -/

def rank2 (s t : Fin 2) : ℕ := 2 * t.1 + s.1 + 1

def ranking2 : GloballyRanked ℕ (Fin 2) (Fin 2) where
  rank := rank2
  source_injective := by decide
  target_injective := by decide

def matching2 : Fin 2 ≃ Fin 2 := Equiv.refl (Fin 2)

theorem ranked_two_by_two_matrix :
    ranking2.rank 0 0 = 1 ∧ ranking2.rank 0 1 = 3 ∧
      ranking2.rank 1 0 = 2 ∧ ranking2.rank 1 1 = 4 := by
  decide

theorem ranked_two_by_two_stable : ranking2.Stable matching2 := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    norm_num [GloballyRanked.Blocks, ranking2, rank2, matching2]

theorem ranked_two_by_two_proposal_logic :
    ranking2.rank 0 0 < ranking2.rank 0 1 ∧
      ranking2.rank 1 0 < ranking2.rank 1 1 ∧
      ranking2.rank 0 0 < ranking2.rank 1 0 := by
  decide

/-! ## The four-by-four residual run -/

def residualRank41 : Fin 4 → Fin 4 → DirectionKey :=
  ![![key41 5 1 (-1) (-1), key41 20 1 (-4) (-1),
      key41 5 1 1 (-1), key41 20 1 4 (-1)],
    ![key41 5 1 (-1) 1, key41 20 1 (-4) 1,
      key41 20 1 4 1, key41 5 1 1 1],
    ![key41 20 1 4 (-1), key41 5 1 1 (-1),
      key41 20 1 (-4) (-1), key41 5 1 (-1) (-1)],
    ![key41 20 1 4 1, key41 5 1 1 1,
      key41 5 1 (-1) 1, key41 20 1 (-4) 1]]

def residualRanking41 : GloballyRanked DirectionKey (Fin 4) (Fin 4) where
  rank := residualRank41
  source_injective := by decide
  target_injective := by decide

/-- The pairs are `(s1,t1)`, `(s2,t2)`, `(s3,t4)`, `(s4,t3)`. -/
def residualMatching41 : Fin 4 ≃ Fin 4 := Equiv.swap (2 : Fin 4) (3 : Fin 4)

theorem residual_table_agrees_with_arithmetic :
    residualRanking41.rank 0 0 = representativeEdgeKey s1 t1 ∧
      residualRanking41.rank 0 1 = representativeEdgeKey s1 t2 ∧
      residualRanking41.rank 0 2 = representativeEdgeKey s1 t3 ∧
      residualRanking41.rank 0 3 = representativeEdgeKey s1 t4 ∧
      residualRanking41.rank 1 0 = representativeEdgeKey s2 t1 ∧
      residualRanking41.rank 1 1 = representativeEdgeKey s2 t2 ∧
      residualRanking41.rank 1 2 = representativeEdgeKey s2 t3 ∧
      residualRanking41.rank 1 3 = representativeEdgeKey s2 t4 ∧
      residualRanking41.rank 2 0 = representativeEdgeKey s3 t1 ∧
      residualRanking41.rank 2 1 = representativeEdgeKey s3 t2 ∧
      residualRanking41.rank 2 2 = representativeEdgeKey s3 t3 ∧
      residualRanking41.rank 2 3 = representativeEdgeKey s3 t4 ∧
      residualRanking41.rank 3 0 = representativeEdgeKey s4 t1 ∧
      residualRanking41.rank 3 1 = representativeEdgeKey s4 t2 ∧
      residualRanking41.rank 3 2 = representativeEdgeKey s4 t3 ∧
      residualRanking41.rank 3 3 = representativeEdgeKey s4 t4 := by
  simp [residualRanking41, residualRank41, edgeKey_s1_t2, edgeKey_s1_t3,
    edgeKey_s1_t4, edgeKey_s2_t1, edgeKey_s2_t2, edgeKey_s2_t3,
    edgeKey_s2_t4, edgeKey_s3_t1, edgeKey_s3_t2, edgeKey_s3_t3,
    edgeKey_s3_t4, edgeKey_s4_t1, edgeKey_s4_t2, edgeKey_s4_t3,
    edgeKey_s4_t4, signed_orbit_edge_key, key41]

theorem residual_matching41_stable :
    residualRanking41.Stable residualMatching41 := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    unfold GloballyRanked.Blocks <;>
    decide

def residualProposalTrace41 : List (Fin 4 × Fin 4) :=
  [(0, 0), (1, 0), (2, 3), (3, 2), (1, 3), (1, 1)]

theorem residual_proposal_trace41_value :
    residualProposalTrace41 =
      [(0, 0), (1, 0), (2, 3), (3, 2), (1, 3), (1, 1)] := rfl

/-- Each source proposes in row order, while `t1` retains `s1` over `s2`
and `t4` retains `s3` over `s2`. -/
theorem residual_proposal_trace41_logic :
    residualRank41 0 0 < residualRank41 0 2 ∧
      residualRank41 1 0 < residualRank41 1 3 ∧
      residualRank41 1 3 < residualRank41 1 1 ∧
      residualRank41 2 3 < residualRank41 2 1 ∧
      residualRank41 3 2 < residualRank41 3 1 ∧
      residualRank41 0 0 < residualRank41 1 0 ∧
      residualRank41 2 3 < residualRank41 1 3 := by
  decide

theorem residual_matching41_pairs :
    residualMatching41 0 = 0 ∧ residualMatching41 1 = 1 ∧
      residualMatching41 2 = 3 ∧ residualMatching41 3 = 2 := by
  decide

theorem residual_proposal_counts41 :
    residualRanking41.proposalCount residualMatching41 0 = 1 ∧
      residualRanking41.proposalCount residualMatching41 1 = 3 ∧
      residualRanking41.proposalCount residualMatching41 2 = 1 ∧
      residualRanking41.proposalCount residualMatching41 3 = 1 := by
  decide

/-- Transfer of the parking inequalities along a computed sorted rearrangement. -/
theorem isParkingFunction_of_sortedCounts_eq {a b : List ℕ}
    (hpos : ∀ x ∈ a, 0 < x) (hb : sortedCounts a = b)
    (hbound : ∀ i : Fin b.length, b.get i ≤ i.1 + 1) :
    IsParkingFunction a := by
  refine ⟨hpos, ?_⟩
  subst hb
  exact hbound

theorem sortedCounts_counts41 : sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] := by
  unfold sortedCounts
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (List.pairwise_mergeSort' (· ≤ ·) [1, 3, 1, 1]) (by decide) ?_
  exact (List.mergeSort_perm [1, 3, 1, 1] _).trans (by decide)

theorem parking_rearrangement41 :
    sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] ∧
      IsParkingFunction [1, 3, 1, 1] ∧
      1 + 3 + 1 + 1 = 6 ∧
      6 ≤ 4 * (4 + 1) / 2 := by
  exact ⟨sortedCounts_counts41,
    isParkingFunction_of_sortedCounts_eq (by decide) sortedCounts_counts41 (by decide),
    by norm_num, by norm_num⟩

/-! ## Representative-level signs and the inverse example -/

theorem preferredTarget_s2_t2 : preferredTarget s2 t2 = negAResidual t2 := by
  have hlt : directionKey (minusVector s2 t2) < directionKey (plusVector s2 t2) := by
    change directionKey ⟨2, -8, 2⟩ < directionKey ⟨-6, -2, 2⟩
    rw [show (⟨2, -8, 2⟩ : Triple) = vsmul 2 ⟨1, -4, 1⟩ by rfl,
      directionKey_two_vsmul _ (by norm_num),
      show (⟨-6, -2, 2⟩ : Triple) = vsmul (-2) ⟨3, 1, -1⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num)]
    simp [directionKey, primitiveDirection_x_one,
      primitiveDirection_z_neg_one_of_x_pos, qForm]
    decide
  simp [preferredTarget, not_lt_of_ge hlt.le]

theorem preferredTarget_s3_t4 : preferredTarget s3 t4 = t4 := by
  have hlt : directionKey (plusVector s3 t4) < directionKey (minusVector s3 t4) := by
    change directionKey ⟨-2, 2, 2⟩ < directionKey ⟨-2, 8, -6⟩
    rw [show (⟨-2, 2, 2⟩ : Triple) = vsmul (-2) ⟨1, -1, -1⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num),
      show (⟨-2, 8, -6⟩ : Triple) = vsmul (-2) ⟨1, -4, 3⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num)]
    simp [directionKey, primitiveDirection_x_one, qForm]
    decide
  simp [preferredTarget, hlt]

theorem preferredTarget_s4_t3 : preferredTarget s4 t3 = t3 := by
  have hlt : directionKey (plusVector s4 t3) < directionKey (minusVector s4 t3) := by
    change directionKey ⟨-2, 2, -2⟩ < directionKey ⟨-2, 8, 6⟩
    rw [show (⟨-2, 2, -2⟩ : Triple) = vsmul (-2) ⟨1, -1, 1⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num),
      show (⟨-2, 8, 6⟩ : Triple) = vsmul (-2) ⟨1, -4, -3⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num)]
    simp [directionKey, primitiveDirection_x_one, qForm]
    decide
  simp [preferredTarget, hlt]

theorem lifted_residual_pairs41 :
    residualTargetLift (preferredTarget s1 t1) = ⟨4, 3, 0⟩ ∧
      residualTargetLift (preferredTarget s2 t2) = ⟨4, -3, 0⟩ ∧
      residualTargetLift (preferredTarget s3 t4) = ⟨0, -3, 4⟩ ∧
      residualTargetLift (preferredTarget s4 t3) = ⟨0, -3, -4⟩ := by
  rw [signed_orbit_edge_prefers_negative_target, preferredTarget_s2_t2,
    preferredTarget_s3_t4, preferredTarget_s4_t3]
  norm_num [negAResidual, negA, negTriple, residualTargetLift, aLift,
    t1, t2, t3, t4]

theorem residual_inverse_sign_example :
    negTriple (residualTargetLift t2) = ⟨4, -3, 0⟩ ∧
      negTriple (negTriple (residualSourceLift s2)) = residualSourceLift s2 ∧
      s2.1.1 = ⟨-2, -5, 1⟩ := by
  norm_num [t2, s2, midpointSource, residualTargetLift, residualSourceLift,
    aLift, bLift, negTriple]

/-! ## The `m = 3` sharpness example -/

theorem sharpness_three_sources :
    (sharpRanking 3).proposalCount (sharpMatching 3) (0 : Fin 3) = 1 ∧
      (sharpRanking 3).proposalCount (sharpMatching 3) (1 : Fin 3) = 2 ∧
      (sharpRanking 3).proposalCount (sharpMatching 3) (2 : Fin 3) = 3 ∧
      (∑ i : Fin 3, (sharpRanking 3).proposalCount (sharpMatching 3) i) = 6 := by
  constructor
  · simpa using sharpProposalCount 3 (0 : Fin 3)
  · constructor
    · simpa using sharpProposalCount 3 (1 : Fin 3)
    · constructor
      · simpa using sharpProposalCount 3 (2 : Fin 3)
      · norm_num [sharpProposalCount_total]

end Examples41
end TunnellMap

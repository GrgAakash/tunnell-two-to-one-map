import TunnellMap.ParkingRearrangement

/-!
# Sharpness of the triangular proposal bound

This file formalizes Proposition 7.2.  The complete bipartite instance on two
copies of `Fin m` has edge key `(m + 1) * i + j`.  Its stable matching is the
diagonal, source `i` has proposal count `i + 1`, and the total attains the
triangular upper bound.
-/

namespace TunnellMap

namespace GloballyRanked

/-- The distinct edge label used in the sharpness family. -/
def sharpRank (m : ℕ) (s t : Fin m) : ℕ :=
  (m + 1) * s.1 + t.1

theorem sharpRank_source_injective (m : ℕ) (s : Fin m) :
    Function.Injective (sharpRank m s) := by
  intro t₁ t₂ h
  apply Fin.ext
  exact Nat.add_left_cancel h

theorem sharpRank_target_injective (m : ℕ) (t : Fin m) :
    Function.Injective (fun s => sharpRank m s t) := by
  intro s₁ s₂ h
  apply Fin.ext
  apply mul_left_cancel₀ (by omega : m + 1 ≠ 0)
  exact Nat.add_right_cancel h

/-- The globally ranked complete bipartite instance witnessing sharpness. -/
def sharpRanking (m : ℕ) : GloballyRanked ℕ (Fin m) (Fin m) where
  rank := sharpRank m
  source_injective := sharpRank_source_injective m
  target_injective := sharpRank_target_injective m

/-- Every edge of the sharpness instance has a different global key. -/
theorem sharpRank_pair_injective (m : ℕ) :
    Function.Injective (fun e : Fin m × Fin m =>
      (sharpRanking m).rank e.1 e.2) := by
  intro e₁ e₂ h
  have htval : e₁.2.1 = e₂.2.1 := by
    have hmod := congrArg (fun k : ℕ => k % (m + 1)) h
    simpa [sharpRanking, sharpRank, Nat.add_mod,
      Nat.mod_eq_of_lt (lt_trans e₁.2.2 (Nat.lt_succ_self m)),
      Nat.mod_eq_of_lt (lt_trans e₂.2.2 (Nat.lt_succ_self m))] using hmod
  have ht : e₁.2 = e₂.2 := Fin.ext htval
  have hsval : e₁.1.1 = e₂.1.1 := by
    change (m + 1) * e₁.1.1 + e₁.2.1 =
      (m + 1) * e₂.1.1 + e₂.2.1 at h
    rw [htval] at h
    apply mul_left_cancel₀ (by omega : m + 1 ≠ 0)
    exact Nat.add_right_cancel h
  exact Prod.ext (Fin.ext hsval) ht

/-- The diagonal matching in the sharpness family. -/
def sharpMatching (m : ℕ) : Fin m ≃ Fin m := Equiv.refl (Fin m)

theorem sharpMatching_stable (m : ℕ) :
    (sharpRanking m).Stable (sharpMatching m) := by
  intro s t hblock
  rcases hblock with ⟨hsource, htarget⟩
  have hts : t.1 < s.1 := by
    change (m + 1) * s.1 + t.1 < (m + 1) * s.1 + s.1 at hsource
    exact Nat.lt_of_add_lt_add_left hsource
  have hmul : (m + 1) * s.1 < (m + 1) * t.1 := by
    change (m + 1) * s.1 + t.1 < (m + 1) * t.1 + t.1 at htarget
    exact Nat.lt_of_add_lt_add_right htarget
  have hst : s.1 < t.1 :=
    (Nat.mul_lt_mul_left (by omega : 0 < m + 1)).mp hmul
  exact (Nat.not_lt_of_ge hts.le) hst

/-- Source `i` has exactly `i + 1` proposals in zero-based notation. -/
theorem sharpProposalCount (m : ℕ) (i : Fin m) :
    (sharpRanking m).proposalCount (sharpMatching m) i = i.1 + 1 := by
  unfold proposalCount preferredTargets
  have hfilter :
      (Finset.univ.filter fun t : Fin m =>
        (sharpRanking m).rank i t <
          (sharpRanking m).rank i (sharpMatching m i)) =
        Finset.univ.filter fun t : Fin m => t.1 < i.1 := by
    ext t
    simp [sharpRanking, sharpRank, sharpMatching]
  rw [hfilter, Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.le_of_lt i.2)]

theorem sharpProposalCount_total_mul_two (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) * 2 =
        m * (m + 1) := by
  have hsum : (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) =
      ∑ i : Fin m, (i.1 + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    exact sharpProposalCount m i
  rw [hsum]
  have hfinrange : (∑ i : Fin m, (i.1 + 1)) =
      Finset.sum (Finset.range m) (fun i => i + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hfinrange]
  exact sum_range_add_one_mul_two m

/-- Proposition 7.2: the triangular bound is attained for every size. -/
theorem sharpProposalCount_total (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) =
        m * (m + 1) / 2 := by
  apply Nat.eq_div_of_mul_eq_left (by norm_num : 2 ≠ 0)
  exact sharpProposalCount_total_mul_two m

end GloballyRanked

end TunnellMap

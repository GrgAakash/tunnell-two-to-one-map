import TunnellMap.ComputableCounting
import TunnellMap.Examples41Deterministic

/-!
# `n = 41`, part 1: exhaustive representation data

Every statement of this file is decided by the *kernel* from the arithmetic
enumerations of `TunnellMap.ComputableCounting`,
`TunnellMap.ComputableRoster` and `TunnellMap.ComputableTargetRoster`.  No
`native_decide`, no hand-written table and no oracle is used: the lists are
recomputed by `decide +kernel` from the coordinate bounds and the
kernel-reducible integer square root `isqrtK`.

The results are

* the cardinality balance `|B₄₁| = 2 |A₄₁|`, with `|B₄₁| = 32`, `|A₄₁| = 16`;
* the split of the source enumeration into its even part (16 points), its odd
  *direct* part (8 points) and its odd *residual* part (8 points), each given
  by an explicit literal list;
* the corresponding split of the target enumeration (8 direct, 8 residual);
* `sourceRosterExec 41 = [s1, s2, s3, s4]` and
  `targetRosterExec 41 = [t1, t2, t3, t4]` in canonical order, together with
  the fact that these lists meet every residual orbit exactly once;
* the manuscript's lifted coordinates for the two rosters.
-/

namespace TunnellMap
namespace Examples41

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! ## Cardinalities -/

/-- The 32 representations of `41` by `2x² + y² + 8z²`. -/
theorem card_BRep_41 : Fintype.card (BRep 41) = 32 := by
  rw [card_bRep]
  decide +kernel

/-- The 16 representations of `41` by `2x² + y² + 32z²`. -/
theorem card_ARep_41 : Fintype.card (ARep 41) = 16 := by
  rw [card_aRep]
  decide +kernel

/-- **The cardinality balance at `n = 41`:** `|B₄₁| = 2 |A₄₁|`. -/
theorem balance_41 : Fintype.card (BRep 41) = 2 * Fintype.card (ARep 41) := by
  rw [card_BRep_41, card_ARep_41]

/-! ## The direct and residual subsets -/

/-- The even part of the source enumeration: sixteen points. -/
theorem bEvenTriples_41 :
    bEvenTriples 41 =
      [⟨-4, -3, 0⟩, ⟨-4, 3, 0⟩, ⟨-2, -1, -2⟩, ⟨-2, -1, 2⟩, ⟨-2, 1, -2⟩, ⟨-2, 1, 2⟩,
       ⟨0, -3, -2⟩, ⟨0, -3, 2⟩, ⟨0, 3, -2⟩, ⟨0, 3, 2⟩, ⟨2, -1, -2⟩, ⟨2, -1, 2⟩,
       ⟨2, 1, -2⟩, ⟨2, 1, 2⟩, ⟨4, -3, 0⟩, ⟨4, 3, 0⟩] := by
  decide +kernel

/-- **The direct source subset:** the eight odd-`z` representations that the
quarter-turn branch consumes. -/
theorem bDirectTriples_41 :
    bDirectTriples 41 =
      [⟨-4, -1, -1⟩, ⟨-4, -1, 1⟩, ⟨-4, 1, -1⟩, ⟨-4, 1, 1⟩,
       ⟨4, -1, -1⟩, ⟨4, -1, 1⟩, ⟨4, 1, -1⟩, ⟨4, 1, 1⟩] := by
  decide +kernel

/-- **The residual source subset:** the eight odd-`z` representations left to
the matching, namely `s1, s2, s3, s4` and their four antipodes. -/
theorem bResidualTriples_41 :
    bResidualTriples 41 =
      [⟨-2, -5, -1⟩, ⟨-2, -5, 1⟩, ⟨-2, 5, -1⟩, ⟨-2, 5, 1⟩,
       ⟨2, -5, -1⟩, ⟨2, -5, 1⟩, ⟨2, 5, -1⟩, ⟨2, 5, 1⟩] := by
  decide +kernel

/-- The three parts exhaust the source enumeration. -/
theorem bTriples_41_split :
    (bEvenTriples 41).length + (bDirectTriples 41).length +
      (bResidualTriples 41).length = Fintype.card (BRep 41) := by
  rw [card_BRep_41]
  decide +kernel

/-- **The direct target subset:** the eight targets the quarter-turn branch
occupies. -/
theorem aDirectTriples_41 :
    aDirectTriples 41 =
      [⟨-2, -1, -1⟩, ⟨-2, -1, 1⟩, ⟨-2, 1, -1⟩, ⟨-2, 1, 1⟩,
       ⟨2, -1, -1⟩, ⟨2, -1, 1⟩, ⟨2, 1, -1⟩, ⟨2, 1, 1⟩] := by
  decide +kernel

/-- **The residual target subset:** `t1, t2, t3, t4` and their antipodes. -/
theorem aResidualTriples_41 :
    aResidualTriples 41 =
      [⟨-4, -3, 0⟩, ⟨-4, 3, 0⟩, ⟨0, -3, -1⟩, ⟨0, -3, 1⟩,
       ⟨0, 3, -1⟩, ⟨0, 3, 1⟩, ⟨4, -3, 0⟩, ⟨4, 3, 0⟩] := by
  decide +kernel

/-- The two parts exhaust the target enumeration. -/
theorem aTriples_41_split :
    (aDirectTriples 41).length + (aResidualTriples 41).length =
      Fintype.card (ARep 41) := by
  rw [card_ARep_41]
  decide +kernel

/-! ## The source roster -/

/-- **The executable residual source roster at `n = 41`.**  Recomputed by the
kernel from the arithmetic enumeration, in the manuscript's canonical order. -/
theorem sourceRosterExec_41 : sourceRosterExec 41 = [s1, s2, s3, s4] := by
  decide +kernel

/-- The four roster entries in raw coordinates. -/
theorem sourceRosterExec_41_coords :
    (sourceRosterExec 41).map (fun s => s.1.1) =
      [⟨-2, -5, -1⟩, ⟨-2, -5, 1⟩, ⟨-2, 5, -1⟩, ⟨-2, 5, 1⟩] := by
  decide +kernel

/-- The four roster entries in the manuscript's lifted coordinates. -/
theorem sourceRosterExec_41_lifts :
    (sourceRosterExec 41).map residualSourceLift =
      [⟨-2, -5, -2⟩, ⟨-2, -5, 2⟩, ⟨-2, 5, -2⟩, ⟨-2, 5, 2⟩] := by
  rw [sourceRosterExec_41]
  obtain ⟨h1, h2, h3, h4, -⟩ := residual_lifts
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4]

/-- **Every residual source orbit is represented exactly once** by the four
entries of the roster. -/
theorem sourceRoster_41_orbit_unique (q : (bResidualInvolution 41).Orbit) :
    ∃! x : BResidual 41, x ∈ [s1, s2, s3, s4] ∧
      (bResidualInvolution 41).orbit x = q := by
  have h := sourceRosterExec_orbit_unique (n := 41) q
  rwa [sourceRosterExec_41] at h

/-- The four roster entries are pairwise distinct. -/
theorem sourceRoster_41_nodup : ([s1, s2, s3, s4] : List (BResidual 41)).Nodup := by
  have h := sourceRosterExec_nodup (n := 41)
  rwa [sourceRosterExec_41] at h

/-! ## The target roster -/

/-- **The executable residual target roster at `n = 41`.** -/
theorem targetRosterExec_41 : targetRosterExec 41 = [t1, t2, t3, t4] := by
  decide +kernel

/-- The four target entries in raw coordinates. -/
theorem targetRosterExec_41_coords :
    (targetRosterExec 41).map (fun t => t.1.1) =
      [⟨-4, -3, 0⟩, ⟨-4, 3, 0⟩, ⟨0, -3, -1⟩, ⟨0, -3, 1⟩] := by
  decide +kernel

/-- The four target entries in the manuscript's lifted coordinates. -/
theorem targetRosterExec_41_lifts :
    (targetRosterExec 41).map residualTargetLift =
      [⟨-4, -3, 0⟩, ⟨-4, 3, 0⟩, ⟨0, -3, -4⟩, ⟨0, -3, 4⟩] := by
  rw [targetRosterExec_41]
  obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := residual_lifts
  simp only [List.map_cons, List.map_nil, h1, h2, h3, h4]

/-- **Every residual target orbit is represented exactly once** by the four
entries of the target roster. -/
theorem targetRoster_41_orbit_unique
    (q : (aResidualInvolution 41 (by norm_num)).Orbit) :
    ∃! y : AResidual 41, y ∈ [t1, t2, t3, t4] ∧
      (aResidualInvolution 41 (by norm_num)).orbit y = q := by
  have h := targetRosterExec_orbit_unique (n := 41) (by norm_num) q
  rwa [targetRosterExec_41] at h

/-- The four target entries are pairwise distinct. -/
theorem targetRoster_41_nodup : ([t1, t2, t3, t4] : List (AResidual 41)).Nodup := by
  have h := targetRosterExec_nodup (n := 41)
  rwa [targetRosterExec_41] at h

end Examples41
end TunnellMap

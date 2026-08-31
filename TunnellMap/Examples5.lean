import TunnellMap.FallbackFreeMap
import TunnellMap.ComputableCounting

/-!
# The empty case `n = 5`

`n = 5` is odd, positive and squarefree, and both representation sets are
empty:

* `2x² + y² + 8z² = 5` has no integral solution,
* `2u² + v² + 32w² = 5` has no integral solution,

so the balance `|BRep 5| = 2 |ARep 5|` holds (both sides are `0`).  The
manuscript hypotheses are therefore satisfied, and the theorem must be
instantiable.

The residual target type `AResidual 5` is empty as well, so *no* fallback
residual target exists: an interface demanding one cannot be instantiated
here.  This file is the regression test for the fallback-free interface: the
public map `paperTunnellMapTotal` and the exactly-two theorem are instantiated
at `n = 5` from the manuscript hypotheses alone.  Everything below is checked
by the Lean kernel.
-/

namespace TunnellMap
namespace Examples5

/-- `5` is positive. -/
theorem pos5 : (0 : ℤ) < 5 := by decide

/-- `5` is odd. -/
theorem odd5 : Odd (5 : ℤ) := ⟨2, by ring⟩

/-- `5` is squarefree. -/
theorem squarefree5 : Squarefree (5 : ℤ) :=
  (by norm_num : Prime (5 : ℤ)).squarefree

/-! ## Both representation sets are empty -/

/-- `2x² + y² + 8z² = 5` has no integral solution. -/
theorem isEmpty_bRep5 : IsEmpty (BRep 5) := by
  constructor
  rintro ⟨⟨x, y, z⟩, h⟩
  change 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = 5 at h
  have hx₁ : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x - 1)]
  have hx₂ : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x + 1)]
  have hy₁ : y ≤ 2 := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y - 2)]
  have hy₂ : -2 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y + 2)]
  have hz₁ : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z - 1)]
  have hz₂ : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- `2u² + v² + 32w² = 5` has no integral solution. -/
theorem isEmpty_aRep5 : IsEmpty (ARep 5) := by
  constructor
  rintro ⟨⟨x, y, z⟩, h⟩
  change 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 = 5 at h
  have hx₁ : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x - 1)]
  have hx₂ : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg (x + 1)]
  have hy₁ : y ≤ 2 := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y - 2)]
  have hy₂ : -2 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg (y + 2)]
  have hz₁ : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z - 1)]
  have hz₂ : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

/-- There is no residual target at `n = 5`, so no fallback residual target can
be supplied: an executable interface requiring one cannot be instantiated
here. -/
theorem isEmpty_aResidual5 : IsEmpty (AResidual 5) :=
  ⟨fun t => isEmpty_aRep5.elim t.1⟩

/-- There is no residual source at `n = 5` either. -/
theorem isEmpty_bResidual5 : IsEmpty (BResidual 5) :=
  ⟨fun s => isEmpty_bRep5.elim ⟨s.1.1, s.1.2.1⟩⟩

/-! ## The manuscript hypotheses hold -/

/-- **The Tunnell balance at `n = 5`**: both cardinalities are `0`. -/
theorem balance5 : Nat.card (BRep 5) = 2 * Nat.card (ARep 5) := by
  have h₁ : Nat.card (BRep 5) = 0 := @Nat.card_of_isEmpty _ isEmpty_bRep5
  have h₂ : Nat.card (ARep 5) = 0 := @Nat.card_of_isEmpty _ isEmpty_aRep5
  rw [h₁, h₂]

/-! ## The theorem and the map are instantiated -/

/-- **The public executable map at `n = 5`.**  No fallback residual target is
needed \- and none exists. -/
def tunnellMap5 : BRep 5 → ARep 5 :=
  paperTunnellMapTotal odd5 pos5 squarefree5 balance5

/-- **The exactly-two theorem at `n = 5`**, instantiated from the manuscript
hypotheses alone.  Its content is vacuous because `ARep 5` is empty, which is
precisely the point: the statement and the map are still available. -/
theorem tunnellMap5_exactly_two (a : ARep 5) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      tunnellMap5 p₁ = a ∧
      tunnellMap5 p₂ = a ∧
      ∀ p, tunnellMap5 p = a ↔ p = p₁ ∨ p = p₂ :=
  paperTunnellMapTotal_exactly_two odd5 pos5 squarefree5 balance5 a

/-- The map agrees with `paperTunnellMap` at `n = 5` as well. -/
theorem tunnellMap5_eq (p : BRep 5) :
    tunnellMap5 p =
      paperTunnellMap odd5 pos5 (fintype_balance_of_nat_card balance5) p :=
  paperTunnellMapTotal_eq odd5 pos5 squarefree5 balance5 p


/-! ## Executable regression run in the empty case -/

/-- The source enumeration at `n = 5` is empty. -/
theorem bRepList5_isEmpty : (bRepList 5).isEmpty = true := by decide

/-- The target enumeration at `n = 5` is empty. -/
theorem aRepList5_isEmpty : (aRepList 5).isEmpty = true := by decide

private def runCheck5 (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"n = 5 regression test failed: {name}")

/-- The executable regression suite for the empty case `n = 5`. -/
def runEmptyCaseTests : IO Unit := do
  runCheck5 "the source enumeration is empty" (bRepList 5).isEmpty
  runCheck5 "the target enumeration is empty" (aRepList 5).isEmpty
  runCheck5 "the public map is total on all sources"
    ((bRepList 5).all fun p => decide (tunnellMap5 p = tunnellMap5 p))
  IO.println "fallback-free public map at n = 5 (empty case): all executable tests passed"

#eval runEmptyCaseTests

end Examples5
end TunnellMap

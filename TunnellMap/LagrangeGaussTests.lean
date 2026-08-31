import TunnellMap.KernelGenerator

/-!
# Regression tests for the Lagrange-Gauss conventions

The manuscript fixes two conventions for the reduction step:

* the size-reduction quotient is the **nearest integer**, with exact
  half-integer ties rounded **toward zero**;
* if the two reduced vectors have **equal norm**, the **lexicographically
  smaller** oriented reduced basis is chosen.

This file pins both conventions by regression tests.  Every test is a kernel
proof by `decide` on the real definitions (`nearestQuot`, `lgQuot`,
`lgReduce`); the same checks are gathered at the end into the executable
action `runLagrangeGaussTests`, which raises an error — breaking the build —
as soon as a computed value differs from the expected one.
-/

namespace TunnellMap
namespace LagrangeGaussTests

/-! ## Half-integer ties round toward zero -/

/-- Positive tie `1/2`: the nearest integer toward zero is `0`, not `1`. -/
theorem tie_pos_half : nearestQuot 1 2 = 0 := by decide

/-- Negative tie `-1/2`: the nearest integer toward zero is `0`, not `-1`. -/
theorem tie_neg_half : nearestQuot (-1) 2 = 0 := by decide

/-- Positive tie `3/2`: rounds down to `1`. -/
theorem tie_pos_three_halves : nearestQuot 3 2 = 1 := by decide

/-- Negative tie `-3/2`: rounds up to `-1`. -/
theorem tie_neg_three_halves : nearestQuot (-3) 2 = -1 := by decide

/-- Positive tie `5/2` against a larger denominator: `10 / 4 = 5/2` rounds to
`2`. -/
theorem tie_pos_five_halves : nearestQuot 10 4 = 2 := by decide

/-- Negative tie `-5/2`: rounds to `-2`. -/
theorem tie_neg_five_halves : nearestQuot (-10) 4 = -2 := by decide

/-! ## Non-ties round to the nearer integer, in both signs -/

/-- Positive non-tie `3/5 = 0.6`: rounds up to `1`. -/
theorem nontie_pos_small : nearestQuot 3 5 = 1 := by decide

/-- Positive non-tie `2/5 = 0.4`: rounds down to `0`. -/
theorem nontie_pos_down : nearestQuot 2 5 = 0 := by decide

/-- Positive non-tie `7/5 = 1.4`: rounds down to `1`. -/
theorem nontie_pos_large : nearestQuot 7 5 = 1 := by decide

/-- Negative non-tie `-3/5 = -0.6`: rounds down to `-1`. -/
theorem nontie_neg_small : nearestQuot (-3) 5 = -1 := by decide

/-- Negative non-tie `-2/5 = -0.4`: rounds up to `0`. -/
theorem nontie_neg_up : nearestQuot (-2) 5 = 0 := by decide

/-- Negative non-tie `-7/5 = -1.4`: rounds up to `-1`. -/
theorem nontie_neg_large : nearestQuot (-7) 5 = -1 := by decide

/-! ## The same conventions, read off the vector-level quotient -/

/-- `⟨u,v⟩ / ⟨u,u⟩ = 1/2` for `u = (1,1,0)`, `v = (1,0,0)`: the tie rounds to
`0`, so the size reduction leaves `v` unchanged. -/
theorem lgQuot_tie_pos : lgQuot ⟨1, 1, 0⟩ ⟨1, 0, 0⟩ = 0 := by decide

/-- `⟨u,v⟩ / ⟨u,u⟩ = -1/2` for `u = (1,1,0)`, `v = (-1,0,0)`: the tie rounds to
`0`. -/
theorem lgQuot_tie_neg : lgQuot ⟨1, 1, 0⟩ ⟨-1, 0, 0⟩ = 0 := by decide

/-- A positive non-tie at vector level: `⟨u,v⟩ / ⟨u,u⟩ = 3/5`. -/
theorem lgQuot_nontie_pos : lgQuot ⟨1, 2, 0⟩ ⟨1, 1, 0⟩ = 1 := by decide

/-- A negative non-tie at vector level: `⟨u,v⟩ / ⟨u,u⟩ = -3/5`. -/
theorem lgQuot_nontie_neg : lgQuot ⟨1, 2, 0⟩ ⟨-1, -1, 0⟩ = -1 := by decide

/-- The tie is genuinely visible in the reduction step: with ties toward zero
the reduced vector is `v` itself. -/
theorem lgNext_tie_pos : lgNext ⟨1, 1, 0⟩ ⟨1, 0, 0⟩ = ⟨1, 0, 0⟩ := by decide

/-! ## Equal-norm oriented bases: the lexicographically smaller one is chosen -/

/-- The pair `((1,0,0), (0,1,0))` is already reduced and its two vectors have
equal norm.  The oriented swap `((0,1,0), (-1,0,0))` is lexicographically
smaller, so it is the selected output.  The reduction loop is defined by
well-founded recursion, so the kernel evaluates it through the fuelled mirror
`lgReduceK`, which is proved equal to it. -/
theorem lgReduce_equal_norm :
    lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ = (⟨0, 1, 0⟩, ⟨-1, 0, 0⟩) := by
  rw [← lgReduceK_eq]; decide

/-- The equal-norm selection preserves the cross product, hence the underlying
source vector. -/
theorem lgReduce_equal_norm_cross :
    cross (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩).1 (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩).2 =
      cross ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ := by
  rw [lgReduce_equal_norm]; decide

/-- A second equal-norm case, reached through the reduction loop rather than
immediately: `((2,0,0), (1,1,0))` reduces to a pair of equal-norm vectors, and
the lexicographically smaller oriented basis is returned. -/
theorem lgReduce_equal_norm_loop :
    lgReduce ⟨2, 0, 0⟩ ⟨1, 1, 0⟩ = (⟨1, -1, 0⟩, ⟨1, 1, 0⟩) := by
  rw [← lgReduceK_eq]; decide

/-- The selected output is reduced. -/
theorem lgReduce_equal_norm_reduced :
    IsReducedPair (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩) := by
  rw [lgReduce_equal_norm]
  exact ⟨by decide, by decide⟩

/-! ## The executable form of the same regression suite -/

private def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"Lagrange-Gauss regression test failed: {name}")

/-- The executable Lagrange-Gauss regression suite. -/
def runLagrangeGaussTests : IO Unit := do
  check "positive 1/2 tie rounds toward zero" (nearestQuot 1 2 == 0)
  check "negative -1/2 tie rounds toward zero" (nearestQuot (-1) 2 == 0)
  check "positive 3/2 tie rounds toward zero" (nearestQuot 3 2 == 1)
  check "negative -3/2 tie rounds toward zero" (nearestQuot (-3) 2 == -1)
  check "positive non-tie 0.6" (nearestQuot 3 5 == 1)
  check "positive non-tie 0.4" (nearestQuot 2 5 == 0)
  check "negative non-tie -0.6" (nearestQuot (-3) 5 == -1)
  check "negative non-tie -0.4" (nearestQuot (-2) 5 == 0)
  check "vector-level positive tie" (lgQuot ⟨1, 1, 0⟩ ⟨1, 0, 0⟩ == 0)
  check "vector-level negative tie" (lgQuot ⟨1, 1, 0⟩ ⟨-1, 0, 0⟩ == 0)
  check "vector-level positive non-tie" (lgQuot ⟨1, 2, 0⟩ ⟨1, 1, 0⟩ == 1)
  check "vector-level negative non-tie" (lgQuot ⟨1, 2, 0⟩ ⟨-1, -1, 0⟩ == -1)
  check "equal-norm lexicographic selection"
    (decide (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ = (⟨0, 1, 0⟩, ⟨-1, 0, 0⟩)))
  check "equal-norm selection preserves the cross product"
    (decide (cross (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩).1
        (lgReduce ⟨1, 0, 0⟩ ⟨0, 1, 0⟩).2 = cross ⟨1, 0, 0⟩ ⟨0, 1, 0⟩))
  check "equal-norm case reached through the loop"
    (decide (lgReduce ⟨2, 0, 0⟩ ⟨1, 1, 0⟩ = (⟨1, -1, 0⟩, ⟨1, 1, 0⟩)))
  IO.println "Lagrange-Gauss conventions: all regression tests passed"

#eval runLagrangeGaussTests

end LagrangeGaussTests
end TunnellMap

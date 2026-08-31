import TunnellMap.N41Fibres
import TunnellMap.FallbackFreeMap

/-!
# `n = 41` for the fallback-free public map

The complete `n = 41` certificate of `TunnellMap.N41Fibres` is stated for the
fallback version `paperTunnellMapExec … t1`.  This file transports it to the
public fallback-free map `paperTunnellMapTotal`, which takes only the
manuscript hypotheses: the two maps agree pointwise, so the exactly-two
theorem and both literal fibres hold verbatim for the public map.

The transported facts are kernel-checked, exactly as the originals: they are
rewritten along `paperTunnellMapTotal_eq_exec` and then closed by the existing
kernel evaluations.  The file ends with an executable regression run of the
public map on the four residual sources and on the two displayed fibres.
-/

namespace TunnellMap
namespace Examples41

open RecordDA

/-- The `Nat.card` form of the `n = 41` balance, as the public map states
it. -/
theorem natBalance_41 : Nat.card (BRep 41) = 2 * Nat.card (ARep 41) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact balance_41

/-- **The public fallback-free map at `n = 41`.** -/
def tunnellMapTotal41 : BRep 41 → ARep 41 :=
  paperTunnellMapTotal odd41 pos41 squarefree41 natBalance_41

/-- The public map agrees with the fallback version used by the `n = 41`
certificate. -/
theorem tunnellMapTotal41_eq (p : BRep 41) :
    tunnellMapTotal41 p = paperTunnellMapExec pos41 squarefree41 t1 p :=
  paperTunnellMapTotal_eq_exec odd41 pos41 squarefree41 natBalance_41 t1 p

/-- **Exactly two preimages at `n = 41`, without a fallback.** -/
theorem tunnellMapTotal41_exactly_two (a : ARep 41) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      tunnellMapTotal41 p₁ = a ∧
      tunnellMapTotal41 p₂ = a ∧
      ∀ p, tunnellMapTotal41 p = a ↔ p = p₁ ∨ p = p₂ :=
  paperTunnellMapTotal_exactly_two odd41 pos41 squarefree41 natBalance_41 a

/-- **The complete direct fibre of the public map.**
`Φ₄₁⁻¹(2,-1,1) = {(2,-1,2), (-4,-1,1)}`. -/
theorem tunnellMapTotal41_fibre_direct (p : BRep 41) :
    tunnellMapTotal41 p = targetDirect41 ↔
      p = sourceDirect41a ∨ p = sourceDirect41b := by
  rw [tunnellMapTotal41_eq]
  exact fibre_direct_41 p

/-- **The complete residual fibre of the public map.**
`Φ₄₁⁻¹(4,-3,0) = {(4,-3,0), (-2,-5,1)}`. -/
theorem tunnellMapTotal41_fibre_residual (p : BRep 41) :
    tunnellMapTotal41 p = targetResidual41 ↔
      p = sourceResidual41a ∨ p = sourceResidual41b := by
  rw [tunnellMapTotal41_eq]
  exact fibre_residual_41 p

/-- The direct fibre of the public map, as a literal set equality. -/
theorem tunnellMapTotal41_fibre_direct_set :
    {p : BRep 41 | tunnellMapTotal41 p = targetDirect41} =
      {sourceDirect41a, sourceDirect41b} := by
  ext p
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
    tunnellMapTotal41_fibre_direct p

/-- The residual fibre of the public map, as a literal set equality. -/
theorem tunnellMapTotal41_fibre_residual_set :
    {p : BRep 41 | tunnellMapTotal41 p = targetResidual41} =
      {sourceResidual41a, sourceResidual41b} := by
  ext p
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
    tunnellMapTotal41_fibre_residual p

/-! ## Executable regression run of the public map -/

/-- The executable regression suite for the public fallback-free map at
`n = 41`. -/
def runTotalMapTests : IO Unit := do
  runCheck "public map on the first residual source"
    (decide (tunnellMapTotal41 sourceResidual41a = targetResidual41))
  runCheck "public map on the second residual source"
    (decide (tunnellMapTotal41 sourceResidual41b = targetResidual41))
  runCheck "public map on the first direct source"
    (decide (tunnellMapTotal41 sourceDirect41a = targetDirect41))
  runCheck "public map on the second direct source"
    (decide (tunnellMapTotal41 sourceDirect41b = targetDirect41))
  runCheck "public map agrees with the fallback version on all 32 sources"
    ((bRepList 41).all fun p =>
      decide (tunnellMapTotal41 p = paperTunnellMapExec pos41 squarefree41 t1 p))
  IO.println "fallback-free public map at n = 41: all executable tests passed"

#eval runTotalMapTests

end Examples41
end TunnellMap

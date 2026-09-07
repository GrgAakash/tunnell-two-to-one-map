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

/-! ## Complete sixteen-row fibre table

The rows below are in the same order as the companion table: the eight direct
targets first, followed by the eight residual targets.  Each row is
`(target, even preimage, odd preimage)` in the original Tunnell coordinates.
-/

/-- The literal sixteen-row fibre table printed in the companion note. -/
def completeFibreTable41 : List (Triple × Triple × Triple) :=
  [ (⟨-2, -1, -1⟩, ⟨-2, -1, -2⟩, ⟨4, -1, -1⟩),
    (⟨-2, -1,  1⟩, ⟨-2, -1,  2⟩, ⟨-4, -1, -1⟩),
    (⟨-2,  1, -1⟩, ⟨-2,  1, -2⟩, ⟨4, 1, -1⟩),
    (⟨-2,  1,  1⟩, ⟨-2,  1,  2⟩, ⟨-4, 1, -1⟩),
    (⟨ 2, -1, -1⟩, ⟨ 2, -1, -2⟩, ⟨4, -1, 1⟩),
    (⟨ 2, -1,  1⟩, ⟨ 2, -1,  2⟩, ⟨-4, -1, 1⟩),
    (⟨ 2,  1, -1⟩, ⟨ 2,  1, -2⟩, ⟨4, 1, 1⟩),
    (⟨ 2,  1,  1⟩, ⟨ 2,  1,  2⟩, ⟨-4, 1, 1⟩),
    (⟨-4, -3, 0⟩, ⟨-4, -3, 0⟩, ⟨2, 5, 1⟩),
    (⟨-4,  3, 0⟩, ⟨-4,  3, 0⟩, ⟨2, 5, -1⟩),
    (⟨0, -3, -1⟩, ⟨0, -3, -2⟩, ⟨-2, 5, 1⟩),
    (⟨0, -3,  1⟩, ⟨0, -3,  2⟩, ⟨-2, 5, -1⟩),
    (⟨0,  3, -1⟩, ⟨0,  3, -2⟩, ⟨2, -5, 1⟩),
    (⟨0,  3,  1⟩, ⟨0,  3,  2⟩, ⟨2, -5, -1⟩),
    (⟨4, -3, 0⟩, ⟨4, -3, 0⟩, ⟨-2, -5, 1⟩),
    (⟨4,  3, 0⟩, ⟨4,  3, 0⟩, ⟨-2, -5, -1⟩) ]

/-- Flatten the fibre table to the thirty-two graph edges
`(source, target)`. -/
def completeFibreTableEdges41 : List (Triple × Triple) :=
  completeFibreTable41.flatMap fun row =>
    [(row.2.1, row.1), (row.2.2, row.1)]

/-- The target column of the printed fibre table. -/
def completeFibreTableTargets41 : List Triple :=
  completeFibreTable41.map Prod.fst

/-- The sixteen target rows are exactly the exhaustive `A_41` roster. -/
theorem completeFibreTable41_targets :
    completeFibreTableTargets41.Perm ((aRepList 41).map Subtype.val) := by
  decide +kernel

/-- The graph of the kernel-reducible executable map on the exhaustive source
roster. -/
def executableMapGraphK41 : List (Triple × Triple) :=
  (bRepList 41).map fun p =>
    (p.1, (paperTunnellMapExecK pos41 squarefree41 t1 8 p).1)

/-- Kernel computation certifies that the executable map graph is exactly the
thirty-two edges obtained by flattening the printed sixteen-row table. -/
theorem executableMapGraphK41_complete_table :
    executableMapGraphK41.Perm completeFibreTableEdges41 := by
  decide +kernel

/-- The graph of the public fallback-free map on the exhaustive source
roster. -/
def publicMapGraph41 : List (Triple × Triple) :=
  (bRepList 41).map fun p => (p.1, (tunnellMapTotal41 p).1)

/-- **Complete `n = 41` fibre-table certificate.**  The literal sixteen rows
in `completeFibreTable41` give the entire graph of the public map: all thirty-two
sources occur, and each row records its target's even and odd preimages. -/
theorem completeFibreTable41_certificate :
    publicMapGraph41.Perm completeFibreTableEdges41 := by
  have hfun :
      (fun p : BRep 41 => (p.1, (tunnellMapTotal41 p).1)) =
        (fun p : BRep 41 =>
          (p.1, (paperTunnellMapExecK pos41 squarefree41 t1 8 p).1)) := by
    funext p
    congr 1
    rw [tunnellMapTotal41_eq,
      ← paperTunnellMapExecK_eq (by norm_num) pos41 squarefree41 t1 8
        fuelSuffices_41]
  rw [publicMapGraph41, hfun]
  exact executableMapGraphK41_complete_table

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
  runCheck "complete sixteen-row fibre table"
    (decide (publicMapGraph41.Perm completeFibreTableEdges41))
  runCheck "sixteen table targets exhaust A_41"
    (decide (completeFibreTableTargets41.Perm ((aRepList 41).map Subtype.val)))
  IO.println "fallback-free public map at n = 41: all executable tests passed"

#eval runTotalMapTests

end Examples41
end TunnellMap

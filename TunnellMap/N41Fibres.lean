import TunnellMap.N41Matching

/-!
# `n = 41`, part 5: the complete fibres of the assembled executable map

`paperTunnellMapExec` is the assembled executable map of the paper's balanced
construction theorem: the even branch, the direct quarter-turn branch and the residual
generator/deferred-acceptance branch.  This file instantiates it at `n = 41`,
with the cardinality balance supplied by `Examples41.balance_41`, and computes
two complete fibres.

The fibre theorems are *equalities of fibres*: for every one of the 32
representations `p` of `41` by `2x² + y² + 8z²` — enumerated exhaustively by
`bRepList 41` — the value `paperTunnellMapExec … p` is compared with the
target, so no additional preimage can exist.
-/

namespace TunnellMap
namespace Examples41

open RecordDA

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## Exactly two preimages at `n = 41` -/

/-- **Exactly two preimages at `n = 41`.**  The assembled executable map is
two-to-one on the representations of `41`. -/
theorem paperTunnellMapExec_41_exactly_two (a : ARep 41) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapExec pos41 squarefree41 t1 p₁ = a ∧
      paperTunnellMapExec pos41 squarefree41 t1 p₂ = a ∧
      ∀ p, paperTunnellMapExec pos41 squarefree41 t1 p = a ↔ p = p₁ ∨ p = p₂ :=
  paperTunnellMapExec_exactly_two odd41 pos41 squarefree41 balance_41 t1 a

/-! ## The two displayed fibres -/

/-- The manuscript's direct target `(2, -1, 1)`. -/
def targetDirect41 : ARep 41 := ⟨⟨2, -1, 1⟩, by norm_num [aForm]⟩

/-- The first preimage of `(2, -1, 1)`. -/
def sourceDirect41a : BRep 41 := ⟨⟨2, -1, 2⟩, by norm_num [bForm]⟩

/-- The second preimage of `(2, -1, 1)`. -/
def sourceDirect41b : BRep 41 := ⟨⟨-4, -1, 1⟩, by norm_num [bForm]⟩

/-- The manuscript's residual target `(4, -3, 0)`. -/
def targetResidual41 : ARep 41 := ⟨⟨4, -3, 0⟩, by norm_num [aForm]⟩

/-- The first preimage of `(4, -3, 0)`. -/
def sourceResidual41a : BRep 41 := ⟨⟨4, -3, 0⟩, by norm_num [bForm]⟩

/-- The second preimage of `(4, -3, 0)`. -/
def sourceResidual41b : BRep 41 := ⟨⟨-2, -5, 1⟩, by norm_num [bForm]⟩

/-- The Boolean fibre test used for the exhaustive check. -/
def fibreCheck41 (p : BRep 41) : Bool :=
  (decide (paperTunnellMapExecK pos41 squarefree41 t1 8 p = targetDirect41) ==
      (decide (p = sourceDirect41a) || decide (p = sourceDirect41b))) &&
    (decide (paperTunnellMapExecK pos41 squarefree41 t1 8 p = targetResidual41) ==
      (decide (p = sourceResidual41a) || decide (p = sourceResidual41b)))

/-- **The exhaustive check.**  Over the complete enumeration of the 32
representations of `41`, the two displayed fibres are exactly the displayed
pairs. -/
theorem fibreCheck41_all : (bRepList 41).all fibreCheck41 = true := by
  decide +kernel

theorem fibreCheck41_holds (p : BRep 41) : fibreCheck41 p = true :=
  List.all_eq_true.mp fibreCheck41_all p (mem_bRepList p)

/-- **The complete direct fibre.**
`paperTunnellMapExec₄₁⁻¹(2,-1,1) = {(2,-1,2), (-4,-1,1)}`. -/
theorem fibre_direct_41 (p : BRep 41) :
    paperTunnellMapExec pos41 squarefree41 t1 p = targetDirect41 ↔
      p = sourceDirect41a ∨ p = sourceDirect41b := by
  rw [← paperTunnellMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41]
  have h := fibreCheck41_holds p
  simp only [fibreCheck41, Bool.and_eq_true, beq_iff_eq, ← Bool.decide_or,
    decide_eq_decide] at h
  exact h.1

/-- **The complete residual fibre.**
`paperTunnellMapExec₄₁⁻¹(4,-3,0) = {(4,-3,0), (-2,-5,1)}`. -/
theorem fibre_residual_41 (p : BRep 41) :
    paperTunnellMapExec pos41 squarefree41 t1 p = targetResidual41 ↔
      p = sourceResidual41a ∨ p = sourceResidual41b := by
  rw [← paperTunnellMapExecK_eq (by norm_num) pos41 squarefree41 t1 8 fuelSuffices_41]
  have h := fibreCheck41_holds p
  simp only [fibreCheck41, Bool.and_eq_true, beq_iff_eq, ← Bool.decide_or,
    decide_eq_decide] at h
  exact h.2

/-- The direct fibre as a literal set equality. -/
theorem fibre_direct_41_set :
    {p : BRep 41 | paperTunnellMapExec pos41 squarefree41 t1 p = targetDirect41} =
      {sourceDirect41a, sourceDirect41b} := by
  ext p
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using fibre_direct_41 p

/-- The residual fibre as a literal set equality. -/
theorem fibre_residual_41_set :
    {p : BRep 41 | paperTunnellMapExec pos41 squarefree41 t1 p = targetResidual41} =
      {sourceResidual41a, sourceResidual41b} := by
  ext p
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using fibre_residual_41 p

/-- Both fibres really have two distinct elements. -/
theorem fibres_41_two_distinct :
    sourceDirect41a ≠ sourceDirect41b ∧ sourceResidual41a ≠ sourceResidual41b := by
  constructor <;> decide

end Examples41
end TunnellMap

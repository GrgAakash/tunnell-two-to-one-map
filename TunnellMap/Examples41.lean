import TunnellMap.ControlCost
import TunnellMap.Finiteness
import TunnellMap.PureCoordinates
import TunnellMap.ResidualDeferredAcceptance

/-!
# The worked examples at `n = 41`

This file checks the numerical examples in the manuscript.  The finite box
below is exhaustive, not a sampling range: positivity of the two forms gives
`|x|, |y| ≤ 7` and `|z| ≤ 2` for every representation of `41`.
-/

namespace TunnellMap
namespace Examples41

set_option maxRecDepth 10000

/-! ## Exhaustive representation counts -/

def tripleEmbedding : ((ℤ × ℤ) × ℤ) ↪ Triple where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  inj' := by
    intro p q h
    cases p with
    | mk pz z =>
      cases pz with
      | mk x y =>
        cases q with
        | mk qz z' =>
          cases qz with
          | mk x' y' =>
            simp only at h
            have hx := congrArg Triple.x h
            have hy := congrArg Triple.y h
            have hz := congrArg Triple.z h
            simp_all

def box41 : Finset Triple :=
  (((OrderedGenerator.intIcc (-7 : ℤ) 7).product
      (OrderedGenerator.intIcc (-7 : ℤ) 7)).product
    (OrderedGenerator.intIcc (-2 : ℤ) 2)).map tripleEmbedding

def bRepresentations41 : Finset Triple := box41.filter fun p => bForm p = 41

def aRepresentations41 : Finset Triple := box41.filter fun p => aForm p = 41

def bSlice41 (z : ℤ) : Finset Triple :=
  bRepresentations41.filter fun p => p.z = z

def aSlice41 (z : ℤ) : Finset Triple :=
  aRepresentations41.filter fun p => p.z = z

theorem b_slice_counts :
    (bSlice41 0).card = 4 ∧
      (bSlice41 1).card = 8 ∧
      (bSlice41 (-1)).card = 8 ∧
      (bSlice41 2).card = 6 ∧
      (bSlice41 (-2)).card = 6 := by
  decide +kernel

theorem a_slice_counts :
    (aSlice41 0).card = 4 ∧
      (aSlice41 1).card = 6 ∧
      (aSlice41 (-1)).card = 6 := by
  decide +kernel

theorem b_total_count : bRepresentations41.card = 32 := by
  decide +kernel

theorem a_total_count : aRepresentations41.card = 16 := by
  decide +kernel

theorem box41_complete_for_b (p : Triple) (hp : bForm p = 41) : p ∈ box41 := by
  have hform : 2 * p.x ^ 2 + p.y ^ 2 + 8 * p.z ^ 2 = 41 := by
    simpa [bForm] using hp
  have hxlo : -7 ≤ p.x := by
    by_contra h
    have hx : p.x ≤ -8 := by omega
    nlinarith [sq_nonneg p.y, sq_nonneg p.z]
  have hxhi : p.x ≤ 7 := by
    by_contra h
    have hx : 8 ≤ p.x := by omega
    nlinarith [sq_nonneg p.y, sq_nonneg p.z]
  have hylo : -7 ≤ p.y := by
    by_contra h
    have hy : p.y ≤ -8 := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.z]
  have hyhi : p.y ≤ 7 := by
    by_contra h
    have hy : 8 ≤ p.y := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.z]
  have hzlo : -2 ≤ p.z := by
    by_contra h
    have hz : p.z ≤ -3 := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.y]
  have hzhi : p.z ≤ 2 := by
    by_contra h
    have hz : 3 ≤ p.z := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.y]
  apply Finset.mem_map.mpr
  refine ⟨((p.x, p.y), p.z), ?_, rfl⟩
  simp [OrderedGenerator.mem_intIcc, hxlo, hxhi, hylo, hyhi, hzlo, hzhi]

theorem box41_complete_for_a (p : Triple) (hp : aForm p = 41) : p ∈ box41 := by
  have hform : 2 * p.x ^ 2 + p.y ^ 2 + 32 * p.z ^ 2 = 41 := by
    simpa [aForm] using hp
  have hxlo : -7 ≤ p.x := by
    by_contra h
    have hx : p.x ≤ -8 := by omega
    nlinarith [sq_nonneg p.y, sq_nonneg p.z]
  have hxhi : p.x ≤ 7 := by
    by_contra h
    have hx : 8 ≤ p.x := by omega
    nlinarith [sq_nonneg p.y, sq_nonneg p.z]
  have hylo : -7 ≤ p.y := by
    by_contra h
    have hy : p.y ≤ -8 := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.z]
  have hyhi : p.y ≤ 7 := by
    by_contra h
    have hy : 8 ≤ p.y := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.z]
  have hzlo : -2 ≤ p.z := by
    by_contra h
    have hz : p.z ≤ -3 := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.y]
  have hzhi : p.z ≤ 2 := by
    by_contra h
    have hz : 3 ≤ p.z := by omega
    nlinarith [sq_nonneg p.x, sq_nonneg p.y]
  apply Finset.mem_map.mpr
  refine ⟨((p.x, p.y), p.z), ?_, rfl⟩
  simp [OrderedGenerator.mem_intIcc, hxlo, hxhi, hylo, hyhi, hzlo, hzhi]

theorem bRepresentations41_complete (p : Triple) :
    p ∈ bRepresentations41 ↔ bForm p = 41 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨box41_complete_for_b p h, h⟩

theorem aRepresentations41_complete (p : Triple) :
    p ∈ aRepresentations41 ↔ aForm p = 41 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨box41_complete_for_a p h, h⟩

theorem balance_at_41 :
    bRepresentations41.card = 2 * aRepresentations41.card := by
  norm_num [b_total_count, a_total_count]

/-! ## Coordinate changes and midpoint arithmetic -/

def Xcoord : BOddRep 41 :=
  ⟨⟨-4, -1, 1⟩, by norm_num [bForm], by norm_num⟩

def Ycoord : ARep 41 :=
  ⟨⟨2, -1, 1⟩, by norm_num [aForm]⟩

theorem coordinate_change_example :
    bLift Xcoord = ⟨-4, -1, 2⟩ ∧
      aLift Ycoord = ⟨2, -1, 4⟩ ∧
      qForm (bLift Xcoord) = 41 ∧
      qForm (aLift Ycoord) = 41 := by
  norm_num [Xcoord, Ycoord, bLift, aLift, qForm]

theorem pure_coordinate_change_example :
    (eBEquiv 41 Xcoord).1 = ⟨-2, -6, -1⟩ ∧
      (eAEquiv 41 Ycoord).1 = ⟨6, -2, -1⟩ ∧
      (eBEquiv 41).symm (eBEquiv 41 Xcoord) = Xcoord ∧
      (eAEquiv 41).symm (eAEquiv 41 Ycoord) = Ycoord := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp

def midpointSource : BOddRep 41 :=
  ⟨⟨-2, -5, 1⟩, by norm_num [bForm], by norm_num⟩

def midpointTarget : ARep 41 :=
  ⟨⟨4, -3, 0⟩, by norm_num [aForm]⟩

theorem midpoint_example :
    bLift midpointSource = ⟨-2, -5, 2⟩ ∧
      aLift midpointTarget = ⟨4, -3, 0⟩ ∧
      IsHalfSum ⟨1, -4, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      IsHalfDiff ⟨-3, -1, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      qForm ⟨1, -4, 1⟩ = 20 ∧
      qForm ⟨3, 1, -1⟩ = 21 ∧
      qBilinear ⟨-2, -5, 2⟩ ⟨1, -4, 1⟩ = 20 ∧
      vadd (negTriple ⟨-2, -5, 2⟩) (vsmul 2 ⟨1, -4, 1⟩) =
        ⟨4, -3, 0⟩ := by
  norm_num [midpointSource, midpointTarget, bLift, aLift, IsHalfSum, IsHalfDiff,
    qForm, qBilinear, vadd, vsmul, negTriple]

theorem midpoint_bound_attained : qForm ⟨1, -4, 1⟩ = (41 - 1) / 2 := by
  norm_num [qForm]

/-! ## The immediate even branch and direct quarter-turn examples -/

def evenSource41 : BEvenParam 41 where
  x := 2
  y := -1
  w := 1
  equation := by norm_num [bForm]

theorem even_branch_example :
    (evenEquiv 41 evenSource41).1 = ⟨2, -1, 1⟩ := by
  rfl

def branch1Source11 : DirectDomain1 11 where
  rep := ⟨⟨-1, -1, 1⟩, by norm_num [bForm], by norm_num⟩
  quotient := 0
  equation := by norm_num

def branch2Source11 : DirectDomain2 11 where
  rep := ⟨⟨-1, 1, -1⟩, by norm_num [bForm], by norm_num⟩
  quotient := 0
  equation := by norm_num

def branch3Source41 : DirectDomain3 41 where
  rep := Xcoord
  quotient := -1
  equation := by norm_num [Xcoord]

theorem quarter_turn_branch_examples :
    (branch1Equiv 11 branch1Source11).rep.1 = ⟨1, -3, 0⟩ ∧
      (branch2Equiv 11 branch2Source11).rep.1 = ⟨1, 3, 0⟩ ∧
      (branch3Equiv 41 branch3Source41).rep.1 = ⟨2, -1, 1⟩ ∧
      (branch3Equiv 41).symm (branch3Equiv 41 branch3Source41) = branch3Source41 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact (branch3Equiv 41).left_inv branch3Source41

end Examples41
end TunnellMap

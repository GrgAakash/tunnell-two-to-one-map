import TunnellMap.OrbitLift
import TunnellMap.MidpointBound

/-!
# Certified preferred midpoint records

For a residual source-target pair, the smaller signed midpoint key selects a
unique target sign.  This file packages the resulting arithmetic data used by
the ordered-adjacency generator.
-/

namespace TunnellMap

theorem vadd_eq_two_vsmul_of_halfSum {h E F : Triple}
    (hh : IsHalfSum h E F) : vadd E F = vsmul 2 h := by
  rcases hh with ⟨hx, hy, hz⟩
  apply Triple.ext <;> simp [vadd, vsmul] at hx hy hz ⊢ <;> omega

theorem halfDiff_is_halfSum_neg {h E F : Triple}
    (hh : IsHalfDiff h E F) : IsHalfSum h E (negTriple F) := by
  rcases hh with ⟨hx, hy, hz⟩
  exact ⟨by simpa [negTriple, sub_eq_add_neg] using hx,
    by simpa [negTriple, sub_eq_add_neg] using hy,
    by simpa [negTriple, sub_eq_add_neg] using hz⟩

structure PreferredMidpointRecord {n : ℤ} (s : BResidual n) (t : AResidual n) where
  target : AResidual n
  target_eq : target = preferredTarget s t
  half : Triple
  half_odd : Odd half.z
  half_sum : IsHalfSum half (residualSourceLift s) (residualTargetLift target)
  direction : Triple
  multiplier : ℤ
  direction_eq : direction = primitiveDirection (preferredVector s t)
  half_decomposition : half = vsmul multiplier direction
  multiplier_odd : Odd multiplier
  direction_third_odd : Odd direction.z
  direction_oriented : FirstNonzeroPositive direction
  bilinear : qBilinear (residualSourceLift s) direction =
    multiplier * qForm direction
  target_formula : residualTargetLift target =
    vadd (negTriple (residualSourceLift s)) (vsmul (2 * multiplier) direction)
  direction_bound : 2 * qForm direction ≤ n - 1

theorem preferred_midpoint_record_of_half {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t target : AResidual n) (htarget : target = preferredTarget s t)
    (h : Triple) (hodd : Odd h.z)
    (hhalf : IsHalfSum h (residualSourceLift s) (residualTargetLift target))
    (hpref : preferredVector s t = vsmul 2 h) :
    Nonempty (PreferredMidpointRecord s t) := by
  have hne : h ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hodd
  let d := primitiveDirection h
  let q := directionScale h
  have hdec : h = vsmul q d := direction_decomposition h
  have hdir : d = primitiveDirection (preferredVector s t) := by
    rw [hpref, primitiveDirection_two_vsmul hne]
  have hqne : q ≠ 0 := directionScale_ne_zero hne
  have hzprod : h.z = q * d.z := congrArg Triple.z hdec
  have hprodOdd : Odd (q * d.z) := by
    rw [← hzprod]
    exact hodd
  have hqodd : Odd q := (Int.odd_mul.mp hprodOdd).1
  have hdodd : Odd d.z := (Int.odd_mul.mp hprodOdd).2
  have hfirst : FirstNonzeroPositive d := by
    exact orientDirection_firstNonzeroPositive (primitivePartTriple_ne_zero hne)
  have hline : vadd (residualSourceLift s) (residualTargetLift target) =
      vsmul (2 * q) d := by
    calc
      vadd (residualSourceLift s) (residualTargetLift target) = vsmul 2 h :=
        vadd_eq_two_vsmul_of_halfSum hhalf
      _ = vsmul 2 (vsmul q d) := by rw [hdec]
      _ = vsmul (2 * q) d := by ext <;> simp [vsmul] <;> ring
  have hnorm : qForm (residualTargetLift target) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have hscale := endpoint_scale_equation hnorm (mul_ne_zero (by norm_num) hqne)
    (Or.inl hline)
  have hbilinear : qBilinear (residualSourceLift s) d = q * qForm d := by
    nlinarith
  have htargetFormula : residualTargetLift target =
      vadd (negTriple (residualSourceLift s)) (vsmul (2 * q) d) := by
    apply Triple.ext
    · have hx := congrArg Triple.x hline
      simp [vadd, vsmul, negTriple] at hx ⊢
      linarith
    · have hy := congrArg Triple.y hline
      simp [vadd, vsmul, negTriple] at hy ⊢
      linarith
    · have hz := congrArg Triple.z hline
      simp [vadd, vsmul, negTriple] at hz ⊢
      linarith
  have hbound := preferred_midpoint_generator_bound hn s t
  refine ⟨{
    target := target
    target_eq := htarget
    half := h
    half_odd := hodd
    half_sum := hhalf
    direction := d
    multiplier := q
    direction_eq := hdir
    half_decomposition := hdec
    multiplier_odd := hqodd
    direction_third_odd := hdodd
    direction_oriented := hfirst
    bilinear := hbilinear
    target_formula := htargetFormula
    direction_bound := ?_ }⟩
  simpa [hdir] using hbound

/-- The complete preferred midpoint record for every residual pair. -/
theorem exists_preferred_midpoint_record {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t : AResidual n) :
    Nonempty (PreferredMidpointRecord s t) := by
  obtain ⟨hPlus, hMinus, hPlusEq, hPlusOdd, hMinusEq, hMinusOdd⟩ :=
    midpoint_parity hn s.1 t.1
  by_cases hkey : directionKey (plusVector s t) < directionKey (minusVector s t)
  · have htarget : t = preferredTarget s t := by simp [preferredTarget, hkey]
    have hpref : preferredVector s t = vsmul 2 hPlus := by
      rw [show preferredVector s t = plusVector s t by simp [preferredVector, hkey]]
      exact plusVector_eq_two_vsmul_of_halfSum s t hPlus hPlusEq
    exact preferred_midpoint_record_of_half hn s t t htarget hPlus hPlusOdd hPlusEq hpref
  · have htarget : negAResidual t = preferredTarget s t := by
      simp [preferredTarget, hkey]
    have hhalf : IsHalfSum hMinus (residualSourceLift s)
        (residualTargetLift (negAResidual t)) := by
      rw [residualTargetLift_neg]
      exact halfDiff_is_halfSum_neg hMinusEq
    have hpref : preferredVector s t = vsmul 2 hMinus := by
      rw [show preferredVector s t = minusVector s t by simp [preferredVector, hkey]]
      exact minusVector_eq_two_vsmul_of_halfDiff s t hMinus hMinusEq
    exact preferred_midpoint_record_of_half hn s t (negAResidual t) htarget
      hMinus hMinusOdd hhalf hpref

end TunnellMap

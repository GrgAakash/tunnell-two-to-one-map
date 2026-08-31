import TunnellMap.ProjectiveKey

/-!
# The preferred midpoint bound

This file proves the bound used to make the ordered-adjacency search finite.
The proof works with the integral half-sum and half-difference, rather than
their doubled raw vectors, so it retains the factor appearing in the paper.
-/

namespace TunnellMap

@[simp] theorem qForm_vsmul (a : ℤ) (p : Triple) :
    qForm (vsmul a p) = a ^ 2 * qForm p := by
  simp [qForm, vsmul]
  ring

theorem plusVector_eq_two_vsmul_of_halfSum {n : ℤ}
    (s : BResidual n) (t : AResidual n) (h : Triple)
    (hh : IsHalfSum h (bLift s.1) (aLift t.1)) :
    plusVector s t = vsmul 2 h := by
  rcases hh with ⟨hx, hy, hz⟩
  apply Triple.ext <;>
    simp [plusVector, residualSourceLift, residualTargetLift, vadd, vsmul] at hx hy hz ⊢ <;>
    omega

theorem minusVector_eq_two_vsmul_of_halfDiff {n : ℤ}
    (s : BResidual n) (t : AResidual n) (h : Triple)
    (hh : IsHalfDiff h (bLift s.1) (aLift t.1)) :
    minusVector s t = vsmul 2 h := by
  rcases hh with ⟨hx, hy, hz⟩
  apply Triple.ext <;>
    simp [minusVector, residualSourceLift, residualTargetLift, vsub, vsmul] at hx hy hz ⊢ <;>
    omega

theorem qForm_halfSum_add_halfDiff {n : ℤ}
    (s : BResidual n) (t : AResidual n) (hPlus hMinus : Triple)
    (hPlusEq : IsHalfSum hPlus (bLift s.1) (aLift t.1))
    (hMinusEq : IsHalfDiff hMinus (bLift s.1) (aLift t.1)) :
    qForm hPlus + qForm hMinus = n := by
  rcases hPlusEq with ⟨hpx, hpy, hpz⟩
  rcases hMinusEq with ⟨hmx, hmy, hmz⟩
  have hpx2 := congrArg (fun a : ℤ => a ^ 2) hpx
  have hpy2 := congrArg (fun a : ℤ => a ^ 2) hpy
  have hpz2 := congrArg (fun a : ℤ => a ^ 2) hpz
  have hmx2 := congrArg (fun a : ℤ => a ^ 2) hmx
  have hmy2 := congrArg (fun a : ℤ => a ^ 2) hmy
  have hmz2 := congrArg (fun a : ℤ => a ^ 2) hmz
  have hs := qForm_bLift s.1
  have ht := qForm_aLift t.1
  simp [bLift, aLift] at hpx2 hpy2 hpz2 hmx2 hmy2 hmz2
  simp [qForm, bLift, aLift] at hs ht ⊢
  nlinarith

/-- Lemma 4.4 in an integral form: if `d` is the primitive direction of the
preferred signed midpoint, then `2 Q(d) ≤ n - 1`.  For odd `n` this is
equivalent to `Q(d) ≤ (n-1)/2`. -/
theorem preferred_midpoint_generator_bound {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t : AResidual n) :
    2 * qForm (primitiveDirection (preferredVector s t)) ≤ n - 1 := by
  obtain ⟨hPlus, hMinus, hPlusEq, hPlusOdd, hMinusEq, hMinusOdd⟩ :=
    midpoint_parity hn s.1 t.1
  have hPlusNe : hPlus ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hPlusOdd
  have hMinusNe : hMinus ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero hMinusOdd
  have hRawPlus := plusVector_eq_two_vsmul_of_halfSum s t hPlus hPlusEq
  have hRawMinus := minusVector_eq_two_vsmul_of_halfDiff s t hMinus hMinusEq
  have hDirPlus : primitiveDirection (plusVector s t) = primitiveDirection hPlus := by
    rw [hRawPlus, primitiveDirection_two_vsmul hPlusNe]
  have hDirMinus : primitiveDirection (minusVector s t) = primitiveDirection hMinus := by
    rw [hRawMinus, primitiveDirection_two_vsmul hMinusNe]
  let a := directionScale hPlus
  let b := directionScale hMinus
  let d := primitiveDirection (plusVector s t)
  let e := primitiveDirection (minusVector s t)
  have hDecPlus : hPlus = vsmul a d := by
    rw [direction_decomposition hPlus, ← hDirPlus]
  have hDecMinus : hMinus = vsmul b e := by
    rw [direction_decomposition hMinus, ← hDirMinus]
  have ha : a ≠ 0 := directionScale_ne_zero hPlusNe
  have hb : b ≠ 0 := directionScale_ne_zero hMinusNe
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (plusVector_ne_zero s t)
  have he : e ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (minusVector_ne_zero s t)
  have hNormSum := qForm_halfSum_add_halfDiff s t hPlus hMinus hPlusEq hMinusEq
  have hNormPlus : qForm hPlus = a ^ 2 * qForm d := by
    rw [hDecPlus, qForm_vsmul]
  have hNormMinus : qForm hMinus = b ^ 2 * qForm e := by
    rw [hDecMinus, qForm_vsmul]
  have haSq : 1 ≤ a ^ 2 := sq_pos_of_ne_zero ha
  have hbSq : 1 ≤ b ^ 2 := sq_pos_of_ne_zero hb
  have hdPos : 0 < qForm d := qForm_pos_of_ne_zero hd
  have hePos : 0 < qForm e := qForm_pos_of_ne_zero he
  have hLowerPlus : qForm d ≤ qForm hPlus := by
    rw [hNormPlus]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right haSq (le_of_lt hdPos)
  have hLowerMinus : qForm e ≤ qForm hMinus := by
    rw [hNormMinus]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hbSq (le_of_lt hePos)
  have hLowerSum : qForm d + qForm e ≤ n := by
    calc
      qForm d + qForm e ≤ qForm hPlus + qForm hMinus :=
        add_le_add hLowerPlus hLowerMinus
      _ = n := hNormSum
  obtain ⟨k, hk⟩ := hn
  have boundPlus (hde : qForm d ≤ qForm e) : 2 * qForm d ≤ n - 1 := by
    omega
  have boundMinus (hed : qForm e ≤ qForm d) : 2 * qForm e ≤ n - 1 := by
    omega
  by_cases hlt : directionKey (plusVector s t) < directionKey (minusVector s t)
  · have hde : qForm d ≤ qForm e := by
      have hfirst := Prod.Lex.monotone_fst_ofLex hlt.le
      simpa [directionKey, d, e] using hfirst
    simpa [preferredVector, hlt, d] using boundPlus hde
  · have hrev : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (plus_minus_keys_ne s t))
    have hed : qForm e ≤ qForm d := by
      have hfirst := Prod.Lex.monotone_fst_ofLex hrev.le
      simpa [directionKey, d, e] using hfirst
    simpa [preferredVector, hlt, e] using boundMinus hed

end TunnellMap

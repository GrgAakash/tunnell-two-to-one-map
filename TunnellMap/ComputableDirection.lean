import TunnellMap.ProjectiveKey

/-!
# A computable projective direction key

The development so far defines `primitiveDirection` through Mathlib's
polynomial content, which is a noncomputable construction.  Nothing about the
mathematics requires this: the content of an integer triple is the greatest
common divisor of its three coordinates, and the primitive part is obtained by
exact division.

This file supplies the executable counterparts

* `tripleGcd`,
* `primitivePartExec`,
* `primitiveDirectionExec`,
* `directionKeyExec`,

and proves that each agrees with the noncomputable specification.  Everything
in this file is a plain `def`, so the arithmetic generator built on top of it
is genuinely executable.
-/

namespace TunnellMap

open Polynomial

/-! ## The content of a triple is a gcd -/

/-- The greatest common divisor of the three coordinates of a triple. -/
def tripleGcd (v : Triple) : ℤ := gcd (gcd v.x v.y) v.z

theorem tripleContent_dvd_x (v : Triple) : tripleContent v ∣ v.x := by
  simpa [tripleContent] using
    Polynomial.content_dvd_coeff (p := triplePolynomial v) (n := 0)

theorem tripleContent_dvd_y (v : Triple) : tripleContent v ∣ v.y := by
  simpa [tripleContent] using
    Polynomial.content_dvd_coeff (p := triplePolynomial v) (n := 1)

theorem tripleContent_dvd_z (v : Triple) : tripleContent v ∣ v.z := by
  simpa [tripleContent] using
    Polynomial.content_dvd_coeff (p := triplePolynomial v) (n := 2)

theorem tripleGcd_dvd_x (v : Triple) : tripleGcd v ∣ v.x :=
  (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)

theorem tripleGcd_dvd_y (v : Triple) : tripleGcd v ∣ v.y :=
  (gcd_dvd_left _ _).trans (gcd_dvd_right _ _)

theorem tripleGcd_dvd_z (v : Triple) : tripleGcd v ∣ v.z := gcd_dvd_right _ _

theorem normalize_tripleGcd (v : Triple) : normalize (tripleGcd v) = tripleGcd v :=
  normalize_gcd _ _

/-- The polynomial content used in the specification is the coordinate gcd. -/
theorem tripleContent_eq_tripleGcd (v : Triple) : tripleContent v = tripleGcd v := by
  refine dvd_antisymm_of_normalize_eq Polynomial.normalize_content
    (normalize_tripleGcd v) ?_ ?_
  · exact dvd_gcd (dvd_gcd (tripleContent_dvd_x v) (tripleContent_dvd_y v))
      (tripleContent_dvd_z v)
  · unfold tripleContent
    rw [Polynomial.dvd_content_iff_C_dvd, Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    match i with
    | 0 => simpa using tripleGcd_dvd_x v
    | 1 => simpa using tripleGcd_dvd_y v
    | 2 => simpa using tripleGcd_dvd_z v
    | (m + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (triplePolynomial_natDegree_le_two v) (by omega))]
      exact dvd_zero _

theorem tripleGcd_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) : tripleGcd v ≠ 0 := by
  rw [← tripleContent_eq_tripleGcd]
  exact tripleContent_ne_zero hv

/-! ## The primitive part by exact division -/

/-- The primitive part of a triple, computed by dividing out the coordinate
gcd. -/
def primitivePartExec (v : Triple) : Triple :=
  ⟨v.x / tripleGcd v, v.y / tripleGcd v, v.z / tripleGcd v⟩

theorem primitivePartExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartExec v = primitivePartTriple v := by
  have hg : tripleGcd v ≠ 0 := tripleGcd_ne_zero hv
  have hdec := content_mul_primitivePartTriple v
  rw [tripleContent_eq_tripleGcd] at hdec
  have hx : v.x = tripleGcd v * (primitivePartTriple v).x := congrArg Triple.x hdec
  have hy : v.y = tripleGcd v * (primitivePartTriple v).y := congrArg Triple.y hdec
  have hz : v.z = tripleGcd v * (primitivePartTriple v).z := congrArg Triple.z hdec
  refine Triple.ext ?_ ?_ ?_ <;> simp only [primitivePartExec]
  · rw [hx, Int.mul_ediv_cancel_left _ hg]
  · rw [hy, Int.mul_ediv_cancel_left _ hg]
  · rw [hz, Int.mul_ediv_cancel_left _ hg]

/-- The executable primitive oriented direction of a nonzero triple. -/
def primitiveDirectionExec (v : Triple) : Triple :=
  orientDirection (primitivePartExec v)

theorem primitiveDirectionExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirectionExec v = primitiveDirection v := by
  rw [primitiveDirectionExec, primitivePartExec_eq hv, primitiveDirection]

/-! ## The executable key -/

/-- The projective key of a triple that is already primitive and oriented.
No gcd computation is needed in that case. -/
def primitiveKey (v : Triple) : DirectionKey :=
  ⟨qForm v, v.x, v.y, v.z⟩

/-! ## Executable comparison of projective keys

The order on `DirectionKey` is lexicographic in the four integer components.
The generator compares keys through the two Boolean functions below, which are
literal integer comparisons, and which are proved to agree with `<` and
`≤`. -/

/-- Executable strict comparison of projective keys. -/
def keyLtExec (k₁ k₂ : DirectionKey) : Bool := DirectionKey.blt k₁ k₂

@[simp] theorem keyLtExec_iff (k₁ k₂ : DirectionKey) :
    keyLtExec k₁ k₂ = true ↔ k₁ < k₂ :=
  (DirectionKey.lt_iff_blt k₁ k₂).symm

/-- Executable comparison of projective keys. -/
def keyLeExec (k₁ k₂ : DirectionKey) : Bool := !keyLtExec k₂ k₁

@[simp] theorem keyLeExec_iff (k₁ k₂ : DirectionKey) :
    keyLeExec k₁ k₂ = true ↔ k₁ ≤ k₂ := by
  rw [keyLeExec, Bool.not_eq_true', ← Bool.not_eq_true, keyLtExec_iff, not_lt]

/-- The executable projective direction key. -/
def directionKeyExec (v : Triple) : DirectionKey :=
  primitiveKey (primitiveDirectionExec v)

theorem directionKeyExec_eq {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKeyExec v = directionKey v := by
  rw [directionKeyExec, primitiveDirectionExec_eq hv, directionKey, primitiveKey]

/-- On a primitive, canonically oriented triple the key needs no
normalization at all. -/
theorem primitiveKey_eq_directionKey {v : Triple}
    (hcontent : tripleGcd v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveKey v = directionKey v := by
  have hc : tripleContent v = 1 := by rw [tripleContent_eq_tripleGcd]; exact hcontent
  rw [directionKey, primitiveDirection_eq_self_of_content_one_of_oriented hc horiented,
    primitiveKey]

/-! ## Invariance of the key under nonzero scaling -/

theorem tripleGcd_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    tripleGcd (vsmul c v) = c * tripleGcd v := by
  have hn : normalize c = c := Int.normalize_of_nonneg hc.le
  unfold tripleGcd vsmul
  simp only []
  rw [gcd_mul_left, hn, gcd_mul_left, hn]

theorem primitivePartExec_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    primitivePartExec (vsmul c v) = primitivePartExec v := by
  unfold primitivePartExec
  rw [tripleGcd_vsmul_pos hc]
  refine Triple.ext ?_ ?_ ?_ <;>
    simp only [vsmul, Int.mul_ediv_mul_of_pos _ _ hc]

theorem primitiveDirectionExec_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    primitiveDirectionExec (vsmul c v) = primitiveDirectionExec v := by
  unfold primitiveDirectionExec
  rw [primitivePartExec_vsmul_pos hc]

theorem vsmul_ne_zero_of {c : ℤ} (hc : c ≠ 0) {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    vsmul c v ≠ ⟨0, 0, 0⟩ := by
  intro h
  apply hv
  have hx := congrArg Triple.x h
  have hy := congrArg Triple.y h
  have hz := congrArg Triple.z h
  simp only [vsmul] at hx hy hz
  exact Triple.ext (by rcases mul_eq_zero.mp hx with h' | h' <;> simp_all)
    (by rcases mul_eq_zero.mp hy with h' | h' <;> simp_all)
    (by rcases mul_eq_zero.mp hz with h' | h' <;> simp_all)

/-- The projective key only depends on the rational line of a triple. -/
theorem directionKey_vsmul {c : ℤ} (hc : c ≠ 0) {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul c v) = directionKey v := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hrw : vsmul c v = negTriple (vsmul (-c) v) := by
      refine Triple.ext ?_ ?_ ?_ <;> simp [vsmul, negTriple]
    rw [hrw, directionKey_negTriple (vsmul_ne_zero_of (by omega) hv),
      ← directionKeyExec_eq (vsmul_ne_zero_of (by omega : (-c) ≠ 0) hv),
      ← directionKeyExec_eq hv, directionKeyExec, directionKeyExec,
      primitiveDirectionExec_vsmul_pos (by omega)]
  · rw [← directionKeyExec_eq (vsmul_ne_zero_of hc hv), ← directionKeyExec_eq hv,
      directionKeyExec, directionKeyExec, primitiveDirectionExec_vsmul_pos hpos]

end TunnellMap

import TunnellMap.AffineLattice
import TunnellMap.Antipodal

/-!
# Primitive integer directions

An integer triple is encoded as the polynomial `x + y X + z X²`.  Mathlib's
standard polynomial content and primitive part then give the gcd-normalized
integer generator of its rational line.  The remaining sign normalization is
the paper's convention that the first nonzero coordinate is positive.
-/

namespace TunnellMap

open Polynomial

noncomputable def triplePolynomial (v : Triple) : ℤ[X] :=
  C v.x + C v.y * X + C v.z * X ^ 2

def polynomialTriple (f : ℤ[X]) : Triple :=
  ⟨f.coeff 0, f.coeff 1, f.coeff 2⟩

@[simp] theorem polynomialTriple_neg (f : ℤ[X]) :
    polynomialTriple (-f) = negTriple (polynomialTriple f) := by
  ext <;> simp [polynomialTriple, negTriple]

@[simp] theorem triplePolynomial_coeff_zero (v : Triple) :
    (triplePolynomial v).coeff 0 = v.x := by
  simp [triplePolynomial]

@[simp] theorem triplePolynomial_coeff_one (v : Triple) :
    (triplePolynomial v).coeff 1 = v.y := by
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  norm_num

@[simp] theorem triplePolynomial_coeff_two (v : Triple) :
    (triplePolynomial v).coeff 2 = v.z := by
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  norm_num

@[simp] theorem polynomialTriple_triplePolynomial (v : Triple) :
    polynomialTriple (triplePolynomial v) = v := by
  ext <;> simp [polynomialTriple]

theorem triplePolynomial_injective : Function.Injective triplePolynomial := by
  intro v w h
  simpa using congrArg polynomialTriple h

@[simp] theorem triplePolynomial_negTriple (v : Triple) :
    triplePolynomial (negTriple v) = -triplePolynomial v := by
  simp [triplePolynomial, negTriple]
  ring

@[simp] theorem triplePolynomial_vsmul (a : ℤ) (v : Triple) :
    triplePolynomial (vsmul a v) = C a * triplePolynomial v := by
  simp [triplePolynomial, vsmul]
  ring

theorem triplePolynomial_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    triplePolynomial v ≠ 0 := by
  intro h
  apply hv
  apply Triple.ext
  · have := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simpa using this
  · have := congrArg (fun f : ℤ[X] => f.coeff 1) h
    simpa using this
  · have := congrArg (fun f : ℤ[X] => f.coeff 2) h
    simpa using this

theorem triplePolynomial_natDegree_le_two (v : Triple) :
    (triplePolynomial v).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp only [triplePolynomial, coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  simp [hn0, hn1, hn2]

noncomputable def tripleContent (v : Triple) : ℤ :=
  (triplePolynomial v).content

noncomputable def primitivePartTriple (v : Triple) : Triple :=
  polynomialTriple (triplePolynomial v).primPart

/-- Converting the primitive polynomial back to a triple loses no
coefficients, because the original polynomial has degree at most two. -/
theorem triplePolynomial_primitivePartTriple (v : Triple) :
    triplePolynomial (primitivePartTriple v) = (triplePolynomial v).primPart := by
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [primitivePartTriple, polynomialTriple]
  · have hnLarge : 2 < n := Nat.lt_of_not_ge hn
    have hleftDeg : (triplePolynomial (primitivePartTriple v)).natDegree ≤ 2 :=
      triplePolynomial_natDegree_le_two _
    have hrightDeg : (triplePolynomial v).primPart.natDegree ≤ 2 := by
      rw [Polynomial.natDegree_primPart]
      exact triplePolynomial_natDegree_le_two _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hleftDeg hnLarge)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hrightDeg hnLarge)]

theorem polynomial_content_neg (f : ℤ[X]) : (-f).content = f.content := by
  rw [show -f = C (-1 : ℤ) * f by simp, Polynomial.content_C_mul]
  rw [← Int.abs_eq_normalize]
  norm_num

@[simp] theorem tripleContent_negTriple (v : Triple) :
    tripleContent (negTriple v) = tripleContent v := by
  simp [tripleContent, polynomial_content_neg]

theorem polynomial_primPart_neg {f : ℤ[X]} (hf : f ≠ 0) :
    (-f).primPart = -f.primPart := by
  have hc : f.content ≠ 0 := by
    intro h
    exact hf (Polynomial.content_eq_zero_iff.mp h)
  have hbase := Polynomial.eq_C_content_mul_primPart f
  have hneg := Polynomial.eq_C_content_mul_primPart (-f)
  rw [polynomial_content_neg] at hneg
  apply mul_left_cancel₀ (show C f.content ≠ (0 : ℤ[X]) by simpa using hc)
  calc
    C f.content * (-f).primPart = -f := hneg.symm
    _ = -(C f.content * f.primPart) := by rw [← hbase]
    _ = C f.content * (-f.primPart) := by simp

theorem polynomial_primPart_two_mul {f : ℤ[X]} (hf : f ≠ 0) :
    (C (2 : ℤ) * f).primPart = f.primPart := by
  have hc : f.content ≠ 0 := by
    intro h
    exact hf (Polynomial.content_eq_zero_iff.mp h)
  have hcontent : (C (2 : ℤ) * f).content = 2 * f.content := by
    rw [Polynomial.content_C_mul, ← Int.abs_eq_normalize]
    norm_num
  have hbase := Polynomial.eq_C_content_mul_primPart f
  have hscaled := Polynomial.eq_C_content_mul_primPart (C (2 : ℤ) * f)
  rw [hcontent] at hscaled
  apply mul_left_cancel₀ (show C (2 * f.content) ≠ (0 : ℤ[X]) by
    simp [hc])
  calc
    C (2 * f.content) * (C (2 : ℤ) * f).primPart = C (2 : ℤ) * f :=
      hscaled.symm
    _ = C (2 : ℤ) * (C f.content * f.primPart) := by rw [← hbase]
    _ = C (2 * f.content) * f.primPart := by simp [mul_assoc]

@[simp] theorem primitivePartTriple_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (negTriple v) = negTriple (primitivePartTriple v) := by
  unfold primitivePartTriple
  rw [triplePolynomial_negTriple,
    polynomial_primPart_neg (triplePolynomial_ne_zero hv), polynomialTriple_neg]

@[simp] theorem primitivePartTriple_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (vsmul 2 v) = primitivePartTriple v := by
  unfold primitivePartTriple
  rw [triplePolynomial_vsmul,
    polynomial_primPart_two_mul (triplePolynomial_ne_zero hv)]

theorem tripleContent_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    tripleContent v ≠ 0 := by
  intro hc
  apply triplePolynomial_ne_zero hv
  exact Polynomial.content_eq_zero_iff.mp hc

@[simp] theorem tripleContent_primitivePartTriple (v : Triple) :
    tripleContent (primitivePartTriple v) = 1 := by
  unfold tripleContent
  rw [triplePolynomial_primitivePartTriple]
  exact Polynomial.content_primPart _

/-- The coordinate form of `Polynomial.eq_C_content_mul_primPart`. -/
theorem content_mul_primitivePartTriple (v : Triple) :
    v = vsmul (tripleContent v) (primitivePartTriple v) := by
  apply Triple.ext
  · have h := congrArg (fun f : ℤ[X] => f.coeff 0)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 1)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h
  · have h := congrArg (fun f : ℤ[X] => f.coeff 2)
      (Polynomial.eq_C_content_mul_primPart (triplePolynomial v))
    simpa [tripleContent, primitivePartTriple, polynomialTriple, vsmul] using h

theorem primitivePartTriple_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple v ≠ ⟨0, 0, 0⟩ := by
  intro hd
  have h := content_mul_primitivePartTriple v
  rw [hd] at h
  apply hv
  simpa [vsmul] using h

def FirstNonzeroPositive (v : Triple) : Prop :=
  0 < v.x ∨ (v.x = 0 ∧ 0 < v.y) ∨ (v.x = 0 ∧ v.y = 0 ∧ 0 < v.z)

instance firstNonzeroPositiveDecidable (v : Triple) : Decidable (FirstNonzeroPositive v) :=
  by
    unfold FirstNonzeroPositive
    infer_instance

theorem firstNonzeroPositive_or_neg {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    FirstNonzeroPositive v ∨ FirstNonzeroPositive (negTriple v) := by
  rcases lt_trichotomy v.x 0 with hx | hx | hx
  · right
    left
    simpa [negTriple]
  · rcases lt_trichotomy v.y 0 with hy | hy | hy
    · right
      right
      left
      simpa [negTriple, hx]
    · have hz : v.z ≠ 0 := by
        intro hz
        apply hv
        ext <;> simp_all
      rcases lt_or_gt_of_ne hz with hz | hz
      · right
        right
        right
        simpa [negTriple, hx, hy]
      · left
        right
        right
        exact ⟨hx, hy, hz⟩
    · left
      right
      left
      exact ⟨hx, hy⟩
  · left
    exact Or.inl hx

theorem firstNonzeroPositive_not_both (v : Triple) :
    ¬ (FirstNonzeroPositive v ∧ FirstNonzeroPositive (negTriple v)) := by
  rintro ⟨hv, hn⟩
  rcases hv with hx | hy | hz <;> rcases hn with hx' | hy' | hz' <;>
    simp [negTriple] at * <;> omega

def orientDirection (v : Triple) : Triple :=
  if FirstNonzeroPositive v then v else negTriple v

@[simp] theorem tripleContent_orientDirection (v : Triple) :
    tripleContent (orientDirection v) = tripleContent v := by
  by_cases h : FirstNonzeroPositive v <;> simp [orientDirection, h]

theorem orientDirection_firstNonzeroPositive {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    FirstNonzeroPositive (orientDirection v) := by
  by_cases h : FirstNonzeroPositive v
  · simp [orientDirection, h]
  · have hn := (firstNonzeroPositive_or_neg hv).resolve_left h
    simpa [orientDirection, h] using hn

theorem orientDirection_neg {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    orientDirection (negTriple v) = orientDirection v := by
  have hnb : ¬ (FirstNonzeroPositive v ∧ FirstNonzeroPositive (negTriple v)) :=
    firstNonzeroPositive_not_both v
  rcases firstNonzeroPositive_or_neg hv with h | h
  · have hn : ¬ FirstNonzeroPositive (negTriple v) := fun hn => hnb ⟨h, hn⟩
    simp [orientDirection, h, hn]
  · have hvn : ¬ FirstNonzeroPositive v := fun hvp => hnb ⟨hvp, h⟩
    simp [orientDirection, h, hvn]

noncomputable def primitiveDirection (v : Triple) : Triple :=
  orientDirection (primitivePartTriple v)

noncomputable def directionScale (v : Triple) : ℤ :=
  if FirstNonzeroPositive (primitivePartTriple v) then
    tripleContent v
  else
    -tripleContent v

@[simp] theorem tripleContent_primitiveDirection (v : Triple) :
    tripleContent (primitiveDirection v) = 1 := by
  simp [primitiveDirection]

theorem primitivePartTriple_eq_self_of_content_one {v : Triple}
    (hv : tripleContent v = 1) : primitivePartTriple v = v := by
  have hp : (triplePolynomial v).IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_content_eq_one]
    exact hv
  unfold primitivePartTriple
  rw [hp.primPart_eq, polynomialTriple_triplePolynomial]

theorem primitiveDirection_eq_self_of_content_one_of_oriented {v : Triple}
    (hcontent : tripleContent v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveDirection v = v := by
  rw [primitiveDirection, primitivePartTriple_eq_self_of_content_one hcontent]
  simp [orientDirection, horiented]

@[simp] theorem primitiveDirection_idem {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (primitiveDirection v) = primitiveDirection v := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_primitiveDirection v
  · exact orientDirection_firstNonzeroPositive (primitivePartTriple_ne_zero hv)

@[simp] theorem primitiveDirection_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (negTriple v) = primitiveDirection v := by
  rw [primitiveDirection, primitivePartTriple_negTriple hv]
  exact orientDirection_neg (primitivePartTriple_ne_zero hv)

@[simp] theorem primitiveDirection_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (vsmul 2 v) = primitiveDirection v := by
  simp [primitiveDirection, primitivePartTriple_two_vsmul hv]

/-- Every integer vector is an integral multiple of the paper-oriented
primitive part selected from its line. -/
theorem direction_decomposition (v : Triple) :
    v = vsmul (directionScale v) (primitiveDirection v) := by
  have hcontent := content_mul_primitivePartTriple v
  by_cases h : FirstNonzeroPositive (primitivePartTriple v)
  · simpa [directionScale, primitiveDirection, orientDirection, h] using hcontent
  · calc
      v = vsmul (tripleContent v) (primitivePartTriple v) := hcontent
      _ = vsmul (-tripleContent v) (negTriple (primitivePartTriple v)) := by
        ext <;> simp [vsmul, negTriple]
      _ = vsmul (directionScale v) (primitiveDirection v) := by
        simp [directionScale, primitiveDirection, orientDirection, h]

theorem primitiveDirection_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection v ≠ ⟨0, 0, 0⟩ := by
  intro hd
  have h := direction_decomposition v
  rw [hd] at h
  apply hv
  simpa [vsmul] using h

theorem directionScale_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionScale v ≠ 0 := by
  by_cases h : FirstNonzeroPositive (primitivePartTriple v) <;>
    simp [directionScale, h, tripleContent_ne_zero hv]

end TunnellMap

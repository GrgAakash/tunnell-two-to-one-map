import TunnellMap.OrderedGenerator

/-!
# The reduced-basis search-interval bound

This file formalizes the optional Lagrange-Gauss reduced-basis estimate in
the manuscript.  It is not used in the correctness proof of the generator.
-/

namespace TunnellMap
namespace OrderedGenerator

variable {p : Triple}

/-- The second diagonal entry of the Gram matrix of the kernel basis. -/
def gamma (F : OrthogonalFrame p) : ℤ := dot F.e₂ F.e₂

/-- The standard Lagrange-Gauss inequalities for the ordered kernel basis. -/
def IsLagrangeGaussReduced (F : OrthogonalFrame p) : Prop :=
  |2 * beta F| ≤ alpha F ∧ alpha F ≤ gamma F

/-- The integral form of the reduced-basis estimate. -/
theorem reduced_alpha_square_bound (F : OrthogonalFrame p)
    (hred : IsLagrangeGaussReduced F) :
    3 * alpha F ^ 2 ≤ 4 * dot p p := by
  rcases hred with ⟨hbetaAbs, hAlphaGamma⟩
  have hAlpha : 0 < alpha F := alpha_pos F
  have hbetaBounds : -alpha F ≤ 2 * beta F ∧ 2 * beta F ≤ alpha F :=
    (abs_le.mp hbetaAbs)
  have hbetaSq : 4 * beta F ^ 2 ≤ alpha F ^ 2 := by
    have hleft : 0 ≤ alpha F - 2 * beta F := sub_nonneg.mpr hbetaBounds.2
    have hright : 0 ≤ alpha F + 2 * beta F := by omega
    nlinarith [mul_nonneg hleft hright]
  have hAlphaSq : alpha F ^ 2 ≤ alpha F * gamma F := by
    have hnonneg : 0 ≤ alpha F * (gamma F - alpha F) :=
      mul_nonneg hAlpha.le (sub_nonneg.mpr hAlphaGamma)
    nlinarith
  have hGram := F.gram_det
  change alpha F * gamma F - beta F ^ 2 = dot p p at hGram
  nlinarith

/-- The real square-root form stated in the manuscript:
`alpha ≤ 2 * sqrt((p·p)/3)`. -/
theorem reduced_alpha_le_two_sqrt_div_three (F : OrthogonalFrame p)
    (hred : IsLagrangeGaussReduced F) :
    (alpha F : ℝ) ≤ 2 * Real.sqrt ((dot p p : ℝ) / 3) := by
  have hAlpha : 0 ≤ (alpha F : ℝ) := by
    exact_mod_cast (alpha_pos F).le
  have hsqInt := reduced_alpha_square_bound F hred
  have hsq : 3 * (alpha F : ℝ) ^ 2 ≤ 4 * (dot p p : ℝ) := by
    exact_mod_cast hsqInt
  have hnorm : 0 ≤ (dot p p : ℝ) := by
    have hnormInt : 0 ≤ dot p p := by
      simp only [dot]
      nlinarith [sq_nonneg p.x, sq_nonneg p.y, sq_nonneg p.z]
    exact_mod_cast hnormInt
  have hhalf : (alpha F : ℝ) / 2 ≤ Real.sqrt ((dot p p : ℝ) / 3) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  nlinarith

end OrderedGenerator
end TunnellMap

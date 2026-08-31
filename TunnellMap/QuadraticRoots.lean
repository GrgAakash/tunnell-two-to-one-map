import TunnellMap.ShortInterval

/-!
# Integral quadratic-root certificates

The ordered-adjacency generator solves a quadratic in the first affine
coordinate.  The lemmas here verify the integral quadratic formula in a form
that uses only squaring and divisibility, including the repeated-root case.
-/

namespace TunnellMap

def quadraticEquation (α c d a : ℤ) : Prop :=
  α * a ^ 2 + 2 * c * a + d = 0

def quadraticHalfDiscriminant (α c d : ℤ) : ℤ := c ^ 2 - α * d

theorem quadraticEquation_iff_root_certificate {α c d a : ℤ} (hα : α ≠ 0) :
    quadraticEquation α c d a ↔
      ∃ u : ℤ, u ^ 2 = quadraticHalfDiscriminant α c d ∧ α * a = -c + u := by
  constructor
  · intro h
    refine ⟨α * a + c, ?_, by ring⟩
    unfold quadraticEquation at h
    unfold quadraticHalfDiscriminant
    have hlinear : α * a ^ 2 + 2 * c * a = -d := by linarith
    calc
      (α * a + c) ^ 2 = c ^ 2 + α * (α * a ^ 2 + 2 * c * a) := by ring
      _ = c ^ 2 + α * (-d) := by rw [hlinear]
      _ = c ^ 2 - α * d := by ring
  · rintro ⟨u, hu, ha⟩
    unfold quadraticEquation quadraticHalfDiscriminant at *
    apply mul_left_cancel₀ hα
    calc
      α * (α * a ^ 2 + 2 * c * a + d) =
          (α * a + c) ^ 2 - (c ^ 2 - α * d) := by ring
      _ = u ^ 2 - (c ^ 2 - α * d) := by rw [ha]; ring
      _ = 0 := by rw [hu]; ring
      _ = α * 0 := by ring

theorem integer_square_roots {u s : ℤ} (h : u ^ 2 = s ^ 2) :
    u = s ∨ u = -s := by
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem quadraticEquation_roots_of_square {α c d s a : ℤ}
    (hα : α ≠ 0) (hs : s ^ 2 = quadraticHalfDiscriminant α c d) :
    quadraticEquation α c d a ↔
      (α * a = -c + s ∨ α * a = -c - s) := by
  rw [quadraticEquation_iff_root_certificate hα]
  constructor
  · rintro ⟨u, hu, ha⟩
    rcases integer_square_roots (hu.trans hs.symm) with huEq | huEq
    · left
      simpa [huEq] using ha
    · right
      rw [huEq] at ha
      linarith
  · intro h
    rcases h with h | h
    · exact ⟨s, hs, h⟩
    · refine ⟨-s, by simpa using hs, ?_⟩
      linarith

namespace OrthogonalFrame

variable {p : Triple} (F : OrthogonalFrame p)

def affineQuadratic (A q a b : ℤ) : ℤ :=
  let α := dot F.e₁ F.e₁
  let β := dot F.e₁ F.e₂
  let γ := dot F.e₂ F.e₂
  let δ := dot F.z F.e₁
  let ε := dot F.z F.e₂
  let ζ := dot F.z F.z
  let t := q * A
  α * a ^ 2 + 2 * (β * b + t * δ) * a +
    γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A

/-- Equation (5.4): the affine vector has norm `A` exactly when its first
coordinate satisfies the displayed quadratic. -/
theorem affine_norm_eq_iff (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      F.affineQuadratic A q a b = 0 := by
  rw [F.affine_norm_expansion]
  simp [affineQuadratic]
  constructor <;> intro h <;> linarith

theorem affineQuadratic_discriminant (A q b : ℤ) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let t := q * A
    quadraticHalfDiscriminant α (β * b + t * δ)
      (γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A) =
        F.halfDiscriminant A q b := by
  simp [quadraticHalfDiscriminant, halfDiscriminant]

/-- The exact integral-root interface used by Algorithm 5.4. -/
theorem affine_norm_root_certificate (A q a b : ℤ) :
    dot (linComb3 a b (q * A) F.e₁ F.e₂ F.z)
        (linComb3 a b (q * A) F.e₁ F.e₂ F.z) = A ↔
      ∃ u : ℤ,
        u ^ 2 = F.halfDiscriminant A q b ∧
        dot F.e₁ F.e₁ * a =
          -(dot F.e₁ F.e₂ * b + q * A * dot F.z F.e₁) + u := by
  rw [F.affine_norm_eq_iff]
  have hquad : F.affineQuadratic A q a b = 0 ↔
      quadraticEquation (dot F.e₁ F.e₁)
        (dot F.e₁ F.e₂ * b + q * A * dot F.z F.e₁)
        (dot F.e₂ F.e₂ * b ^ 2 +
          2 * (q * A) * dot F.z F.e₂ * b +
          (q * A) ^ 2 * dot F.z F.z - A) a := by
    unfold affineQuadratic quadraticEquation
    constructor <;> intro h <;> nlinarith
  rw [hquad]
  have hα : dot F.e₁ F.e₁ ≠ 0 := by
    intro hzero
    have hx : F.e₁.x = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.y, sq_nonneg F.e₁.z]
    have hy : F.e₁.y = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.x, sq_nonneg F.e₁.z]
    have hz : F.e₁.z = 0 := by
      simp [dot] at hzero
      nlinarith [sq_nonneg F.e₁.x, sq_nonneg F.e₁.y]
    have hdet := F.det_eq_one
    simp [det3, cross, dot, hx, hy, hz] at hdet
  rw [quadraticEquation_iff_root_certificate hα]
  rw [F.affineQuadratic_discriminant]

end OrthogonalFrame

end TunnellMap

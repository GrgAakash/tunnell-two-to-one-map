import TunnellMap.AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor

/-!
# The short-interval discriminant identity

This file formalizes Lemma 5.3's central polynomial identity.  It is the
algebraic reason that the ordered-adjacency generator scans a finite interval
of the second affine coordinate instead of an unrestricted rank-two lattice.
-/

namespace TunnellMap

/-- An integral square lies below `X` exactly when its argument lies between
the rational ceiling and floor obtained by dividing by a positive integer.
This is the rounding statement used in equation (5.8) of the manuscript. -/
theorem square_le_iff_mem_floorCeilInterval {n c X b : ℤ}
    (hn : 0 < n) (hX : 0 ≤ X) :
    (n * b - c) ^ 2 ≤ X ↔
      ⌈((c - Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((c + Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌋ := by
  rw [← Int.abs_le_sqrt_iff_sq_le hX, abs_le]
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [Int.ceil_le]
      apply (div_le_iff₀ hnq).2
      have h : c - Int.sqrt X ≤ n * b := by omega
      exact_mod_cast (show c - Int.sqrt X ≤ b * n by simpa [mul_comm] using h)
    · rw [Int.le_floor]
      apply (le_div_iff₀ hnq).2
      have h : n * b ≤ c + Int.sqrt X := by omega
      exact_mod_cast (show b * n ≤ c + Int.sqrt X by simpa [mul_comm] using h)
  · rintro ⟨hlower, hupper⟩
    rw [Int.ceil_le] at hlower
    rw [Int.le_floor] at hupper
    have hlower' := (div_le_iff₀ hnq).1 hlower
    have hupper' := (le_div_iff₀ hnq).1 hupper
    have hlowerInt : c - Int.sqrt X ≤ b * n := by exact_mod_cast hlower'
    have hupperInt : b * n ≤ c + Int.sqrt X := by exact_mod_cast hupper'
    have hlowerInt' : c - Int.sqrt X ≤ n * b := by
      simpa [mul_comm] using hlowerInt
    have hupperInt' : n * b ≤ c + Int.sqrt X := by
      simpa [mul_comm] using hupperInt
    constructor <;> omega

namespace OrthogonalFrame

variable {p : Triple} (F : OrthogonalFrame p)

def halfDiscriminant (A q b : ℤ) : ℤ :=
  let α := dot F.e₁ F.e₁
  let β := dot F.e₁ F.e₂
  let γ := dot F.e₂ F.e₂
  let δ := dot F.z F.e₁
  let ε := dot F.z F.e₂
  let ζ := dot F.z F.z
  let t := q * A
  (β * b + t * δ) ^ 2 -
    α * (γ * b ^ 2 + 2 * t * ε * b + t ^ 2 * ζ - A)

/-- Equation (5.7) in the manuscript: `n D_b = α M - (n b - t K)^2`. -/
theorem short_interval_identity (A q b : ℤ) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let n := dot p p
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    n * F.halfDiscriminant A q b = α * M - (n * b - t * K) ^ 2 := by
  dsimp [halfDiscriminant]
  have hg := F.gram_det
  have hc := F.gram_cubic_identity
  dsimp at hc
  rw [← hg]
  linear_combination
    (-dot F.e₁ F.e₁ * q ^ 2 * A ^ 2) * hc

/-- The exact floor/ceiling form of the finite `b`-interval in Lemma 5.3. -/
theorem halfDiscriminant_nonneg_iff_interval
    {n A q b : ℤ} (hn : 0 < n) (hpNorm : dot p p = n)
    (hAM :
      0 ≤ dot F.e₁ F.e₁ * (A * (n - q ^ 2 * A))) :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let t := q * A
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    0 ≤ F.halfDiscriminant A q b ↔
      ⌈((t * K - Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((t * K + Int.sqrt (α * M) : ℤ) : ℚ) / (n : ℚ)⌋ := by
  dsimp
  have hid := F.short_interval_identity A q b
  rw [hpNorm] at hid
  dsimp at hid
  have hsign :
      0 ≤ F.halfDiscriminant A q b ↔
        (n * b - q * A *
          (dot F.e₁ F.e₂ * dot F.z F.e₁ -
            dot F.e₁ F.e₁ * dot F.z F.e₂)) ^ 2 ≤
          dot F.e₁ F.e₁ * (A * (n - q ^ 2 * A)) := by
    constructor <;> intro h <;> nlinarith
  exact hsign.trans (square_le_iff_mem_floorCeilInterval hn hAM)

end OrthogonalFrame

end TunnellMap

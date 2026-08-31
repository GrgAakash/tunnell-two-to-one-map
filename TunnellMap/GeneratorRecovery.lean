import TunnellMap.MidpointRecord
import TunnellMap.OrthogonalFrameExistence
import TunnellMap.QuadraticRoots
import TunnellMap.TauLattice

/-!
# Recovery of every incident edge by the affine search

This file proves the completeness direction of the ordered-adjacency
generator.  Every preferred orbit edge supplies parameters in all finite
outer ranges, unique affine coordinates, and one of the certified quadratic
roots.
-/

namespace TunnellMap

theorem isHalfSum_unique {h₁ h₂ E F : Triple}
    (h₁sum : IsHalfSum h₁ E F) (h₂sum : IsHalfSum h₂ E F) : h₁ = h₂ := by
  rcases h₁sum with ⟨h₁x, h₁y, h₁z⟩
  rcases h₂sum with ⟨h₂x, h₂y, h₂z⟩
  apply Triple.ext <;> omega

theorem preferred_half_norm_lt {n : ℤ} (hn : Odd n)
    {s : BResidual n} {t : AResidual n} (R : PreferredMidpointRecord s t) :
    R.multiplier ^ 2 * qForm R.direction < n := by
  obtain ⟨hPlus, hMinus, hPlusEq, _hPlusOdd, hMinusEq, hMinusOdd⟩ :=
    midpoint_parity hn s.1 R.target.1
  have hPlusEqRecord : hPlus = R.half :=
    isHalfSum_unique hPlusEq R.half_sum
  subst hPlus
  have hsum := qForm_halfSum_add_halfDiff s R.target R.half hMinus
    R.half_sum hMinusEq
  have hminusPos : 0 < qForm hMinus :=
    qForm_pos_of_ne_zero (odd_third_ne_zero hMinusOdd)
  have hhalfNorm : qForm R.half = R.multiplier ^ 2 * qForm R.direction := by
    rw [R.half_decomposition, qForm_vsmul]
  nlinarith

structure GeneratorWitness {n : ℤ} (s : BResidual n) (t : AResidual n)
    (R : PreferredMidpointRecord s t) where
  frame : OrthogonalFrame (tau (residualSourceLift s))
  A : ℤ
  q : ℤ
  r : Triple
  a : ℤ
  b : ℤ
  u : ℤ
  A_eq : A = qForm R.direction
  q_eq : q = R.multiplier
  r_eq : r = tau R.direction
  A_pos : 0 < A
  A_bound : 2 * A ≤ n - 1
  q_odd : Odd q
  q_range : q ^ 2 * A < n
  r_tau_parity : InTauLattice r
  affine_coordinates :
    r = linComb3 a b (q * A) frame.e₁ frame.e₂ frame.z
  affine_norm : dot r r = A
  root_certificate :
    u ^ 2 = frame.halfDiscriminant A q b ∧
      dot frame.e₁ frame.e₁ * a =
        -(dot frame.e₁ frame.e₂ * b + q * A * dot frame.z frame.e₁) + u
  short_window :
    let α := dot frame.e₁ frame.e₁
    let β := dot frame.e₁ frame.e₂
    let δ := dot frame.z frame.e₁
    let ε := dot frame.z frame.e₂
    let K := β * δ - α * ε
    let M := A * (n - q ^ 2 * A)
    (n * b - q * A * K) ^ 2 ≤ α * M

/-- Every preferred residual edge has affine search data in any oriented
frame for the source normal.  Consequently the final generated list is
independent of the auxiliary frame. -/
theorem generatorWitness_with_frame {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) (R : PreferredMidpointRecord s t)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∃ W : GeneratorWitness s t R, W.frame = F := by
  let E := residualSourceLift s
  let d := R.direction
  let A := qForm d
  let q := R.multiplier
  let r := tau d
  have hdne : d ≠ ⟨0, 0, 0⟩ := odd_third_ne_zero R.direction_third_odd
  have hApos : 0 < A := qForm_pos_of_ne_zero hdne
  have hpNorm : dot (tau E) (tau E) = n := by
    rw [qForm_tau]
    simp [E, residualSourceLift]
  have hdot : dot (tau E) r = q * A := by
    calc
      dot (tau E) r = qBilinear E d := by
        simp [r, qBilinear]
      _ = q * qForm d := R.bilinear
      _ = q * A := rfl
  obtain ⟨ab, hab, _habUnique⟩ := F.affine_coset (q * A) r hdot
  let a := ab.1
  let b := ab.2
  have haffine : r = linComb3 a b (q * A) F.e₁ F.e₂ F.z := by
    simpa [a, b] using hab
  have hrnorm : dot r r = A := by
    simpa [r, A] using qForm_tau d
  obtain ⟨u, huSquare, huLinear⟩ :=
    (F.affine_norm_root_certificate A q a b).mp (by
      rw [← haffine]
      exact hrnorm)
  have hDnonneg : 0 ≤ F.halfDiscriminant A q b := by
    rw [← huSquare]
    exact sq_nonneg u
  have hshort := F.short_interval_identity A q b
  rw [hpNorm] at hshort
  dsimp at hshort
  have hnDnonneg : 0 ≤ n * F.halfDiscriminant A q b :=
    mul_nonneg (le_of_lt hnpos) hDnonneg
  have hwindow :
      let α := dot F.e₁ F.e₁
      let β := dot F.e₁ F.e₂
      let δ := dot F.z F.e₁
      let ε := dot F.z F.e₂
      let K := β * δ - α * ε
      let M := A * (n - q ^ 2 * A)
      (n * b - q * A * K) ^ 2 ≤ α * M := by
    dsimp
    nlinarith
  refine ⟨{
    frame := F
    A := A
    q := q
    r := r
    a := a
    b := b
    u := u
    A_eq := rfl
    q_eq := rfl
    r_eq := rfl
    A_pos := hApos
    A_bound := R.direction_bound
    q_odd := R.multiplier_odd
    q_range := preferred_half_norm_lt hn R
    r_tau_parity := tau_mem d
    affine_coordinates := haffine
    affine_norm := hrnorm
    root_certificate := ⟨huSquare, huLinear⟩
    short_window := hwindow }, rfl⟩

/-- Every preferred residual edge is recovered by the finite affine loops in
Algorithm 5.4. -/
theorem exists_generatorWitness {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    (hsquarefree : Squarefree n) (s : BResidual n) (t : AResidual n)
    (R : PreferredMidpointRecord s t) : Nonempty (GeneratorWitness s t R) := by
  have hpNorm : dot (tau (residualSourceLift s)) (tau (residualSourceLift s)) = n := by
    rw [qForm_tau]
    simp [residualSourceLift]
  obtain ⟨F⟩ := orthogonalFrame_exists_of_squarefree_norm hsquarefree hpNorm
  obtain ⟨W, _⟩ := generatorWitness_with_frame hn hnpos s t R F
  exact ⟨W⟩

end TunnellMap

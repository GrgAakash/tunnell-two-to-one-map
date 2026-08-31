import TunnellMap.GeneratorRecovery

/-!
# Soundness of reconstructed generator candidates

The affine search reconstructs a signed target as `-E + 2 q d`.  Its two
scalar equations imply that this target has the same quadratic norm as `E`.
The remaining congruence and residual conditions are the explicit filters in
the algorithm.
-/

namespace TunnellMap

def reconstructedTarget (E : Triple) (q : ℤ) (d : Triple) : Triple :=
  vadd (negTriple E) (vsmul (2 * q) d)

theorem qForm_reconstructedTarget (E : Triple) (q : ℤ) (d : Triple) :
    qForm (reconstructedTarget E q d) =
      qForm E - 4 * q * qBilinear E d + 4 * q ^ 2 * qForm d := by
  simp [reconstructedTarget, qForm, qBilinear, vadd, vsmul, negTriple]
  ring

theorem reconstructedTarget_same_norm {E d : Triple} {A q : ℤ}
    (hA : qForm d = A) (hB : qBilinear E d = q * A) :
    qForm (reconstructedTarget E q d) = qForm E := by
  rw [qForm_reconstructedTarget, hA, hB]
  ring

theorem reconstructedTarget_same_norm_of_tau {E d : Triple} {A q : ℤ}
    (hnorm : dot (tau d) (tau d) = A)
    (haffine : dot (tau E) (tau d) = q * A) :
    qForm (reconstructedTarget E q d) = qForm E := by
  apply reconstructedTarget_same_norm (A := A) (q := q)
  · exact (qForm_tau d).symm.trans hnorm
  · simpa [qBilinear] using haffine

theorem generatorWitness_reconstructs_target {n : ℤ} {s : BResidual n}
    {t : AResidual n} {R : PreferredMidpointRecord s t}
    (W : GeneratorWitness s t R) :
    residualTargetLift R.target =
      reconstructedTarget (residualSourceLift s) W.q R.direction := by
  rw [W.q_eq]
  exact R.target_formula

end TunnellMap

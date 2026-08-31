import TunnellMap.BlockGeneratorCorrect
import TunnellMap.CanonicalSignLift

/-!
# The sign stored in a generated record is the canonical edge sign

The executable generator of `TunnellMap.BlockGenerator` emits records
`(key, target, sign)` in which `target` is the canonical lift of a residual
target orbit and `sign` is the sign relating the reconstructed target to that
canonical lift.  This file proves that this stored sign is *exactly* the
manuscript's canonical edge sign `η` of `TunnellMap.canonicalEta`, so that the
sign-lift formula can be read off a generated record.

The key arithmetic step is `BlockGen.retained_plus_key_lt`: the retention test
of the generator states literally that the reconstructed edge is the one with
the smaller signed midpoint key, i.e. that its point-level `η` is `+1`.
-/

namespace TunnellMap

namespace BlockGen

open OrderedGenerator

variable {n : ℤ} {s : BResidual n}

/-- The reconstructed target of a generator index is the antipode of the
source, shifted by twice the retained midpoint direction; hence the plus
midpoint line of the resulting edge is that direction. -/
theorem plusVector_eq_vsmul_dValue
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex)
    {t : AResidual n} (ht : residualTargetLift t = targetValue s F i) :
    plusVector s t = vsmul (2 * i.q) (dValue F i) := by
  rw [plusVector, ht]
  unfold targetValue reconstructedTarget
  apply Triple.ext <;> simp [vadd, vsmul, negTriple]

/-- **The retention test is the manuscript's sign condition.**  The target
reconstructed at a retained index is the signed representative for which the
plus midpoint key is the smaller one. -/
theorem retained_plus_key_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hret : Retained s F i) {t : AResidual n}
    (ht : residualTargetLift t = targetValue s F i) :
    directionKey (plusVector s t) < directionKey (minusVector s t) := by
  obtain ⟨-, hgcd, horient, -, -, hkey⟩ := hret
  have hplus : plusVector s t = vsmul (2 * i.q) (dValue F i) :=
    plusVector_eq_vsmul_dValue F i ht
  have hne : plusVector s t ≠ ⟨0, 0, 0⟩ := plusVector_ne_zero s t
  have hq : (2 * i.q) ≠ 0 := by
    intro h0
    apply hne
    rw [hplus, h0]
    apply Triple.ext <;> simp [vsmul]
  have hd : dValue F i ≠ ⟨0, 0, 0⟩ := by
    intro h0
    apply hne
    rw [hplus, h0]
    apply Triple.ext <;> simp [vsmul]
  have h1 : directionKey (plusVector s t) = directionKey (dValue F i) := by
    rw [hplus, directionKey_vsmul hq hd]
  have h2 : primitiveKey (dValue F i) = directionKey (dValue F i) :=
    primitiveKey_eq_directionKey hgcd horient
  have hminus : minusVector s t =
      vsub (residualSourceLift s) (targetValue s F i) := by
    rw [minusVector, ht]
  have h3 : directionKeyExec (vsub (residualSourceLift s) (targetValue s F i)) =
      directionKey (minusVector s t) := by
    rw [← hminus]
    exact directionKeyExec_eq (minusVector_ne_zero s t)
  rw [h1, ← h2, ← h3]
  exact hkey

/-- The reconstructed target of a retained index is the canonical
representative of its orbit, multiplied by the sign stored in the record. -/
theorem target_eq_signAct_canonical (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex)
    {t : AResidual n} (ht : residualTargetLift t = targetValue s F i) :
    t = signActA hnpos ((recordOf s F i).sign)
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) := by
  have hspec : residualTargetLift t =
      vsmul (targetLiftSign (residualTargetLift t))
        (canonicalTargetLift (residualTargetLift t)) :=
    canonicalTargetLift_spec _
  have hsign : (recordOf s F i).sign = targetLiftSign (residualTargetLift t) := by
    rw [recordOf, ht]
  have hcanon : canonicalTargetLift (residualTargetLift t) =
      residualTargetLift (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) :=
    canonicalTargetLift_eq hnpos t
  rw [hsign]
  apply residualTargetLift_injective
  rcases targetLiftSign_mem (residualTargetLift t) with hm | hm
  · rw [hm, signActA_one]
    rw [hspec, hm, hcanon, vsmul_one]
  · rw [hm, signActA_neg_one, ← negTriple_residualTargetLift]
    rw [hspec, hm, hcanon, vsmul_neg_one]

/-- **The record sign is the canonical edge sign.**  For a retained index whose
record stores the canonical lift of the target orbit `o`, the stored sign is
`η` of the manuscript, computed from the two canonical representatives. -/
theorem recordOf_sign_eq_etaPoint (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {i : GeneratorIndex}
    (hret : Retained s F i) {o : (aResidualInvolution n hnpos).Orbit}
    (hrt : (recordOf s F i).target = orbitTargetLift hnpos o) :
    (recordOf s F i).sign =
      etaPoint s (canonicalAResidualRepresentative hnpos o) := by
  obtain ⟨t, ht⟩ :=
    (isResidualTargetLift_iff n (targetValue s F i)).mp hret.2.2.2.2.1
  have hrecTarget : (recordOf s F i).target =
      orbitTargetLift hnpos ((aResidualInvolution n hnpos).orbit t) := by
    show canonicalTargetLift (targetValue s F i) = _
    rw [← ht, canonicalTargetLift_eq hnpos t]
    rfl
  have horbit : (aResidualInvolution n hnpos).orbit t = o :=
    orbitTargetLift_injective hnpos (hrecTarget.symm.trans hrt)
  have hdecomp := target_eq_signAct_canonical hnpos F i ht
  rw [horbit] at hdecomp
  have hone : etaPoint s t = 1 :=
    (etaPoint_eq_one_iff s t).mpr (retained_plus_key_lt F hret ht)
  have hsm : (recordOf s F i).sign = 1 ∨ (recordOf s F i).sign = -1 :=
    recordOf_sign_eq_one_or_neg_one F i
  rw [hdecomp, etaPoint_signActA hnpos hsm] at hone
  rcases hsm with hm | hm <;> rw [hm] at hone ⊢ <;> omega

end BlockGen

end TunnellMap

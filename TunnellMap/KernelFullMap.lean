import TunnellMap.KernelPipeline
import TunnellMap.ComputableFullMap

/-!
# A kernel-reducible mirror of the executable full map

`paperTunnellMapExec` calls the residual pipeline, which runs
`RecordDA.run`; that recursion is well-founded, so the kernel cannot reduce it.
This file mirrors the whole assembled map with the fuel-driven `RecordDA.runK`
and proves the mirror equal to the original as soon as the fuel suffices.
-/

namespace TunnellMap

namespace RecordDA

open OrderedGenerator BlockGen

variable {n : ℤ}

/-- The fuel-driven terminal state of the executable run. -/
def terminalRunK (hsq : Squarefree n) (fuel : ℕ) : DARun n :=
  runK (framesExecK hsq) fuel (DARun.initial (sourceRosterExec n))

/-- The fuel condition: the state reached admits no further step. -/
def FuelSuffices (hsq : Squarefree n) (fuel : ℕ) : Prop :=
  (stepK (framesExecK hsq) (terminalRunK hsq fuel)).isNone = true

theorem terminalRunK_eq (hn : 0 ≤ n) (hsq : Squarefree n) (fuel : ℕ)
    (hfuel : FuelSuffices hsq fuel) :
    terminalRunK hsq fuel = terminalRunExec (framesExec hsq) := by
  rw [terminalRunK, runK_eq hn _ fuel _ (genStarted_initial _) hfuel,
    terminalRunExec, framesExecK_eq]

/-! ## The kernel-reducible residual map and its inverse -/

/-- Kernel-reducible form of `RecordDA.residualMapExec`. -/
def residualMapExecK (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ) (x : BResidual n) : AResidual n :=
  match (terminalRunK hsq fuel).assigned (canonicalBExec x) with
  | none => fallback
  | some r =>
      match aResidualOfTriple n r.target with
      | none => fallback
      | some F =>
          signActA hnpos
            (bResidualSignExec x * etaPointExec (canonicalBExec x) F) F

theorem residualMapExecK_eq (hn : 0 ≤ n) (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ) (hfuel : FuelSuffices hsq fuel)
    (x : BResidual n) :
    residualMapExecK hnpos hsq fallback fuel x =
      residualMapExec hnpos hsq fallback x := by
  rw [residualMapExecK, residualMapExec, terminalRunK_eq hn hsq fuel hfuel]
  rfl

/-- Kernel-reducible form of `RecordDA.inverseByRerunExec`. -/
def inverseByRerunExecK (hsq : Squarefree n) (fallback : BResidual n)
    (fuel : ℕ) (y : AResidual n) : BResidual n :=
  ((terminalRunK hsq fuel).held
      (canonicalTargetLift (residualTargetLift y))).elim fallback
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1

theorem inverseByRerunExecK_eq (hn : 0 ≤ n) (hsq : Squarefree n)
    (fallback : BResidual n) (fuel : ℕ) (hfuel : FuelSuffices hsq fuel)
    (y : AResidual n) :
    inverseByRerunExecK hsq fallback fuel y =
      inverseByRerunExec hsq fallback y := by
  rw [inverseByRerunExecK, inverseByRerunExec, terminalRunK_eq hn hsq fuel hfuel]

end RecordDA

/-! ## The kernel-reducible full map -/

variable {n : ℤ}

/-- Kernel-reducible form of `oddMapExec`. -/
def oddMapExecK (hnpos : 0 < n) (hsq : Squarefree n) (fallback : AResidual n)
    (fuel : ℕ) (q : BOddRep n) : ARep n :=
  if hd : SourceUsedTriple q.1 then
    (directMapExec q).getD fallback.1
  else
    (RecordDA.residualMapExecK hnpos hsq fallback fuel
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).1

theorem oddMapExecK_eq (hn : 0 ≤ n) (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ)
    (hfuel : RecordDA.FuelSuffices hsq fuel) (q : BOddRep n) :
    oddMapExecK hnpos hsq fallback fuel q = oddMapExec hnpos hsq fallback q := by
  unfold oddMapExecK oddMapExec
  by_cases hd : SourceUsedTriple q.1
  · rw [dif_pos hd, dif_pos hd]
  · rw [dif_neg hd, dif_neg hd,
      RecordDA.residualMapExecK_eq hn hnpos hsq fallback fuel hfuel]

/-- **The kernel-reducible full map.** -/
def paperTunnellMapExecK (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (fuel : ℕ) (p : BRep n) : ARep n :=
  if h : p.1.z % 2 = 0 then
    evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩)
  else
    oddMapExecK hnpos hsq fallback fuel ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩

theorem paperTunnellMapExecK_eq (hn : 0 ≤ n) (hnpos : 0 < n)
    (hsq : Squarefree n) (fallback : AResidual n) (fuel : ℕ)
    (hfuel : RecordDA.FuelSuffices hsq fuel) (p : BRep n) :
    paperTunnellMapExecK hnpos hsq fallback fuel p =
      paperTunnellMapExec hnpos hsq fallback p := by
  unfold paperTunnellMapExecK paperTunnellMapExec
  by_cases h : p.1.z % 2 = 0
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    exact oddMapExecK_eq hn hnpos hsq fallback fuel hfuel
      ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩

end TunnellMap

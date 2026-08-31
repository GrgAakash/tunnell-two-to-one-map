import TunnellMap.RecordDeferredAcceptanceCorrect
import TunnellMap.RecordSign

/-!
# Recovering the residual preimage by rerunning the computation

The manuscript recovers the inverse of the residual map at a target point by
*rerunning the same deterministic global computation* and then applying a local
sign calculation; no proposal transcript and no stored matching table is kept.

This file implements that literally.  `RecordDA.inverseByRerun`

* canonicalizes the given residual target point, obtaining its canonical orbit
  lift `F₀` and the sign `ρ` with `y = ρ F₀`;
* reruns the record-driven deferred-acceptance machine
  `RecordDA.run … (DARun.initial (sourceRoster n))`, whose proposals are
  generated one at a time by the executable one-block generator
  `BlockGen.advance`;
* looks up the record held at `F₀` in the state produced by that rerun,
  reading off the proposing source point `E₀` and the emitted sign `η`;
* returns the signed canonical source point `ρ η E₀`.

No step consults `Equiv.symm`, `Classical.choose`, `Quotient.out`, the
structural matching `residualOrbitMatching`, or a precomputed matching table:
the answer is produced by the deferred-acceptance run itself.  Equality with
the inverse of the structural equivalence is proved *afterwards*, in
`RecordDA.inverseByRerun_eq_residualEquiv_symm`.
-/

namespace TunnellMap

namespace RecordDA

open OrderedGenerator BlockGen GloballyRanked

variable {n : ℤ}

/-! ## Held records are generated records -/

/-- Every record held by a target was emitted by the proposer's generator. -/
def HeldGenerated (frames : FrameFamily n) (E : DARun n) : Prop :=
  ∀ v s' r', E.held v = some (s', r') → r' ∈ fullTrace s' (frames s')

theorem heldGenerated_initial (frames : FrameFamily n)
    (sources : List (BResidual n)) :
    HeldGenerated frames (DARun.initial sources) := by
  intro v s' r' h
  exact absurd h (by simp [DARun.initial])

section Fin

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

omit [Fintype (BOddRep n)] [Fintype (ARep n)] in
theorem heldGenerated_step (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} (hSim : Sim hnpos frames E)
    (hHG : HeldGenerated frames E) (h : step frames E = some E') :
    HeldGenerated frames E' := by
  by_cases hq0 : E.queue = []
  · rw [step_nil hq0] at h; exact absurd h (by simp)
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  by_cases hs : s ∈ E.sources
  · rcases hadv : BlockGen.advance s (frames s) (E.gen s) with _ | ⟨r, g⟩
    · rw [step_exhausted hq hs hadv] at h; exact absurd h (by simp)
    · have hrmem : r ∈ fullTrace s (frames s) := by
        have hcons : remainingTrace s (frames s) (E.gen s) =
            r :: remainingTrace s (frames s) g := advance_eq_some _ hadv
        have hmem : r ∈ remainingTrace s (frames s) (E.gen s) := by
          rw [hcons]; exact List.mem_cons_self
        exact (hSim.suffix s).subset hmem
      have hupd : ∀ E'' : DARun n,
          E''.held = Function.update E.held r.target (some (s, r)) →
          HeldGenerated frames E'' := by
        intro E'' hE'' v s' r' hv
        rw [hE''] at hv
        by_cases hvr : v = r.target
        · subst hvr
          rw [Function.update_self] at hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact hrmem
        · rw [Function.update_of_ne hvr] at hv
          exact hHG v s' r' hv
      rcases hheld : E.held r.target with _ | ⟨old, rold⟩
      · rw [step_accept hq hs hadv hheld] at h
        obtain rfl := Option.some.inj h
        exact hupd _ rfl
      · by_cases hlt : r.key < rold.key
        · rw [step_replace hq hs hadv hheld hlt] at h
          obtain rfl := Option.some.inj h
          exact hupd _ rfl
        · rw [step_reject hq hs hadv hheld hlt] at h
          obtain rfl := Option.some.inj h
          exact hHG
  · rw [step_not_source hq hs] at h; exact absurd h (by simp)

theorem heldGenerated_run (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    ∀ {E : DARun n}, Sim hnpos frames E → HeldGenerated frames E →
      HeldGenerated frames (run frames E) := by
  intro E
  induction E using run.induct (frames := frames) with
  | case1 E hstep =>
      intro _ hHG
      rw [run, hstep]
      exact hHG
  | case2 E E' hstep ih =>
      intro hSim hHG
      rw [run, hstep]
      exact ih (step_some_sim hn hnpos frames hSim hstep).1
        (heldGenerated_step hnpos frames hSim hHG hstep)

theorem heldGenerated_terminalRun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) : HeldGenerated frames (terminalRun frames) :=
  heldGenerated_run hn hnpos frames (sim_initial hnpos frames sourceRoster_canon)
    (heldGenerated_initial frames (sourceRoster n))

/-! ## The sign carried by the terminal held records -/

/-- **The terminal state stores the canonical edge sign.**  For every residual
source orbit `q`, the target orbit matched to `q` holds a record proposed by
the canonical representative of `q` whose stored sign is the manuscript's
canonical edge sign `η`. -/
theorem terminalRun_held_sign (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    ∃ r : IncidentRecord,
      (terminalRun frames).held
          (orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q)) =
          some (canonicalBResidualRepresentative q, r) ∧
        r.target =
          orbitTargetLift hnpos (residualOrbitMatching hnpos hcard q) ∧
        r.sign =
          canonicalEta hnpos q (residualOrbitMatching hnpos hcard q) := by
  obtain ⟨r, hheld, hrt, -⟩ := terminalRun_held hn hnpos frames hcard q
  refine ⟨r, hheld, hrt, ?_⟩
  have hmem := heldGenerated_terminalRun hn hnpos frames _ _ _ hheld
  obtain ⟨i, hi, rfl⟩ := (mem_fullTrace _ r).mp hmem
  have hret : Retained (canonicalBResidualRepresentative q)
      (frames (canonicalBResidualRepresentative q)) i :=
    (block_of_mem_validIndices _ hi).2.2.2
  exact recordOf_sign_eq_etaPoint hnpos _ hret hrt

/-! ## Determinism of the rerun -/

/-- Reachability by finitely many executable steps. -/
inductive Reaches (frames : FrameFamily n) : DARun n → DARun n → Prop
  | refl (E : DARun n) : Reaches frames E E
  | step {E E' E'' : DARun n} : step frames E = some E' →
      Reaches frames E' E'' → Reaches frames E E''

omit [Fintype (BOddRep n)] [Fintype (ARep n)] in
/-- **Determinism.**  Any terminating sequence of executable steps from a state
ends at exactly the state computed by `run`; in particular every rerun of the
machine from the canonical initial state regenerates the same held table, the
same records and the same signs. -/
theorem run_eq_of_reaches (frames : FrameFamily n) {E E' : DARun n}
    (hreach : Reaches frames E E') (hstop : step frames E' = none) :
    run frames E = E' := by
  induction hreach with
  | refl E => rw [run, hstop]
  | step hstep _ ih => rw [run, hstep]; dsimp only; exact ih hstop

end Fin

/-! ## The inverse by rerunning -/

variable [Fintype (BOddRep n)]

/-- **The inverse of the residual map, computed by rerunning.**  The target
point is canonicalized, the record-driven deferred-acceptance machine is rerun
from the canonical initial state, the record held by the canonical target lift
is located, and the signed canonical source point is reconstructed from the
stored proposer and sign.

The `fallback` argument makes the function total; under the hypotheses of
`inverseByRerun_apply` the lookup always succeeds, so the value never depends
on it. -/
noncomputable def inverseByRerun (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) : BResidual n :=
  ((run frames (DARun.initial (sourceRoster n))).held
      (canonicalTargetLift (residualTargetLift y))).elim fallback
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1

/-- The rerun performed by `inverseByRerun` is the canonical integrated run. -/
theorem inverseByRerun_rerun (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      ((terminalRun frames).held
          (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 :=
  rfl

section Inverse

variable [Fintype (ARep n)]

/-- The value of `inverseByRerun`, in the manuscript's notation
`ρ F₀ ↦ ρ η E₀`. -/
theorem inverseByRerun_apply (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      signActB (targetLiftSign (residualTargetLift y) *
          canonicalEta hnpos
            ((residualOrbitMatching hnpos hcard).symm
              ((aResidualInvolution n hnpos).orbit y))
            ((aResidualInvolution n hnpos).orbit y))
        (canonicalBResidualRepresentative
          ((residualOrbitMatching hnpos hcard).symm
            ((aResidualInvolution n hnpos).orbit y))) := by
  set M := residualOrbitMatching hnpos hcard with hM
  set o := (aResidualInvolution n hnpos).orbit y with ho
  obtain ⟨r, hheld, -, hsign⟩ := terminalRun_held_sign hn hnpos frames hcard
    (M.symm o)
  rw [Equiv.apply_symm_apply] at hheld hsign
  have hlift : canonicalTargetLift (residualTargetLift y) =
      orbitTargetLift hnpos o := canonicalTargetLift_eq hnpos y
  rw [inverseByRerun_rerun, hlift, hheld]
  simp only [Option.elim_some]
  rw [hsign]

omit [Fintype (ARep n)] in
/-- **The rerun really is a rerun.**  The record located by `inverseByRerun`
is the record held by the state reached by *any* terminating execution of the
executable machine from the canonical initial state. -/
theorem inverseByRerun_of_reaches (frames : FrameFamily n)
    (fallback : BResidual n) (y : AResidual n) {E : DARun n}
    (hreach : Reaches frames (DARun.initial (sourceRoster n)) E)
    (hstop : step frames E = none) :
    inverseByRerun frames fallback y =
      (E.held (canonicalTargetLift (residualTargetLift y))).elim fallback
        fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1 := by
  rw [inverseByRerun, run_eq_of_reaches frames hreach hstop]

/-- **First inverse identity.**  Rerunning the computation at the image of a
residual source point returns that point, signs included. -/
theorem inverseByRerun_canonicalResidualMap (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (x : BResidual n) :
    inverseByRerun frames fallback
        (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by
  set M := residualOrbitMatching hnpos hcard with hM
  set q := (bResidualInvolution n).orbit x with hq
  set F := canonicalAResidualRepresentative hnpos (M q) with hF
  set sigma := bResidualSign x with hsigma
  set eta := canonicalEta hnpos q (M q) with heta
  have hsm : sigma = 1 ∨ sigma = -1 := bResidualSign_mem x
  have hem : eta = 1 ∨ eta = -1 := canonicalEta_mem hnpos q (M q)
  have hprod : sigma * eta = 1 ∨ sigma * eta = -1 := by
    rcases hsm with h | h <;> rcases hem with h' | h' <;> rw [h, h'] <;> norm_num
  have hy : canonicalResidualMapOf hnpos M x = signActA hnpos (sigma * eta) F := rfl
  have horb : (aResidualInvolution n hnpos).orbit
      (canonicalResidualMapOf hnpos M x) = M q := by
    rw [hy, orbit_signActA, hF, orbit_canonicalAResidualRepresentative]
  have hrho : targetLiftSign
      (residualTargetLift (canonicalResidualMapOf hnpos M x)) = sigma * eta := by
    refine (aResidualInvolution n hnpos).signAct_inj_sign
      (x := F) (targetLiftSign_mem _) hprod ?_
    have hdec := residualTarget_decomposition hnpos (canonicalResidualMapOf hnpos M x)
    rw [horb, ← hF] at hdec
    show signActA hnpos _ F = signActA hnpos (sigma * eta) F
    rw [hdec, hy]
  rw [inverseByRerun_apply hn hnpos frames hcard, horb, hrho,
    Equiv.symm_apply_apply, ← heta, mul_assoc]
  rcases hem with h | h <;> rw [h] <;> norm_num <;>
    exact bResidual_decomposition x

/-- **Second inverse identity.**  The canonical residual map sends the point
recovered by rerunning back to the given residual target point. -/
theorem canonicalResidualMap_inverseByRerun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
        (inverseByRerun frames fallback y) = y := by
  set M := residualOrbitMatching hnpos hcard with hM
  set o := (aResidualInvolution n hnpos).orbit y with ho
  set q := M.symm o with hqdef
  set rho := targetLiftSign (residualTargetLift y) with hrho
  set eta := canonicalEta hnpos q o with heta
  have hMq : M q = o := Equiv.apply_symm_apply M o
  have hrm : rho = 1 ∨ rho = -1 := targetLiftSign_mem _
  have hem : eta = 1 ∨ eta = -1 := canonicalEta_mem hnpos q o
  have hprod : rho * eta = 1 ∨ rho * eta = -1 := by
    rcases hrm with h | h <;> rcases hem with h' | h' <;> rw [h, h'] <;> norm_num
  have hx : inverseByRerun frames fallback y =
      signActB (rho * eta) (canonicalBResidualRepresentative q) := by
    rw [inverseByRerun_apply hn hnpos frames hcard]
  rw [hx, canonicalResidualMapOf_signAct hnpos M q hprod, hMq, ← heta, mul_assoc]
  have hdec := residualTarget_decomposition hnpos y
  rw [← ho, ← hrho] at hdec
  rcases hem with h | h <;> rw [h] <;> norm_num <;> exact hdec

/-- **Agreement with the structural inverse.**  After being defined and
verified independently, `inverseByRerun` is extensionally the inverse of the
pre-existing residual equivalence. -/
theorem inverseByRerun_eq_residualEquiv_symm (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  apply (residualEquivOfOrbitCard hnpos hcard).injective
  rw [Equiv.apply_symm_apply,
    ← canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard]
  exact canonicalResidualMap_inverseByRerun hn hnpos frames hcard fallback y

/-- The canonical residual map is a bijection with `inverseByRerun` as its
two-sided inverse. -/
theorem canonicalResidualMap_bijective (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) :
    Function.Bijective
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨inverseByRerun frames fallback,
      inverseByRerun_canonicalResidualMap hn hnpos frames hcard fallback,
      canonicalResidualMap_inverseByRerun hn hnpos frames hcard fallback⟩

end Inverse

end RecordDA

end TunnellMap

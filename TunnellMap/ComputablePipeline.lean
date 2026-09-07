import TunnellMap.ComputableRoster
import TunnellMap.InverseByRerun
import TunnellMap.LagrangeGauss
import TunnellMap.DeterministicFrame

/-!
# The executable end-to-end residual pipeline

Everything the manuscript's residual construction needs is assembled here as
ordinary computable `def`s:

* `RecordDA.framesExec` attaches the *computed* reduced orthogonal frame
  (`reduceFrame (orthogonalFrameExec …)`) to every residual source;
* `RecordDA.terminalRunExec` runs the record-driven deferred-acceptance
  machine from the *computed* roster `sourceRosterExec`;
* `RecordDA.residualMapExec` reads the forward value off the terminal state
  and applies the canonical sign lift;
* `RecordDA.inverseByRerunExec` recovers the preimage by rerunning the very
  same computation.

None of these declarations is `noncomputable`; classical reasoning appears
only inside proofs.  The agreement theorems with the structural objects
(`canonicalResidualMapOf`, `inverseByRerun`, `sourceRoster`) are proved
*after* the definitions.
-/

namespace TunnellMap

namespace RecordDA

open OrderedGenerator BlockGen

variable {n : ℤ}

/-! ## The computable frame family -/

/-- A residual source lift has squared norm `n`. -/
theorem dot_tau_residualSourceLift (s : BResidual n) :
    dot (tau (residualSourceLift s)) (tau (residualSourceLift s)) = n := by
  rw [qForm_tau]
  simp [residualSourceLift]

/-- Squarefreeness of `n` makes every residual source lift primitive. -/
theorem tripleGCD_tau_residualSourceLift (hsq : Squarefree n) (s : BResidual n) :
    tripleGCD (tau (residualSourceLift s)) = 1 :=
  tripleGCD_eq_one_of_squarefree_norm hsq (dot_tau_residualSourceLift s)

/-- **The computed frame at a residual source.**  The extended-Euclidean frame
of `TunnellMap.DeterministicFrame` is built from the source lift and then
Lagrange–Gauss reduced.  No choice is involved. -/
def frameExec (hsq : Squarefree n) (s : BResidual n) :
    OrthogonalFrame (tau (residualSourceLift s)) :=
  reduceFrame (orthogonalFrameExec (tau (residualSourceLift s))
    (tripleGCD_tau_residualSourceLift hsq s))

/-- **The computable frame family** consumed by `BlockGen` and `RecordDA`. -/
def framesExec (hsq : Squarefree n) : FrameFamily n := frameExec hsq

@[simp] theorem framesExec_apply (hsq : Squarefree n) (s : BResidual n) :
    framesExec hsq s = frameExec hsq s := rfl

/-- The computed frame is Lagrange–Gauss reduced. -/
theorem isLagrangeGaussReduced_frameExec (hsq : Squarefree n) (s : BResidual n) :
    IsLagrangeGaussReduced (frameExec hsq s) :=
  isLagrangeGaussReduced_reduceFrame _

/-- The computed frame family is deterministic: it does not depend on the
proof of squarefreeness. -/
theorem framesExec_deterministic (hsq hsq' : Squarefree n) :
    framesExec hsq = framesExec hsq' := rfl

/-! ## The computed frame family satisfies the generator hypotheses -/

section FrameHypotheses

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- **The computed frame generates the manuscript's preference row.**  This is
the hypothesis `BlockGen` and `RecordDA` require of a frame family: the
incident stream produced from it is the globally ranked preference list of the
source orbit.  It replaces the `Classical.choice` frame of
`canonicalIncidentStream_eq_preferenceList`. -/
theorem canonicalIncidentStream_framesExec_eq_preferenceList
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (q : (bResidualInvolution n).Orbit) :
    incidentStream hnpos (canonicalBResidualRepresentative q)
        (framesExec hsq (canonicalBResidualRepresentative q)) =
      (residualOrbitRanking hnpos).preferenceList q := by
  rw [incidentStream_eq_preferenceList hn hnpos]
  congr 1
  simpa [canonicalBResidualRepresentative] using
    (bResidualInvolution n).orbit_canonicalRepresentative
      bResidualLexKey bResidualLexKey_injective q

end FrameHypotheses

/-! ## The computable terminal state -/

/-- **The executable integrated run**, started from the computed roster. -/
def terminalRunExec (frames : FrameFamily n) : DARun n :=
  run frames (DARun.initial (sourceRosterExec n))

theorem terminalRunExec_eq [Fintype (BOddRep n)] (frames : FrameFamily n) :
    terminalRunExec frames = terminalRun frames := by
  rw [terminalRunExec, terminalRun, sourceRosterExec_eq_sourceRoster]

/-- The one-block storage invariant holds throughout the executable run. -/
theorem oneBlockAll_terminalRunExec (frames : FrameFamily n) :
    OneBlockAll frames (terminalRunExec frames) :=
  oneBlockAll_run frames (oneBlockAll_initial frames (sourceRosterExec n))

section TerminalExec

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- **The executable run computes the structural stable matching.** -/
theorem runMatching_framesExec_eq (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    runMatching hn hnpos (framesExec hsq) hcard =
      residualOrbitMatching hnpos hcard :=
  runMatching_eq hn hnpos (framesExec hsq) hcard

/-- **The executable run terminates with an empty queue**, i.e. with every
source assigned. -/
theorem terminalRunExec_queue_nil (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (terminalRunExec frames).queue = [] := by
  rw [terminalRunExec_eq]
  exact terminalRun_queue_nil hn hnpos frames hcard

end TerminalExec

/-! ## Executable canonicalization of residual sources -/

/-- The executable canonical representative of the antipodal orbit of a
residual source. -/
def canonicalBExec (x : BResidual n) : BResidual n :=
  if tripleLexLtExec x.1.1 (negBResidual x).1.1 then x else negBResidual x

/-- The executable sign relating a residual source to the canonical
representative of its orbit. -/
def bResidualSignExec (x : BResidual n) : ℤ :=
  if tripleLexLtExec x.1.1 (negBResidual x).1.1 then 1 else -1

theorem canonicalBExec_eq (x : BResidual n) :
    canonicalBExec x =
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) := by
  show _ = (bResidualInvolution n).canonicalPoint bResidualLexKey x
  have hneg : (bResidualInvolution n).neg x = negBResidual x := rfl
  unfold canonicalBExec FreeInvolution.canonicalPoint bResidualLexKey
  rw [hneg]
  by_cases h : tripleLexLtExec x.1.1 (negBResidual x).1.1 = true
  · rw [if_pos h, if_pos ((tripleLexLtExec_iff _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((tripleLexLtExec_iff _ _).mpr hc))]

theorem bResidualSignExec_eq (x : BResidual n) :
    bResidualSignExec x = bResidualSign x := by
  show _ = (bResidualInvolution n).signOf bResidualLexKey x
  have hneg : (bResidualInvolution n).neg x = negBResidual x := rfl
  unfold bResidualSignExec FreeInvolution.signOf bResidualLexKey
  rw [hneg]
  by_cases h : tripleLexLtExec x.1.1 (negBResidual x).1.1 = true
  · rw [if_pos h, if_pos ((tripleLexLtExec_iff _ _).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((tripleLexLtExec_iff _ _).mpr hc))]

/-! ## Executable recognition of residual targets -/

/-- The residual target whose lift is the given triple, if there is one. -/
def aResidualOfTriple (n : ℤ) (v : Triple) : Option (AResidual n) :=
  if h : IsResidualTargetLift n v then
    some ⟨⟨⟨v.x, v.y, v.z / 4⟩, h.2.1⟩, fun hc =>
      h.2.2 ((directTargetUsed_iff
        (⟨⟨v.x, v.y, v.z / 4⟩, h.2.1⟩ : ARep n)).mp hc)⟩
  else none

theorem aResidualOfTriple_residualTargetLift (t : AResidual n) :
    aResidualOfTriple n (residualTargetLift t) = some t := by
  have hmem : IsResidualTargetLift n (residualTargetLift t) :=
    (isResidualTargetLift_iff n _).mpr ⟨t, rfl⟩
  unfold aResidualOfTriple
  rw [dif_pos hmem]
  have h4 : (4 * t.1.1.z) / 4 = t.1.1.z := by omega
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  apply Triple.ext <;> simp [residualTargetLift, aLift, h4]

/-! ## The executable forward residual map -/

/-- **The executable residual map.**  The source is canonicalized, the record
assigned to its canonical representative by the executable run is read off,
the target lift stored in that record is decoded, and the manuscript's
canonical sign lift is applied.

The `fallback` argument makes the function total; under the hypotheses of
`residualMapExec_eq` the lookups always succeed. -/
def residualMapExec (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (x : BResidual n) : AResidual n :=
  match (terminalRunExec (framesExec hsq)).assigned (canonicalBExec x) with
  | none => fallback
  | some r =>
      match aResidualOfTriple n r.target with
      | none => fallback
      | some F =>
          signActA hnpos
            (bResidualSignExec x * etaPointExec (canonicalBExec x) F) F

section Agreement

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- **Agreement of the executable forward map with the canonical residual
map.** -/
theorem residualMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x := by
  set M := residualOrbitMatching hnpos hcard with hM
  set q := (bResidualInvolution n).orbit x with hq
  set F := canonicalAResidualRepresentative hnpos (M q) with hF
  obtain ⟨r, hassign, hrt⟩ :=
    terminalRun_assigned hn hnpos (framesExec hsq) hcard q
  have hE : canonicalBExec x = canonicalBResidualRepresentative q :=
    canonicalBExec_eq x
  have hassign' : (terminalRunExec (framesExec hsq)).assigned
      (canonicalBExec x) = some r := by
    rw [terminalRunExec_eq, hE]; exact hassign
  have hdecode : aResidualOfTriple n r.target = some F := by
    rw [hrt]
    exact aResidualOfTriple_residualTargetLift F
  rw [residualMapExec, hassign']
  dsimp only
  rw [hdecode]
  dsimp only
  rw [etaPointExec_eq, bResidualSignExec_eq, hE]
  rfl

end Agreement

/-! ## The executable inverse -/

/-- **The executable inverse of the residual map.**  The residual target is
canonicalized and the *same* computation is rerun; the record held at the
canonical target lift supplies the proposing source and its sign. -/
def inverseByRerunExec (hsq : Squarefree n) (fallback : BResidual n)
    (y : AResidual n) : BResidual n :=
  ((terminalRunExec (framesExec hsq)).held
      (canonicalTargetLift (residualTargetLift y))).elim fallback
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1

section Inverse

variable [Fintype (BOddRep n)]

/-- **Agreement of the executable inverse with `inverseByRerun`.** -/
theorem inverseByRerunExec_eq (hsq : Squarefree n) (fallback : BResidual n)
    (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      inverseByRerun (framesExec hsq) fallback y := by
  rw [inverseByRerunExec, inverseByRerun_rerun, terminalRunExec_eq]

section WithTargets

variable [Fintype (ARep n)]

/-- **First inverse identity for the executable pair.** -/
theorem inverseByRerunExec_residualMapExec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) (x : BResidual n) :
    inverseByRerunExec hsq fallbackB (residualMapExec hnpos hsq fallbackA x) = x := by
  rw [residualMapExec_eq hn hnpos hsq hcard, inverseByRerunExec_eq]
  exact inverseByRerun_canonicalResidualMap hn hnpos (framesExec hsq) hcard
    fallbackB x

/-- **Second inverse identity for the executable pair.** -/
theorem residualMapExec_inverseByRerunExec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) (y : AResidual n) :
    residualMapExec hnpos hsq fallbackA (inverseByRerunExec hsq fallbackB y) = y := by
  rw [residualMapExec_eq hn hnpos hsq hcard, inverseByRerunExec_eq]
  exact canonicalResidualMap_inverseByRerun hn hnpos (framesExec hsq) hcard
    fallbackB y

/-- **The executable residual map is a bijection**, with the executable
rerun inverse as its two-sided inverse. -/
theorem residualMapExec_bijective (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) :
    Function.Bijective (residualMapExec hnpos hsq fallbackA) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨inverseByRerunExec hsq fallbackB,
      inverseByRerunExec_residualMapExec hn hnpos hsq hcard fallbackA fallbackB,
      residualMapExec_inverseByRerunExec hn hnpos hsq hcard fallbackA fallbackB⟩

/-- The executable inverse agrees with the inverse of the structural
equivalence. -/
theorem inverseByRerunExec_eq_residualEquiv_symm (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  rw [inverseByRerunExec_eq]
  exact inverseByRerun_eq_residualEquiv_symm hn hnpos (framesExec hsq) hcard
    fallback y

/-- The executable forward map agrees with the structural residual
equivalence. -/
theorem residualMapExec_eq_residualEquiv (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      residualEquivOfOrbitCard hnpos hcard x := by
  rw [residualMapExec_eq hn hnpos hsq hcard,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard]

end WithTargets

end Inverse

end RecordDA

end TunnellMap

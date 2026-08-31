import TunnellMap.ComputableFullMap

/-!
# The fallback-free executable map

`paperTunnellMapExec` is total because it is handed a `fallback : AResidual n`
to return in the two lookup situations that the theorem's hypotheses exclude.
That extra argument is *stronger than the manuscript hypotheses*: when the
residual sets are empty — for instance at `n = 5`, where `BRep 5` and `ARep 5`
are both empty and the balance holds trivially — the type `AResidual n` is
uninhabited and no fallback can be supplied at all.

This file removes the fallback from the public interface.  The pipeline is run
into an `Option`,

* `RecordDA.residualMapExecOpt`, `oddMapExecOpt`, `paperTunnellMapExecOpt`,

and the successful decoding of that `Option` is *proved* from the manuscript
hypotheses (`Odd n`, `0 < n`, `Squarefree n` and the cardinality balance).  The
public map

* `paperTunnellMapTotal`

is then an ordinary computable `def` taking exactly those hypotheses; it agrees
with `paperTunnellMap`, and every target has exactly two preimages under it.
The balance hypothesis is stated with `Nat.card`, so the definition mentions no
`Fintype` instance; the noncomputable instances appear only inside proofs.
-/

namespace TunnellMap

variable {n : ℤ}

namespace RecordDA

/-! ## The residual branch, as an `Option` -/

/-- **The executable residual map, without a fallback.**  Exactly the
computation of `residualMapExec`, returning `none` instead of a default value
when a lookup fails. -/
def residualMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (x : BResidual n) :
    Option (AResidual n) :=
  match (terminalRunExec (framesExec hsq)).assigned (canonicalBExec x) with
  | none => none
  | some r =>
      match aResidualOfTriple n r.target with
      | none => none
      | some F =>
          some (signActA hnpos
            (bResidualSignExec x * etaPointExec (canonicalBExec x) F) F)

/-- The fallback version is the `Option` version with a default. -/
theorem residualMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      (residualMapExecOpt hnpos hsq x).getD fallback := by
  unfold residualMapExec residualMapExecOpt
  cases (terminalRunExec (framesExec hsq)).assigned (canonicalBExec x) with
  | none => simp
  | some r =>
      rcases hd : aResidualOfTriple n r.target with _ | F
      · simp [hd]
      · simp [hd]

section Agreement

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- **The residual lookups succeed** under the manuscript hypotheses, and the
decoded value is the canonical residual map. -/
theorem residualMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    residualMapExecOpt hnpos hsq x =
      some (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) := by
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
  rw [residualMapExecOpt, hassign']
  dsimp only
  rw [hdecode]
  dsimp only
  rw [etaPointExec_eq, bResidualSignExec_eq, hE]
  rfl

/-- **The public executable residual map.**  This is the successful value of
the option-valued residual computation.  The proof argument certifies that the
lookup cannot fail under the residual balance hypothesis. -/
def residualMapExecTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) : AResidual n :=
  (residualMapExecOpt hnpos hsq x).get (by
    rw [residualMapExecOpt_eq_some hn hnpos hsq hcard x]
    rfl)

/-- The fallback-free executable residual map agrees with the structural
residual correspondence. -/
theorem residualMapExecTotal_eq_canonical (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    residualMapExecTotal hn hnpos hsq hcard x =
      canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x := by
  apply Option.some.inj
  exact (Option.some_get (by
      rw [residualMapExecOpt_eq_some hn hnpos hsq hcard x]
      rfl)).trans
    (residualMapExecOpt_eq_some hn hnpos hsq hcard x)

end Agreement

/-! ## The residual inverse, without a fallback -/

/-- **The executable rerun inverse, without a fallback.**  The target is
canonicalized and the same terminal computation is inspected; failure is
reported as `none`. -/
def inverseByRerunExecOpt (hsq : Squarefree n) (y : AResidual n) :
    Option (BResidual n) :=
  ((terminalRunExec (framesExec hsq)).held
      (canonicalTargetLift (residualTargetLift y))).map
    fun p => signActB (targetLiftSign (residualTargetLift y) * p.2.sign) p.1

section InverseAgreement

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- Under the residual balance hypothesis, the rerun lookup succeeds and
returns the signed canonical source recorded at the matched target. -/
theorem inverseByRerunExecOpt_eq_some_value (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    inverseByRerunExecOpt hsq y =
      some (signActB (targetLiftSign (residualTargetLift y) *
          canonicalEta hnpos
            ((residualOrbitMatching hnpos hcard).symm
              ((aResidualInvolution n hnpos).orbit y))
            ((aResidualInvolution n hnpos).orbit y))
        (canonicalBResidualRepresentative
          ((residualOrbitMatching hnpos hcard).symm
            ((aResidualInvolution n hnpos).orbit y)))) := by
  set M := residualOrbitMatching hnpos hcard with hM
  set o := (aResidualInvolution n hnpos).orbit y with ho
  obtain ⟨r, hheld, -, hsign⟩ :=
    terminalRun_held_sign hn hnpos (framesExec hsq) hcard (M.symm o)
  rw [Equiv.apply_symm_apply] at hheld hsign
  have hlift : canonicalTargetLift (residualTargetLift y) =
      BlockGen.orbitTargetLift hnpos o := canonicalTargetLift_eq hnpos y
  rw [inverseByRerunExecOpt, terminalRunExec_eq, hlift, hheld]
  simp only [Option.map_some]
  rw [hsign]

/-- The fallback-free rerun lookup succeeds under the residual balance
hypothesis. -/
theorem inverseByRerunExecOpt_isSome (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    (inverseByRerunExecOpt hsq y).isSome = true := by
  rw [inverseByRerunExecOpt_eq_some_value hn hnpos hsq hcard y]
  rfl

/-- **The public executable residual inverse.**  This is an ordinary
computable definition obtained by rerunning the same deterministic machine;
the proof argument certifies that its lookup cannot fail. -/
def inverseByRerunExecTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) : BResidual n :=
  (inverseByRerunExecOpt hsq y).get
    (inverseByRerunExecOpt_isSome hn hnpos hsq hcard y)

/-- The fallback-free executable inverse agrees with the inverse of the
structural residual equivalence. -/
theorem inverseByRerunExecTotal_eq_residualEquiv_symm
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  let z := inverseByRerunExecTotal hn hnpos hsq hcard y
  have hsame : z = inverseByRerunExec hsq z y := by
    rw [inverseByRerunExec_eq, inverseByRerun_apply hn hnpos (framesExec hsq) hcard]
    apply Option.some.inj
    exact (Option.some_get
      (inverseByRerunExecOpt_isSome hn hnpos hsq hcard y)).trans
      (inverseByRerunExecOpt_eq_some_value hn hnpos hsq hcard y)
  change z = (residualEquivOfOrbitCard hnpos hcard).symm y
  exact hsame.trans
    (inverseByRerunExec_eq_residualEquiv_symm hn hnpos hsq hcard z y)

/-- First inverse identity for the fallback-free executable inverse. -/
theorem inverseByRerunExecTotal_residualMapExecOpt
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by
  rw [inverseByRerunExecTotal_eq_residualEquiv_symm,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard,
    Equiv.symm_apply_apply]

/-- Second inverse identity for the fallback-free executable inverse. -/
theorem residualMapExecOpt_inverseByRerunExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by
  rw [inverseByRerunExecTotal_eq_residualEquiv_symm,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard,
    Equiv.apply_symm_apply]

/-- First inverse identity for the two public fallback-free residual
interfaces. -/
theorem inverseByRerunExecTotal_residualMapExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (residualMapExecTotal hn hnpos hsq hcard x) = x := by
  rw [residualMapExecTotal_eq_canonical,
    inverseByRerunExecTotal_residualMapExecOpt]

/-- Second inverse identity for the two public fallback-free residual
interfaces. -/
theorem residualMapExecTotal_inverseByRerunExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    residualMapExecTotal hn hnpos hsq hcard
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by
  rw [residualMapExecTotal_eq_canonical,
    residualMapExecOpt_inverseByRerunExecTotal]

end InverseAgreement

end RecordDA

/-! ## The odd branch, as an `Option` -/

/-- **The executable odd branch, without a fallback.** -/
def oddMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (q : BOddRep n) :
    Option (ARep n) :=
  if hd : SourceUsedTriple q.1 then
    directMapExec q
  else
    (RecordDA.residualMapExecOpt hnpos hsq
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).map Subtype.val

theorem oddMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q =
      (oddMapExecOpt hnpos hsq q).getD fallback.1 := by
  unfold oddMapExec oddMapExecOpt
  by_cases hd : SourceUsedTriple q.1
  · rw [dif_pos hd, dif_pos hd]
  · rw [dif_neg hd, dif_neg hd, RecordDA.residualMapExec_eq_getD]
    cases RecordDA.residualMapExecOpt hnpos hsq
      (⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩ : BResidual n) <;> rfl

section OddAgreement

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- **The odd branch always decodes** under the manuscript hypotheses, and its
value is the structural odd equivalence. -/
theorem oddMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n)) (q : BOddRep n) :
    oddMapExecOpt hnpos hsq q = some (oddEquivOfBalance hn hnpos hbal q) := by
  by_cases hd : DirectSourceUsed q
  · have hd' : SourceUsedTriple q.1 := (directSourceUsed_iff q).mp hd
    rw [oddEquivOfBalance_apply_direct hn hnpos hbal q hd, oddMapExecOpt,
      dif_pos hd', directMapExec_eq hn q hd]
  · have hd' : ¬ SourceUsedTriple q.1 := fun hc =>
      hd ((directSourceUsed_iff q).mpr hc)
    rw [oddEquivOfBalance_apply_residual hn hnpos hbal q hd, oddMapExecOpt,
      dif_neg hd', RecordDA.residualMapExecOpt_eq_some hn hnpos hsq
        (residual_orbit_card_eq hn hnpos hbal)]
    rw [Option.map_some]
    congr 1
    exact congrArg Subtype.val
      (canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos
        (residual_orbit_card_eq hn hnpos hbal) _)

end OddAgreement

/-! ## The full map, as an `Option` -/

/-- **The executable full map, without a fallback.** -/
def paperTunnellMapExecOpt (hnpos : 0 < n) (hsq : Squarefree n) (p : BRep n) :
    Option (ARep n) :=
  if h : p.1.z % 2 = 0 then
    some (evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩))
  else
    oddMapExecOpt hnpos hsq ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩

theorem paperTunnellMapExec_eq_getD (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      (paperTunnellMapExecOpt hnpos hsq p).getD fallback.1 := by
  unfold paperTunnellMapExec paperTunnellMapExecOpt
  by_cases h : p.1.z % 2 = 0
  · rw [dif_pos h, dif_pos h, Option.getD_some]
  · rw [dif_neg h, dif_neg h, oddMapExec_eq_getD]

section FullAgreement

variable [Fintype (BRep n)] [Fintype (ARep n)]

/-- **The full map always decodes** under the manuscript hypotheses, and its
value is `paperTunnellMap`. -/
theorem paperTunnellMapExecOpt_eq_some (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (p : BRep n) :
    paperTunnellMapExecOpt hnpos hsq p =
      some (paperTunnellMap hn hnpos hbalance p) := by
  classical
  show _ = some (conditionalTunnellMap (paperOddEquiv hn hnpos hbalance)
    ((Equiv.sumCongr (evenRepParamEquiv n)
        ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
          (bOddSubtypeEquiv n)))
      ((Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm p)))
  by_cases h : p.1.z % 2 = 0
  · have he : (fun p : BRep n => Even p.1.z) p := Int.even_iff.mpr h
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExecOpt, dif_pos h]
    rfl
  · have he : ¬ (fun p : BRep n => Even p.1.z) p := fun hc => h (Int.even_iff.mp hc)
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExecOpt, dif_neg h]
    show oddMapExecOpt hnpos hsq _ =
      some (paperOddEquiv hn hnpos hbalance ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩)
    exact oddMapExecOpt_eq_some hn hnpos hsq (odd_card_eq_of_full_balance hbalance) _

end FullAgreement

/-! ## The public fallback-free map -/

/-- The `Nat.card` form of the balance hypothesis — the form in which the
public map states it, so that its definition mentions no `Fintype` instance —
gives the `Fintype.card` form used by the structural theory. -/
theorem fintype_balance_of_nat_card
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Fintype.card (BRep n) = 2 * Fintype.card (ARep n) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hbal

/-- **The full map always decodes** under exactly the manuscript
hypotheses. -/
theorem paperTunnellMapExecOpt_isSome (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    (paperTunnellMapExecOpt hnpos hsq p).isSome = true := by
  rw [paperTunnellMapExecOpt_eq_some hn hnpos hsq
    (fintype_balance_of_nat_card hbal) p]
  rfl

/-- **The public executable map of Theorem 1.1.**  An ordinary computable
`def` requiring exactly the manuscript hypotheses: `n` odd, positive and
squarefree, and the cardinality balance `|BRep n| = 2 |ARep n|`.  No fallback
residual target is required, so the definition also makes sense — and is
used — when the residual sets are empty. -/
def paperTunnellMapTotal (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) : ARep n :=
  (paperTunnellMapExecOpt hnpos hsq p).get
    (paperTunnellMapExecOpt_isSome hn hnpos hsq hbal p)

theorem some_paperTunnellMapTotal (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) :
    some (paperTunnellMapTotal hn hnpos hsq hbal p) =
      paperTunnellMapExecOpt hnpos hsq p :=
  Option.some_get _

/-- **The public map agrees with `paperTunnellMap`.** -/
theorem paperTunnellMapTotal_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMap hn hnpos (fintype_balance_of_nat_card hbal) p :=
  Option.some.inj
    ((some_paperTunnellMapTotal hn hnpos hsq hbal p).trans
      (paperTunnellMapExecOpt_eq_some hn hnpos hsq
        (fintype_balance_of_nat_card hbal) p))

/-- **The public map agrees with the fallback version** wherever the latter is
defined, i.e. for every choice of fallback residual target. -/
theorem paperTunnellMapTotal_eq_exec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMapExec hnpos hsq fallback p := by
  rw [paperTunnellMapTotal_eq hn hnpos hsq hbal,
    paperTunnellMapExec_eq hn hnpos hsq (fintype_balance_of_nat_card hbal)]

/-- **Exactly two preimages, without a fallback.**  Every target
representation has exactly two preimages under the public map, under exactly
the manuscript hypotheses. -/
theorem paperTunnellMapTotal_exactly_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₁ = a ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₂ = a ∧
      ∀ p, paperTunnellMapTotal hn hnpos hsq hbal p = a ↔ p = p₁ ∨ p = p₂ := by
  obtain ⟨p₁, p₂, hne, h₁, h₂, hfib⟩ :=
    paperTunnellMap_exactly_two hn hnpos (fintype_balance_of_nat_card hbal) a
  refine ⟨p₁, p₂, hne, ?_, ?_, ?_⟩
  · rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]; exact h₁
  · rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]; exact h₂
  · intro p
    rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]
    exact hfib p

end TunnellMap

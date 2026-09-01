import TunnellMap.ComputableDirect
import TunnellMap.ComputablePipeline
import TunnellMap.FullAssembly

/-!
# The executable full map

The three branches of the manuscript's map — the even branch, the direct
branch and the residual branch — are assembled into one ordinary computable
`def`, `paperTunnellMapExec`.  It is proved to agree pointwise with the
structural `paperTunnellMap`, and therefore to have exactly two preimages over
every target.
-/

namespace TunnellMap

variable {n : ℤ}

/-! ## The executable odd branch -/

/-- **The executable odd branch.**  A direct source is mapped by the
executable quarter-turn branch; a residual source is mapped by the executable
generator/deferred-acceptance pipeline. -/
def oddMapExec (hnpos : 0 < n) (hsq : Squarefree n) (fallback : AResidual n)
    (q : BOddRep n) : ARep n :=
  if hd : SourceUsedTriple q.1 then
    (directMapExec q).getD fallback.1
  else
    (RecordDA.residualMapExec hnpos hsq fallback
      ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩).1

section Agreement

variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem oddEquivOfBalance_apply_direct (hn : Odd n) (hnpos : 0 < n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (q : BOddRep n) (hd : DirectSourceUsed q) :
    oddEquivOfBalance hn hnpos hbal q = (directSubsetEquiv hn ⟨q, hd⟩).1 := by
  classical
  show (Equiv.sumCompl DirectTargetUsed)
    (Equiv.sumCongr (directSubsetEquiv hn)
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal))
      ((Equiv.sumCompl DirectSourceUsed).symm q)) = _
  rw [Equiv.sumCompl_symm_apply_of_pos hd]
  rfl

theorem oddEquivOfBalance_apply_residual (hn : Odd n) (hnpos : 0 < n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (q : BOddRep n) (hd : ¬ DirectSourceUsed q) :
    oddEquivOfBalance hn hnpos hbal q =
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal)
        ⟨q, hd⟩).1 := by
  classical
  show (Equiv.sumCompl DirectTargetUsed)
    (Equiv.sumCongr (directSubsetEquiv hn)
      (residualEquivOfOrbitCard hnpos (residual_orbit_card_eq hn hnpos hbal))
      ((Equiv.sumCompl DirectSourceUsed).symm q)) = _
  rw [Equiv.sumCompl_symm_apply_of_neg hd]
  rfl

/-- **The executable odd branch agrees with the structural odd equivalence.** -/
theorem oddMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q = oddEquivOfBalance hn hnpos hbal q := by
  by_cases hd : DirectSourceUsed q
  · have hd' : SourceUsedTriple q.1 := (directSourceUsed_iff q).mp hd
    rw [oddEquivOfBalance_apply_direct hn hnpos hbal q hd, oddMapExec,
      dif_pos hd', directMapExec_eq hn q hd]
    rfl
  · have hd' : ¬ SourceUsedTriple q.1 := fun hc =>
      hd ((directSourceUsed_iff q).mpr hc)
    rw [oddEquivOfBalance_apply_residual hn hnpos hbal q hd, oddMapExec,
      dif_neg hd']
    congr 1
    exact RecordDA.residualMapExec_eq_residualEquiv hn hnpos hsq
      (residual_orbit_card_eq hn hnpos hbal) fallback _

end Agreement

/-! ## The executable full map -/

/-- **The executable full map of the balanced construction theorem.**  An ordinary computable `def`:
the even branch is the explicit reparametrization, the odd branch is the
executable direct/residual assembly. -/
def paperTunnellMapExec (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (p : BRep n) : ARep n :=
  if h : p.1.z % 2 = 0 then
    evenEquiv n (evenRepToParam ⟨p, Int.even_iff.mpr h⟩)
  else
    oddMapExec hnpos hsq fallback ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩

section FullAgreement

variable [Fintype (BRep n)] [Fintype (ARep n)]

/-- **The executable full map agrees with `paperTunnellMap`.** -/
theorem paperTunnellMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      paperTunnellMap hn hnpos hbalance p := by
  classical
  show _ = conditionalTunnellMap (paperOddEquiv hn hnpos hbalance)
    ((Equiv.sumCongr (evenRepParamEquiv n)
        ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
          (bOddSubtypeEquiv n)))
      ((Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm p))
  by_cases h : p.1.z % 2 = 0
  · have he : (fun p : BRep n => Even p.1.z) p := Int.even_iff.mpr h
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExec, dif_pos h]
    rfl
  · have he : ¬ (fun p : BRep n => Even p.1.z) p := fun hc => h (Int.even_iff.mp hc)
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExec, dif_neg h]
    show oddMapExec hnpos hsq fallback _ =
      paperOddEquiv hn hnpos hbalance ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
    exact oddMapExec_eq hn hnpos hsq (odd_card_eq_of_full_balance hbalance)
      fallback _

/-- **Exactly two preimages.**  Every target representation has exactly two
preimages under the executable full map. -/
theorem paperTunnellMapExec_exactly_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapExec hnpos hsq fallback p₁ = a ∧
      paperTunnellMapExec hnpos hsq fallback p₂ = a ∧
      ∀ p, paperTunnellMapExec hnpos hsq fallback p = a ↔ p = p₁ ∨ p = p₂ := by
  obtain ⟨p₁, p₂, hne, h₁, h₂, hfib⟩ :=
    paperTunnellMap_exactly_two hn hnpos hbalance a
  refine ⟨p₁, p₂, hne, ?_, ?_, ?_⟩
  · rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]; exact h₁
  · rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]; exact h₂
  · intro p
    rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]
    exact hfib p

end FullAgreement

end TunnellMap

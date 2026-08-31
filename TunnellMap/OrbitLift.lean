import TunnellMap.OrbitRanking
import TunnellMap.Assembly

/-!
# Lifting an antipodal orbit matching

An equivalence of orbit sets, together with one Boolean sign equivalence per
source orbit, lifts to an equivalence of the original free-involution types.
For the Tunnell residual sets, orbit balance therefore supplies a residual
bijection.  Combining it with the direct subset equivalence gives the full
odd-branch bijection and hence the two-element fibers.
-/

namespace TunnellMap

namespace FreeInvolution

variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)

def signedOrbitProductEquiv (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) :
    I.Orbit × Bool ≃ J.Orbit × Bool where
  toFun qb := ⟨M qb.1, sign qb.1 qb.2⟩
  invFun rb := ⟨M.symm rb.1, (sign (M.symm rb.1)).symm rb.2⟩
  left_inv := by
    intro qb
    rcases qb with ⟨q, b⟩
    simp
  right_inv := by
    intro rb
    rcases rb with ⟨r, b⟩
    simp

section Finite

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

noncomputable def liftOrbitEquiv (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) : X ≃ Y :=
  I.orbitBoolEquiv.trans
    ((I.signedOrbitProductEquiv J M sign).trans J.orbitBoolEquiv.symm)

omit [Fintype X] [Fintype Y] in
theorem liftOrbitEquiv_representative (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) (q : I.Orbit) :
    I.liftOrbitEquiv J M sign (I.representative q) =
      if sign q false then J.neg (J.representative (M q))
      else J.representative (M q) := by
  classical
  simp [liftOrbitEquiv, orbitBoolEquiv, signedOrbitProductEquiv]

end Finite

end FreeInvolution

/-- The nontrivial permutation of the two signs in an antipodal orbit. -/
def boolFlipEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- The sign selected by the smaller of the two signed midpoint keys.  The
Boolean `false` denotes the chosen target representative and `true` its
antipode. -/
noncomputable def orbitSignEquiv {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) : Bool ≃ Bool :=
  if directionKey
      (plusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) <
      directionKey
      (minusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) then
    Equiv.refl Bool
  else
    boolFlipEquiv

theorem orbitSignEquiv_false {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) :
    orbitSignEquiv hnpos s t false =
      if directionKey
          (plusVector ((bResidualInvolution n).representative s)
            ((aResidualInvolution n hnpos).representative t)) <
          directionKey
          (minusVector ((bResidualInvolution n).representative s)
            ((aResidualInvolution n hnpos).representative t)) then
        false
      else
        true := by
  by_cases h : directionKey
      (plusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) <
      directionKey
      (minusVector ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative t)) <;>
    simp [orbitSignEquiv, boolFlipEquiv, h]

/-- The preferred signed target for a pair of representative-level residual
points. -/
noncomputable def preferredTarget {n : ℤ} (s : BResidual n) (t : AResidual n) :
    AResidual n :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    t
  else
    negAResidual t

noncomputable def residualEquivOfOrbitCard {n : ℤ} (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    BResidual n ≃ AResidual n := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let M : BI.Orbit ≃ AI.Orbit := residualOrbitMatching hnpos hcard
  exact BI.liftOrbitEquiv AI M (fun s => orbitSignEquiv hnpos s (M s))

/-- On a chosen source representative, the residual equivalence is precisely
the preferred signed lift of the stable orbit edge. -/
theorem residualEquivOfOrbitCard_representative {n : ℤ} (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (s : (bResidualInvolution n).Orbit) :
    residualEquivOfOrbitCard hnpos hcard
        ((bResidualInvolution n).representative s) =
      preferredTarget ((bResidualInvolution n).representative s)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard s)) := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let M : BI.Orbit ≃ AI.Orbit := residualOrbitMatching hnpos hcard
  let E := BI.representative s
  let F := AI.representative (M s)
  change BI.liftOrbitEquiv AI M (fun q => orbitSignEquiv hnpos q (M q))
      (BI.representative s) = preferredTarget E F
  rw [BI.liftOrbitEquiv_representative]
  rw [orbitSignEquiv_false]
  change (if
      (if directionKey (plusVector E F) < directionKey (minusVector E F) then
        false else true) = true then AI.neg F else F) = preferredTarget E F
  by_cases hkey : directionKey (plusVector E F) < directionKey (minusVector E F)
  · simp [preferredTarget, hkey]
  · simp [preferredTarget, hkey, AI, aResidualInvolution]

noncomputable def oddEquivOfBalance {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    BOddRep n ≃ ARep n := by
  classical
  have horbit := residual_orbit_card_eq hn hnpos hbalance
  let residual : BResidual n ≃ AResidual n := residualEquivOfOrbitCard hnpos horbit
  exact (Equiv.sumCompl DirectSourceUsed).symm.trans
    ((Equiv.sumCongr (directSubsetEquiv hn) residual).trans
      (Equiv.sumCompl DirectTargetUsed))

/-- The two-fiber theorem after the paper's equivalent odd-branch balance
hypothesis has been supplied. -/
theorem conditionalTunnellMap_exactly_two_of_odd_balance {n : ℤ}
    (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₁ = a ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₂ = a ∧
      ∀ x, conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x = a ↔
        x = x₁ ∨ x = x₂ :=
  conditionalTunnellMap_exactly_two (oddEquivOfBalance hn hnpos hbalance) a

end TunnellMap

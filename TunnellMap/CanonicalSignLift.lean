import TunnellMap.OrbitLift
import TunnellMap.ResidualTargetTest
import TunnellMap.ComputableDirection

/-!
# The canonical sign-lift bridge

`TunnellMap.OrbitLift` lifts an orbit matching to a residual bijection through
`FreeInvolution.orbitBoolEquiv`, which selects orbit representatives with
`Quotient.out`.  The manuscript instead fixes a *canonical* representative of
every antipodal orbit — the lexicographically smaller of the two points — and
lifts an orbit edge by the explicit rule

    σ E  ↦  σ η([E],[F]) F .

This file makes that rule literal:

* `FreeInvolution.signOf` and `FreeInvolution.signAct` give the unique
  decomposition of a point as a sign times the canonical representative of its
  orbit (`FreeInvolution.exists_unique_sign`);
* `etaPoint` and `canonicalEta` are the manuscript's edge sign `η`, defined
  from the two signed midpoint keys of the canonical representatives;
* `canonicalResidualMapOf` is the canonical residual map, and
  `canonicalResidualMapOf_signAct` is the pointwise sign-lift formula;
* `canonicalResidualMapOf_eq_residualEquivOfOrbitCard` proves that the
  canonical formula agrees pointwise with the pre-existing `OrbitLift`
  equivalence, so no claim below depends on an arbitrary representative.
-/

namespace TunnellMap

namespace FreeInvolution

variable {X : Type*} (I : FreeInvolution X)

/-- The action of a sign `σ ∈ {±1}` on a point of a free involution. -/
def signAct (σ : ℤ) (x : X) : X := if σ = 1 then x else I.neg x

@[simp] theorem signAct_one (x : X) : I.signAct 1 x = x := by simp [signAct]

@[simp] theorem signAct_neg_one (x : X) : I.signAct (-1) x = I.neg x := by
  simp [signAct]

theorem signAct_neg (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (x : X) :
    I.signAct σ (I.neg x) = I.signAct (-σ) x := by
  rcases hσ with rfl | rfl <;> simp [I.neg_neg]

theorem signAct_mul (σ τ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (x : X) : I.signAct σ (I.signAct τ x) = I.signAct (σ * τ) x := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
    simp [I.neg_neg]

theorem signAct_neg_sign {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (x : X) :
    I.signAct (-σ) x = I.neg (I.signAct σ x) := by
  rcases hσ with rfl | rfl <;> simp [I.neg_neg]

@[simp] theorem orbit_signAct (σ : ℤ) (x : X) :
    I.orbit (I.signAct σ x) = I.orbit x := by
  unfold signAct
  split
  · rfl
  · exact I.orbit_neg x

/-- Two signs acting equally on a point of a free involution are equal. -/
theorem signAct_inj_sign {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    {x : X} (h : I.signAct σ x = I.signAct τ x) : σ = τ := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · rfl
  · rw [signAct_one, signAct_neg_one] at h
    exact absurd h.symm (I.no_fixed x)
  · rw [signAct_one, signAct_neg_one] at h
    exact absurd h (I.no_fixed x)
  · rfl

section Key

variable {K : Type*} [LinearOrder K]

/-- The sign relating a point to the canonical (key-minimal) representative of
its orbit. -/
def signOf (key : X → K) (x : X) : ℤ := if key x < key (I.neg x) then 1 else -1

theorem signOf_mem (key : X → K) (x : X) :
    I.signOf key x = 1 ∨ I.signOf key x = -1 := by
  unfold signOf; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem signAct_signOf_canonicalPoint (key : X → K) (x : X) :
    I.signAct (I.signOf key x) (I.canonicalPoint key x) = x := by
  unfold signOf canonicalPoint
  by_cases h : key x < key (I.neg x)
  · simp [h]
  · simp [h, I.neg_neg]

theorem signAct_signOf_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (x : X) :
    I.signAct (I.signOf key x)
      (I.canonicalRepresentative key hkey (I.orbit x)) = x := by
  rw [canonicalRepresentative_orbit]
  exact I.signAct_signOf_canonicalPoint key x

/-- **Unique signed decomposition.**  Every point of a free involution is the
canonical representative of its orbit, multiplied by a unique sign. -/
theorem exists_unique_sign (key : X → K) (hkey : Function.Injective key)
    (x : X) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      I.signAct σ (I.canonicalRepresentative key hkey (I.orbit x)) = x := by
  refine ⟨I.signOf key x, ⟨I.signOf_mem key x, ?_⟩, ?_⟩
  · rw [canonicalRepresentative_orbit]
    exact I.signAct_signOf_canonicalPoint key x
  · rintro τ ⟨hτ, hτx⟩
    rw [canonicalRepresentative_orbit] at hτx
    refine I.signAct_inj_sign (x := I.canonicalPoint key x) hτ
      (I.signOf_mem key x) ?_
    rw [hτx, I.signAct_signOf_canonicalPoint key x]

theorem signOf_neg (key : X → K) (hkey : Function.Injective key) (x : X) :
    I.signOf key (I.neg x) = - I.signOf key x := by
  have hne : key x ≠ key (I.neg x) := fun h => I.no_fixed x (hkey h).symm
  unfold signOf
  rw [I.neg_neg]
  by_cases h : key x < key (I.neg x)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : key (I.neg x) < key x := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    rw [if_pos h', if_neg h]; norm_num

theorem signOf_canonicalPoint (key : X → K) (hkey : Function.Injective key)
    (x : X) : I.signOf key (I.canonicalPoint key x) = 1 := by
  unfold canonicalPoint
  by_cases h : key x < key (I.neg x)
  · rw [if_pos h]
    simp [signOf, h]
  · have hne : key x ≠ key (I.neg x) := fun hc => I.no_fixed x (hkey hc).symm
    have h' : key (I.neg x) < key x := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    rw [if_neg h]
    simp [signOf, I.neg_neg, h']

@[simp] theorem signOf_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.signOf key (I.canonicalRepresentative key hkey q) = 1 := by
  induction q using Quotient.inductionOn with
  | _ x => exact I.signOf_canonicalPoint key hkey x

theorem signOf_signAct (key : X → K) (hkey : Function.Injective key)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (q : I.Orbit) :
    I.signOf key (I.signAct σ (I.canonicalRepresentative key hkey q)) = σ := by
  rcases hσ with rfl | rfl
  · simp [I.signOf_canonicalRepresentative key hkey q]
  · rw [signAct_neg_one, I.signOf_neg key hkey, I.signOf_canonicalRepresentative]

end Key

end FreeInvolution

/-! ## Canonical representatives and signs of residual points -/

variable {n : ℤ}

/-- The action of a sign on a residual source point. -/
abbrev signActB (σ : ℤ) (x : BResidual n) : BResidual n :=
  (bResidualInvolution n).signAct σ x

/-- The action of a sign on a residual target point. -/
abbrev signActA {n : ℤ} (hnpos : 0 < n) (σ : ℤ) (y : AResidual n) : AResidual n :=
  (aResidualInvolution n hnpos).signAct σ y

@[simp] theorem signActB_one (x : BResidual n) : signActB 1 x = x :=
  (bResidualInvolution n).signAct_one x

@[simp] theorem signActB_neg_one (x : BResidual n) :
    signActB (-1) x = negBResidual x :=
  (bResidualInvolution n).signAct_neg_one x

@[simp] theorem signActA_one {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos 1 y = y :=
  (aResidualInvolution n hnpos).signAct_one y

@[simp] theorem signActA_neg_one {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (-1) y = negAResidual y :=
  (aResidualInvolution n hnpos).signAct_neg_one y

@[simp] theorem orbit_canonicalBResidualRepresentative
    (q : (bResidualInvolution n).Orbit) :
    (bResidualInvolution n).orbit (canonicalBResidualRepresentative q) = q :=
  (bResidualInvolution n).orbit_canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective q

@[simp] theorem orbit_canonicalAResidualRepresentative {n : ℤ} (hnpos : 0 < n)
    (o : (aResidualInvolution n hnpos).Orbit) :
    (aResidualInvolution n hnpos).orbit
      (canonicalAResidualRepresentative hnpos o) = o :=
  (aResidualInvolution n hnpos).orbit_canonicalRepresentative aResidualLexKey
    aResidualLexKey_injective o

theorem signActB_neg_sign {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (x : BResidual n) :
    signActB (-σ) x = negBResidual (signActB σ x) :=
  (bResidualInvolution n).signAct_neg_sign hσ x

theorem signActA_neg_sign {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (y : AResidual n) :
    signActA hnpos (-σ) y = negAResidual (signActA hnpos σ y) :=
  (aResidualInvolution n hnpos).signAct_neg_sign hσ y

/-- The sign of a residual source point relative to the canonical
representative of its antipodal orbit. -/
def bResidualSign (x : BResidual n) : ℤ :=
  (bResidualInvolution n).signOf bResidualLexKey x

/-- The sign of a residual target point relative to the canonical
representative of its antipodal orbit. -/
def aResidualSign {n : ℤ} (hnpos : 0 < n) (y : AResidual n) : ℤ :=
  (aResidualInvolution n hnpos).signOf aResidualLexKey y

theorem bResidualSign_mem (x : BResidual n) :
    bResidualSign x = 1 ∨ bResidualSign x = -1 :=
  (bResidualInvolution n).signOf_mem _ x

theorem aResidualSign_mem {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    aResidualSign hnpos y = 1 ∨ aResidualSign hnpos y = -1 :=
  (aResidualInvolution n hnpos).signOf_mem _ y

/-- **Unique canonical decomposition of a residual source point.** -/
theorem bResidual_exists_unique_sign (x : BResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActB σ
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x :=
  (bResidualInvolution n).exists_unique_sign bResidualLexKey
    bResidualLexKey_injective x

/-- **Unique canonical decomposition of a residual target point.** -/
theorem aResidual_exists_unique_sign {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    ∃! σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      signActA hnpos σ
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y :=
  (aResidualInvolution n hnpos).exists_unique_sign aResidualLexKey
    aResidualLexKey_injective y

theorem bResidual_decomposition (x : BResidual n) :
    signActB (bResidualSign x)
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x :=
  (bResidualInvolution n).signAct_signOf_canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective x

theorem aResidual_decomposition {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (aResidualSign hnpos y)
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y :=
  (aResidualInvolution n hnpos).signAct_signOf_canonicalRepresentative
    aResidualLexKey aResidualLexKey_injective y

theorem bResidualSign_signAct {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (q : (bResidualInvolution n).Orbit) :
    bResidualSign (signActB σ (canonicalBResidualRepresentative q)) = σ :=
  (bResidualInvolution n).signOf_signAct bResidualLexKey
    bResidualLexKey_injective hσ q

theorem aResidualSign_signAct {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (o : (aResidualInvolution n hnpos).Orbit) :
    aResidualSign hnpos
        (signActA hnpos σ (canonicalAResidualRepresentative hnpos o)) = σ :=
  (aResidualInvolution n hnpos).signOf_signAct aResidualLexKey
    aResidualLexKey_injective hσ o

@[simp] theorem orbit_signActB (σ : ℤ) (x : BResidual n) :
    (bResidualInvolution n).orbit (signActB σ x) =
      (bResidualInvolution n).orbit x :=
  (bResidualInvolution n).orbit_signAct σ x

@[simp] theorem orbit_signActA {n : ℤ} (hnpos : 0 < n) (σ : ℤ) (y : AResidual n) :
    (aResidualInvolution n hnpos).orbit (signActA hnpos σ y) =
      (aResidualInvolution n hnpos).orbit y :=
  (aResidualInvolution n hnpos).orbit_signAct σ y

theorem vsmul_one (v : Triple) : vsmul 1 v = v := by
  apply Triple.ext <;> simp [vsmul]

theorem vsmul_neg_one (v : Triple) : vsmul (-1) v = negTriple v := by
  apply Triple.ext <;> simp [vsmul, negTriple]

/-- The coordinate-level sign of a lifted residual target is the sign of the
point relative to the canonical representative of its orbit. -/
theorem residualTarget_decomposition {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (targetLiftSign (residualTargetLift y))
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y := by
  have hspec : residualTargetLift y =
      vsmul (targetLiftSign (residualTargetLift y))
        (canonicalTargetLift (residualTargetLift y)) :=
    canonicalTargetLift_spec _
  have hcanon : canonicalTargetLift (residualTargetLift y) =
      residualTargetLift (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit y)) :=
    canonicalTargetLift_eq hnpos y
  apply residualTargetLift_injective
  rcases targetLiftSign_mem (residualTargetLift y) with hm | hm
  · rw [hm, signActA_one]
    conv_rhs => rw [hspec, hm, hcanon, vsmul_one]
  · rw [hm, signActA_neg_one, ← negTriple_residualTargetLift]
    conv_rhs => rw [hspec, hm, hcanon, vsmul_neg_one]

theorem targetLiftSign_eq_aResidualSign {n : ℤ} (hnpos : 0 < n)
    (y : AResidual n) :
    targetLiftSign (residualTargetLift y) = aResidualSign hnpos y := by
  refine (aResidualInvolution n hnpos).signAct_inj_sign
    (x := canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit y))
    (targetLiftSign_mem _) (aResidualSign_mem hnpos y) ?_
  show signActA hnpos (targetLiftSign (residualTargetLift y))
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit y)) =
    signActA hnpos (aResidualSign hnpos y)
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit y))
  rw [residualTarget_decomposition hnpos y, aResidual_decomposition hnpos y]

/-! ## The canonical edge sign η -/

/-- The manuscript's edge sign at the level of signed representatives: `+1`
when the plus midpoint line has the smaller projective key, `-1` otherwise.
By Lemma 4.1 the two keys are never equal. -/
noncomputable def etaPoint {n : ℤ} (s : BResidual n) (t : AResidual n) : ℤ :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then 1 else -1

/-- The executable form of `etaPoint`. -/
def etaPointExec {n : ℤ} (s : BResidual n) (t : AResidual n) : ℤ :=
  if keyLtExec (directionKeyExec (plusVector s t))
      (directionKeyExec (minusVector s t)) then 1 else -1

theorem etaPointExec_eq {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPointExec s t = etaPoint s t := by
  unfold etaPointExec etaPoint
  rw [directionKeyExec_eq (plusVector_ne_zero s t),
    directionKeyExec_eq (minusVector_ne_zero s t)]
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t) <;>
    simp [h]

theorem etaPoint_mem {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s t = 1 ∨ etaPoint s t = -1 := by
  unfold etaPoint; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem etaPoint_eq_one_iff {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s t = 1 ↔
      directionKey (plusVector s t) < directionKey (minusVector s t) := by
  unfold etaPoint
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t) <;>
    simp [h]

theorem etaPoint_neg_target {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s (negAResidual t) = - etaPoint s t := by
  unfold etaPoint
  rw [plusVector_neg_target, minusVector_neg_target]
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (plus_minus_keys_ne s t))
    rw [if_pos h', if_neg h]
    norm_num

theorem etaPoint_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint (negBResidual s) t = - etaPoint s t := by
  unfold etaPoint
  rw [plusVector_neg_source, minusVector_neg_source,
    directionKey_negTriple (minusVector_ne_zero s t),
    directionKey_negTriple (plusVector_ne_zero s t)]
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · rw [if_neg (not_lt_of_gt h), if_pos h]
  · have h' : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (plus_minus_keys_ne s t))
    rw [if_pos h', if_neg h]
    norm_num

theorem etaPoint_signActB {n : ℤ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (s : BResidual n) (t : AResidual n) :
    etaPoint (signActB σ s) t = σ * etaPoint s t := by
  rcases hσ with rfl | rfl
  · simp
  · rw [signActB_neg_one, etaPoint_neg_source]; ring

theorem etaPoint_signActA {n : ℤ} (hnpos : 0 < n) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (s : BResidual n) (t : AResidual n) :
    etaPoint s (signActA hnpos σ t) = σ * etaPoint s t := by
  rcases hσ with rfl | rfl
  · simp
  · rw [signActA_neg_one, etaPoint_neg_target]; ring

/-- **The canonical edge sign η([E],[F]) of the manuscript.**  It is computed
from the canonical representatives of the two antipodal orbits, so it does not
depend on any choice of representative. -/
noncomputable def canonicalEta {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) : ℤ :=
  etaPoint (canonicalBResidualRepresentative q)
    (canonicalAResidualRepresentative hnpos o)

theorem canonicalEta_mem {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o = 1 ∨ canonicalEta hnpos q o = -1 :=
  etaPoint_mem _ _

theorem canonicalEta_mul_self {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o * canonicalEta hnpos q o = 1 := by
  rcases canonicalEta_mem hnpos q o with h | h <;> rw [h] <;> ring

/-! ## The signed partner of a residual source point -/

/-- The signed target attached to a source point and any signed representative
of a target orbit.  By `signedPartner_neg_target` it depends only on the target
*orbit*. -/
noncomputable def signedPartner {n : ℤ} (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) : AResidual n :=
  signActA hnpos (etaPoint s t) t

theorem signedPartner_eq_preferredTarget {n : ℤ} (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    signedPartner hnpos s t = preferredTarget s t := by
  unfold signedPartner preferredTarget etaPoint
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t) <;>
    simp [h]
  rfl

theorem signedPartner_neg_target {n : ℤ} (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) :
    signedPartner hnpos s (negAResidual t) = signedPartner hnpos s t := by
  unfold signedPartner
  rw [etaPoint_neg_target]
  rcases etaPoint_mem s t with h | h <;> rw [h]
  · rw [signActA_neg_one, signActA_one, negAResidual_neg]
  · rw [show - (-1 : ℤ) = 1 by norm_num, signActA_one, signActA_neg_one]

theorem signedPartner_signActA {n : ℤ} (hnpos : 0 < n) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (s : BResidual n) (t : AResidual n) :
    signedPartner hnpos s (signActA hnpos σ t) = signedPartner hnpos s t := by
  rcases hσ with rfl | rfl
  · rw [signActA_one]
  · rw [signActA_neg_one]
    exact signedPartner_neg_target hnpos s t

/-! ## The canonical residual map -/

/-- **The manuscript's canonical residual map.**  A residual source point is
decomposed as `σ E` with `E` the canonical representative of its orbit; the
matched target orbit contributes its canonical representative `F` and the
canonical edge sign `η`; the image is `σ η F`.  No arbitrary representative
occurs. -/
noncomputable def canonicalResidualMapOf {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) : AResidual n :=
  signActA hnpos
    (bResidualSign x *
      canonicalEta hnpos ((bResidualInvolution n).orbit x)
        (M ((bResidualInvolution n).orbit x)))
    (canonicalAResidualRepresentative hnpos
      (M ((bResidualInvolution n).orbit x)))

/-- **The literal pointwise sign-lift formula** `σ E ↦ σ η F`. -/
theorem canonicalResidualMapOf_signAct {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    canonicalResidualMapOf hnpos M
        (signActB σ (canonicalBResidualRepresentative q)) =
      signActA hnpos (σ * canonicalEta hnpos q (M q))
        (canonicalAResidualRepresentative hnpos (M q)) := by
  unfold canonicalResidualMapOf
  rw [orbit_signActB, orbit_canonicalBResidualRepresentative,
    bResidualSign_signAct hσ]

/-- The canonical residual map is the signed partner of the matched canonical
target representative. -/
theorem canonicalResidualMapOf_eq_signedPartner {n : ℤ} (hnpos : 0 < n)
    (M : (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    canonicalResidualMapOf hnpos M x =
      signedPartner hnpos x
        (canonicalAResidualRepresentative hnpos
          (M ((bResidualInvolution n).orbit x))) := by
  obtain ⟨q, hq⟩ : ∃ q, (bResidualInvolution n).orbit x = q := ⟨_, rfl⟩
  have hσ : bResidualSign x = 1 ∨ bResidualSign x = -1 := bResidualSign_mem x
  have hx : signActB (bResidualSign x) (canonicalBResidualRepresentative q) = x := by
    rw [← hq]; exact bResidual_decomposition x
  have hkey : etaPoint x
      (canonicalAResidualRepresentative hnpos (M q)) =
      bResidualSign x *
        etaPoint (canonicalBResidualRepresentative q)
          (canonicalAResidualRepresentative hnpos (M q)) := by
    conv_lhs => rw [← hx]
    rw [etaPoint_signActB hσ]
  unfold canonicalResidualMapOf signedPartner canonicalEta
  rw [hq, hkey]

/-! ## Agreement with the `OrbitLift` equivalence -/

namespace FreeInvolution

variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [Fintype X] [Fintype Y] in
/-- The value of the lifted equivalence at the antipode of a chosen source
representative. -/
theorem liftOrbitEquiv_neg_representative (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) (q : I.Orbit) :
    I.liftOrbitEquiv J M sign (I.neg (I.representative q)) =
      if sign q true then J.neg (J.representative (M q))
      else J.representative (M q) := by
  classical
  simp [liftOrbitEquiv, orbitBoolEquiv, signedOrbitProductEquiv, I.orbit_neg,
    I.orbit_representative, I.no_fixed]

end FreeInvolution

section Agreement

variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- The pre-existing lifted equivalence at the antipode of the chosen source
representative. -/
theorem residualEquivOfOrbitCard_neg_representative
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    residualEquivOfOrbitCard hnpos hcard
        (negBResidual ((bResidualInvolution n).representative q)) =
      negAResidual
        (preferredTarget ((bResidualInvolution n).representative q)
          ((aResidualInvolution n hnpos).representative
            (residualOrbitMatching hnpos hcard q))) := by
  classical
  show (bResidualInvolution n).liftOrbitEquiv (aResidualInvolution n hnpos)
      (residualOrbitMatching hnpos hcard)
      (fun s => orbitSignEquiv hnpos s (residualOrbitMatching hnpos hcard s))
      ((bResidualInvolution n).neg
        ((bResidualInvolution n).representative q)) = _
  rw [FreeInvolution.liftOrbitEquiv_neg_representative]
  unfold orbitSignEquiv
  by_cases hlt : directionKey
      (plusVector ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q))) <
      directionKey
      (minusVector ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)))
  · rw [if_pos hlt]
    simp only [Equiv.refl_apply]
    rw [show preferredTarget ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) =
        (aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q) by
      unfold preferredTarget; rw [if_pos hlt]]
    rfl
  · rw [if_neg hlt]
    simp only [boolFlipEquiv, Equiv.coe_fn_mk, Bool.not_true,
      if_neg (by simp : ¬ (false = true))]
    rw [show preferredTarget ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) =
        negAResidual ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) by
      unfold preferredTarget; rw [if_neg hlt]]
    rw [negAResidual_neg]

/-- The pre-existing lifted equivalence, evaluated at an arbitrary point, is
the signed partner of the `Quotient.out` representative of the matched target
orbit. -/
theorem residualEquivOfOrbitCard_apply
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    residualEquivOfOrbitCard hnpos hcard x =
      signedPartner hnpos x
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard
            ((bResidualInvolution n).orbit x))) := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, (bResidualInvolution n).orbit x = q := ⟨_, rfl⟩
  have hrel : x = (bResidualInvolution n).representative q ∨
      x = negBResidual ((bResidualInvolution n).representative q) :=
    (bResidualInvolution n).orbit_eq_iff.mp
      (((bResidualInvolution n).orbit_representative q).trans hq.symm)
  rw [hq]
  rcases hrel with hx | hx
  · rw [hx, residualEquivOfOrbitCard_representative hnpos hcard q,
      signedPartner_eq_preferredTarget]
  · rw [hx, residualEquivOfOrbitCard_neg_representative hnpos hcard q,
      ← signedPartner_eq_preferredTarget hnpos]
    unfold signedPartner
    rw [etaPoint_neg_source, signActA_neg_sign hnpos (etaPoint_mem _ _)]

/-- **The canonical formula agrees with the pre-existing lift.**  Even though
`residualEquivOfOrbitCard` was built from `Quotient.out` representatives, it
coincides pointwise with the manuscript's canonical sign-lift formula. -/
theorem canonicalResidualMapOf_eq_residualEquivOfOrbitCard
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) (x : BResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x =
      residualEquivOfOrbitCard hnpos hcard x := by
  classical
  rw [canonicalResidualMapOf_eq_signedPartner, residualEquivOfOrbitCard_apply]
  obtain ⟨o, ho⟩ : ∃ o, residualOrbitMatching hnpos hcard
      ((bResidualInvolution n).orbit x) = o := ⟨_, rfl⟩
  rw [ho]
  have hdec := aResidual_decomposition hnpos
    ((aResidualInvolution n hnpos).representative o)
  rw [(aResidualInvolution n hnpos).orbit_representative o] at hdec
  rw [← hdec, signedPartner_signActA hnpos (aResidualSign_mem hnpos _)]

end Agreement

end TunnellMap

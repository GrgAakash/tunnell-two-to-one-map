import TunnellMap.Midpoint

/-!
# Residual complements and antipodal orbits

The direct domains and images are invariant under negation.  We therefore
obtain fixed-point-free involutions on the residual source and target sets.
The generic orbit construction below also proves that a finite free
involution has exactly twice as many points as antipodal orbits.
-/

namespace TunnellMap

def negTriple (p : Triple) : Triple := ⟨-p.x, -p.y, -p.z⟩

@[simp] theorem negTriple_neg (p : Triple) : negTriple (negTriple p) = p := by
  ext <;> simp [negTriple]

@[simp] theorem bForm_negTriple (p : Triple) : bForm (negTriple p) = bForm p := by
  simp [bForm, negTriple]

@[simp] theorem aForm_negTriple (p : Triple) : aForm (negTriple p) = aForm p := by
  simp [aForm, negTriple]

def negBOdd {n : ℤ} (p : BOddRep n) : BOddRep n :=
  ⟨negTriple p.1, by simpa using p.2.1, p.2.2.neg⟩

def negA {n : ℤ} (p : ARep n) : ARep n :=
  ⟨negTriple p.1, by simpa using p.2⟩

@[simp] theorem negBOdd_neg {n : ℤ} (p : BOddRep n) : negBOdd (negBOdd p) = p := by
  apply Subtype.ext
  exact negTriple_neg p.1

@[simp] theorem negA_neg {n : ℤ} (p : ARep n) : negA (negA p) = p := by
  apply Subtype.ext
  exact negTriple_neg p.1

def DirectSourceUsed {n : ℤ} (p : BOddRep n) : Prop :=
  DirectPredicate1 p ∨ DirectPredicate2 p ∨ DirectPredicate3 p

def DirectTargetUsed {n : ℤ} (p : ARep n) : Prop :=
  ImagePredicate1 p ∨ ImagePredicate2 p ∨ ImagePredicate3 p

theorem directPredicate1_neg_iff {n : ℤ} (p : BOddRep n) :
    DirectPredicate1 (negBOdd p) ↔ DirectPredicate1 p := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate1, negBOdd, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate1, negBOdd, negTriple] at hq ⊢
    linarith

theorem directPredicate2_neg_iff {n : ℤ} (p : BOddRep n) :
    DirectPredicate2 (negBOdd p) ↔ DirectPredicate2 p := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate2, negBOdd, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate2, negBOdd, negTriple] at hq ⊢
    linarith

theorem directPredicate3_neg_iff {n : ℤ} (p : BOddRep n) :
    DirectPredicate3 (negBOdd p) ↔ DirectPredicate3 p := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate3, negBOdd, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    dsimp [DirectPredicate3, negBOdd, negTriple] at hq ⊢
    linarith

theorem directSourceUsed_neg_iff {n : ℤ} (p : BOddRep n) :
    DirectSourceUsed (negBOdd p) ↔ DirectSourceUsed p := by
  simp only [DirectSourceUsed, directPredicate1_neg_iff,
    directPredicate2_neg_iff, directPredicate3_neg_iff]

theorem imagePredicate1_neg_iff {n : ℤ} (p : ARep n) :
    ImagePredicate1 (negA p) ↔ ImagePredicate1 p := by
  constructor
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate1, negA, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate1, negA, negTriple] at hq ⊢
    linarith

theorem imagePredicate2_neg_iff {n : ℤ} (p : ARep n) :
    ImagePredicate2 (negA p) ↔ ImagePredicate2 p := by
  constructor
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate2, negA, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate2, negA, negTriple] at hq ⊢
    linarith

theorem imagePredicate3_neg_iff {n : ℤ} (p : ARep n) :
    ImagePredicate3 (negA p) ↔ ImagePredicate3 p := by
  constructor
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate3, negA, negTriple] at hq ⊢
    linarith
  · rintro ⟨q, hodd, hq⟩
    refine ⟨-q, hodd.neg, ?_⟩
    dsimp [ImagePredicate3, negA, negTriple] at hq ⊢
    linarith

theorem directTargetUsed_neg_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed (negA p) ↔ DirectTargetUsed p := by
  simp only [DirectTargetUsed, imagePredicate1_neg_iff,
    imagePredicate2_neg_iff, imagePredicate3_neg_iff]

abbrev BResidual (n : ℤ) := {p : BOddRep n // ¬ DirectSourceUsed p}

abbrev AResidual (n : ℤ) := {p : ARep n // ¬ DirectTargetUsed p}

def negBResidual {n : ℤ} (p : BResidual n) : BResidual n := by
  refine ⟨negBOdd p.1, ?_⟩
  simpa [directSourceUsed_neg_iff] using p.2

def negAResidual {n : ℤ} (p : AResidual n) : AResidual n := by
  refine ⟨negA p.1, ?_⟩
  simpa [directTargetUsed_neg_iff] using p.2

@[simp] theorem negBResidual_neg {n : ℤ} (p : BResidual n) :
    negBResidual (negBResidual p) = p := by
  apply Subtype.ext
  exact negBOdd_neg p.1

@[simp] theorem negAResidual_neg {n : ℤ} (p : AResidual n) :
    negAResidual (negAResidual p) = p := by
  apply Subtype.ext
  exact negA_neg p.1

/-! ## A generic free-involution quotient -/

structure FreeInvolution (X : Type*) where
  neg : X → X
  neg_neg : ∀ x, neg (neg x) = x
  no_fixed : ∀ x, neg x ≠ x

namespace FreeInvolution

variable {X : Type*} (I : FreeInvolution X)

def Rel (x y : X) : Prop := y = x ∨ y = I.neg x

theorem rel_refl (x : X) : I.Rel x x := Or.inl rfl

theorem rel_symm {x y : X} (h : I.Rel x y) : I.Rel y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    rw [h, I.neg_neg]

theorem rel_trans {x y z : X} (hxy : I.Rel x y) (hyz : I.Rel y z) : I.Rel x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · left
      rw [hyz, hxy, I.neg_neg]

def setoid : Setoid X where
  r := I.Rel
  iseqv := ⟨I.rel_refl, I.rel_symm, I.rel_trans⟩

abbrev Orbit := Quotient I.setoid

/-- Orbit equality is decidable whenever an executable finite construction
needs it.  The quotient itself is proof-relevant only through its extensional
equality, so the standard classical decision procedure is sufficient. -/
noncomputable instance orbitDecidableEq : DecidableEq I.Orbit :=
  Classical.decEq I.Orbit

def orbit (x : X) : I.Orbit := Quotient.mk I.setoid x

@[simp] theorem orbit_neg (x : X) : I.orbit (I.neg x) = I.orbit x := by
  apply Quotient.sound
  exact Or.inr (I.neg_neg x).symm

theorem orbit_eq_iff {x y : X} : I.orbit x = I.orbit y ↔ y = x ∨ y = I.neg x := by
  exact Quotient.eq_iff_equiv

noncomputable def representative (q : I.Orbit) : X := Quotient.out q

@[simp] theorem orbit_representative (q : I.Orbit) :
    I.orbit (I.representative q) = q := Quotient.out_eq q

section CanonicalRepresentative

variable {K : Type*} [LinearOrder K]

/-- Select the member of a free orbit having smaller value under an injective
key. -/
def canonicalPoint (key : X → K) (x : X) : X :=
  if key x < key (I.neg x) then x else I.neg x

theorem canonicalPoint_neg (key : X → K) (hkey : Function.Injective key)
    (x : X) : I.canonicalPoint key (I.neg x) = I.canonicalPoint key x := by
  have hne : key x ≠ key (I.neg x) := by
    intro h
    exact I.no_fixed x (hkey h).symm
  by_cases hlt : key x < key (I.neg x)
  · have hnlt : ¬ key (I.neg x) < key x := not_lt_of_ge hlt.le
    simp [canonicalPoint, I.neg_neg, hlt, hnlt]
  · have hrev : key (I.neg x) < key x :=
      lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    simp [canonicalPoint, I.neg_neg, hlt, hrev]

/-- The key-minimal representative, defined directly on the quotient rather
than by an arbitrary choice of representative. -/
def canonicalRepresentative (key : X → K) (hkey : Function.Injective key) :
    I.Orbit → X :=
  Quotient.lift (I.canonicalPoint key) (by
    intro x y hxy
    rcases hxy with rfl | hneg
    · rfl
    · rw [hneg, I.canonicalPoint_neg key hkey])

@[simp] theorem canonicalRepresentative_orbit (key : X → K)
    (hkey : Function.Injective key) (x : X) :
    I.canonicalRepresentative key hkey (I.orbit x) = I.canonicalPoint key x :=
  rfl

theorem orbit_canonicalRepresentative (key : X → K)
    (hkey : Function.Injective key) (q : I.Orbit) :
    I.orbit (I.canonicalRepresentative key hkey q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change I.orbit (I.canonicalPoint key x) = I.orbit x
      unfold canonicalPoint
      split <;> simp [I.orbit_neg]

end CanonicalRepresentative

section Finite

variable [Fintype X] [DecidableEq X]

noncomputable instance orbitFintype : Fintype I.Orbit := Fintype.ofFinite I.Orbit

noncomputable def orbitBoolEquiv : X ≃ I.Orbit × Bool where
  toFun x :=
    let q := I.orbit x
    (q, if x = I.representative q then false else true)
  invFun qb := if qb.2 then I.neg (I.representative qb.1) else I.representative qb.1
  left_inv := by
    intro x
    by_cases h : x = I.representative (I.orbit x)
    · change (if (if x = I.representative (I.orbit x) then false else true)
          then I.neg (I.representative (I.orbit x))
          else I.representative (I.orbit x)) = x
      rw [if_pos h]
      exact h.symm
    · have hclass : I.orbit (I.representative (I.orbit x)) = I.orbit x :=
        I.orbit_representative (I.orbit x)
      have hrel : x = I.representative (I.orbit x) ∨
          x = I.neg (I.representative (I.orbit x)) :=
        (I.orbit_eq_iff.mp hclass)
      change (if (if x = I.representative (I.orbit x) then false else true)
          then I.neg (I.representative (I.orbit x))
          else I.representative (I.orbit x)) = x
      rw [if_neg h]
      exact (hrel.resolve_left h).symm
  right_inv := by
    intro qb
    rcases qb with ⟨q, b⟩
    cases b <;> dsimp
    · simp [I.orbit_representative]
    · simp [I.orbit_representative, I.no_fixed]

theorem card_eq_twice_orbit_card :
    Fintype.card X = 2 * Fintype.card I.Orbit := by
  rw [Fintype.card_congr I.orbitBoolEquiv, Fintype.card_prod, Fintype.card_bool]
  omega

end Finite

end FreeInvolution

def bResidualInvolution (n : ℤ) : FreeInvolution (BResidual n) where
  neg := negBResidual
  neg_neg := negBResidual_neg
  no_fixed := by
    intro p h
    have hz : -p.1.1.z = p.1.1.z := congrArg (fun q : BResidual n => q.1.1.z) h
    have hz0 : p.1.1.z = 0 := by linarith
    have hodd := p.1.2.2
    rw [hz0] at hodd
    exact Int.not_odd_zero hodd

def aResidualInvolution (n : ℤ) (hn : 0 < n) : FreeInvolution (AResidual n) where
  neg := negAResidual
  neg_neg := negAResidual_neg
  no_fixed := by
    intro p h
    have hx : -p.1.1.x = p.1.1.x := congrArg (fun q : AResidual n => q.1.1.x) h
    have hy : -p.1.1.y = p.1.1.y := congrArg (fun q : AResidual n => q.1.1.y) h
    have hz : -p.1.1.z = p.1.1.z := congrArg (fun q : AResidual n => q.1.1.z) h
    have hform := p.1.2
    change 2 * p.1.1.x ^ 2 + p.1.1.y ^ 2 + 32 * p.1.1.z ^ 2 = n at hform
    nlinarith

end TunnellMap

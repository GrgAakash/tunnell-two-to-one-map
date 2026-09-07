import TunnellMap.BranchSpec

/-!
# Solution for Palomar entry A

The declarations `TunnellChallenge.BRep`, `TunnellChallenge.ARep`,
`TunnellChallenge.DirectTargetUsed` and `TunnellChallenge.AResidual` repeat the
Challenge definitions verbatim.  `TunnellChallenge.tunnellMap` is the
definition hole; its value here is the project's fallback-free assembled
executable map `TunnellMap.paperTunnellMapTotal`, transported along the
coordinate equivalences between `ℤ × ℤ × ℤ` and `TunnellMap.Triple`.
`tunnellMap_exactly_two` is then `TunnellMap.paperTunnellMapTotal_exactly_two`,
and the branch specifications are the corresponding theorems of
`TunnellMap.BranchSpec`.
-/

namespace TunnellChallenge

set_option maxHeartbeats 1000000

/-- `BRep n` — the representations of `n` by `2x² + y² + 8z²`. -/
def BRep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 8 * p.2.2 ^ 2 = n}

/-- `ARep n` — the representations of `n` by `2u² + v² + 32w² = n`. -/
def ARep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 32 * p.2.2 ^ 2 = n}

/-- A target `(u, v, w) ∈ ARep n` is *directly used* when it is the image of
one of the three quarter-turn branches. -/
def DirectTargetUsed {n : ℤ} (p : ARep n) : Prop :=
  (∃ q : ℤ, Odd q ∧ p.1.1 + 4 * p.1.2.2 - p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 - 4 * p.1.2.2 + p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 = 2 * q)

/-- The *residual* targets. -/
def AResidual (n : ℤ) : Type := {p : ARep n // ¬ DirectTargetUsed p}

/-! ## Residual stable-matching specification -/

def BOddRep (n : ℤ) : Type := {p : BRep n // Odd p.1.2.2}

def DirectSourceUsed {n : ℤ} (p : BOddRep n) : Prop :=
  (∃ q : ℤ, p.1.1.1 + 2 * p.1.1.2.2 + p.1.1.2.1 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.2.1 - p.1.1.1 + 2 * p.1.1.2.2 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.1 = 4 * q)

def BResidual (n : ℤ) : Type := {p : BOddRep n // ¬ DirectSourceUsed p}

def negBResidual {n : ℤ} (p : BResidual n) : BResidual n := by
  refine ⟨⟨⟨(-p.1.1.1.1, -p.1.1.1.2.1, -p.1.1.1.2.2), ?_⟩, p.1.2.neg⟩, ?_⟩
  · simpa using p.1.1.2
  · intro h
    apply p.2
    rcases h with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩
    · exact Or.inr (Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩)
    · exact Or.inr (Or.inr ⟨-q, by dsimp at hq ⊢; linarith⟩)

def negAResidual {n : ℤ} (p : AResidual n) : AResidual n := by
  refine ⟨⟨(-p.1.1.1, -p.1.1.2.1, -p.1.1.2.2), ?_⟩, ?_⟩
  · simpa using p.1.2
  · intro h
    apply p.2
    rcases h with ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
    · exact Or.inl ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩
    · exact Or.inr (Or.inl ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩)
    · exact Or.inr (Or.inr ⟨-q, hq.neg, by dsimp at heq ⊢; linarith⟩)

abbrev Triple := ℤ × ℤ × ℤ
abbrev TripleLexKey := ℤ ×ₗ (ℤ ×ₗ ℤ)
abbrev DirectionKey := ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℤ))

def tripleLexKey (v : Triple) : TripleLexKey :=
  toLex (v.1, toLex (v.2.1, v.2.2))

def CanonicalB (n : ℤ) : Type :=
  {p : BResidual n // tripleLexKey p.1.1.1 < tripleLexKey (negBResidual p).1.1.1}

def CanonicalA (n : ℤ) : Type :=
  {p : AResidual n // tripleLexKey p.1.1 < tripleLexKey (negAResidual p).1.1}

open Polynomial

noncomputable def triplePolynomial (v : Triple) : ℤ[X] :=
  C v.1 + C v.2.1 * X + C v.2.2 * X ^ 2

def polynomialTriple (f : ℤ[X]) : Triple :=
  (f.coeff 0, f.coeff 1, f.coeff 2)

def FirstNonzeroPositive (v : Triple) : Prop :=
  0 < v.1 ∨ (v.1 = 0 ∧ 0 < v.2.1) ∨
    (v.1 = 0 ∧ v.2.1 = 0 ∧ 0 < v.2.2)

instance firstNonzeroPositiveDecidable (v : Triple) :
    Decidable (FirstNonzeroPositive v) := by
  unfold FirstNonzeroPositive
  infer_instance

def negTriple (v : Triple) : Triple := (-v.1, -v.2.1, -v.2.2)

def orientDirection (v : Triple) : Triple :=
  if FirstNonzeroPositive v then v else negTriple v

noncomputable def primitiveDirection (v : Triple) : Triple :=
  orientDirection (polynomialTriple (triplePolynomial v).primPart)

def qForm (v : Triple) : ℤ := 2 * v.1 ^ 2 + v.2.1 ^ 2 + 2 * v.2.2 ^ 2

noncomputable def directionKey (v : Triple) : DirectionKey :=
  let d := primitiveDirection v
  toLex (qForm d, toLex (d.1, toLex (d.2.1, d.2.2)))

def residualSourceLift {n : ℤ} (s : BResidual n) : Triple :=
  (s.1.1.1.1, s.1.1.1.2.1, 2 * s.1.1.1.2.2)

def residualTargetLift {n : ℤ} (t : AResidual n) : Triple :=
  (t.1.1.1, t.1.1.2.1, 4 * t.1.1.2.2)

def plusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  let E := residualSourceLift s
  let F := residualTargetLift t
  (E.1 + F.1, E.2.1 + F.2.1, E.2.2 + F.2.2)

def minusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  let E := residualSourceLift s
  let F := residualTargetLift t
  (E.1 - F.1, E.2.1 - F.2.1, E.2.2 - F.2.2)

noncomputable def residualEdgeKey {n : ℤ} (s : BResidual n) (t : AResidual n) :
    DirectionKey :=
  min (directionKey (plusVector s t)) (directionKey (minusVector s t))

def StableResidualMatching {n : ℤ} (M : CanonicalB n ≃ CanonicalA n) : Prop :=
  ∀ s t, ¬ (residualEdgeKey s.1 t.1 < residualEdgeKey s.1 (M s).1 ∧
    residualEdgeKey s.1 t.1 < residualEdgeKey (M.symm t).1 t.1)

noncomputable def preferredTarget {n : ℤ} (s : BResidual n)
    (t : AResidual n) : AResidual n :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    t
  else
    negAResidual t

/-! ## Coordinate bridge -/

/-- `BRep n` in product coordinates is `TunnellMap.BRep n`. -/
def bEquiv (n : ℤ) : BRep n ≃ TunnellMap.BRep n where
  toFun p := ⟨⟨p.1.1, p.1.2.1, p.1.2.2⟩, p.2⟩
  invFun q := ⟨(q.1.x, q.1.y, q.1.z), q.2⟩
  left_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl

/-- `ARep n` in product coordinates is `TunnellMap.ARep n`. -/
def aEquiv (n : ℤ) : ARep n ≃ TunnellMap.ARep n where
  toFun p := ⟨⟨p.1.1, p.1.2.1, p.1.2.2⟩, p.2⟩
  invFun q := ⟨(q.1.x, q.1.y, q.1.z), q.2⟩
  left_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h⟩; rfl

theorem directTargetUsed_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ TunnellMap.DirectTargetUsed (aEquiv n p) :=
  Iff.rfl

/-- The residual targets in product coordinates are `TunnellMap.AResidual n`. -/
def arEquiv (n : ℤ) : AResidual n ≃ TunnellMap.AResidual n :=
  (aEquiv n).subtypeEquiv fun p => not_congr (directTargetUsed_iff p)

theorem card_bRep (n : ℤ) : Nat.card (BRep n) = Nat.card (TunnellMap.BRep n) :=
  Nat.card_congr (bEquiv n)

theorem card_aRep (n : ℤ) : Nat.card (ARep n) = Nat.card (TunnellMap.ARep n) :=
  Nat.card_congr (aEquiv n)

/-- The balance hypothesis, transported to the project's coordinates. -/
theorem balance_transport {n : ℤ}
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Nat.card (TunnellMap.BRep n) = 2 * Nat.card (TunnellMap.ARep n) := by
  rw [← card_bRep n, ← card_aRep n]; exact hbalance

/-- Odd source representations in product and project coordinates. -/
def boEquiv (n : ℤ) : BOddRep n ≃ TunnellMap.BOddRep n where
  toFun p := ⟨⟨p.1.1.1, p.1.1.2.1, p.1.1.2.2⟩, p.1.2, p.2⟩
  invFun q := ⟨⟨(q.1.x, q.1.y, q.1.z), q.2.1⟩, q.2.2⟩
  left_inv := by rintro ⟨⟨⟨a, b, c⟩, h⟩, ho⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, h, ho⟩; rfl

theorem directSourceUsed_iff {n : ℤ} (p : BOddRep n) :
    DirectSourceUsed p ↔ TunnellMap.DirectSourceUsed (boEquiv n p) :=
  Iff.rfl

/-- Residual source points in product and project coordinates. -/
def brEquiv (n : ℤ) : BResidual n ≃ TunnellMap.BResidual n :=
  (boEquiv n).subtypeEquiv fun p => not_congr (directSourceUsed_iff p)

@[simp] theorem brEquiv_neg {n : ℤ} (p : BResidual n) :
    brEquiv n (negBResidual p) = TunnellMap.negBResidual (brEquiv n p) := rfl

@[simp] theorem arEquiv_neg {n : ℤ} (p : AResidual n) :
    arEquiv n (negAResidual p) = TunnellMap.negAResidual (arEquiv n p) := rfl

def coreTriple (v : Triple) : TunnellMap.Triple := ⟨v.1, v.2.1, v.2.2⟩

@[simp] theorem tripleLexKey_brEquiv {n : ℤ} (s : BResidual n) :
    tripleLexKey s.1.1.1 = TunnellMap.bResidualLexKey (brEquiv n s) := rfl

@[simp] theorem tripleLexKey_arEquiv {n : ℤ} (t : AResidual n) :
    tripleLexKey t.1.1 = TunnellMap.aResidualLexKey (arEquiv n t) := rfl

theorem canonicalBRepresentative_lt_neg {n : ℤ}
    (q : (TunnellMap.bResidualInvolution n).Orbit) :
    TunnellMap.bResidualLexKey (TunnellMap.canonicalBResidualRepresentative q) <
      TunnellMap.bResidualLexKey
        (TunnellMap.negBResidual (TunnellMap.canonicalBResidualRepresentative q)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change TunnellMap.bResidualLexKey
          ((TunnellMap.bResidualInvolution n).canonicalPoint
            TunnellMap.bResidualLexKey x) <
        TunnellMap.bResidualLexKey
          (TunnellMap.negBResidual
            ((TunnellMap.bResidualInvolution n).canonicalPoint
              TunnellMap.bResidualLexKey x))
      have hne : TunnellMap.bResidualLexKey x ≠
          TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) := by
        intro h
        exact (TunnellMap.bResidualInvolution n).no_fixed x
          (TunnellMap.bResidualLexKey_injective h).symm
      change TunnellMap.bResidualLexKey
          (if TunnellMap.bResidualLexKey x <
              TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) then x
            else TunnellMap.negBResidual x) <
        TunnellMap.bResidualLexKey
          (TunnellMap.negBResidual
            (if TunnellMap.bResidualLexKey x <
                TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) then x
              else TunnellMap.negBResidual x))
      by_cases hlt : TunnellMap.bResidualLexKey x <
          TunnellMap.bResidualLexKey (TunnellMap.negBResidual x)
      · simp [hlt]
      · have hrev : TunnellMap.bResidualLexKey (TunnellMap.negBResidual x) <
            TunnellMap.bResidualLexKey x :=
          lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        simp [hlt, hrev]

theorem canonicalARepresentative_lt_neg {n : ℤ} (hpos : 0 < n)
    (q : (TunnellMap.aResidualInvolution n hpos).Orbit) :
    TunnellMap.aResidualLexKey
        (TunnellMap.canonicalAResidualRepresentative hpos q) <
      TunnellMap.aResidualLexKey
        (TunnellMap.negAResidual
          (TunnellMap.canonicalAResidualRepresentative hpos q)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      change TunnellMap.aResidualLexKey
          ((TunnellMap.aResidualInvolution n hpos).canonicalPoint
            TunnellMap.aResidualLexKey x) <
        TunnellMap.aResidualLexKey
          (TunnellMap.negAResidual
            ((TunnellMap.aResidualInvolution n hpos).canonicalPoint
              TunnellMap.aResidualLexKey x))
      have hne : TunnellMap.aResidualLexKey x ≠
          TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) := by
        intro h
        exact (TunnellMap.aResidualInvolution n hpos).no_fixed x
          (TunnellMap.aResidualLexKey_injective h).symm
      change TunnellMap.aResidualLexKey
          (if TunnellMap.aResidualLexKey x <
              TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) then x
            else TunnellMap.negAResidual x) <
        TunnellMap.aResidualLexKey
          (TunnellMap.negAResidual
            (if TunnellMap.aResidualLexKey x <
                TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) then x
              else TunnellMap.negAResidual x))
      by_cases hlt : TunnellMap.aResidualLexKey x <
          TunnellMap.aResidualLexKey (TunnellMap.negAResidual x)
      · simp [hlt]
      · have hrev : TunnellMap.aResidualLexKey (TunnellMap.negAResidual x) <
            TunnellMap.aResidualLexKey x :=
          lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        simp [hlt, hrev]

noncomputable def canonicalBOfOrbit {n : ℤ}
    (q : (TunnellMap.bResidualInvolution n).Orbit) : CanonicalB n :=
  ⟨(brEquiv n).symm (TunnellMap.canonicalBResidualRepresentative q), by
    simpa using canonicalBRepresentative_lt_neg q⟩

noncomputable def canonicalAOfOrbit {n : ℤ} (hpos : 0 < n)
    (q : (TunnellMap.aResidualInvolution n hpos).Orbit) : CanonicalA n :=
  ⟨(arEquiv n).symm (TunnellMap.canonicalAResidualRepresentative hpos q), by
    simpa using canonicalARepresentative_lt_neg hpos q⟩

noncomputable def canonicalBOrbitEquiv (n : ℤ) :
    CanonicalB n ≃ (TunnellMap.bResidualInvolution n).Orbit where
  toFun s := (TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)
  invFun := canonicalBOfOrbit
  left_inv := by
    intro s
    apply Subtype.ext
    apply (brEquiv n).injective
    change brEquiv n ((brEquiv n).symm
        (TunnellMap.canonicalBResidualRepresentative
          ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)))) = brEquiv n s.1
    rw [Equiv.apply_symm_apply]
    change TunnellMap.canonicalBResidualRepresentative
        ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)) = brEquiv n s.1
    change (TunnellMap.bResidualInvolution n).canonicalPoint
        TunnellMap.bResidualLexKey (brEquiv n s.1) = brEquiv n s.1
    have hslt : TunnellMap.bResidualLexKey (brEquiv n s.1) <
        TunnellMap.bResidualLexKey
          ((TunnellMap.bResidualInvolution n).neg (brEquiv n s.1)) := by
      change tripleLexKey s.1.1.1.1 < tripleLexKey (negBResidual s.1).1.1.1
      exact s.2
    rw [TunnellMap.FreeInvolution.canonicalPoint, if_pos hslt]
  right_inv := by
    intro q
    change (TunnellMap.bResidualInvolution n).orbit
      (TunnellMap.canonicalBResidualRepresentative q) = q
    exact (TunnellMap.bResidualInvolution n).orbit_canonicalRepresentative
      TunnellMap.bResidualLexKey TunnellMap.bResidualLexKey_injective q

noncomputable def canonicalAOrbitEquiv {n : ℤ} (hpos : 0 < n) :
    CanonicalA n ≃ (TunnellMap.aResidualInvolution n hpos).Orbit where
  toFun t := (TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)
  invFun := canonicalAOfOrbit hpos
  left_inv := by
    intro t
    apply Subtype.ext
    apply (arEquiv n).injective
    change arEquiv n ((arEquiv n).symm
        (TunnellMap.canonicalAResidualRepresentative hpos
          ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)))) = arEquiv n t.1
    rw [Equiv.apply_symm_apply]
    change TunnellMap.canonicalAResidualRepresentative hpos
        ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t.1)) = arEquiv n t.1
    change (TunnellMap.aResidualInvolution n hpos).canonicalPoint
        TunnellMap.aResidualLexKey (arEquiv n t.1) = arEquiv n t.1
    have htlt : TunnellMap.aResidualLexKey (arEquiv n t.1) <
        TunnellMap.aResidualLexKey
          ((TunnellMap.aResidualInvolution n hpos).neg (arEquiv n t.1)) := by
      change tripleLexKey t.1.1.1 < tripleLexKey (negAResidual t.1).1.1
      exact t.2
    rw [TunnellMap.FreeInvolution.canonicalPoint, if_pos htlt]
  right_inv := by
    intro q
    change (TunnellMap.aResidualInvolution n hpos).orbit
      (TunnellMap.canonicalAResidualRepresentative hpos q) = q
    exact (TunnellMap.aResidualInvolution n hpos).orbit_canonicalRepresentative
      TunnellMap.aResidualLexKey TunnellMap.aResidualLexKey_injective q

theorem primitiveDirection_bridge (v : Triple) :
    coreTriple (primitiveDirection v) =
      TunnellMap.primitiveDirection (coreTriple v) := by
  let w := polynomialTriple (triplePolynomial v).primPart
  change coreTriple (orientDirection w) = TunnellMap.orientDirection (coreTriple w)
  by_cases h : FirstNonzeroPositive w
  · have hc : TunnellMap.FirstNonzeroPositive (coreTriple w) := h
    simp only [orientDirection, TunnellMap.orientDirection, if_pos h, if_pos hc]
  · have hc : ¬ TunnellMap.FirstNonzeroPositive (coreTriple w) := h
    simp only [orientDirection, TunnellMap.orientDirection, if_neg h, if_neg hc]
    rfl

theorem directionKey_bridge (v : Triple) :
    directionKey v =
      TunnellMap.DirectionKey.toLexKey (TunnellMap.directionKey (coreTriple v)) := by
  unfold directionKey TunnellMap.directionKey TunnellMap.DirectionKey.toLexKey
  rw [← primitiveDirection_bridge]
  rfl

@[simp] theorem sourceLift_bridge {n : ℤ} (s : BResidual n) :
    coreTriple (residualSourceLift s) =
      TunnellMap.residualSourceLift (brEquiv n s) := rfl

@[simp] theorem targetLift_bridge {n : ℤ} (t : AResidual n) :
    coreTriple (residualTargetLift t) =
      TunnellMap.residualTargetLift (arEquiv n t) := rfl

@[simp] theorem plusVector_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    coreTriple (plusVector s t) =
      TunnellMap.plusVector (brEquiv n s) (arEquiv n t) := rfl

@[simp] theorem minusVector_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    coreTriple (minusVector s t) =
      TunnellMap.minusVector (brEquiv n s) (arEquiv n t) := rfl

theorem residualEdgeKey_bridge {n : ℤ} (s : BResidual n) (t : AResidual n) :
    residualEdgeKey s t =
      TunnellMap.DirectionKey.toLexKey
        (TunnellMap.representativeEdgeKey (brEquiv n s) (arEquiv n t)) := by
  rw [residualEdgeKey, TunnellMap.representativeEdgeKey, directionKey_bridge,
    directionKey_bridge, plusVector_bridge, minusVector_bridge]
  exact (show Monotone TunnellMap.DirectionKey.toLexKey from fun _ _ h => h).map_min.symm

theorem residualEdgeKey_orbit_bridge {n : ℤ} (hpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    residualEdgeKey s t = TunnellMap.DirectionKey.toLexKey
      (TunnellMap.orbitEdgeKey hpos
        ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s))
        ((TunnellMap.aResidualInvolution n hpos).orbit (arEquiv n t))) := by
  rw [residualEdgeKey_bridge,
    TunnellMap.representativeEdgeKey_eq_orbitEdgeKey]

theorem preferredTarget_bridge {n : ℤ} (hpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    arEquiv n (preferredTarget s t) =
      TunnellMap.preferredTarget (brEquiv n s) (arEquiv n t) := by
  unfold preferredTarget TunnellMap.preferredTarget
  rw [directionKey_bridge, directionKey_bridge, plusVector_bridge, minusVector_bridge]
  by_cases h : TunnellMap.directionKey
      (TunnellMap.plusVector (brEquiv n s) (arEquiv n t)) <
    TunnellMap.directionKey
      (TunnellMap.minusVector (brEquiv n s) (arEquiv n t))
  · have hlex : TunnellMap.DirectionKey.toLexKey
        (TunnellMap.directionKey
          (TunnellMap.plusVector (brEquiv n s) (arEquiv n t))) <
      TunnellMap.DirectionKey.toLexKey
        (TunnellMap.directionKey
          (TunnellMap.minusVector (brEquiv n s) (arEquiv n t))) := h
    simp [h, hlex]
  · have hnlex : ¬ TunnellMap.DirectionKey.toLexKey
        (TunnellMap.directionKey
          (TunnellMap.plusVector (brEquiv n s) (arEquiv n t))) <
      TunnellMap.DirectionKey.toLexKey
        (TunnellMap.directionKey
          (TunnellMap.minusVector (brEquiv n s) (arEquiv n t))) := h
    simp [h, hnlex, arEquiv_neg]

theorem coreResidualOrbitCardEq {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    Fintype.card (TunnellMap.bResidualInvolution n).Orbit =
      Fintype.card (TunnellMap.aResidualInvolution n hpos).Orbit :=
  TunnellMap.residual_orbit_card_eq hodd hpos
    (TunnellMap.odd_card_eq_of_full_balance
      (TunnellMap.fintype_balance_of_nat_card (balance_transport hbalance)))

noncomputable def registeredResidualMatching {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    CanonicalB n ≃ CanonicalA n :=
  (canonicalBOrbitEquiv n).trans
    ((TunnellMap.residualOrbitMatching hpos
      (coreResidualOrbitCardEq hodd hpos hbalance)).trans
        (canonicalAOrbitEquiv hpos).symm)

@[simp] theorem registeredResidualMatching_orbit_apply {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : CanonicalB n) :
    canonicalAOrbitEquiv hpos (registeredResidualMatching hodd hpos hbalance s) =
      TunnellMap.residualOrbitMatching hpos
        (coreResidualOrbitCardEq hodd hpos hbalance) (canonicalBOrbitEquiv n s) := by
  simp [registeredResidualMatching]

@[simp] theorem registeredResidualMatching_orbit_symm {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (t : CanonicalA n) :
    canonicalBOrbitEquiv n ((registeredResidualMatching hodd hpos hbalance).symm t) =
      (TunnellMap.residualOrbitMatching hpos
        (coreResidualOrbitCardEq hodd hpos hbalance)).symm
          (canonicalAOrbitEquiv hpos t) := by
  simp [registeredResidualMatching]

@[simp] theorem registeredResidualMatching_target_rep {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : CanonicalB n) :
    arEquiv n (registeredResidualMatching hodd hpos hbalance s).1 =
      TunnellMap.canonicalAResidualRepresentative hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)
            ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1))) := by
  change (arEquiv n) ((arEquiv n).symm _) = _
  exact (arEquiv n).apply_symm_apply _

theorem registeredResidualMatching_stable {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    StableResidualMatching (registeredResidualMatching hodd hpos hbalance) := by
  intro s t hblock
  have hstable := TunnellMap.residualOrbitMatching_stable hpos
    (coreResidualOrbitCardEq hodd hpos hbalance)
      (canonicalBOrbitEquiv n s) (canonicalAOrbitEquiv hpos t)
  apply hstable
  rcases hblock with ⟨hs, ht⟩
  constructor
  · rw [residualEdgeKey_orbit_bridge hpos,
      residualEdgeKey_orbit_bridge hpos] at hs
    change TunnellMap.orbitEdgeKey hpos (canonicalBOrbitEquiv n s)
        (canonicalAOrbitEquiv hpos t) <
      TunnellMap.orbitEdgeKey hpos (canonicalBOrbitEquiv n s)
        (canonicalAOrbitEquiv hpos
          (registeredResidualMatching hodd hpos hbalance s)) at hs
    rw [registeredResidualMatching_orbit_apply] at hs
    exact hs
  · rw [residualEdgeKey_orbit_bridge hpos,
      residualEdgeKey_orbit_bridge hpos] at ht
    change TunnellMap.orbitEdgeKey hpos (canonicalBOrbitEquiv n s)
        (canonicalAOrbitEquiv hpos t) <
      TunnellMap.orbitEdgeKey hpos
        (canonicalBOrbitEquiv n
          ((registeredResidualMatching hodd hpos hbalance).symm t))
        (canonicalAOrbitEquiv hpos t) at ht
    rw [registeredResidualMatching_orbit_symm] at ht
    exact ht

noncomputable def registeredResidualRanking {n : ℤ} (hpos : 0 < n) :
    TunnellMap.GloballyRanked DirectionKey (CanonicalB n) (CanonicalA n) where
  rank := fun s t => residualEdgeKey s.1 t.1
  source_injective := by
    intro s t₁ t₂ hkey
    apply (canonicalAOrbitEquiv hpos).injective
    apply (TunnellMap.residualOrbitRanking hpos).source_injective
    apply TunnellMap.DirectionKey.toLexKey_injective
    exact (residualEdgeKey_orbit_bridge hpos s.1 t₁.1).symm.trans
      (hkey.trans (residualEdgeKey_orbit_bridge hpos s.1 t₂.1))
  target_injective := by
    intro t s₁ s₂ hkey
    apply (canonicalBOrbitEquiv n).injective
    apply (TunnellMap.residualOrbitRanking hpos).target_injective
    apply TunnellMap.DirectionKey.toLexKey_injective
    exact (residualEdgeKey_orbit_bridge hpos s₁.1 t.1).symm.trans
      (hkey.trans (residualEdgeKey_orbit_bridge hpos s₂.1 t.1))

theorem registeredResidualMatching_unique {n : ℤ} (hodd : Odd n)
    (hpos : 0 < n) (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (N : CanonicalB n ≃ CanonicalA n) (hN : StableResidualMatching N) :
    N = registeredResidualMatching hodd hpos hbalance := by
  classical
  letI : Fintype (CanonicalB n) :=
    Fintype.ofEquiv _ (canonicalBOrbitEquiv n).symm
  letI : Fintype (CanonicalA n) :=
    Fintype.ofEquiv _ (canonicalAOrbitEquiv hpos).symm
  change (registeredResidualRanking hpos).Stable N at hN
  have hM := registeredResidualMatching_stable hodd hpos hbalance
  change (registeredResidualRanking hpos).Stable
    (registeredResidualMatching hodd hpos hbalance) at hM
  exact TunnellMap.GloballyRanked.stable_unique
    (registeredResidualRanking hpos) N
      (registeredResidualMatching hodd hpos hbalance) hN hM

/-! ## The registered map -/

/-- **The map of the theorem**: the project's fallback-free assembled
executable map `TunnellMap.paperTunnellMapTotal`, read in product
coordinates. -/
def tunnellMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BRep n → ARep n := fun p =>
  (aEquiv n).symm
    (TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
      (bEquiv n p))

/-- The fallback-free executable residual map, read in product coordinates. -/
def tunnellResidualMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BResidual n → AResidual n := fun s =>
  (arEquiv n).symm
    (TunnellMap.RecordDA.residualMapExecTotal hodd hpos hsq
      (coreResidualOrbitCardEq hodd hpos hbalance) (brEquiv n s))

/-- The residual inverse obtained by rerunning the same deterministic
computation, read in product coordinates. -/
def tunnellResidualInverse {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    AResidual n → BResidual n := fun t =>
  (brEquiv n).symm
    (TunnellMap.RecordDA.inverseByRerunExecTotal hodd hpos hsq
      (coreResidualOrbitCardEq hodd hpos hbalance) (arEquiv n t))

theorem tunnellResidualInverse_left {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    tunnellResidualInverse hodd hpos hsq hbalance
      (tunnellResidualMap hodd hpos hsq hbalance s) = s := by
  apply (brEquiv n).injective
  simp only [tunnellResidualInverse, tunnellResidualMap,
    Equiv.apply_symm_apply]
  exact TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecTotal
    hodd hpos hsq (coreResidualOrbitCardEq hodd hpos hbalance) (brEquiv n s)

theorem tunnellResidualInverse_right {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (t : AResidual n) :
    tunnellResidualMap hodd hpos hsq hbalance
      (tunnellResidualInverse hodd hpos hsq hbalance t) = t := by
  apply (arEquiv n).injective
  simp only [tunnellResidualMap, tunnellResidualInverse,
    Equiv.apply_symm_apply]
  exact TunnellMap.RecordDA.residualMapExecTotal_inverseByRerunExecTotal
    hodd hpos hsq (coreResidualOrbitCardEq hodd hpos hbalance) (arEquiv n t)

theorem tunnellMap_apply {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance p) =
      TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
        (bEquiv n p) := by
  rw [tunnellMap, Equiv.apply_symm_apply]

/-- The coordinates of the image, in product form. -/
theorem tunnellMap_val {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      ((TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.x,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.y,
        (TunnellMap.paperTunnellMapTotal hodd hpos hsq
          (balance_transport hbalance) (bEquiv n p)).1.z) := rfl

/-- **Every target has exactly two preimages.** -/
theorem tunnellMap_exactly_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂ : BRep n,
      p₁ ≠ p₂ ∧
      tunnellMap hodd hpos hsq hbalance p₁ = a ∧
      tunnellMap hodd hpos hsq hbalance p₂ = a ∧
      ∀ p, tunnellMap hodd hpos hsq hbalance p = a ↔ p = p₁ ∨ p = p₂ := by
  classical
  obtain ⟨q₁, q₂, hne, h₁, h₂, hfib⟩ :=
    TunnellMap.paperTunnellMapTotal_exactly_two hodd hpos hsq
      (balance_transport hbalance) (aEquiv n a)
  refine ⟨(bEquiv n).symm q₁, (bEquiv n).symm q₂, ?_, ?_, ?_, ?_⟩
  · simpa using hne
  · simp only [tunnellMap, Equiv.apply_symm_apply, h₁, Equiv.symm_apply_apply]
  · simp only [tunnellMap, Equiv.apply_symm_apply, h₂, Equiv.symm_apply_apply]
  · intro p
    have hiff : tunnellMap hodd hpos hsq hbalance p = a ↔
        TunnellMap.paperTunnellMapTotal hodd hpos hsq (balance_transport hbalance)
          (bEquiv n p) = aEquiv n a := by
      constructor
      · intro h
        exact (Equiv.symm_apply_eq (aEquiv n)).mp h
      · intro h
        simp only [tunnellMap, h, Equiv.symm_apply_apply]
    rw [hiff, hfib (bEquiv n p)]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [← h, Equiv.symm_apply_apply])
      · exact Or.inr (by rw [← h, Equiv.symm_apply_apply])
    · rintro (h | h)
      · exact Or.inl (by rw [h, Equiv.apply_symm_apply])
      · exact Or.inr (by rw [h, Equiv.apply_symm_apply])

/-! ## The branch specification -/

/-- **The even branch.** -/
theorem tunnellMap_even {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.2.2 % 2 = 0) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1, p.1.2.1, p.1.2.2 / 2) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_even hodd hpos hsq
    (balance_transport hbalance) (bEquiv n p) hz]
  rfl

/-- **The first quarter-turn.** -/
theorem tunnellMap_quarterTurn_one {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (4 * ((p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) - p.1.2.1,
        p.1.1 - 2 * p.1.2.2,
        (p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_quarterTurn_one hodd hpos
    hsq (balance_transport hbalance) (bEquiv n p) hz h₁]
  rfl

/-- **The second quarter-turn.** -/
theorem tunnellMap_quarterTurn_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1 - 2 * p.1.2.2 + 4 * ((p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8),
        -p.1.1 - 2 * p.1.2.2,
        (p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_quarterTurn_two hodd hpos
    hsq (balance_transport hbalance) (bEquiv n p) hz h₁ h₂]
  rfl

/-- **The third quarter-turn.** -/
theorem tunnellMap_quarterTurn_three {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : (4 : ℤ) ∣ p.1.1) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (2 * p.1.2.2, p.1.2.1, -(p.1.1 / 4)) := by
  rw [tunnellMap_val, TunnellMap.paperTunnellMapTotal_quarterTurn_three hodd hpos
    hsq (balance_transport hbalance) (bEquiv n p) hz h₁ h₂ h₃]
  rfl

/-- **The residual branch lands in the residual targets.** -/
theorem tunnellMap_residual_target {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : ¬ (4 : ℤ) ∣ p.1.1) :
    ¬ DirectTargetUsed (tunnellMap hodd hpos hsq hbalance p) := by
  rw [directTargetUsed_iff, tunnellMap_apply]
  exact TunnellMap.paperTunnellMapTotal_residual_target hodd hpos hsq
    (balance_transport hbalance) (bEquiv n p) hz
    (fun hc => by
      rcases hc with hc | hc | hc
      · exact h₁ hc
      · exact h₂ hc
      · exact h₃ hc)

theorem tunnellMap_residual_value {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (x : BResidual n) :
    aEquiv n (tunnellMap hodd hpos hsq hbalance x.1.1) =
      (TunnellMap.canonicalResidualMapOf hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)) (brEquiv n x)).1 := by
  let p : TunnellMap.BRep n := bEquiv n x.1.1
  let q : TunnellMap.BOddRep n := boEquiv n x.1
  let y : TunnellMap.BResidual n := brEquiv n x
  have hz : ¬ p.1.z % 2 = 0 := by
    change ¬ x.1.1.1.2.2 % 2 = 0
    have hoddz : x.1.1.1.2.2 % 2 = 1 := Int.odd_iff.mp x.1.2
    omega
  have hd : ¬ TunnellMap.SourceUsedTriple p.1 := by
    intro hc
    apply x.2
    exact (directSourceUsed_iff x.1).mpr hc
  have hdq : ¬ TunnellMap.SourceUsedTriple q.1 := hd
  have hres := TunnellMap.RecordDA.residualMapExecOpt_eq_some hodd hpos hsq
    (coreResidualOrbitCardEq hodd hpos hbalance) y
  have hopt : TunnellMap.paperTunnellMapExecOpt hpos hsq p =
      some (TunnellMap.canonicalResidualMapOf hpos
        (TunnellMap.residualOrbitMatching hpos
          (coreResidualOrbitCardEq hodd hpos hbalance)) y).1 := by
    rw [TunnellMap.paperTunnellMapExecOpt, dif_neg hz]
    change TunnellMap.oddMapExecOpt hpos hsq q = _
    calc
      TunnellMap.oddMapExecOpt hpos hsq q = Option.map Subtype.val
          (TunnellMap.RecordDA.residualMapExecOpt hpos hsq y) := dif_neg hdq
      _ = _ := congrArg (Option.map Subtype.val) hres
  rw [tunnellMap_apply]
  exact Option.some.inj
    ((TunnellMap.some_paperTunnellMapTotal hodd hpos hsq
      (balance_transport hbalance) p).trans hopt)

theorem tunnellResidualMap_agrees {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    (tunnellResidualMap hodd hpos hsq hbalance s).1 =
      tunnellMap hodd hpos hsq hbalance s.1.1 := by
  apply (aEquiv n).injective
  rw [tunnellMap_residual_value]
  change (arEquiv n (tunnellResidualMap hodd hpos hsq hbalance s)).1 = _
  rw [tunnellResidualMap, Equiv.apply_symm_apply,
    TunnellMap.RecordDA.residualMapExecTotal_eq_canonical]

/-- **The residual branch is the projectively ranked stable perfect
equivalence with its canonical sign lift.** -/
theorem tunnellMap_residual_stable {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    ∃ M : CanonicalB n ≃ CanonicalA n,
      StableResidualMatching M ∧
        (∀ N : CanonicalB n ≃ CanonicalA n,
          StableResidualMatching N → N = M) ∧
        ∀ s : CanonicalB n,
          tunnellMap hodd hpos hsq hbalance s.1.1.1 =
              (preferredTarget s.1 (M s).1).1 ∧
            tunnellMap hodd hpos hsq hbalance (negBResidual s.1).1.1 =
              (preferredTarget (negBResidual s.1) (M s).1).1 := by
  let M := registeredResidualMatching hodd hpos hbalance
  refine ⟨M, registeredResidualMatching_stable hodd hpos hbalance,
    ?_, ?_⟩
  · intro N hN
    exact registeredResidualMatching_unique hodd hpos hbalance N hN
  intro s
  constructor
  · apply (aEquiv n).injective
    rw [tunnellMap_residual_value]
    change _ = (arEquiv n (preferredTarget s.1 (M s).1)).1
    apply congrArg Subtype.val
    rw [preferredTarget_bridge hpos]
    rw [TunnellMap.canonicalResidualMapOf_eq_signedPartner,
      TunnellMap.signedPartner_eq_preferredTarget]
    change TunnellMap.preferredTarget (brEquiv n s.1)
        (TunnellMap.canonicalAResidualRepresentative hpos
          (TunnellMap.residualOrbitMatching hpos
            (coreResidualOrbitCardEq hodd hpos hbalance)
              ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1)))) =
      TunnellMap.preferredTarget (brEquiv n s.1) (arEquiv n (M s).1)
    rw [show arEquiv n (M s).1 =
        TunnellMap.canonicalAResidualRepresentative hpos
          (TunnellMap.residualOrbitMatching hpos
            (coreResidualOrbitCardEq hodd hpos hbalance)
              ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1))) by
      simpa [M] using registeredResidualMatching_target_rep hodd hpos hbalance s]
  · apply (aEquiv n).injective
    rw [tunnellMap_residual_value]
    change _ = (arEquiv n (preferredTarget (negBResidual s.1) (M s).1)).1
    apply congrArg Subtype.val
    rw [preferredTarget_bridge hpos]
    rw [TunnellMap.canonicalResidualMapOf_eq_signedPartner,
      TunnellMap.signedPartner_eq_preferredTarget]
    rw [brEquiv_neg]
    have horbit : (TunnellMap.bResidualInvolution n).orbit
        (TunnellMap.negBResidual (brEquiv n s.1)) =
      (TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1) :=
      (TunnellMap.bResidualInvolution n).orbit_neg (brEquiv n s.1)
    rw [horbit]
    rw [show arEquiv n (M s).1 =
        TunnellMap.canonicalAResidualRepresentative hpos
          (TunnellMap.residualOrbitMatching hpos
            (coreResidualOrbitCardEq hodd hpos hbalance)
              ((TunnellMap.bResidualInvolution n).orbit (brEquiv n s.1))) by
      simpa [M] using registeredResidualMatching_target_rep hodd hpos hbalance s]

end TunnellChallenge

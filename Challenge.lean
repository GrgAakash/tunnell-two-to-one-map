import Mathlib
/-!
# A two-to-one map under the Tunnell balance

For odd positive squarefree `n`, assume the explicit balance
`Nat.card (BRep n) = 2 * Nat.card (ARep n)`.  The registered fallback-free map
`BRep n → ARep n` has exactly two distinct and exhaustive preimages over every
target.  Its even and three quarter-turn branches are fixed by coordinate
formulas.  The remaining branch is fixed by the unique stable equivalence of
canonical antipodal representatives for the primitive-midpoint projective
ranking and by the preferred-sign lift.

The residual forward map, its inverse, agreement with the assembled map, and
both inverse identities are also registered.  The submitted Solution computes
the inverse by rerunning the deterministic generator/deferred-acceptance
machine; the Challenge fixes its extensional value through the inverse laws.
Tunnell's modular-form theorem is not formalized, so the Challenge imports its
established cardinality balance as a hypothesis.  For odd positive squarefree
congruent `n`, Tunnell's theorem supplies that hypothesis.  No new
congruent-number criterion is claimed.
-/
namespace TunnellChallenge
/-- `BRep n` — the representations of `n` by `2x² + y² + 8z²`. -/
def BRep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 8 * p.2.2 ^ 2 = n}
/-- `ARep n` — the representations of `n` by `2u² + v² + 32w² = n`. -/
def ARep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 32 * p.2.2 ^ 2 = n}

/-- A target `(u, v, w) ∈ ARep n` is *directly used* when it is the image of
one of the three quarter-turn branches.  Each disjunct is the congruence
characterising the image of one branch: `u + 4w - v ≡ 4 (mod 8)`,
`u - 4w + v ≡ 4 (mod 8)`, and `u ≡ 2 (mod 4)`. -/
def DirectTargetUsed {n : ℤ} (p : ARep n) : Prop :=
  (∃ q : ℤ, Odd q ∧ p.1.1 + 4 * p.1.2.2 - p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 - 4 * p.1.2.2 + p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 = 2 * q)

/-- The *residual* targets: the targets left over by the three quarter-turn
branches.  These are the targets matched by the stable-matching branch. -/
def AResidual (n : ℤ) : Type := {p : ARep n // ¬ DirectTargetUsed p}
/-! ## Residual stable-matching specification -/

/-- The odd source representations. -/
def BOddRep (n : ℤ) : Type := {p : BRep n // Odd p.1.2.2}

/-- The union of the three quarter-turn source domains. -/
def DirectSourceUsed {n : ℤ} (p : BOddRep n) : Prop :=
  (∃ q : ℤ, p.1.1.1 + 2 * p.1.1.2.2 + p.1.1.2.1 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.2.1 - p.1.1.1 + 2 * p.1.1.2.2 = 8 * q) ∨
    (∃ q : ℤ, p.1.1.1 = 4 * q)

/-- Odd sources not used by a quarter-turn branch. -/
def BResidual (n : ℤ) : Type := {p : BOddRep n // ¬ DirectSourceUsed p}
/-- Negation on residual source points. -/
def negBResidual {n : ℤ} (p : BResidual n) : BResidual n := by
  refine ⟨⟨⟨(-p.1.1.1.1, -p.1.1.1.2.1, -p.1.1.1.2.2), ?_⟩, p.1.2.neg⟩, ?_⟩
  · simpa using p.1.1.2
  · intro h
    apply p.2
    rcases h with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩
    · exact Or.inr (Or.inl ⟨-q, by dsimp at hq ⊢; linarith⟩)
    · exact Or.inr (Or.inr ⟨-q, by dsimp at hq ⊢; linarith⟩)

/-- Negation on residual target points. -/
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

/-- The lexicographically smaller member of each residual source orbit. -/
def CanonicalB (n : ℤ) : Type :=
  {p : BResidual n // tripleLexKey p.1.1.1 < tripleLexKey (negBResidual p).1.1.1}

/-- The lexicographically smaller member of each residual target orbit. -/
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

/-- The projective midpoint key used to rank a residual edge. -/
noncomputable def residualEdgeKey {n : ℤ} (s : BResidual n) (t : AResidual n) :
    DirectionKey :=
  min (directionKey (plusVector s t)) (directionKey (minusVector s t))
/-- Stability of a perfect equivalence in the complete bipartite graph of
canonical residual points. -/
def StableResidualMatching {n : ℤ} (M : CanonicalB n ≃ CanonicalA n) : Prop :=
  ∀ s t, ¬ (residualEdgeKey s.1 t.1 < residualEdgeKey s.1 (M s).1 ∧
    residualEdgeKey s.1 t.1 < residualEdgeKey (M.symm t).1 t.1)
/-- The canonical sign lift of a matched residual target. -/
noncomputable def preferredTarget {n : ℤ} (s : BResidual n)
    (t : AResidual n) : AResidual n :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    t
  else
    negAResidual t

/-- **The map of the theorem.**  A definition hole: the Solution supplies the
explicit computable assembled map described in the module documentation.  It
takes exactly the hypotheses of the theorem; in particular no default residual
target is required, so it is defined also when the residual sets are empty. -/
def tunnellMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BRep n → ARep n := sorry

/-- The fallback-free executable residual branch, exposed separately so that
its independently regenerated reverse interface can be registered. -/
def tunnellResidualMap {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    BResidual n → AResidual n := sorry

/-- The fallback-free residual inverse.  The submitted implementation reruns
the deterministic arithmetic computation; it does not retain a matching
table or a proposal transcript. -/
def tunnellResidualInverse {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n)) :
    AResidual n → BResidual n := sorry

/-- The separately exposed residual map agrees pointwise with the residual
branch of the assembled map. -/
theorem tunnellResidualMap_agrees {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    (tunnellResidualMap hodd hpos hsq hbalance s).1 =
      tunnellMap hodd hpos hsq hbalance s.1.1 := sorry

/-- The regenerated inverse is a left inverse of the residual map. -/
theorem tunnellResidualInverse_left {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (s : BResidual n) :
    tunnellResidualInverse hodd hpos hsq hbalance
      (tunnellResidualMap hodd hpos hsq hbalance s) = s := sorry

/-- The regenerated inverse is a right inverse of the residual map. -/
theorem tunnellResidualInverse_right {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (t : AResidual n) :
    tunnellResidualMap hodd hpos hsq hbalance
      (tunnellResidualInverse hodd hpos hsq hbalance t) = t := sorry

/-- **Every target has exactly two preimages.**  Let `n` be odd, positive and
squarefree and assume the Tunnell balance `|BRep n| = 2 |ARep n|`.  Then for
every target `a` there are two *distinct* sources `p₁ ≠ p₂` mapping to `a`,
and a source maps to `a` if and only if it is one of those two; so the fibre
over `a` is exactly `{p₁, p₂}`. -/
theorem tunnellMap_exactly_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂ : BRep n,
      p₁ ≠ p₂ ∧
      tunnellMap hodd hpos hsq hbalance p₁ = a ∧
      tunnellMap hodd hpos hsq hbalance p₂ = a ∧
      ∀ p, tunnellMap hodd hpos hsq hbalance p = a ↔ p = p₁ ∨ p = p₂ := sorry

/-- **The even branch.**  A source with even third coordinate is halved in
that coordinate. -/
theorem tunnellMap_even {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.2.2 % 2 = 0) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1, p.1.2.1, p.1.2.2 / 2) := sorry

/-- **The first quarter-turn.**  If the third coordinate is odd and
`8 ∣ x + 2z + y`, with quotient `q`, the image is `(4q - y, x - 2z, q)`. -/
theorem tunnellMap_quarterTurn_one {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (4 * ((p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) - p.1.2.1,
        p.1.1 - 2 * p.1.2.2,
        (p.1.1 + 2 * p.1.2.2 + p.1.2.1) / 8) := sorry

/-- **The second quarter-turn.**  If the third coordinate is odd,
`8 ∤ x + 2z + y` and `8 ∣ y - x + 2z`, with quotient `q`, the image is
`(x - 2z + 4q, -x - 2z, q)`. -/
theorem tunnellMap_quarterTurn_two {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2)) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (p.1.1 - 2 * p.1.2.2 + 4 * ((p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8),
        -p.1.1 - 2 * p.1.2.2,
        (p.1.2.1 - p.1.1 + 2 * p.1.2.2) / 8) := sorry

/-- **The third quarter-turn.**  If the third coordinate is odd, neither of
the first two congruences holds and `4 ∣ x`, with quotient `q`, the image is
`(2z, y, -q)`. -/
theorem tunnellMap_quarterTurn_three {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : (4 : ℤ) ∣ p.1.1) :
    (tunnellMap hodd hpos hsq hbalance p).1 =
      (2 * p.1.2.2, p.1.2.1, -(p.1.1 / 4)) := sorry

/-- **The residual branch lands in the residual targets.**  A source with odd
third coordinate satisfying none of the three congruences is mapped to a
target that no quarter-turn branch produces.  The following theorem fixes the
stable-matching and sign-lift specification. -/
theorem tunnellMap_residual_target {n : ℤ} (hodd : Odd n) (hpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.2.2 % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.1 + 2 * p.1.2.2 + p.1.2.1))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.2.1 - p.1.1 + 2 * p.1.2.2))
    (h₃ : ¬ (4 : ℤ) ∣ p.1.1) :
    ¬ DirectTargetUsed (tunnellMap hodd hpos hsq hbalance p) := sorry

/-- **The residual branch is the projectively ranked stable perfect equivalence
with its canonical sign lift.**  It uses the lexicographically canonical
antipodal representatives and the primitive projective edge key of
the two midpoint directions, and both signs of every source orbit are required
to follow the preferred-sign rule.  Uniqueness below is among stable perfect
equivalences. -/
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
              (preferredTarget (negBResidual s.1) (M s).1).1 := sorry

end TunnellChallenge

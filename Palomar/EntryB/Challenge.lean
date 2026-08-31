import Mathlib

/-!
# An executable certificate at `n = 41`

Let

* `BRep n = {(x,y,z) ∈ ℤ³ : 2x² + y² + 8z² = n}`,
* `ARep n = {(u,v,w) ∈ ℤ³ : 2u² + v² + 32w² = n}`

be the two ternary representation sets occurring in Tunnell's work on
congruent numbers.  This entry records the complete `n = 41` instance of the
two-to-one construction:

1. the two representation counts `|B₄₁| = 32` and `|A₄₁| = 16`, so that the
   balance `|B₄₁| = 2|A₄₁|` holds;
2. exactly two preimages of every target under the map `tunnellMap41`;
3. four canonical residual-orbit representative pairs, as literal coordinate
   values of the map;
4. the two complete fibres
   `tunnellMap41⁻¹(2,-1,1) = {(2,-1,2), (-4,-1,1)}` (quarter-turn lane) and
   `tunnellMap41⁻¹(4,-3,0) = {(4,-3,0), (-2,-5,1)}` (stable-matching lane);
5. the literal six-event trace certificate associated with the residual
   matching, together with its event counts.

## Definition holes, and what pins them

`tunnellMap41` and `daTrace41` are *definition holes*: the Challenge fixes
their types and the Solution supplies their values.  The Solution's
fallback-free `tunnellMap41` is the assembled computable map of the construction (even
branch, three quarter-turn branches, and the stable matching of the remaining
antipodal orbits computed by an arithmetic generator feeding deferred
acceptance), instantiated at `n = 41`; its `daTrace41` is filled in the
submitted Solution by converting the actual instrumented run to plain integer
tuples.

The map is pinned at this finite level by `tunnellMap41_exactly_two`, by the four literal values in
`residualPairs_41` and by the two complete fibre statements.  The trace is
pinned by `daTrace41_eq` together with `daTrace41_accepted_image`, which ties
every free-target acceptance event of the trace to the value of the registered map at the
proposing source.  The *algorithm* producing the trace is not part of this
finite Challenge; Entry A registers the family-level stable-matching
specification.  Thus this Comparator contract registers the literal trace, its
length, its two non-free-target-accepting events, and its agreement with the map, but does not
by itself certify the provenance of that list from the full generator state.

## External input

Tunnell's theorem is **not** formalized and is not used: at `n = 41` the
balance `|B₄₁| = 2|A₄₁|` is proved here by finite computation.
-/

namespace TunnellN41

/-- `BRep n` — the representations of `n` by `2x² + y² + 8z²`. -/
def BRep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 8 * p.2.2 ^ 2 = n}

/-- `ARep n` — the representations of `n` by `2u² + v² + 32w²`. -/
def ARep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 32 * p.2.2 ^ 2 = n}

/-- A target `(u, v, w) ∈ ARep n` is *directly used* when it is the image of
one of the three quarter-turn branches: `u + 4w - v ≡ 4 (mod 8)`,
`u - 4w + v ≡ 4 (mod 8)`, or `u ≡ 2 (mod 4)`. -/
def DirectTargetUsed {n : ℤ} (p : ARep n) : Prop :=
  (∃ q : ℤ, Odd q ∧ p.1.1 + 4 * p.1.2.2 - p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 - 4 * p.1.2.2 + p.1.2.1 = 4 * q) ∨
    (∃ q : ℤ, Odd q ∧ p.1.1 = 2 * q)

/-- The *residual* targets: those left over by the three quarter-turn
branches. -/
def AResidual (n : ℤ) : Type := {p : ARep n // ¬ DirectTargetUsed p}

/-! ## The two representation counts -/

/-- **`|B₄₁| = 32`.** -/
theorem card_BRep_41 : Nat.card (BRep 41) = 32 := sorry

/-- **`|A₄₁| = 16`.**  With `card_BRep_41` this is the balance
`|B₄₁| = 2 |A₄₁|` at `n = 41`. -/
theorem card_ARep_41 : Nat.card (ARep 41) = 16 := sorry

/-! ## The map at `n = 41` -/

/-- **The assembled fallback-free map at `n = 41`.** -/
def tunnellMap41 : BRep 41 → ARep 41 := sorry

/-- **Every target of `A₄₁` has exactly two preimages in `B₄₁`.** -/
theorem tunnellMap41_exactly_two (a : ARep 41) :
    ∃ p₁ p₂ : BRep 41,
      p₁ ≠ p₂ ∧
      tunnellMap41 p₁ = a ∧
      tunnellMap41 p₂ = a ∧
      ∀ p, tunnellMap41 p = a ↔ p = p₁ ∨ p = p₂ := sorry

/-! ## Four canonical residual-orbit representative pairs -/

/-- The first of four canonical residual source-orbit representatives at
`n = 41`. -/
def source1 : BRep 41 := ⟨(-2, -5, -1), by norm_num⟩
/-- The second canonical residual source-orbit representative. -/
def source2 : BRep 41 := ⟨(-2, -5, 1), by norm_num⟩
/-- The third canonical residual source-orbit representative. -/
def source3 : BRep 41 := ⟨(-2, 5, -1), by norm_num⟩
/-- The fourth canonical residual source-orbit representative. -/
def source4 : BRep 41 := ⟨(-2, 5, 1), by norm_num⟩

/-- **Four canonical residual-orbit representative pairs at `n = 41`**, in
the original coordinates:
`(-2,-5,-1) ↦ (4,3,0)`, `(-2,-5,1) ↦ (4,-3,0)`,
`(-2,5,-1) ↦ (0,-3,1)`, `(-2,5,1) ↦ (0,-3,-1)`. -/
theorem residualPairs_41 :
    (tunnellMap41 source1).1 = (4, 3, 0) ∧
      (tunnellMap41 source2).1 = (4, -3, 0) ∧
      (tunnellMap41 source3).1 = (0, -3, 1) ∧
      (tunnellMap41 source4).1 = (0, -3, -1) := sorry

/-! ## The two complete fibres -/

/-- The target `(2,-1,1)` of the quarter-turn lane. -/
def targetDirect : ARep 41 := ⟨(2, -1, 1), by norm_num⟩
/-- Its even preimage. -/
def sourceDirectEven : BRep 41 := ⟨(2, -1, 2), by norm_num⟩
/-- Its odd preimage. -/
def sourceDirectOdd : BRep 41 := ⟨(-4, -1, 1), by norm_num⟩

/-- The target `(4,-3,0)` of the stable-matching lane. -/
def targetResidual : ARep 41 := ⟨(4, -3, 0), by norm_num⟩
/-- Its even preimage. -/
def sourceResidualEven : BRep 41 := ⟨(4, -3, 0), by norm_num⟩
/-- Its odd preimage. -/
def sourceResidualOdd : BRep 41 := ⟨(-2, -5, 1), by norm_num⟩

/-- **The complete fibre of the quarter-turn lane**:
`tunnellMap41⁻¹(2,-1,1) = {(2,-1,2), (-4,-1,1)}`. -/
theorem fibre_direct_41 (p : BRep 41) :
    tunnellMap41 p = targetDirect ↔
      p = sourceDirectEven ∨ p = sourceDirectOdd := sorry

/-- **The complete fibre of the stable-matching lane**:
`tunnellMap41⁻¹(4,-3,0) = {(4,-3,0), (-2,-5,1)}`. -/
theorem fibre_residual_41 (p : BRep 41) :
    tunnellMap41 p = targetResidual ↔
      p = sourceResidualEven ∨ p = sourceResidualOdd := sorry

/-! ## The deferred-acceptance trace -/

/-- One proposal event of the deferred-acceptance run.  `proposer` and
`target` are the canonical orbit representatives in the manuscript's lifted
coordinates (`(x,y,z) ↦ (x,y,2z)` on sources, `(u,v,w) ↦ (u,v,4w)` on
targets); `key` is the projective edge key `(Q(d), d₁, d₂, d₃)` of the
proposed edge; `sign` is the sign `η ∈ {±1}` lifting the orbit edge to
representatives; `accepted` is true exactly for `DAOutcome.accept`, meaning
acceptance by a previously free target.  Replacement and rejection outcomes
are false. -/
structure DAEvent where
  /-- The canonical lifted representative of the proposing source orbit. -/
  proposer : ℤ × ℤ × ℤ
  /-- The canonical lifted representative of the proposed target orbit. -/
  target : ℤ × ℤ × ℤ
  /-- The projective key `(Q(d), d₁, d₂, d₃)` of the proposed edge. -/
  key : ℤ × ℤ × ℤ × ℤ
  /-- The sign `η ∈ {±1}` of the proposed edge. -/
  sign : ℤ
  /-- Whether a previously free target accepted the proposal. -/
  accepted : Bool

/-- **The six-event trace certificate at `n = 41`.**  A definition hole: the
submitted Solution supplies the plain-coordinate image of the actual run, but
the registered statement below fixes only the resulting literal list. -/
def daTrace41 : List DAEvent := sorry

/-- **The six proposals of the `n = 41` run**, in the order they are made:
`s₁ → t₁`, `s₂ → t₁` (rejected), `s₃ → t₄`, `s₄ → t₃`, `s₂ → t₄` (rejected),
`s₂ → t₂`. -/
theorem daTrace41_eq :
    daTrace41 =
      [⟨(-2, -5, -2), (-4, -3, 0), (5, 1, -1, -1), -1, true⟩,
       ⟨(-2, -5, 2), (-4, -3, 0), (5, 1, -1, 1), -1, false⟩,
       ⟨(-2, 5, -2), (0, -3, 4), (5, 1, -1, -1), 1, true⟩,
       ⟨(-2, 5, 2), (0, -3, -4), (5, 1, -1, 1), 1, true⟩,
       ⟨(-2, -5, 2), (0, -3, 4), (5, 1, 1, 1), -1, false⟩,
       ⟨(-2, -5, 2), (-4, 3, 0), (20, 1, -4, 1), -1, true⟩] := sorry

/-- **Six proposal-processing steps.**  Each step advances one generator once,
so the run also performs six generator advances. -/
theorem daTrace41_length : daTrace41.length = 6 := sorry

/-- **Exactly two events are not free-target acceptances.**  The separate
supporting development records the richer outcomes and proves that these two
events are rejections, but this short Comparator contract registers only the
Boolean count.  A distinct machine-level theorem proves that the run performs
two held-key comparisons. -/
theorem daTrace41_nonaccepting :
    (daTrace41.filter fun e => !e.accepted).length = 2 := sorry

/-- Unlifting a source representative: `(x, y, 2z) ↦ (x, y, z)`. -/
def unliftSource (E : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (E.1, E.2.1, E.2.2 / 2)

/-- Unlifting a target representative: `(u, v, 4w) ↦ (u, v, w)`. -/
def unliftTarget (F : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (F.1, F.2.1, F.2.2 / 4)

/-- Scaling a triple by a sign. -/
def scaleTriple (s : ℤ) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (s * v.1, s * v.2.1, s * v.2.2)

/-- **The trace computes the map.**  For every free-target acceptance event, the
registered map sends the proposing source (unlifted) to the signed target
(unlifted): this is the sign-lift rule `σE ↦ σ η F` at `σ = 1`. -/
theorem daTrace41_accepted_image (p : BRep 41)
    (e : DAEvent) (he : e ∈ daTrace41) (hacc : e.accepted = true)
    (hp : p.1 = unliftSource e.proposer) :
    (tunnellMap41 p).1 = unliftTarget (scaleTriple e.sign e.target) := sorry

end TunnellN41

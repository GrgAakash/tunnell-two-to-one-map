import TunnellMap.N41TotalMap

/-!
# Solution for Palomar entry B

The Challenge definitions are repeated verbatim.  The definition holes
`TunnellN41.tunnellMap41` and `TunnellN41.daTrace41` are filled by the
project's fallback-free assembled executable map `TunnellMap.Examples41.tunnellMapTotal41` at
`n = 41` and by the event list of the actual instrumented deferred-acceptance
run `TunnellMap.Examples41.daEvents41`, both read in plain integer
coordinates.
-/

namespace TunnellN41

open TunnellMap TunnellMap.Examples41

/-- `BRep n` — the representations of `n` by `2x² + y² + 8z²`. -/
def BRep (n : ℤ) : Type :=
  {p : ℤ × ℤ × ℤ // 2 * p.1 ^ 2 + p.2.1 ^ 2 + 8 * p.2.2 ^ 2 = n}

/-- `ARep n` — the representations of `n` by `2u² + v² + 32w²`. -/
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

theorem aEquiv_symm_fst {n : ℤ} (Y : TunnellMap.ARep n) :
    ((aEquiv n).symm Y).1 = (Y.1.x, Y.1.y, Y.1.z) := rfl

theorem directTargetUsed_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ TunnellMap.DirectTargetUsed (aEquiv n p) :=
  Iff.rfl

/-- The residual targets in product coordinates are `TunnellMap.AResidual n`. -/
def arEquiv (n : ℤ) : AResidual n ≃ TunnellMap.AResidual n :=
  (aEquiv n).subtypeEquiv fun p => not_congr (directTargetUsed_iff p)

/-! ## The two representation counts -/

/-- **`|B₄₁| = 32`.** -/
theorem card_BRep_41 : Nat.card (BRep 41) = 32 := by
  classical
  rw [Nat.card_congr (bEquiv 41), Nat.card_eq_fintype_card]
  exact TunnellMap.Examples41.card_BRep_41

/-- **`|A₄₁| = 16`.** -/
theorem card_ARep_41 : Nat.card (ARep 41) = 16 := by
  classical
  rw [Nat.card_congr (aEquiv 41), Nat.card_eq_fintype_card]
  exact TunnellMap.Examples41.card_ARep_41

/-! ## The map at `n = 41` -/

/-- **The assembled fallback-free map at `n = 41`**, read in product coordinates. -/
def tunnellMap41 : BRep 41 → ARep 41 := fun p =>
  (aEquiv 41).symm
    (TunnellMap.Examples41.tunnellMapTotal41 (bEquiv 41 p))

theorem tunnellMap41_apply (p : BRep 41) :
    tunnellMap41 p =
      (aEquiv 41).symm
        (TunnellMap.Examples41.tunnellMapTotal41 (bEquiv 41 p)) := rfl

/-- **Every target of `A₄₁` has exactly two preimages in `B₄₁`.** -/
theorem tunnellMap41_exactly_two (a : ARep 41) :
    ∃ p₁ p₂ : BRep 41,
      p₁ ≠ p₂ ∧
      tunnellMap41 p₁ = a ∧
      tunnellMap41 p₂ = a ∧
      ∀ p, tunnellMap41 p = a ↔ p = p₁ ∨ p = p₂ := by
  classical
  obtain ⟨q₁, q₂, hne, h₁, h₂, hfib⟩ :=
    TunnellMap.Examples41.tunnellMapTotal41_exactly_two (aEquiv 41 a)
  refine ⟨(bEquiv 41).symm q₁, (bEquiv 41).symm q₂, ?_, ?_, ?_, ?_⟩
  · simpa using hne
  · simp only [tunnellMap41, Equiv.apply_symm_apply, h₁, Equiv.symm_apply_apply]
  · simp only [tunnellMap41, Equiv.apply_symm_apply, h₂, Equiv.symm_apply_apply]
  · intro p
    have hiff : tunnellMap41 p = a ↔
        TunnellMap.Examples41.tunnellMapTotal41 (bEquiv 41 p) = aEquiv 41 a := by
      constructor
      · intro h
        exact (Equiv.symm_apply_eq (aEquiv 41)).mp h
      · intro h
        simp only [tunnellMap41, h, Equiv.symm_apply_apply]
    rw [hiff, hfib (bEquiv 41 p)]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [← h, Equiv.symm_apply_apply])
      · exact Or.inr (by rw [← h, Equiv.symm_apply_apply])
    · rintro (h | h)
      · exact Or.inl (by rw [h, Equiv.apply_symm_apply])
      · exact Or.inr (by rw [h, Equiv.apply_symm_apply])

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

/-- On a residual odd source the assembled map is the residual branch. -/
theorem exec_residual_apply {n : ℤ} (hnpos : 0 < n) (hsq : Squarefree n)
    (fb : TunnellMap.AResidual n) (s : TunnellMap.BResidual n) (q : TunnellMap.BRep n)
    (hq : q.1 = s.1.1) :
    TunnellMap.paperTunnellMapExec hnpos hsq fb q =
      (TunnellMap.RecordDA.residualMapExec hnpos hsq fb s).1 := by
  have hodd : Odd s.1.1.z := s.1.2.2
  have hz : ¬ q.1.z % 2 = 0 := by
    rw [hq]
    obtain ⟨k, hk⟩ := hodd
    omega
  have hd : ¬ TunnellMap.SourceUsedTriple q.1 := by
    rw [hq]
    exact fun hc => s.2 ((TunnellMap.directSourceUsed_iff s.1).mpr hc)
  let qOdd : TunnellMap.BOddRep n := ⟨q.1, q.2, Int.odd_iff.mpr (by omega)⟩
  rw [TunnellMap.paperTunnellMapExec, dif_neg hz]
  change TunnellMap.oddMapExec hnpos hsq fb qOdd = _
  rw [TunnellMap.oddMapExec, dif_neg hd]
  congr 2
  exact Subtype.ext (Subtype.ext hq)

theorem pair1 : (tunnellMap41 source1).1 = (4, 3, 0) := by
  have h : TunnellMap.paperTunnellMapExec pos41 squarefree41 t1 (bEquiv 41 source1) =
      (residualMapExec41 s1).1 :=
    exec_residual_apply pos41 squarefree41 t1 s1 _ rfl
  rw [tunnellMap41_apply, TunnellMap.Examples41.tunnellMapTotal41_eq, h, aEquiv_symm_fst,
    TunnellMap.Examples41.residualMap_41_coords.1]

theorem pair2 : (tunnellMap41 source2).1 = (4, -3, 0) := by
  have h : TunnellMap.paperTunnellMapExec pos41 squarefree41 t1 (bEquiv 41 source2) =
      (residualMapExec41 s2).1 :=
    exec_residual_apply pos41 squarefree41 t1 s2 _ rfl
  rw [tunnellMap41_apply, TunnellMap.Examples41.tunnellMapTotal41_eq, h, aEquiv_symm_fst,
    TunnellMap.Examples41.residualMap_41_coords.2.1]

theorem pair3 : (tunnellMap41 source3).1 = (0, -3, 1) := by
  have h : TunnellMap.paperTunnellMapExec pos41 squarefree41 t1 (bEquiv 41 source3) =
      (residualMapExec41 s3).1 :=
    exec_residual_apply pos41 squarefree41 t1 s3 _ rfl
  rw [tunnellMap41_apply, TunnellMap.Examples41.tunnellMapTotal41_eq, h, aEquiv_symm_fst,
    TunnellMap.Examples41.residualMap_41_coords.2.2.1]

theorem pair4 : (tunnellMap41 source4).1 = (0, -3, -1) := by
  have h : TunnellMap.paperTunnellMapExec pos41 squarefree41 t1 (bEquiv 41 source4) =
      (residualMapExec41 s4).1 :=
    exec_residual_apply pos41 squarefree41 t1 s4 _ rfl
  rw [tunnellMap41_apply, TunnellMap.Examples41.tunnellMapTotal41_eq, h, aEquiv_symm_fst,
    TunnellMap.Examples41.residualMap_41_coords.2.2.2]

/-- **Four canonical residual-orbit representative pairs at `n = 41`.** -/
theorem residualPairs_41 :
    (tunnellMap41 source1).1 = (4, 3, 0) ∧
      (tunnellMap41 source2).1 = (4, -3, 0) ∧
      (tunnellMap41 source3).1 = (0, -3, 1) ∧
      (tunnellMap41 source4).1 = (0, -3, -1) :=
  ⟨pair1, pair2, pair3, pair4⟩

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

/-- **The complete fibre of the quarter-turn lane.** -/
theorem fibre_direct_41 (p : BRep 41) :
    tunnellMap41 p = targetDirect ↔
      p = sourceDirectEven ∨ p = sourceDirectOdd := by
  rw [tunnellMap41_apply, Equiv.symm_apply_eq]
  rw [show aEquiv 41 targetDirect = TunnellMap.Examples41.targetDirect41 from rfl]
  rw [TunnellMap.Examples41.tunnellMapTotal41_fibre_direct (bEquiv 41 p)]
  constructor
  · rintro (h | h)
    · exact Or.inl ((bEquiv 41).injective h)
    · exact Or.inr ((bEquiv 41).injective h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

/-- **The complete fibre of the stable-matching lane.** -/
theorem fibre_residual_41 (p : BRep 41) :
    tunnellMap41 p = targetResidual ↔
      p = sourceResidualEven ∨ p = sourceResidualOdd := by
  rw [tunnellMap41_apply, Equiv.symm_apply_eq]
  rw [show aEquiv 41 targetResidual = TunnellMap.Examples41.targetResidual41 from rfl]
  rw [TunnellMap.Examples41.tunnellMapTotal41_fibre_residual (bEquiv 41 p)]
  constructor
  · rintro (h | h)
    · exact Or.inl ((bEquiv 41).injective h)
    · exact Or.inr ((bEquiv 41).injective h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

/-! ## The deferred-acceptance trace -/

/-- One proposal event of the deferred-acceptance run. -/
structure DAEvent where
  /-- The canonical lifted representative of the proposing source orbit. -/
  proposer : ℤ × ℤ × ℤ
  /-- The canonical lifted representative of the proposed target orbit. -/
  target : ℤ × ℤ × ℤ
  /-- The projective key `(Q(d), d₁, d₂, d₃)` of the proposed edge. -/
  key : ℤ × ℤ × ℤ × ℤ
  /-- The sign `η ∈ {±1}` of the proposed edge. -/
  sign : ℤ
  /-- Whether the outcome was acceptance by a previously free target. -/
  accepted : Bool

/-- Plain coordinates of a triple. -/
def prodOf (t : TunnellMap.Triple) : ℤ × ℤ × ℤ := (t.x, t.y, t.z)

/-- The plain-coordinate reading of one instrumented event. -/
def eventOf (e : TunnellMap.RecordDA.DAEvent 41) : DAEvent where
  proposer := prodOf (TunnellMap.residualSourceLift e.proposer)
  target := prodOf e.target
  key := (e.key.form, e.key.x, e.key.y, e.key.z)
  sign := e.sign
  accepted := decide (e.outcome = TunnellMap.RecordDA.DAOutcome.accept)

/-- **The deferred-acceptance trace at `n = 41`**: the events of the actual
instrumented run, in plain coordinates. -/
def daTrace41 : List DAEvent := TunnellMap.Examples41.daEvents41.map eventOf

/-- **The six proposals of the `n = 41` run.** -/
theorem daTrace41_eq :
    daTrace41 =
      [⟨(-2, -5, -2), (-4, -3, 0), (5, 1, -1, -1), -1, true⟩,
       ⟨(-2, -5, 2), (-4, -3, 0), (5, 1, -1, 1), -1, false⟩,
       ⟨(-2, 5, -2), (0, -3, 4), (5, 1, -1, -1), 1, true⟩,
       ⟨(-2, 5, 2), (0, -3, -4), (5, 1, -1, 1), 1, true⟩,
       ⟨(-2, -5, 2), (0, -3, 4), (5, 1, 1, 1), -1, false⟩,
       ⟨(-2, -5, 2), (-4, 3, 0), (20, 1, -4, 1), -1, true⟩] := by
  rw [daTrace41, TunnellMap.Examples41.daTrace_41]
  rfl

/-- **Six proposal-processing steps.** -/
theorem daTrace41_length : daTrace41.length = 6 := by
  rw [daTrace41_eq]; rfl

/-- **Exactly two events are not free-target acceptances.** -/
theorem daTrace41_nonaccepting :
    (daTrace41.filter fun e => !e.accepted).length = 2 := by
  rw [daTrace41_eq]; rfl

/-- Unlifting a source representative: `(x, y, 2z) ↦ (x, y, z)`. -/
def unliftSource (E : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (E.1, E.2.1, E.2.2 / 2)

/-- Unlifting a target representative: `(u, v, 4w) ↦ (u, v, w)`. -/
def unliftTarget (F : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (F.1, F.2.1, F.2.2 / 4)

/-- Scaling a triple by a sign. -/
def scaleTriple (s : ℤ) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (s * v.1, s * v.2.1, s * v.2.2)

/-- **The trace computes the map.** -/
theorem daTrace41_accepted_image (p : BRep 41)
    (e : DAEvent) (he : e ∈ daTrace41) (hacc : e.accepted = true)
    (hp : p.1 = unliftSource e.proposer) :
    (tunnellMap41 p).1 = unliftTarget (scaleTriple e.sign e.target) := by
  rw [daTrace41_eq] at he
  have hsub : ∀ v : ℤ × ℤ × ℤ, ∀ h : 2 * v.1 ^ 2 + v.2.1 ^ 2 + 8 * v.2.2 ^ 2 = 41,
      p.1 = v → p = ⟨v, h⟩ := by
    intro v h hv
    exact Subtype.ext hv
  fin_cases he
  · rw [hsub (-2, -5, -1) (by norm_num) (by simpa [unliftSource] using hp)]
    exact pair1
  · simp at hacc
  · rw [hsub (-2, 5, -1) (by norm_num) (by simpa [unliftSource] using hp)]
    exact pair3
  · rw [hsub (-2, 5, 1) (by norm_num) (by simpa [unliftSource] using hp)]
    exact pair4
  · simp at hacc
  · rw [hsub (-2, -5, 1) (by norm_num) (by simpa [unliftSource] using hp)]
    exact pair2

end TunnellN41

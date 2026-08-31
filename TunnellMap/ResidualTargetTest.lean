import TunnellMap.OrbitRanking

/-!
# A computable test for residual targets

Step 6 of the ordered-adjacency generator retains a reconstructed vector only
when it is the lift of a residual target orbit representative.  The three
"direct image" predicates that must fail are existential statements about odd
integers; this file replaces them by explicit congruences, so that the whole
test becomes a Boolean computation on integer coordinates.
-/

namespace TunnellMap

/-! ## Odd multiples as congruences -/

theorem exists_odd_four_mul_iff (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 4 * q) ↔ a % 8 = 4 := by
  constructor
  · rintro ⟨q, ⟨k, hk⟩, ha⟩
    subst hk
    omega
  · intro ha
    refine ⟨2 * (a / 8) + 1, ⟨a / 8, by ring⟩, ?_⟩
    omega

theorem exists_odd_two_mul_iff (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 2 * q) ↔ a % 4 = 2 := by
  constructor
  · rintro ⟨q, ⟨k, hk⟩, ha⟩
    subst hk
    omega
  · intro ha
    refine ⟨2 * (a / 4) + 1, ⟨a / 4, by ring⟩, ?_⟩
    omega

/-! ## The direct-image tests on raw coordinates -/

/-- The coordinate form of the three direct-image predicates. -/
def ImageUsedTriple (w : Triple) : Prop :=
  (w.x + 4 * w.z - w.y) % 8 = 4 ∨ (w.x - 4 * w.z + w.y) % 8 = 4 ∨ w.x % 4 = 2

instance imageUsedTripleDecidable (w : Triple) : Decidable (ImageUsedTriple w) := by
  unfold ImageUsedTriple
  infer_instance

theorem directTargetUsed_iff {n : ℤ} (p : ARep n) :
    DirectTargetUsed p ↔ ImageUsedTriple p.1 := by
  unfold DirectTargetUsed ImageUsedTriple ImagePredicate1 ImagePredicate2
    ImagePredicate3
  rw [exists_odd_four_mul_iff, exists_odd_four_mul_iff, exists_odd_two_mul_iff]

/-! ## Recognizing lifts of residual targets -/

/-- A triple is the lift of a residual target exactly when this decidable
predicate holds.  The three coordinates come from the generator's
reconstruction step, so the test is a finite integer computation. -/
def IsResidualTargetLift (n : ℤ) (v : Triple) : Prop :=
  (4 : ℤ) ∣ v.z ∧ aForm ⟨v.x, v.y, v.z / 4⟩ = n ∧
    ¬ ImageUsedTriple ⟨v.x, v.y, v.z / 4⟩

instance isResidualTargetLiftDecidable (n : ℤ) (v : Triple) :
    Decidable (IsResidualTargetLift n v) := by
  unfold IsResidualTargetLift
  infer_instance

theorem isResidualTargetLift_iff (n : ℤ) (v : Triple) :
    IsResidualTargetLift n v ↔ ∃ t : AResidual n, residualTargetLift t = v := by
  constructor
  · rintro ⟨⟨k, hk⟩, hform, hused⟩
    have hzdiv : v.z / 4 = k := by omega
    refine ⟨⟨⟨⟨v.x, v.y, v.z / 4⟩, hform⟩, ?_⟩, ?_⟩
    · rw [directTargetUsed_iff]
      exact hused
    · show aLift (⟨⟨v.x, v.y, v.z / 4⟩, hform⟩ : ARep n) = v
      apply Triple.ext <;> (simp [aLift]; try omega)
  · rintro ⟨t, rfl⟩
    refine ⟨⟨t.1.1.z, by simp [residualTargetLift, aLift]⟩, ?_, ?_⟩
    · have : (4 * t.1.1.z) / 4 = t.1.1.z := by omega
      simpa [residualTargetLift, aLift, this] using t.1.2
    · have h4 : (4 * t.1.1.z) / 4 = t.1.1.z := by omega
      have hused : ¬ DirectTargetUsed t.1 := t.2
      rw [directTargetUsed_iff] at hused
      have hcoord : (⟨(residualTargetLift t).x, (residualTargetLift t).y,
          (residualTargetLift t).z / 4⟩ : Triple) = t.1.1 := by
        apply Triple.ext <;> simp [residualTargetLift, aLift, h4]
      rw [hcoord]
      exact hused

/-! ## The canonical signed representative of a target orbit, at lift level -/

/-- The executable form of the lexicographic comparison of two triples.  The
lexicographic order of `TripleLexKey` is the order of a nested product, whose
derived decision procedure is unusable in compiled code; this Boolean function
is a literal integer comparison. -/
def tripleLexLtExec (u w : Triple) : Bool :=
  u.x < w.x || (u.x == w.x && (u.y < w.y || (u.y == w.y && u.z < w.z)))

/-- The lexicographically smaller of a lifted target and its antipode.  This
is the coordinate form of `canonicalAResidualRepresentative`. -/
def canonicalTargetLift (v : Triple) : Triple :=
  if tripleLexLtExec v (negTriple v) then v else negTriple v

/-- The sign `η` recorded by the generator: the actual reconstructed target is
`η` times the canonical representative of its orbit. -/
def targetLiftSign (v : Triple) : ℤ :=
  if tripleLexLtExec v (negTriple v) then 1 else -1

theorem canonicalTargetLift_spec (v : Triple) :
    v = vsmul (targetLiftSign v) (canonicalTargetLift v) := by
  unfold canonicalTargetLift targetLiftSign
  split <;> (apply Triple.ext <;> simp [vsmul, negTriple])

theorem targetLiftSign_mem (v : Triple) :
    targetLiftSign v = 1 ∨ targetLiftSign v = -1 := by
  unfold targetLiftSign
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem negTriple_residualTargetLift {n : ℤ} (t : AResidual n) :
    negTriple (residualTargetLift t) = residualTargetLift (negAResidual t) := by
  apply Triple.ext <;> simp [negTriple, residualTargetLift, aLift, negAResidual,
    negA, negTriple]

theorem tripleLexKey_lt_iff (u w : Triple) :
    tripleLexKey u < tripleLexKey w ↔
      u.x < w.x ∨ (u.x = w.x ∧ (u.y < w.y ∨ (u.y = w.y ∧ u.z < w.z))) := by
  unfold tripleLexKey
  simp [Prod.Lex.toLex_lt_toLex]

@[simp] theorem tripleLexLtExec_iff (u w : Triple) :
    tripleLexLtExec u w = true ↔ tripleLexKey u < tripleLexKey w := by
  rw [tripleLexKey_lt_iff]
  simp only [tripleLexLtExec, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]

theorem tripleLexKey_residualTargetLift_lt_iff {n : ℤ} (t₁ t₂ : AResidual n) :
    tripleLexKey (residualTargetLift t₁) < tripleLexKey (residualTargetLift t₂) ↔
      aResidualLexKey t₁ < aResidualLexKey t₂ := by
  rw [tripleLexKey_lt_iff, aResidualLexKey, aResidualLexKey, tripleLexKey_lt_iff]
  simp only [residualTargetLift, aLift]
  omega

/-- The coordinate-level canonical representative agrees with the quotient
level one. -/
theorem canonicalTargetLift_eq {n : ℤ} (hnpos : 0 < n) (t : AResidual n) :
    canonicalTargetLift (residualTargetLift t) =
      residualTargetLift (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) := by
  have hcanon : canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit t) =
      (aResidualInvolution n hnpos).canonicalPoint aResidualLexKey t := rfl
  rw [hcanon]
  have hneg := negTriple_residualTargetLift t
  show (if tripleLexLtExec (residualTargetLift t)
        (negTriple (residualTargetLift t)) = true then residualTargetLift t
        else negTriple (residualTargetLift t)) =
      residualTargetLift (if aResidualLexKey t < aResidualLexKey (negAResidual t)
        then t else negAResidual t)
  by_cases h : aResidualLexKey t < aResidualLexKey (negAResidual t)
  · have h' : tripleLexLtExec (residualTargetLift t)
        (negTriple (residualTargetLift t)) = true := by
      rw [tripleLexLtExec_iff, hneg]
      exact (tripleLexKey_residualTargetLift_lt_iff t (negAResidual t)).mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ tripleLexLtExec (residualTargetLift t)
        (negTriple (residualTargetLift t)) = true := by
      rw [tripleLexLtExec_iff, hneg]
      exact fun hc => h ((tripleLexKey_residualTargetLift_lt_iff t (negAResidual t)).mp hc)
    rw [if_neg h', if_neg h, hneg]

end TunnellMap

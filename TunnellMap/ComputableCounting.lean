import TunnellMap.ComputableTargetRoster

/-!
# Arithmetic enumeration of the two representation sets

`TunnellMap.Finiteness` supplies `Fintype` instances for `BRep n` and `ARep n`
through `Fintype.ofFinite`, which is not executable.  This file exhibits, for
every `n`, explicit *lists*

* `bRepList n : List (BRep n)`, containing every solution of `2x² + y² + 8z² = n`;
* `aRepList n : List (ARep n)`, containing every solution of `2x² + y² + 32z² = n`;

and reduces the two cardinalities `Fintype.card (BRep n)` and
`Fintype.card (ARep n)` to the lengths of the deduplicated lists.  Both lists
are built from `sourceTriples`/`targetTriples`, whose square roots are the
kernel-reducible `isqrtK`, so the cardinalities can be *decided* by the kernel.

The file also splits the source enumeration into its even part, its odd direct
part and its odd residual part.
-/

namespace TunnellMap

instance bRepDecidableEq (n : ℤ) : DecidableEq (BRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n})

instance bOddRepDecidableEq (n : ℤ) : DecidableEq (BOddRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n ∧ Odd p.z})

instance bResidualDecidableEq' (n : ℤ) : DecidableEq (BResidual n) :=
  inferInstanceAs (DecidableEq {p : BOddRep n // ¬ DirectSourceUsed p})

/-! ## The source enumeration -/

/-- Every representation of `n` by `2x² + y² + 8z²`, enumerated arithmetically. -/
def bRepList (n : ℤ) : List (BRep n) :=
  (sourceTriples n).filterMap fun w => if h : bForm w = n then some ⟨w, h⟩ else none

theorem mem_bRepList {n : ℤ} (p : BRep n) : p ∈ bRepList n := by
  refine List.mem_filterMap.mpr ⟨p.1, mem_sourceTriples p.2, ?_⟩
  rw [dif_pos p.2]
  rfl

theorem bRepList_toFinset_eq_univ (n : ℤ) : (bRepList n).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun p => List.mem_toFinset.mpr (mem_bRepList p)

/-- **The source cardinality is computed by the enumeration.** -/
theorem card_bRep (n : ℤ) : Fintype.card (BRep n) = (bRepList n).dedup.length := by
  rw [← Finset.card_univ, ← bRepList_toFinset_eq_univ, List.card_toFinset]

/-! ## The target enumeration -/

/-- Every representation of `n` by `2x² + y² + 32z²`, enumerated arithmetically. -/
def aRepList (n : ℤ) : List (ARep n) :=
  (targetTriples n).filterMap fun w => if h : aForm w = n then some ⟨w, h⟩ else none

theorem mem_aRepList {n : ℤ} (p : ARep n) : p ∈ aRepList n := by
  refine List.mem_filterMap.mpr ⟨p.1, mem_targetTriples p.2, ?_⟩
  rw [dif_pos p.2]
  rfl

theorem aRepList_toFinset_eq_univ (n : ℤ) : (aRepList n).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun p => List.mem_toFinset.mpr (mem_aRepList p)

/-- **The target cardinality is computed by the enumeration.** -/
theorem card_aRep (n : ℤ) : Fintype.card (ARep n) = (aRepList n).dedup.length := by
  rw [← Finset.card_univ, ← aRepList_toFinset_eq_univ, List.card_toFinset]

/-! ## The three parts of the source enumeration -/

/-- The even-`z` part of the source enumeration. -/
def bEvenTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => !decide (Odd w.z)

/-- The odd-`z`, *direct* part of the source enumeration. -/
def bDirectTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => decide (Odd w.z) && decide (SourceUsedTriple w)

/-- The odd-`z`, *residual* part of the source enumeration. -/
def bResidualTriples (n : ℤ) : List Triple :=
  (sourceTriples n).filter fun w => decide (Odd w.z) && !decide (SourceUsedTriple w)

/-- The *direct* part of the target enumeration. -/
def aDirectTriples (n : ℤ) : List Triple :=
  (targetTriples n).filter fun w => decide (ImageUsedTriple w)

/-- The *residual* part of the target enumeration. -/
def aResidualTriples (n : ℤ) : List Triple :=
  (targetTriples n).filter fun w => !decide (ImageUsedTriple w)

theorem mem_bResidualTriples_iff {n : ℤ} (w : Triple) :
    w ∈ bResidualTriples n ↔ (bForm w = n ∧ Odd w.z) ∧ ¬ SourceUsedTriple w := by
  constructor
  · intro hw
    obtain ⟨hmem, hfil⟩ := List.mem_filter.mp hw
    have hz : Odd w.z := by
      by_contra h
      simp [h] at hfil
    have hd : ¬ SourceUsedTriple w := by
      by_contra h
      simp [h, hz] at hfil
    refine ⟨⟨?_, hz⟩, hd⟩
    obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hmem
    obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hx
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
    have : 8 * (z * z) = n - 2 * (x * x) - y * y := by
      unfold zCandidates at hz'
      split_ifs at hz' with h1 h2 h3
      · exact absurd hz' (by simp)
      · rw [List.mem_singleton.mp hz'] at *
        simp only [mul_zero] at h2 ⊢
        rw [h3] at h2
        simpa using h2
      · rcases List.mem_cons.mp hz' with h | h
        · rw [h]; rw [show (-isqrtK ((n - 2 * (x * x) - y * y) / 8)) *
            (-isqrtK ((n - 2 * (x * x) - y * y) / 8)) =
            isqrtK ((n - 2 * (x * x) - y * y) / 8) *
              isqrtK ((n - 2 * (x * x) - y * y) / 8) by ring]
          exact h2
        · rw [List.mem_singleton.mp h]; exact h2
      · exact absurd hz' (by simp)
    show 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = n
    nlinarith [this]
  · rintro ⟨⟨hform, hz⟩, hd⟩
    refine List.mem_filter.mpr ⟨mem_sourceTriples hform, ?_⟩
    simp [hz, hd]

theorem mem_aResidualTriples_iff {n : ℤ} (w : Triple) :
    w ∈ aResidualTriples n ↔ aForm w = n ∧ ¬ ImageUsedTriple w := by
  constructor
  · intro hw
    obtain ⟨hmem, hfil⟩ := List.mem_filter.mp hw
    have hd : ¬ ImageUsedTriple w := by
      by_contra h
      simp [h] at hfil
    refine ⟨?_, hd⟩
    obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hmem
    obtain ⟨y, -, hy⟩ := List.mem_flatMap.mp hx
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
    have : 32 * (z * z) = n - 2 * (x * x) - y * y := by
      unfold wCandidates at hz'
      split_ifs at hz' with h1 h2 h3
      · exact absurd hz' (by simp)
      · rw [List.mem_singleton.mp hz'] at *
        simp only [mul_zero] at h2 ⊢
        rw [h3] at h2
        simpa using h2
      · rcases List.mem_cons.mp hz' with h | h
        · rw [h]; rw [show (-isqrtK ((n - 2 * (x * x) - y * y) / 32)) *
            (-isqrtK ((n - 2 * (x * x) - y * y) / 32)) =
            isqrtK ((n - 2 * (x * x) - y * y) / 32) *
              isqrtK ((n - 2 * (x * x) - y * y) / 32) by ring]
          exact h2
        · rw [List.mem_singleton.mp h]; exact h2
      · exact absurd hz' (by simp)
    show 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 = n
    nlinarith [this]
  · rintro ⟨hform, hd⟩
    refine List.mem_filter.mpr ⟨mem_targetTriples hform, ?_⟩
    simp [hd]

end TunnellMap

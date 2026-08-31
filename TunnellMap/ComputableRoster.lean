import TunnellMap.RecordDeferredAcceptanceCorrect
import TunnellMap.CanonicalSignLift
import TunnellMap.Finiteness
import TunnellMap.KernelArith

/-!
# The computable residual source roster

`TunnellMap.RecordDA.sourceRoster` is defined by sorting `Finset.univ` of the
antipodal orbit quotient, which is only a `Fintype` through
`Classical.choice`.  This file constructs the very same list *arithmetically*:

* `sourceTriples n` enumerates every integral triple satisfying
  `2x² + y² + 8z² = n` from explicit coordinate bounds — the two first
  coordinates range over `[-n, n]` and the third is obtained from an integer
  square root;
* the enumeration is filtered by the decidable residual-source test and by the
  manuscript's lexicographic convention, which keeps exactly one point of each
  antipodal pair;
* the survivors are sorted in the manuscript's canonical source order.

`sourceRosterExec_eq_sourceRoster` proves that the resulting computable list is
literally `sourceRoster n`.
-/

namespace TunnellMap

/-! ## The direct-source test on raw coordinates -/

/-- The coordinate form of the three direct-source predicates. -/
def SourceUsedTriple (w : Triple) : Prop :=
  (8 : ℤ) ∣ (w.x + 2 * w.z + w.y) ∨ (8 : ℤ) ∣ (w.y - w.x + 2 * w.z) ∨ (4 : ℤ) ∣ w.x

instance sourceUsedTripleDecidable (w : Triple) : Decidable (SourceUsedTriple w) := by
  unfold SourceUsedTriple
  infer_instance

theorem directSourceUsed_iff {n : ℤ} (p : BOddRep n) :
    DirectSourceUsed p ↔ SourceUsedTriple p.1 := by
  unfold DirectSourceUsed SourceUsedTriple DirectPredicate1 DirectPredicate2
    DirectPredicate3
  exact Iff.rfl

/-! ## Arithmetic enumeration of the sources -/

/-- The integers of `[-m, m]`, in increasing order. -/
def intRangeSym (m : ℤ) : List ℤ :=
  (List.range (2 * m.toNat + 1)).map (fun i : ℕ => (i : ℤ) - m)

theorem mem_intRangeSym {m a : ℤ} (h₁ : -m ≤ a) (h₂ : a ≤ m) : a ∈ intRangeSym m := by
  have hmem : (a + m).toNat ∈ List.range (2 * m.toNat + 1) :=
    List.mem_range.mpr (by omega)
  have h := List.mem_map_of_mem (f := fun i : ℕ => (i : ℤ) - m) hmem
  have hv : ((a + m).toNat : ℤ) - m = a := by omega
  simp only [hv] at h
  unfold intRangeSym
  exact h

/-- The solutions `z` of `8 z² = r`, in increasing order.  The square root is
the kernel-reducible `isqrtK`, so the whole enumeration can be evaluated by
the kernel as well as by the compiler. -/
def zCandidates (r : ℤ) : List ℤ :=
  if r < 0 then []
  else if 8 * (isqrtK (r / 8) * isqrtK (r / 8)) = r then
    (if isqrtK (r / 8) = 0 then [0]
      else [-isqrtK (r / 8), isqrtK (r / 8)])
  else []

theorem mem_zCandidates {r z : ℤ} (h : 8 * (z * z) = r) : z ∈ zCandidates r := by
  simp only [zCandidates, isqrtK_eq]
  have hzz : 0 ≤ z * z := mul_self_nonneg z
  have hr : ¬ r < 0 := by omega
  have hdiv : r / 8 = z * z := by
    rw [← h]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hs : Int.sqrt (r / 8) = (z.natAbs : ℤ) := by rw [hdiv]; exact Int.sqrt_eq z
  have habs : ((z.natAbs : ℤ)) * ((z.natAbs : ℤ)) = z * z := Int.natAbs_mul_self' z
  rw [if_neg hr, hs, if_pos (by rw [habs]; exact h)]
  by_cases h0 : ((z.natAbs : ℤ)) = 0
  · rw [if_pos h0]
    have hz : z = 0 := by omega
    rw [hz]
    exact List.mem_singleton.mpr rfl
  · rw [if_neg h0]
    have hcase : z = -(z.natAbs : ℤ) ∨ z = (z.natAbs : ℤ) := by omega
    rcases hcase with h' | h'
    · exact List.mem_cons.mpr (Or.inl h')
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr h'))

/-- Every integral triple with `2x² + y² + 8z² = n`. -/
def sourceTriples (n : ℤ) : List Triple :=
  (intRangeSym n).flatMap fun x =>
    (intRangeSym n).flatMap fun y =>
      (zCandidates (n - 2 * (x * x) - y * y)).map fun z => ⟨x, y, z⟩

theorem mem_sourceTriples {n : ℤ} {w : Triple} (h : bForm w = n) :
    w ∈ sourceTriples n := by
  have hform : 2 * w.x ^ 2 + w.y ^ 2 + 8 * w.z ^ 2 = n := h
  have hn : 0 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.y, sq_nonneg w.z]
  have hxsq : w.x ^ 2 ≤ n := by nlinarith [sq_nonneg w.y, sq_nonneg w.z]
  have hysq : w.y ^ 2 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.z]
  obtain ⟨hx₁, hx₂⟩ := coordinate_bounds_of_sq_le hn hxsq
  obtain ⟨hy₁, hy₂⟩ := coordinate_bounds_of_sq_le hn hysq
  refine List.mem_flatMap.mpr ⟨w.x, mem_intRangeSym hx₁ hx₂, ?_⟩
  refine List.mem_flatMap.mpr ⟨w.y, mem_intRangeSym hy₁ hy₂, ?_⟩
  refine List.mem_map.mpr ⟨w.z, ?_, rfl⟩
  refine mem_zCandidates ?_
  nlinarith [hform]

/-! ## The residual, canonical filter -/

/-- The decidable test selecting exactly the canonical representatives of the
residual source orbits. -/
def IsSourceRosterTriple (n : ℤ) (w : Triple) : Prop :=
  (bForm w = n ∧ Odd w.z) ∧ ¬ SourceUsedTriple w ∧
    tripleLexLtExec w (negTriple w) = true

instance isSourceRosterTripleDecidable (n : ℤ) (w : Triple) :
    Decidable (IsSourceRosterTriple n w) := by
  unfold IsSourceRosterTriple
  infer_instance

/-- The unsorted list of canonical residual source representatives. -/
def sourceRosterUnsorted (n : ℤ) : List (BResidual n) :=
  (sourceTriples n).filterMap fun w =>
    if h : IsSourceRosterTriple n w then
      some ⟨⟨w, h.1⟩, by rw [directSourceUsed_iff]; exact h.2.1⟩
    else none

theorem mem_sourceRosterUnsorted_iff {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterUnsorted n ↔ IsSourceRosterTriple n x.1.1 := by
  constructor
  · intro hx
    obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hx
    by_cases h : IsSourceRosterTriple n w
    · rw [dif_pos h] at hw
      have : x.1.1 = w := by rw [← Option.some.inj hw]
      rw [this]; exact h
    · rw [dif_neg h] at hw; exact absurd hw (by simp)
  · intro h
    refine List.mem_filterMap.mpr ⟨x.1.1, mem_sourceTriples h.1.1, ?_⟩
    rw [dif_pos h]
    rfl

/-! ## Sorting in the canonical source order -/

/-- The manuscript's canonical source order: increasing lexicographic order of
the signed representative. -/
def BLexLe {n : ℤ} (a b : BResidual n) : Prop :=
  (!tripleLexLtExec b.1.1 a.1.1) = true

instance bLexLeDecidable {n : ℤ} : DecidableRel (BLexLe (n := n)) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem bLexLe_iff {n : ℤ} (a b : BResidual n) :
    BLexLe a b ↔ bResidualLexKey a ≤ bResidualLexKey b := by
  unfold BLexLe bResidualLexKey
  rw [Bool.not_eq_true', ← Bool.not_eq_true, tripleLexLtExec_iff, not_lt]

instance bLexLeTotal {n : ℤ} : Std.Total (BLexLe (n := n)) :=
  ⟨fun a b => by
    rcases le_total (bResidualLexKey a) (bResidualLexKey b) with h | h
    · exact Or.inl ((bLexLe_iff a b).mpr h)
    · exact Or.inr ((bLexLe_iff b a).mpr h)⟩

instance bLexLeTrans {n : ℤ} : IsTrans (BResidual n) BLexLe :=
  ⟨fun a b c hab hbc =>
    (bLexLe_iff a c).mpr (le_trans ((bLexLe_iff a b).mp hab) ((bLexLe_iff b c).mp hbc))⟩

/-- **The computable residual source roster.** -/
def sourceRosterExec (n : ℤ) : List (BResidual n) :=
  List.insertionSort BLexLe (sourceRosterUnsorted n).dedup

theorem mem_sourceRosterExec_iff {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔ IsSourceRosterTriple n x.1.1 := by
  rw [sourceRosterExec, (List.perm_insertionSort _ _).mem_iff, List.mem_dedup,
    mem_sourceRosterUnsorted_iff]

theorem sourceRosterExec_nodup {n : ℤ} : (sourceRosterExec n).Nodup :=
  ((List.perm_insertionSort (BLexLe (n := n)) _).nodup_iff).mpr (List.nodup_dedup _)

theorem sourceRosterExec_pairwise {n : ℤ} :
    (sourceRosterExec n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by
  refine List.Pairwise.imp ?_ (List.pairwise_insertionSort BLexLe _)
  intro a b hab
  exact (bLexLe_iff a b).mp hab

/-! ## Soundness and canonicity of the enumeration -/

/-- **Soundness.**  Every enumerated point really is a residual source, and it
is the canonical representative of its antipodal orbit. -/
theorem canonical_of_mem_sourceRosterExec {n : ℤ} {x : BResidual n}
    (hx : x ∈ sourceRosterExec n) :
    canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by
  have h := (mem_sourceRosterExec_iff x).mp hx
  have hlt : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x) := by
    have := (tripleLexLtExec_iff x.1.1 (negTriple x.1.1)).mp h.2.2
    exact this
  show (bResidualInvolution n).canonicalPoint bResidualLexKey x = x
  unfold FreeInvolution.canonicalPoint
  rw [if_pos hlt]

/-- **Completeness.**  The canonical representative of every residual source
orbit is enumerated. -/
theorem mem_sourceRosterExec_of_canonical {n : ℤ} {x : BResidual n}
    (hx : canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x) :
    x ∈ sourceRosterExec n := by
  have hcanon : (bResidualInvolution n).canonicalPoint bResidualLexKey x = x := hx
  have hlt : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x) := by
    unfold FreeInvolution.canonicalPoint at hcanon
    by_cases h : bResidualLexKey x < bResidualLexKey ((bResidualInvolution n).neg x)
    · exact h
    · rw [if_neg h] at hcanon
      exact absurd hcanon ((bResidualInvolution n).no_fixed x)
  refine (mem_sourceRosterExec_iff x).mpr ⟨x.1.2, ?_, ?_⟩
  · rw [← directSourceUsed_iff]; exact x.2
  · rw [tripleLexLtExec_iff]; exact hlt

theorem mem_sourceRosterExec_iff_canonical {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x :=
  ⟨canonical_of_mem_sourceRosterExec, mem_sourceRosterExec_of_canonical⟩

/-- **Every residual source orbit occurs exactly once.** -/
theorem sourceRosterExec_orbit_unique {n : ℤ}
    (q : (bResidualInvolution n).Orbit) :
    ∃! x : BResidual n, x ∈ sourceRosterExec n ∧
      (bResidualInvolution n).orbit x = q := by
  refine ⟨canonicalBResidualRepresentative q, ⟨?_, ?_⟩, ?_⟩
  · refine mem_sourceRosterExec_of_canonical ?_
    rw [orbit_canonicalBResidualRepresentative]
  · exact orbit_canonicalBResidualRepresentative q
  · rintro y ⟨hy, rfl⟩
    exact (canonical_of_mem_sourceRosterExec hy).symm

/-! ## Agreement with the structural roster -/

section Structural

variable {n : ℤ} [Fintype (BOddRep n)]

open RecordDA

theorem mem_sourceRoster_iff (x : BResidual n) :
    x ∈ sourceRoster n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by
  constructor
  · exact fun hx => sourceRoster_canon x hx
  · intro hx
    rw [sourceRoster]
    refine List.mem_map.mpr ⟨(bResidualInvolution n).orbit x, ?_, hx⟩
    exact mem_residualSourceOrder _

theorem sourceRoster_nodup : (sourceRoster n).Nodup := by
  rw [sourceRoster]
  refine List.Nodup.map_on ?_ residualSourceOrder_nodup
  intro q₁ _ q₂ _ heq
  rw [← orbit_canonicalBResidualRepresentative q₁, heq,
    orbit_canonicalBResidualRepresentative]

theorem sourceRoster_pairwise :
    (sourceRoster n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by
  classical
  letI : LinearOrder (bResidualInvolution n).Orbit :=
    LinearOrder.lift' residualSourceOrbitKey residualSourceOrbitKey_injective
  have hsorted : (residualSourceOrder (n := n)).Pairwise (· ≤ ·) := by
    unfold residualSourceOrder
    exact Finset.pairwise_sort _ _
  rw [sourceRoster]
  refine List.Pairwise.map _ ?_ hsorted
  intro q₁ q₂ h
  exact h

/-- **The computable roster is the manuscript's source roster.** -/
theorem sourceRosterExec_eq_sourceRoster :
    sourceRosterExec n = sourceRoster n := by
  refine List.Perm.eq_of_pairwise ?_ sourceRosterExec_pairwise sourceRoster_pairwise ?_
  · intro a b _ _ hab hba
    exact bResidualLexKey_injective (le_antisymm hab hba)
  · refine (List.perm_ext_iff_of_nodup sourceRosterExec_nodup sourceRoster_nodup).mpr ?_
    intro x
    rw [mem_sourceRosterExec_iff_canonical, mem_sourceRoster_iff]

end Structural

end TunnellMap

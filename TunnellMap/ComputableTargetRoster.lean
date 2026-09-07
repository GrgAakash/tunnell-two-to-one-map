import TunnellMap.ComputableRoster

/-!
# The computable residual target roster

`TunnellMap.ComputableRoster` enumerates the canonical representatives of the
residual *source* orbits arithmetically.  This file does the same for the
residual *target* orbits: `targetRosterExec n` enumerates every integral triple
with `2x² + y² + 32z² = n` from explicit coordinate bounds, keeps those that
are residual targets, keeps exactly one point of each antipodal pair by the
manuscript's lexicographic convention, and sorts the survivors canonically.

The resulting list is proved to contain the canonical representative of every
residual target orbit exactly once.
-/

namespace TunnellMap

instance aRepDecidableEq (n : ℤ) : DecidableEq (ARep n) :=
  inferInstanceAs (DecidableEq {p : Triple // aForm p = n})

instance aResidualDecidableEq (n : ℤ) : DecidableEq (AResidual n) :=
  inferInstanceAs (DecidableEq {p : ARep n // ¬ DirectTargetUsed p})

/-! ## Arithmetic enumeration of the targets -/

/-- The solutions `z` of `32 z² = r`, in increasing order. -/
def wCandidates (r : ℤ) : List ℤ :=
  if r < 0 then []
  else if 32 * (isqrtK (r / 32) * isqrtK (r / 32)) = r then
    (if isqrtK (r / 32) = 0 then [0]
      else [-isqrtK (r / 32), isqrtK (r / 32)])
  else []

theorem mem_wCandidates {r z : ℤ} (h : 32 * (z * z) = r) : z ∈ wCandidates r := by
  simp only [wCandidates, isqrtK_eq]
  have hzz : 0 ≤ z * z := mul_self_nonneg z
  have hr : ¬ r < 0 := by omega
  have hdiv : r / 32 = z * z := by
    rw [← h]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hs : Int.sqrt (r / 32) = (z.natAbs : ℤ) := by rw [hdiv]; exact Int.sqrt_eq z
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

/-- Every integral triple with `2x² + y² + 32z² = n`. -/
def targetTriples (n : ℤ) : List Triple :=
  (intRangeSym n).flatMap fun x =>
    (intRangeSym n).flatMap fun y =>
      (wCandidates (n - 2 * (x * x) - y * y)).map fun z => ⟨x, y, z⟩

theorem mem_targetTriples {n : ℤ} {w : Triple} (h : aForm w = n) :
    w ∈ targetTriples n := by
  have hform : 2 * w.x ^ 2 + w.y ^ 2 + 32 * w.z ^ 2 = n := h
  have hn : 0 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.y, sq_nonneg w.z]
  have hxsq : w.x ^ 2 ≤ n := by nlinarith [sq_nonneg w.y, sq_nonneg w.z]
  have hysq : w.y ^ 2 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.z]
  obtain ⟨hx₁, hx₂⟩ := coordinate_bounds_of_sq_le hn hxsq
  obtain ⟨hy₁, hy₂⟩ := coordinate_bounds_of_sq_le hn hysq
  refine List.mem_flatMap.mpr ⟨w.x, mem_intRangeSym hx₁ hx₂, ?_⟩
  refine List.mem_flatMap.mpr ⟨w.y, mem_intRangeSym hy₁ hy₂, ?_⟩
  refine List.mem_map.mpr ⟨w.z, ?_, rfl⟩
  refine mem_wCandidates ?_
  nlinarith [hform]

/-! ## The residual, canonical filter -/

/-- The decidable test selecting exactly the canonical representatives of the
residual target orbits. -/
def IsTargetRosterTriple (n : ℤ) (w : Triple) : Prop :=
  aForm w = n ∧ ¬ ImageUsedTriple w ∧ tripleLexLtExec w (negTriple w) = true

instance isTargetRosterTripleDecidable (n : ℤ) (w : Triple) :
    Decidable (IsTargetRosterTriple n w) := by
  unfold IsTargetRosterTriple
  infer_instance

/-- The unsorted list of canonical residual target representatives. -/
def targetRosterUnsorted (n : ℤ) : List (AResidual n) :=
  (targetTriples n).filterMap fun w =>
    if h : IsTargetRosterTriple n w then
      some ⟨⟨w, h.1⟩, fun hc =>
        h.2.1 ((directTargetUsed_iff (⟨w, h.1⟩ : ARep n)).mp hc)⟩
    else none

theorem mem_targetRosterUnsorted_iff {n : ℤ} (x : AResidual n) :
    x ∈ targetRosterUnsorted n ↔ IsTargetRosterTriple n x.1.1 := by
  constructor
  · intro hx
    obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hx
    by_cases h : IsTargetRosterTriple n w
    · rw [dif_pos h] at hw
      have : x.1.1 = w := by rw [← Option.some.inj hw]
      rw [this]; exact h
    · rw [dif_neg h] at hw; exact absurd hw (by simp)
  · intro h
    refine List.mem_filterMap.mpr ⟨x.1.1, mem_targetTriples h.1, ?_⟩
    rw [dif_pos h]
    rfl

/-! ## Sorting in the canonical target order -/

/-- The manuscript's canonical target order: increasing lexicographic order of
the signed representative. -/
def ALexLe {n : ℤ} (a b : AResidual n) : Prop :=
  (!tripleLexLtExec b.1.1 a.1.1) = true

instance aLexLeDecidable {n : ℤ} : DecidableRel (ALexLe (n := n)) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem aLexLe_iff {n : ℤ} (a b : AResidual n) :
    ALexLe a b ↔ aResidualLexKey a ≤ aResidualLexKey b := by
  unfold ALexLe aResidualLexKey
  rw [Bool.not_eq_true', ← Bool.not_eq_true, tripleLexLtExec_iff, not_lt]

instance aLexLeTotal {n : ℤ} : Std.Total (ALexLe (n := n)) :=
  ⟨fun a b => by
    rcases le_total (aResidualLexKey a) (aResidualLexKey b) with h | h
    · exact Or.inl ((aLexLe_iff a b).mpr h)
    · exact Or.inr ((aLexLe_iff b a).mpr h)⟩

instance aLexLeTrans {n : ℤ} : IsTrans (AResidual n) ALexLe :=
  ⟨fun a b c hab hbc =>
    (aLexLe_iff a c).mpr (le_trans ((aLexLe_iff a b).mp hab) ((aLexLe_iff b c).mp hbc))⟩

/-- **The computable residual target roster.** -/
def targetRosterExec (n : ℤ) : List (AResidual n) :=
  List.insertionSort ALexLe (targetRosterUnsorted n).dedup

theorem mem_targetRosterExec_iff {n : ℤ} (x : AResidual n) :
    x ∈ targetRosterExec n ↔ IsTargetRosterTriple n x.1.1 := by
  rw [targetRosterExec, (List.perm_insertionSort _ _).mem_iff, List.mem_dedup,
    mem_targetRosterUnsorted_iff]

theorem targetRosterExec_nodup {n : ℤ} : (targetRosterExec n).Nodup :=
  ((List.perm_insertionSort (ALexLe (n := n)) _).nodup_iff).mpr (List.nodup_dedup _)

theorem targetRosterExec_pairwise {n : ℤ} :
    (targetRosterExec n).Pairwise fun a b => aResidualLexKey a ≤ aResidualLexKey b := by
  refine List.Pairwise.imp ?_ (List.pairwise_insertionSort ALexLe _)
  intro a b hab
  exact (aLexLe_iff a b).mp hab

/-! ## Soundness and canonicity of the enumeration -/

/-- **Soundness.**  Every enumerated point really is a residual target, and it
is the canonical representative of its antipodal orbit. -/
theorem canonical_of_mem_targetRosterExec {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n} (hx : x ∈ targetRosterExec n) :
    canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x := by
  have h := (mem_targetRosterExec_iff x).mp hx
  have hlt : aResidualLexKey x <
      aResidualLexKey ((aResidualInvolution n hnpos).neg x) :=
    (tripleLexLtExec_iff x.1.1 (negTriple x.1.1)).mp h.2.2
  show (aResidualInvolution n hnpos).canonicalPoint aResidualLexKey x = x
  unfold FreeInvolution.canonicalPoint
  rw [if_pos hlt]

/-- **Completeness.**  The canonical representative of every residual target
orbit is enumerated. -/
theorem mem_targetRosterExec_of_canonical {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n}
    (hx : canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x) :
    x ∈ targetRosterExec n := by
  have hcanon : (aResidualInvolution n hnpos).canonicalPoint aResidualLexKey x = x := hx
  have hlt : aResidualLexKey x <
      aResidualLexKey ((aResidualInvolution n hnpos).neg x) := by
    unfold FreeInvolution.canonicalPoint at hcanon
    by_cases h : aResidualLexKey x <
        aResidualLexKey ((aResidualInvolution n hnpos).neg x)
    · exact h
    · rw [if_neg h] at hcanon
      exact absurd hcanon ((aResidualInvolution n hnpos).no_fixed x)
  refine (mem_targetRosterExec_iff x).mpr ⟨x.1.2, ?_, ?_⟩
  · rw [← directTargetUsed_iff]; exact x.2
  · rw [tripleLexLtExec_iff]; exact hlt

theorem mem_targetRosterExec_iff_canonical {n : ℤ} (hnpos : 0 < n)
    (x : AResidual n) :
    x ∈ targetRosterExec n ↔
      canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit x) = x :=
  ⟨canonical_of_mem_targetRosterExec hnpos, mem_targetRosterExec_of_canonical hnpos⟩

/-- **Every residual target orbit occurs exactly once.** -/
theorem targetRosterExec_orbit_unique {n : ℤ} (hnpos : 0 < n)
    (q : (aResidualInvolution n hnpos).Orbit) :
    ∃! x : AResidual n, x ∈ targetRosterExec n ∧
      (aResidualInvolution n hnpos).orbit x = q := by
  refine ⟨canonicalAResidualRepresentative hnpos q, ⟨?_, ?_⟩, ?_⟩
  · refine mem_targetRosterExec_of_canonical hnpos ?_
    rw [orbit_canonicalAResidualRepresentative]
  · exact orbit_canonicalAResidualRepresentative hnpos q
  · rintro y ⟨hy, rfl⟩
    exact (canonical_of_mem_targetRosterExec hnpos hy).symm

end TunnellMap

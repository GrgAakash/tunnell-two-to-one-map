import TunnellMap.KernelArith
import TunnellMap.BlockGeneratorCorrect
import TunnellMap.LagrangeGauss

/-!
# A kernel-reducible mirror of the block generator

`TunnellMap.BlockGen` is executable: Lean's compiler runs it.  Its definition
however goes through `Finset.sort`, `List.mergeSort`, `Int.sqrt`, rational
`⌊·⌋`/`⌈·⌉` and well-founded recursion, none of which the *kernel* can reduce.
Consequently no `decide` proof can evaluate it.

This file mirrors every such step by a structurally recursive, kernel-reducible
definition and proves the mirror equal to the original.  The mirrors carry a
`K` suffix.  No new mathematics is introduced: each `…K_eq` theorem says the
mirror computes exactly the same value.
-/

namespace TunnellMap

open OrderedGenerator

/-! ## Kernel-reducible integer intervals -/

/-- The increasing list of integers of `[lo, hi]`. -/
def intIccL (lo hi : ℤ) : List ℤ :=
  if lo ≤ hi then (List.range ((hi - lo).toNat + 1)).map (fun k : ℕ => lo + (k : ℤ)) else []

theorem mem_intIccL {lo hi x : ℤ} : x ∈ intIccL lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  unfold intIccL
  by_cases h : lo ≤ hi
  · rw [if_pos h]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · rintro ⟨h₁, h₂⟩
      exact ⟨(x - lo).toNat, by omega, by omega⟩
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_iff]
    omega

theorem intIccL_pairwise_lt (lo hi : ℤ) : (intIccL lo hi).Pairwise (· < ·) := by
  unfold intIccL
  by_cases h : lo ≤ hi
  · rw [if_pos h]
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} (hab : a < b) => by omega)
      (List.pairwise_lt_range (n := (hi - lo).toNat + 1))
  · rw [if_neg h]; exact List.Pairwise.nil

theorem intIcc_sort_eq (lo hi : ℤ) : (intIcc lo hi).sort (· ≤ ·) = intIccL lo hi :=
  Finset.sort_eq_of_sorted_lt _ _ (intIccL_pairwise_lt lo hi) fun x => by
    rw [mem_intIccL, mem_intIcc]

/-! ## The `q`-loop -/

/-- The increasing list of admissible odd multipliers. -/
def qValuesL (n A : ℤ) : List ℤ :=
  (intIccL (-n) n).filter fun q => decide (q ≠ 0 ∧ Odd q ∧ q ^ 2 * A < n)

theorem qValues_sort_eq (n A : ℤ) :
    (qValues n A).sort (· ≤ ·) = qValuesL n A := by
  refine Finset.sort_eq_of_sorted_lt _ _ ?_ ?_
  · exact List.Pairwise.filter _ (intIccL_pairwise_lt _ _)
  · intro x
    simp only [qValuesL, List.mem_filter, mem_intIccL, decide_eq_true_eq, qValues,
      Finset.mem_filter, mem_intIcc]

/-! ## The `b`-loop -/

/-- Kernel-reducible form of `bLower`. -/
def bLowerK (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  -((-(q * A * K F - isqrtK (alpha F * M n A q))) / n)

/-- Kernel-reducible form of `bUpper`. -/
def bUpperK (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  (q * A * K F + isqrtK (alpha F * M n A q)) / n

theorem bLowerK_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bLowerK n F A q = bLower n F A q := by
  rw [bLowerK, bLower, ceil_intCast_div_intCast _ _ hn, isqrtK_eq]

theorem bUpperK_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bUpperK n F A q = bUpper n F A q := by
  rw [bUpperK, bUpper, floor_intCast_div_intCast _ _ hn, isqrtK_eq]

/-- The increasing list of admissible short-interval coordinates. -/
def bValuesL (n : ℤ) {p : Triple} (F : OrthogonalFrame p) (A q : ℤ) : List ℤ :=
  intIccL (bLowerK n F A q) (bUpperK n F A q)

theorem bValues_sort_eq {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : (bValues n F A q).sort (· ≤ ·) = bValuesL n F A q := by
  rw [bValues, intIcc_sort_eq, bValuesL, bLowerK_eq hn, bUpperK_eq hn]

/-! ## The root loop -/

/-- The increasing list of admissible square roots. -/
def rootValuesL {p : Triple} (F : OrthogonalFrame p) (A q b : ℤ) : List ℤ :=
  let D := F.halfDiscriminant A q b
  let c := beta F * b + q * A * delta F
  let s := isqrtK D
  (if s = 0 then [0] else [-s, s]).filter fun u => decide (u ^ 2 = D ∧ alpha F ∣ -c + u)

theorem rootValues_sort_eq {p : Triple} (F : OrthogonalFrame p) (A q b : ℤ) :
    (rootValues F A q b).sort (· ≤ ·) = rootValuesL F A q b := by
  have hs0 : 0 ≤ Int.sqrt (F.halfDiscriminant A q b) := Int.sqrt_nonneg _
  refine Finset.sort_eq_of_sorted_lt _ _ ?_ ?_
  · refine List.Pairwise.filter _ ?_
    simp only [isqrtK_eq]
    by_cases h : Int.sqrt (F.halfDiscriminant A q b) = 0
    · rw [if_pos h]; exact List.pairwise_singleton _ _
    · rw [if_neg h]
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
      intro y hy
      rw [List.mem_singleton] at hy
      omega
  · intro x
    simp only [rootValuesL, isqrtK_eq, List.mem_filter, decide_eq_true_eq,
      mem_rootValues]
    constructor
    · rintro ⟨hmem, hcond⟩
      refine ⟨?_, hcond.1, ?_⟩
      · by_cases h : Int.sqrt (F.halfDiscriminant A q b) = 0
        · rw [if_pos h] at hmem
          rw [List.mem_singleton] at hmem
          exact Or.inl (by omega)
        · rw [if_neg h] at hmem
          rcases List.mem_cons.mp hmem with h' | h'
          · exact Or.inr h'
          · exact Or.inl (List.mem_singleton.mp h')
      · simpa using hcond.2
    · rintro ⟨hmem, hsq, hdvd⟩
      refine ⟨?_, hsq, by simpa using hdvd⟩
      by_cases h : Int.sqrt (F.halfDiscriminant A q b) = 0
      · rw [if_pos h]
        rcases hmem with h' | h' <;> (rw [List.mem_singleton]; omega)
      · rw [if_neg h]
        rcases hmem with h' | h'
        · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr h'))
        · exact List.mem_cons.mpr (Or.inl h')

/-! ## The index list of one block -/

namespace BlockGen

variable {n : ℤ} {p : Triple}

/-- Kernel-reducible form of `BlockGen.blockIndexList`. -/
def blockIndexListK (n : ℤ) (F : OrthogonalFrame p) (h : ℤ) : List GeneratorIndex :=
  (qValuesL n h).flatMap fun q =>
    (bValuesL n F h q).flatMap fun b =>
      (rootValuesL F h q b).map fun u => ⟨h, q, b, u⟩

theorem blockIndexListK_eq (hn : 0 ≤ n) (F : OrthogonalFrame p) (h : ℤ) :
    blockIndexListK n F h = blockIndexList n F h := by
  rw [blockIndexListK, blockIndexList, qValues_sort_eq]
  refine List.flatMap_congr fun q _ => ?_
  rw [bValues_sort_eq hn]
  refine List.flatMap_congr fun b _ => ?_
  rw [rootValues_sort_eq]

/-! ## The records of one block -/

variable {s : BResidual n}

/-- Kernel-reducible form of `BlockGen.blockRecords`. -/
def blockRecordsK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ) : List IncidentRecord :=
  isortB recordLe ((blockIndexListK n F h).filterMap (emit s F))

theorem blockRecordsK_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {h : ℤ}
    (h1 : 1 ≤ h) (h2 : h ≤ hMax n) :
    blockRecordsK s F h = blockRecords s F h := by
  rw [blockRecordsK, blockIndexListK_eq hn, blockRecords,
    mergeSort_eq_isortB recordLe (fun a b => by
        simpa using recordLe_total a b)
      (fun a b c => recordLe_trans a b c) ?_]
  intro a ha b hb hab hba
  have hperm : ((blockIndexList n F h).filterMap (emit s F)).Perm
      (blockRecords s F h) := (List.mergeSort_perm _ _).symm
  have hne := blockRecords_pairwise_key_ne (s := s) F h1 h2
  have ha' : a ∈ blockRecords s F h := hperm.mem_iff.mp ha
  have hb' : b ∈ blockRecords s F h := hperm.mem_iff.mp hb
  have hkey : a.key = b.key := by
    simp only [recordLe, keyLeExec_iff] at hab hba
    exact le_antisymm hab hba
  by_contra hab'
  obtain ⟨i, hi, hia⟩ := (mem_blockRecords F h a).mp ha'
  obtain ⟨j, hj, hjb⟩ := (mem_blockRecords F h b).mp hb'
  have hij : i = j :=
    recordOf_injOn_valid F (mem_validIndices_of_block F h1 h2 hi.1 hi.2)
      (mem_validIndices_of_block F h1 h2 hj.1 hj.2) (by rw [← hia, ← hjb]; exact hkey)
  exact hab' (by rw [hia, hjb, hij])

/-! ## The remaining blocks, with an explicit fuel -/

/-- Kernel-reducible form of `BlockGen.blocksFrom`, driven by a fuel argument. -/
def blocksFromK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : ℕ → ℤ → List IncidentRecord
  | 0, _ => []
  | fuel + 1, h =>
      if h ≤ hMax n then blockRecordsK s F h ++ blocksFromK s F fuel (h + 1) else []

theorem blocksFromK_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∀ (fuel : ℕ) (h : ℤ), 1 ≤ h → (hMax n + 1 - h).toNat ≤ fuel →
      blocksFromK s F fuel h = blocksFrom s F h := by
  intro fuel
  induction fuel with
  | zero =>
      intro h h1 hfuel
      have hgt : ¬ h ≤ hMax n := by omega
      rw [blocksFromK, blocksFrom, if_neg hgt]
  | succ fuel ih =>
      intro h h1 hfuel
      rw [blocksFromK, blocksFrom]
      by_cases hle : h ≤ hMax n
      · rw [if_pos hle, if_pos hle, blockRecordsK_eq hn F h1 hle,
          ih (h + 1) (by omega) (by omega)]
      · rw [if_neg hle, if_neg hle]

/-! ## One generator advance, with an explicit fuel -/

/-- Kernel-reducible form of `BlockGen.advance`, driven by a fuel argument. -/
def advanceKAux (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ℕ → GenState → Option (IncidentRecord × GenState)
  | _, ⟨h, r :: rest⟩ => some (r, ⟨h, rest⟩)
  | 0, ⟨_, []⟩ => none
  | fuel + 1, ⟨h, []⟩ =>
      if h ≤ hMax n then advanceKAux s F fuel ⟨h + 1, blockRecordsK s F h⟩ else none

theorem advanceKAux_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    ∀ (fuel : ℕ) (st : GenState), 1 ≤ st.nextBlock →
      (hMax n + 1 - st.nextBlock).toNat ≤ fuel →
      advanceKAux s F fuel st = advance s F st := by
  intro fuel
  induction fuel with
  | zero =>
      rintro ⟨h, pend⟩ h1 hfuel
      cases pend with
      | cons r rest => rw [advanceKAux, advance]
      | nil =>
          have h1' : (1 : ℤ) ≤ h := h1
          have hfuel' : (hMax n + 1 - h).toNat ≤ 0 := hfuel
          have hgt : ¬ h ≤ hMax n := by omega
          rw [advanceKAux, advance, if_neg hgt]
  | succ fuel ih =>
      rintro ⟨h, pend⟩ h1 hfuel
      cases pend with
      | cons r rest => rw [advanceKAux, advance]
      | nil =>
          have h1' : (1 : ℤ) ≤ h := h1
          have hfuel' : (hMax n + 1 - h).toNat ≤ fuel + 1 := hfuel
          by_cases hle : h ≤ hMax n
          · rw [advanceKAux, advance, if_pos hle, if_pos hle,
              blockRecordsK_eq hn F h1' hle,
              ih ⟨h + 1, blockRecords s F h⟩
                (show (1 : ℤ) ≤ h + 1 by omega)
                (show (hMax n + 1 - (h + 1)).toNat ≤ fuel by omega)]
          · rw [advanceKAux, advance, if_neg hle, if_neg hle]

/-- Kernel-reducible form of `BlockGen.advance`: the fuel is computed from the
state, so no hypothesis on it is needed. -/
def advanceK (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState) :
    Option (IncidentRecord × GenState) :=
  advanceKAux s F (hMax n + 1 - st.nextBlock).toNat st

theorem advanceK_eq (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (st : GenState)
    (h1 : 1 ≤ st.nextBlock) : advanceK s F st = advance s F st :=
  advanceKAux_eq hn F _ st h1 le_rfl

end BlockGen

/-! ## Kernel-reducible Lagrange–Gauss reduction -/

/-- Kernel-reducible form of `lgReduceAux`, driven by a fuel argument. -/
def lgReduceAuxK : ℕ → Triple → Triple → Triple × Triple
  | 0, u, v => (u, lgNext u v)
  | fuel + 1, u, v =>
      if dot (lgNext u v) (lgNext u v) < dot u u then
        lgReduceAuxK fuel (lgNext u v) (negTriple u)
      else (u, lgNext u v)

theorem lgReduceAuxK_eq :
    ∀ (fuel : ℕ) (u v : Triple), (dot u u).toNat ≤ fuel →
      lgReduceAuxK fuel u v = lgReduceAux u v := by
  intro fuel
  induction fuel with
  | zero =>
      intro u v hfuel
      have hnn := dot_self_nonneg u
      have hzero : dot u u = 0 := by omega
      have hlt : ¬ dot (lgNext u v) (lgNext u v) < dot u u := by
        have := dot_self_nonneg (lgNext u v); omega
      rw [lgReduceAuxK, lgReduceAux, dif_neg hlt]
  | succ fuel ih =>
      intro u v hfuel
      rw [lgReduceAuxK, lgReduceAux]
      by_cases h : dot (lgNext u v) (lgNext u v) < dot u u
      · rw [if_pos h, dif_pos h]
        refine ih _ _ ?_
        have := dot_self_nonneg (lgNext u v)
        omega
      · rw [if_neg h, dif_neg h]

/-- Kernel-reducible form of `lgReduce`. -/
def lgReduceK (u v : Triple) : Triple × Triple :=
  lgSelect (lgReduceAuxK (dot u u).toNat u v)

theorem lgReduceK_eq (u v : Triple) : lgReduceK u v = lgReduce u v := by
  rw [lgReduceK, lgReduce, lgReduceAuxK_eq _ u v le_rfl]

/-- Two orthogonal frames with the same data are equal. -/
theorem OrthogonalFrame.ext' {p : Triple} {F G : OrthogonalFrame p}
    (h₁ : F.e₁ = G.e₁) (h₂ : F.e₂ = G.e₂) (h₃ : F.z = G.z) : F = G := by
  cases F; cases G; cases h₁; cases h₂; cases h₃; rfl

/-- Kernel-reducible form of `reduceFrame`. -/
def reduceFrameK {p : Triple} (F : OrthogonalFrame p) : OrthogonalFrame p where
  e₁ := (lgReduceK F.e₁ F.e₂).1
  e₂ := (lgReduceK F.e₁ F.e₂).2
  z := F.z
  cross_eq := by rw [lgReduceK_eq, lgReduce_cross]; exact F.cross_eq
  bezout := F.bezout

theorem reduceFrameK_eq {p : Triple} (F : OrthogonalFrame p) :
    reduceFrameK F = reduceFrame F :=
  OrthogonalFrame.ext' (by simp [reduceFrameK, reduceFrame, lgReduceK_eq])
    (by simp [reduceFrameK, reduceFrame, lgReduceK_eq]) rfl

end TunnellMap

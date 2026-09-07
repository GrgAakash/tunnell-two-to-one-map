import TunnellMap.GeneratorSoundness
import TunnellMap.OrbitRanking
import TunnellMap.PreferenceList

/-!
# The finite ordered-adjacency generator

This file implements Algorithm 5.4 as nested finite integer ranges.  The
outer parameters are the direction norm `A`, the odd multiplier `q`, the
short-interval coordinate `b`, and the two-set of possible square-root signs
`u`.  The first affine coordinate is recovered by exact division.
-/

namespace TunnellMap

structure GeneratorIndex where
  A : ℤ
  q : ℤ
  b : ℤ
  u : ℤ
deriving DecidableEq

namespace OrderedGenerator

variable {n : ℤ} {p : Triple}

def alpha (F : OrthogonalFrame p) : ℤ := dot F.e₁ F.e₁

def beta (F : OrthogonalFrame p) : ℤ := dot F.e₁ F.e₂

def delta (F : OrthogonalFrame p) : ℤ := dot F.z F.e₁

def epsilon (F : OrthogonalFrame p) : ℤ := dot F.z F.e₂

def K (F : OrthogonalFrame p) : ℤ :=
  beta F * delta F - alpha F * epsilon F

def M (n A q : ℤ) : ℤ := A * (n - q ^ 2 * A)

def intOffsetEmbedding (lo : ℤ) : ℕ ↪ ℤ where
  toFun k := lo + k
  inj' := by intro a b h; exact_mod_cast (Int.add_left_cancel h)

/-- A computable closed interval of integers. -/
def intIcc (lo hi : ℤ) : Finset ℤ :=
  if lo ≤ hi then
    (Finset.range (Int.toNat (hi - lo) + 1)).map (intOffsetEmbedding lo)
  else
    ∅

@[simp] theorem mem_intIcc {lo hi x : ℤ} :
    x ∈ intIcc lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  by_cases hbounds : lo ≤ hi
  · constructor
    · intro hx
      have hxMap : x ∈
          (Finset.range (Int.toNat (hi - lo) + 1)).map
            (intOffsetEmbedding lo) := by
        simpa [intIcc, hbounds] using hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_map.mp hxMap
      have hklt : k < Int.toNat (hi - lo) + 1 := Finset.mem_range.mp hk
      have hdiff : 0 ≤ hi - lo := sub_nonneg.mpr hbounds
      have hkLeInt : (k : ℤ) ≤ hi - lo := by
        have hkLe : k ≤ Int.toNat (hi - lo) := by omega
        rw [← Int.toNat_of_nonneg hdiff]
        exact_mod_cast hkLe
      have hkx' : lo + (k : ℤ) = x := hkx
      constructor <;> omega
    · rintro ⟨hlo, hhi⟩
      let k : ℕ := Int.toNat (x - lo)
      have hxDiff : 0 ≤ x - lo := sub_nonneg.mpr hlo
      have hiDiff : 0 ≤ hi - lo := sub_nonneg.mpr hbounds
      have hkCast : (k : ℤ) = x - lo := by
        simp [k, Int.toNat_of_nonneg hxDiff]
      have hkLeInt : (k : ℤ) ≤ hi - lo := by omega
      have hkLe : k ≤ Int.toNat (hi - lo) := by
        have hkCastLe : (k : ℤ) ≤ (Int.toNat (hi - lo) : ℤ) := by
          simpa [Int.toNat_of_nonneg hiDiff] using hkLeInt
        exact Int.ofNat_le.mp hkCastLe
      have hkMem : k ∈ Finset.range (Int.toNat (hi - lo) + 1) := by
        simp only [Finset.mem_range]
        omega
      have hmap : x ∈
          (Finset.range (Int.toNat (hi - lo) + 1)).map
            (intOffsetEmbedding lo) := by
        apply Finset.mem_map.mpr
        refine ⟨k, hkMem, ?_⟩
        change lo + (k : ℤ) = x
        omega
      simpa [intIcc, hbounds] using hmap
  · constructor
    · simp [intIcc, hbounds]
    · rintro ⟨hlo, hhi⟩
      exact (hbounds (hlo.trans hhi)).elim

def AValues (n : ℤ) : Finset ℤ := intIcc 1 ((n - 1) / 2)

def qValues (n A : ℤ) : Finset ℤ :=
  (intIcc (-n) n).filter fun q => q ≠ 0 ∧ Odd q ∧ q ^ 2 * A < n

def bLower (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  ⌈(((q * A * K F - Int.sqrt (alpha F * M n A q) : ℤ) : ℚ) / (n : ℚ))⌉

def bUpper (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : ℤ :=
  ⌊(((q * A * K F + Int.sqrt (alpha F * M n A q) : ℤ) : ℚ) / (n : ℚ))⌋

def bValues (n : ℤ) (F : OrthogonalFrame p) (A q : ℤ) : Finset ℤ :=
  intIcc (bLower n F A q) (bUpper n F A q)

def rootValues (F : OrthogonalFrame p) (A q b : ℤ) : Finset ℤ :=
  let D := F.halfDiscriminant A q b
  let c := beta F * b + q * A * delta F
  ({Int.sqrt D, -Int.sqrt D} : Finset ℤ).filter fun u =>
    u ^ 2 = D ∧ alpha F ∣ -c + u

def indexEmbedding (A q b : ℤ) : ℤ ↪ GeneratorIndex where
  toFun u := ⟨A, q, b, u⟩
  inj' := by intro u v h; exact congrArg GeneratorIndex.u h

/-- The literal finite nest of steps 1--4 of Algorithm 5.4. -/
def rawIndices (n : ℤ) (F : OrthogonalFrame p) : Finset GeneratorIndex :=
  (AValues n).biUnion fun A =>
    (qValues n A).biUnion fun q =>
      (bValues n F A q).biUnion fun b =>
        (rootValues F A q b).map (indexEmbedding A q b)

@[simp] theorem mem_rawIndices (n : ℤ) (F : OrthogonalFrame p)
    (i : GeneratorIndex) :
    i ∈ rawIndices n F ↔
      i.A ∈ AValues n ∧ i.q ∈ qValues n i.A ∧
        i.b ∈ bValues n F i.A i.q ∧
          i.u ∈ rootValues F i.A i.q i.b := by
  simp only [rawIndices, Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨A, hA, q, hq, b, hb, u, hu, hui⟩
    have hi : i = ⟨A, q, b, u⟩ := hui.symm
    subst i
    simpa using ⟨hA, hq, hb, hu⟩
  · rintro ⟨hA, hq, hb, hu⟩
    refine ⟨i.A, hA, i.q, hq, i.b, hb, i.u, hu, ?_⟩
    rfl

@[simp] theorem mem_rootValues (F : OrthogonalFrame p) (A q b u : ℤ) :
    u ∈ rootValues F A q b ↔
      (u = Int.sqrt (F.halfDiscriminant A q b) ∨
        u = -Int.sqrt (F.halfDiscriminant A q b)) ∧
      u ^ 2 = F.halfDiscriminant A q b ∧
      alpha F ∣ -(beta F * b + q * A * delta F) + u := by
  simp [rootValues]

def aValue (F : OrthogonalFrame p) (i : GeneratorIndex) : ℤ :=
  (-(beta F * i.b + i.q * i.A * delta F) + i.u) / alpha F

def rValue (F : OrthogonalFrame p) (i : GeneratorIndex) : Triple :=
  linComb3 (aValue F i) i.b (i.q * i.A) F.e₁ F.e₂ F.z

def dValue (F : OrthogonalFrame p) (i : GeneratorIndex) : Triple :=
  tauInv (rValue F i)

def targetValue (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Triple :=
  reconstructedTarget (residualSourceLift s) i.q (dValue F i)

theorem alpha_pos (F : OrthogonalFrame p) : 0 < alpha F := by
  have he₁ : F.e₁ ≠ ⟨0, 0, 0⟩ := by
    intro hzero
    have hdet := F.det_eq_one
    simp [det3, cross, dot, hzero] at hdet
  by_cases hx : F.e₁.x = 0
  · by_cases hy : F.e₁.y = 0
    · have hz : F.e₁.z ≠ 0 := by
        intro hz
        apply he₁
        ext <;> simp_all
      simpa [alpha, dot, hx, hy] using hz
    · have hysq : 0 < F.e₁.y ^ 2 := sq_pos_of_ne_zero hy
      have hzsq : 0 ≤ F.e₁.z ^ 2 := sq_nonneg _
      simp [alpha, dot, hx]
      nlinarith
  · have hxsq : 0 < F.e₁.x ^ 2 := sq_pos_of_ne_zero hx
    have hysq : 0 ≤ F.e₁.y ^ 2 := sq_nonneg _
    have hzsq : 0 ≤ F.e₁.z ^ 2 := sq_nonneg _
    simp [alpha, dot]
    nlinarith

theorem q_mem_search_bounds {n A q : ℤ} (hn : 0 < n) (hA : 0 < A)
    (hq : q ^ 2 * A < n) : -n ≤ q ∧ q ≤ n := by
  have hqSqLe : q ^ 2 ≤ q ^ 2 * A := by
    have hAone : 1 ≤ A := hA
    nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (sub_nonneg.mpr (by omega : 0 ≤ A - 1))]
  have hqSqLt : q ^ 2 < n := lt_of_le_of_lt hqSqLe hq
  have hnSq : n ≤ n ^ 2 := by
    nlinarith [sq_nonneg (n - 1)]
  have hsq : q ^ 2 < n ^ 2 := hqSqLt.trans_le hnSq
  have habs : |q| < n := abs_lt_of_sq_lt_sq hsq hn.le
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩

theorem aValue_linear_of_dvd (F : OrthogonalFrame p) (i : GeneratorIndex)
    (hdiv : alpha F ∣ -(beta F * i.b + i.q * i.A * delta F) + i.u) :
    alpha F * aValue F i =
      -(beta F * i.b + i.q * i.A * delta F) + i.u := by
  rw [aValue, mul_comm]
  exact Int.ediv_mul_cancel hdiv

theorem dot_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    dot p (rValue F i) = i.q * i.A := by
  simp only [rValue, linComb3, vadd, vsmul, dot]
  have h₁ := F.e₁_orthogonal
  have h₂ := F.e₂_orthogonal
  have hz := F.bezout
  simp only [dot] at h₁ h₂ hz
  linear_combination (aValue F i) * h₁ + i.b * h₂ + (i.q * i.A) * hz

theorem tau_dValue_of_parity (F : OrthogonalFrame p) (i : GeneratorIndex)
    (hparity : InTauLattice (rValue F i)) :
    tau (dValue F i) = rValue F i := by
  exact tau_tauInv hparity

@[simp] theorem coeff₁_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    F.coeff₁ (rValue F i) = aValue F i := by
  unfold OrthogonalFrame.coeff₁ rValue
  rw [dot_linComb3_cross_e₂_z, F.det_eq_one]
  ring

@[simp] theorem coeff₂_rValue (F : OrthogonalFrame p) (i : GeneratorIndex) :
    F.coeff₂ (rValue F i) = i.b := by
  unfold OrthogonalFrame.coeff₂ rValue
  rw [dot_linComb3_cross_z_e₁, F.det_eq_one]
  ring

theorem affine_norm_of_rawIndex (F : OrthogonalFrame p) {i : GeneratorIndex}
    (hi : i ∈ rawIndices n F) : dot (rValue F i) (rValue F i) = i.A := by
  have hu := (mem_rawIndices n F i).mp hi |>.2.2.2
  have hroot := (mem_rootValues F i.A i.q i.b i.u).mp hu
  rw [rValue, F.affine_norm_root_certificate]
  refine ⟨i.u, hroot.2.1, ?_⟩
  exact aValue_linear_of_dvd F i hroot.2.2

theorem qForm_dValue_of_rawIndex (F : OrthogonalFrame p) {i : GeneratorIndex}
    (hi : i ∈ rawIndices n F) (hparity : InTauLattice (rValue F i)) :
    qForm (dValue F i) = i.A := by
  rw [← qForm_tau, tau_dValue_of_parity F i hparity]
  exact affine_norm_of_rawIndex F hi

theorem bilinear_dValue_of_rawIndex
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hparity : InTauLattice (rValue F i)) :
    qBilinear (residualSourceLift s) (dValue F i) = i.q * i.A := by
  calc
    qBilinear (residualSourceLift s) (dValue F i) =
        dot (tau (residualSourceLift s)) (tau (dValue F i)) := by
          simp [qBilinear]
    _ = dot (tau (residualSourceLift s)) (rValue F i) := by
      rw [tau_dValue_of_parity F i hparity]
    _ = i.q * i.A := dot_rValue F i

/-- The explicit retention tests in steps 5--7.  The final equality says that
the generated signed direction is the smaller of the two midpoint directions;
it is exactly the semantic result of the key comparison in step 7. -/
def PassesFilters (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) : Prop :=
  InTauLattice (rValue F i) ∧
    tripleContent (dValue F i) = 1 ∧
    FirstNonzeroPositive (dValue F i) ∧
    Odd (dValue F i).z ∧
    ∃ t : AResidual n,
      residualTargetLift t = targetValue s F i ∧
        directionKey (dValue F i) = representativeEdgeKey s t

noncomputable def validIndices (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) : Finset GeneratorIndex := by
  classical
  exact (rawIndices n F).filter (PassesFilters s F)

theorem mem_validIndices_iff (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    i ∈ validIndices s F ↔ i ∈ rawIndices n F ∧ PassesFilters s F i := by
  classical
  simp [validIndices]

noncomputable def targetOfValid (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : AResidual n := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact Classical.choose hfilters.2.2.2.2

theorem targetOfValid_lift (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    residualTargetLift (targetOfValid s F i) = targetValue s F i.1 := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact (Classical.choose_spec hfilters.2.2.2.2).1

theorem targetOfValid_key (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    directionKey (dValue F i.1) =
      representativeEdgeKey s (targetOfValid s F i) := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact (Classical.choose_spec hfilters.2.2.2.2).2

theorem validIndex_raw (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : i.1 ∈ rawIndices n F :=
  (mem_validIndices_iff s F i.1).mp i.2 |>.1

theorem validIndex_filters (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : PassesFilters s F i.1 :=
  (mem_validIndices_iff s F i.1).mp i.2 |>.2

/-- Intrinsic uniqueness of the arithmetic search coordinates. -/
theorem validIndex_eq_of_directionKey_eq
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i j : {i // i ∈ validIndices s F})
    (hkey : directionKey (dValue F i.1) = directionKey (dValue F j.1)) :
    i = j := by
  have hiRaw := validIndex_raw s F i
  have hjRaw := validIndex_raw s F j
  have hiFilters := validIndex_filters s F i
  have hjFilters := validIndex_filters s F j
  have hdiFix := primitiveDirection_eq_self_of_content_one_of_oriented
    hiFilters.2.1 hiFilters.2.2.1
  have hdjFix := primitiveDirection_eq_self_of_content_one_of_oriented
    hjFilters.2.1 hjFilters.2.2.1
  have hd : dValue F i.1 = dValue F j.1 := by
    have hprimitive := directionKey_eq_iff.mp hkey
    rw [hdiFix, hdjFix] at hprimitive
    exact hprimitive
  have hAi := qForm_dValue_of_rawIndex F hiRaw hiFilters.1
  have hAj := qForm_dValue_of_rawIndex F hjRaw hjFilters.1
  have hA : i.1.A = j.1.A := by
    calc
      i.1.A = qForm (dValue F i.1) := hAi.symm
      _ = qForm (dValue F j.1) := congrArg qForm hd
      _ = j.1.A := hAj
  have hApos : 0 < i.1.A := by
    have hmem := (mem_rawIndices n F i.1).mp hiRaw |>.1
    rw [AValues, mem_intIcc] at hmem
    omega
  have hbi := bilinear_dValue_of_rawIndex s F hiFilters.1
  have hbj := bilinear_dValue_of_rawIndex s F hjFilters.1
  have hqMul : i.1.q * i.1.A = j.1.q * i.1.A := by
    calc
      i.1.q * i.1.A = qBilinear (residualSourceLift s) (dValue F i.1) := hbi.symm
      _ = qBilinear (residualSourceLift s) (dValue F j.1) := congrArg _ hd
      _ = j.1.q * j.1.A := hbj
      _ = j.1.q * i.1.A := by rw [hA]
  have hq : i.1.q = j.1.q :=
    mul_right_cancel₀ (ne_of_gt hApos) hqMul
  have hr : rValue F i.1 = rValue F j.1 := by
    calc
      rValue F i.1 = tau (dValue F i.1) :=
        (tau_dValue_of_parity F i.1 hiFilters.1).symm
      _ = tau (dValue F j.1) := congrArg tau hd
      _ = rValue F j.1 := tau_dValue_of_parity F j.1 hjFilters.1
  have hb : i.1.b = j.1.b := by
    simpa using congrArg F.coeff₂ hr
  have ha : aValue F i.1 = aValue F j.1 := by
    simpa using congrArg F.coeff₁ hr
  have hui := (mem_rootValues F i.1.A i.1.q i.1.b i.1.u).mp
    ((mem_rawIndices n F i.1).mp hiRaw |>.2.2.2)
  have huj := (mem_rootValues F j.1.A j.1.q j.1.b j.1.u).mp
    ((mem_rawIndices n F j.1).mp hjRaw |>.2.2.2)
  have hlinearI := aValue_linear_of_dvd F i.1 hui.2.2
  have hlinearJ := aValue_linear_of_dvd F j.1 huj.2.2
  have hu : i.1.u = j.1.u := by
    rw [hA, hq, hb, ha] at hlinearI
    linarith
  apply Subtype.ext
  cases hi : i.1 with
  | mk Ai qi bi ui =>
      cases hj : j.1 with
      | mk Aj qj bj uj =>
          simp_all

theorem validIndex_key_injective
    (s : BResidual n) (F : OrthogonalFrame (tau (residualSourceLift s))) :
    Function.Injective (fun i : {i // i ∈ validIndices s F} =>
      directionKey (dValue F i.1)) := by
  intro i j h
  exact validIndex_eq_of_directionKey_eq s F i j h

noncomputable def targetOrbitOfValid (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    (aResidualInvolution n hnpos).Orbit :=
  (aResidualInvolution n hnpos).orbit (targetOfValid s F i)

theorem validIndex_key_eq_orbitEdgeKey (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    directionKey (dValue F i.1) =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        (targetOrbitOfValid hnpos s F i) := by
  calc
    directionKey (dValue F i.1) =
        representativeEdgeKey s (targetOfValid s F i) :=
      targetOfValid_key s F i
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((aResidualInvolution n hnpos).orbit (targetOfValid s F i)) :=
      representativeEdgeKey_eq_orbitEdgeKey hnpos s (targetOfValid s F i)
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        (targetOrbitOfValid hnpos s F i) := rfl

theorem targetOrbitOfValid_injective (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    Function.Injective (targetOrbitOfValid hnpos s F) := by
  intro i j horbit
  apply validIndex_eq_of_directionKey_eq s F
  calc
    directionKey (dValue F i.1) =
        orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
          (targetOrbitOfValid hnpos s F i) :=
      validIndex_key_eq_orbitEdgeKey hnpos s F i
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
          (targetOrbitOfValid hnpos s F j) := by rw [horbit]
    _ = directionKey (dValue F j.1) :=
      (validIndex_key_eq_orbitEdgeKey hnpos s F j).symm

noncomputable def orderedIndexList (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    List {i // i ∈ validIndices s F} :=
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  (validIndices s F).attach.sort (· ≤ ·)

theorem orderedIndexList_pairwise (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (orderedIndexList s F).Pairwise fun i j =>
      directionKey (dValue F i.1) ≤ directionKey (dValue F j.1) := by
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  exact Finset.pairwise_sort ((validIndices s F).attach) (· ≤ ·)

theorem orderedIndexList_nodup (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (orderedIndexList s F).Nodup := by
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  exact Finset.sort_nodup ((validIndices s F).attach) (· ≤ ·)

@[simp] theorem mem_orderedIndexList (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : i ∈ orderedIndexList s F := by
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  have h : i ∈ ((validIndices s F).attach).sort
      (α := {i // i ∈ validIndices s F}) (· ≤ ·) := by
    simp
  exact h

theorem orderedIndexList_key_strict (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (orderedIndexList s F).length} (hij : i < j) :
    directionKey (dValue F ((orderedIndexList s F).get i).1) <
      directionKey (dValue F ((orderedIndexList s F).get j).1) := by
  have hle := (orderedIndexList_pairwise s F).rel_get_of_lt hij
  have hne : (orderedIndexList s F).get i ≠ (orderedIndexList s F).get j := by
    intro h
    exact (ne_of_lt hij) ((orderedIndexList_nodup s F).injective_get h)
  apply lt_of_le_of_ne hle
  intro hkey
  exact hne (validIndex_key_injective s F hkey)

/-- The stateful generator's extensional output list.  Its finite construction
is the termination certificate for Algorithm 5.4. -/
noncomputable def incidentStream (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    List (aResidualInvolution n hnpos).Orbit :=
  (orderedIndexList s F).map (targetOrbitOfValid hnpos s F)

theorem incidentStream_nodup (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Nodup := by
  exact (orderedIndexList_nodup s F).map
    (targetOrbitOfValid_injective hnpos s F)

theorem orbit_preferredTarget (hnpos : 0 < n) (s : BResidual n)
    (t : AResidual n) :
    (aResidualInvolution n hnpos).orbit (preferredTarget s t) =
      (aResidualInvolution n hnpos).orbit t := by
  by_cases hkey : directionKey (plusVector s t) < directionKey (minusVector s t)
  · simp [preferredTarget, hkey]
  · rw [show preferredTarget s t = negAResidual t by simp [preferredTarget, hkey]]
    exact (aResidualInvolution n hnpos).orbit_neg t

theorem representativeEdgeKey_preferredTarget (s : BResidual n)
    (t : AResidual n) :
    representativeEdgeKey s (preferredTarget s t) = representativeEdgeKey s t := by
  unfold preferredTarget
  split <;> simp

/-- Completeness of the nested arithmetic loops: every residual target orbit
occurs among the retained indices for every oriented source frame. -/
theorem exists_validIndex_for_targetOrbit (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃ i : {i // i ∈ validIndices s F},
      targetOrbitOfValid hnpos s F i = tOrbit := by
  let t₀ := canonicalAResidualRepresentative hnpos tOrbit
  let R : PreferredMidpointRecord s t₀ :=
    Classical.choice (exists_preferred_midpoint_record hn s t₀)
  obtain ⟨W, hWF⟩ := generatorWitness_with_frame hn hnpos s t₀ R F
  subst F
  let i : GeneratorIndex := ⟨W.A, W.q, W.b, W.u⟩
  have hAupper : W.A ≤ (n - 1) / 2 := by
    apply (Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)).2
    nlinarith [W.A_bound]
  have hAmem : W.A ∈ AValues n := by
    rw [AValues, mem_intIcc]
    exact ⟨by have h := W.A_pos; omega, hAupper⟩
  have hqne : W.q ≠ 0 := by
    intro hq
    apply Int.not_odd_zero
    simpa [hq] using W.q_odd
  have hqbounds := q_mem_search_bounds hnpos W.A_pos W.q_range
  have hqmem : W.q ∈ qValues n W.A := by
    simp [qValues, hqbounds, hqne, W.q_odd, W.q_range]
  have hwindow :
      (n * W.b - W.q * W.A * K W.frame) ^ 2 ≤
        alpha W.frame * M n W.A W.q := by
    simpa [alpha, beta, delta, epsilon, K, M] using W.short_window
  have hAM : 0 ≤ alpha W.frame * M n W.A W.q :=
    (sq_nonneg (n * W.b - W.q * W.A * K W.frame)).trans hwindow
  have hbBounds :=
    (square_le_iff_mem_floorCeilInterval hnpos hAM).mp hwindow
  have hbmem : W.b ∈ bValues n W.frame W.A W.q := by
    rw [bValues, mem_intIcc]
    simpa [bLower, bUpper] using hbBounds
  have huSquare := W.root_certificate.1
  have hrootExists : ∃ x : ℤ, x * x = W.frame.halfDiscriminant W.A W.q W.b := by
    exact ⟨W.u, by simpa [pow_two] using huSquare⟩
  have hsqrtMul := (Int.exists_mul_self _).mp hrootExists
  have hsqrtSquare : (Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b)) ^ 2 =
      W.frame.halfDiscriminant W.A W.q W.b := by
    simpa [pow_two] using hsqrtMul
  have huCases : W.u = Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b) ∨
      W.u = -Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b) :=
    integer_square_roots (huSquare.trans hsqrtSquare.symm)
  have huDiv : alpha W.frame ∣
      -(beta W.frame * W.b + W.q * W.A * delta W.frame) + W.u := by
    refine ⟨W.a, ?_⟩
    simpa [alpha, beta, delta, mul_comm] using W.root_certificate.2.symm
  have humem : W.u ∈ rootValues W.frame W.A W.q W.b := by
    rw [mem_rootValues]
    exact ⟨huCases, huSquare, huDiv⟩
  have hiRaw : i ∈ rawIndices n W.frame := by
    rw [mem_rawIndices]
    exact ⟨hAmem, hqmem, hbmem, humem⟩
  have haValue : aValue W.frame i = W.a := by
    apply mul_left_cancel₀ (ne_of_gt (alpha_pos W.frame))
    calc
      alpha W.frame * aValue W.frame i =
          -(beta W.frame * W.b + W.q * W.A * delta W.frame) + W.u := by
            simpa [i] using
              aValue_linear_of_dvd W.frame i (by simpa [i] using huDiv)
      _ = alpha W.frame * W.a := by
        simpa [alpha, beta, delta] using W.root_certificate.2.symm
  have hrValue : rValue W.frame i = W.r := by
    rw [W.affine_coordinates]
    simp [rValue, i, haValue]
  have hdValue : dValue W.frame i = R.direction := by
    rw [dValue, hrValue, W.r_eq, tauInv_tau]
  have htargetValue : residualTargetLift R.target = targetValue s W.frame i := by
    unfold targetValue
    change residualTargetLift R.target =
      reconstructedTarget (residualSourceLift s) W.q (dValue W.frame i)
    rw [hdValue]
    exact generatorWitness_reconstructs_target W
  have hkey : directionKey (dValue W.frame i) = representativeEdgeKey s R.target := by
    calc
      directionKey (dValue W.frame i) = directionKey R.direction := by rw [hdValue]
      _ = directionKey (preferredVector s t₀) := by
        rw [R.direction_eq,
          directionKey_primitiveDirection (preferredVector_ne_zero s t₀)]
      _ = representativeEdgeKey s t₀ :=
        (representativeEdgeKey_eq_preferred s t₀).symm
      _ = representativeEdgeKey s R.target := by
        rw [R.target_eq, representativeEdgeKey_preferredTarget]
  have hfilters : PassesFilters s W.frame i := by
    refine ⟨?_, ?_, ?_, ?_, R.target, htargetValue, hkey⟩
    · simpa [hrValue] using W.r_tau_parity
    · simp [hdValue, R.direction_eq]
    · simpa [hdValue] using R.direction_oriented
    · simpa [hdValue] using R.direction_third_odd
  have hiValid : i ∈ validIndices s W.frame :=
    (mem_validIndices_iff s W.frame i).2 ⟨hiRaw, hfilters⟩
  let iv : {i // i ∈ validIndices s W.frame} := ⟨i, hiValid⟩
  refine ⟨iv, ?_⟩
  have htSigned : targetOfValid s W.frame iv = R.target := by
    apply residualTargetLift_injective
    exact (targetOfValid_lift s W.frame iv).trans htargetValue.symm
  rw [targetOrbitOfValid, htSigned, R.target_eq, orbit_preferredTarget]
  exact (aResidualInvolution n hnpos).orbit_canonicalRepresentative
    aResidualLexKey aResidualLexKey_injective tOrbit

/-- Every residual target orbit occurs in the generated incident stream. -/
theorem mem_incidentStream (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    tOrbit ∈ incidentStream hnpos s F := by
  obtain ⟨i, hi⟩ := exists_validIndex_for_targetOrbit hn hnpos s F tOrbit
  rw [incidentStream, List.mem_map]
  exact ⟨i, mem_orderedIndexList s F i, hi⟩

/-- Each residual target orbit has exactly one position in the incident
stream.  This is the literal exact-once assertion of Theorem 5.6. -/
theorem incidentStream_exactly_once (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃! i : Fin (incidentStream hnpos s F).length,
      (incidentStream hnpos s F).get i = tOrbit := by
  obtain ⟨i, hi⟩ := List.get_of_mem
    (mem_incidentStream hn hnpos s F tOrbit)
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (incidentStream_nodup hnpos s F).injective_get (hj.trans hi.symm)

set_option maxHeartbeats 800000 in
/-- The emitted incident orbits occur in strictly increasing projective-key
order. -/
theorem incidentStream_key_strict (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (incidentStream hnpos s F).length} (hij : i < j) :
    orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get i) <
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get j) := by
  let i' : Fin (orderedIndexList s F).length :=
    ⟨i.1, by simpa [incidentStream] using i.2⟩
  let j' : Fin (orderedIndexList s F).length :=
    ⟨j.1, by simpa [incidentStream] using j.2⟩
  have hij' : i' < j' := hij
  have hkey := orderedIndexList_key_strict s F hij'
  rw [validIndex_key_eq_orbitEdgeKey hnpos s F
      ((orderedIndexList s F).get i'),
    validIndex_key_eq_orbitEdgeKey hnpos s F
      ((orderedIndexList s F).get j')] at hkey
  have hiMap : (incidentStream hnpos s F).get i =
      targetOrbitOfValid hnpos s F ((orderedIndexList s F).get i') :=
    List.getElem_map (targetOrbitOfValid hnpos s F)
      (l := orderedIndexList s F) (i := i.1) (h := i.2)
  have hjMap : (incidentStream hnpos s F).get j =
      targetOrbitOfValid hnpos s F ((orderedIndexList s F).get j') :=
    List.getElem_map (targetOrbitOfValid hnpos s F)
      (l := orderedIndexList s F) (i := j.1) (h := j.2)
  exact (congrArg (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) hiMap).trans_lt
    (hkey.trans_eq
      (congrArg (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) hjMap.symm))

end OrderedGenerator

end TunnellMap

import TunnellMap.Examples41

/-!
# The residual `n = 41` table

The declarations in this file certify the residual source and target
representatives used in the manuscript and the arithmetic attached to all
sixteen orbit edges.
-/

namespace TunnellMap
namespace Examples41

set_option maxRecDepth 10000

/-! ## Residual representatives -/

def s1 : BResidual 41 := by
  refine ⟨⟨⟨-2, -5, -1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega

def s2 : BResidual 41 := by
  refine ⟨midpointSource, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    simp only [midpointSource]
    omega
  · constructor
    · intro q
      simp only [midpointSource]
      omega
    · intro q
      simp only [midpointSource]
      omega

def s3 : BResidual 41 := by
  refine ⟨⟨⟨-2, 5, -1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega

def s4 : BResidual 41 := by
  refine ⟨⟨⟨-2, 5, 1⟩, by norm_num [bForm], by norm_num⟩, ?_⟩
  simp only [DirectSourceUsed, DirectPredicate1, DirectPredicate2, DirectPredicate3]
  push Not
  constructor
  · intro q
    omega
  · constructor
    · intro q
      omega
    · intro q
      omega

def t1 : AResidual 41 := by
  refine ⟨⟨⟨-4, -3, 0⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega

def t2 : AResidual 41 := by
  refine ⟨⟨⟨-4, 3, 0⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega

def t3 : AResidual 41 := by
  refine ⟨⟨⟨0, -3, -1⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega

def t4 : AResidual 41 := by
  refine ⟨⟨⟨0, -3, 1⟩, by norm_num [aForm]⟩, ?_⟩
  simp only [DirectTargetUsed, ImagePredicate1, ImagePredicate2, ImagePredicate3]
  push Not
  constructor
  · intro q hq
    rcases hq with ⟨k, hk⟩
    norm_num at hk ⊢
    omega
  · constructor
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega
    · intro q hq
      rcases hq with ⟨k, hk⟩
      norm_num at hk ⊢
      omega

theorem residual_lifts :
    residualSourceLift s1 = ⟨-2, -5, -2⟩ ∧
      residualSourceLift s2 = ⟨-2, -5, 2⟩ ∧
      residualSourceLift s3 = ⟨-2, 5, -2⟩ ∧
      residualSourceLift s4 = ⟨-2, 5, 2⟩ ∧
      residualTargetLift t1 = ⟨-4, -3, 0⟩ ∧
      residualTargetLift t2 = ⟨-4, 3, 0⟩ ∧
      residualTargetLift t3 = ⟨0, -3, -4⟩ ∧
      residualTargetLift t4 = ⟨0, -3, 4⟩ := by
  norm_num [s1, s2, s3, s4, t1, t2, t3, t4, residualSourceLift,
    residualTargetLift, bLift, aLift, midpointSource]

/-! ## Primitive directions and their keys -/

theorem tripleContent_eq_one_of_x_one (y z : ℤ) :
    tripleContent ⟨1, y, z⟩ = 1 := by
  apply Polynomial.isPrimitive_iff_content_eq_one.mp
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hdiv : r ∣ (triplePolynomial ⟨1, y, z⟩).coeff 0 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 0
  simp only [triplePolynomial_coeff_zero] at hdiv
  exact isUnit_iff_dvd_one.mpr hdiv

theorem tripleContent_eq_one_of_z_one (x y : ℤ) :
    tripleContent ⟨x, y, 1⟩ = 1 := by
  apply Polynomial.isPrimitive_iff_content_eq_one.mp
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hdiv : r ∣ (triplePolynomial ⟨x, y, 1⟩).coeff 2 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 2
  simp only [triplePolynomial_coeff_two] at hdiv
  exact isUnit_iff_dvd_one.mpr hdiv

theorem tripleContent_eq_one_of_z_neg_one (x y : ℤ) :
    tripleContent ⟨x, y, -1⟩ = 1 := by
  apply Polynomial.isPrimitive_iff_content_eq_one.mp
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hdiv : r ∣ (triplePolynomial ⟨x, y, -1⟩).coeff 2 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 2
  simp only [triplePolynomial_coeff_two] at hdiv
  exact isUnit_of_dvd_unit hdiv (by norm_num)

@[simp] theorem primitiveDirection_x_one (y z : ℤ) :
    primitiveDirection ⟨1, y, z⟩ = ⟨1, y, z⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_x_one y z
  · exact Or.inl (by norm_num)

theorem primitiveDirection_z_one_of_x_pos (x y : ℤ) (hx : 0 < x) :
    primitiveDirection ⟨x, y, 1⟩ = ⟨x, y, 1⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_z_one x y
  · exact Or.inl hx

theorem primitiveDirection_z_neg_one_of_x_pos (x y : ℤ) (hx : 0 < x) :
    primitiveDirection ⟨x, y, -1⟩ = ⟨x, y, -1⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_z_neg_one x y
  · exact Or.inl hx

theorem directionKey_two_vsmul (d : Triple) (hd : d ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul 2 d) = directionKey d := by
  rw [directionKey_eq_iff, primitiveDirection_two_vsmul hd]

theorem directionKey_neg_two_vsmul (d : Triple) (hd : d ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul (-2) d) = directionKey d := by
  have hvec : vsmul (-2) d = negTriple (vsmul 2 d) := by
    ext <;> simp [vsmul, negTriple]
  rw [hvec, directionKey_negTriple]
  · exact directionKey_two_vsmul d hd
  · intro hzero
    apply hd
    apply Triple.ext <;>
      simp [vsmul] at hzero ⊢ <;>
      omega

theorem primitiveDirection_1_neg1_neg1 :
    primitiveDirection ⟨1, -1, -1⟩ = ⟨1, -1, -1⟩ := by
  apply primitiveDirection_eq_self_of_content_one_of_oriented
  · exact tripleContent_eq_one_of_x_one (-1) (-1)
  · norm_num [FirstNonzeroPositive]

theorem directionKey_two_1_neg1_neg1 :
    directionKey (vsmul 2 ⟨1, -1, -1⟩) = (⟨5, 1, -1, -1⟩ : DirectionKey) := by
  have hprim : primitiveDirection (vsmul 2 ⟨1, -1, -1⟩) = ⟨1, -1, -1⟩ := by
    rw [primitiveDirection_two_vsmul (by norm_num), primitiveDirection_1_neg1_neg1]
  simp [directionKey, hprim, qForm]

theorem signed_orbit_edge_key :
    representativeEdgeKey s1 t1 = (⟨5, 1, -1, -1⟩ : DirectionKey) := by
  change min (directionKey ⟨-6, -8, -2⟩) (directionKey ⟨2, -2, -2⟩) =
    (⟨5, 1, -1, -1⟩ : DirectionKey)
  rw [show (⟨-6, -8, -2⟩ : Triple) = vsmul (-2) ⟨3, 4, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, -2, -2⟩ : Triple) = vsmul 2 ⟨1, -1, -1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [directionKey, primitiveDirection_z_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem signed_orbit_edge_prefers_negative_target :
    preferredTarget s1 t1 = negAResidual t1 := by
  have hlt : directionKey (minusVector s1 t1) < directionKey (plusVector s1 t1) := by
    change directionKey ⟨2, -2, -2⟩ < directionKey ⟨-6, -8, -2⟩
    rw [show (⟨2, -2, -2⟩ : Triple) = vsmul 2 ⟨1, -1, -1⟩ by rfl,
      directionKey_two_vsmul _ (by norm_num),
      show (⟨-6, -8, -2⟩ : Triple) = vsmul (-2) ⟨3, 4, 1⟩ by rfl,
      directionKey_neg_two_vsmul _ (by norm_num)]
    simp [directionKey, primitiveDirection_z_one_of_x_pos,
      primitiveDirection_x_one, qForm, DirectionKey.lt_iff_blt, DirectionKey.blt]
  simp [preferredTarget, not_lt_of_ge hlt.le]

def key41 (h x y z : ℤ) : DirectionKey := ⟨h, x, y, z⟩

theorem edgeKey_s1_t2 : representativeEdgeKey s1 t2 = key41 20 1 (-4) (-1) := by
  change min (directionKey ⟨-6, -2, -2⟩) (directionKey ⟨2, -8, -2⟩) = _
  rw [show (⟨-6, -2, -2⟩ : Triple) = vsmul (-2) ⟨3, 1, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, -8, -2⟩ : Triple) = vsmul 2 ⟨1, -4, -1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s1_t3 : representativeEdgeKey s1 t3 = key41 5 1 1 (-1) := by
  change min (directionKey ⟨-2, -8, -6⟩) (directionKey ⟨-2, -2, 2⟩) = _
  rw [show (⟨-2, -8, -6⟩ : Triple) = vsmul (-2) ⟨1, 4, 3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, -2, 2⟩ : Triple) = vsmul (-2) ⟨1, 1, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s1_t4 : representativeEdgeKey s1 t4 = key41 20 1 4 (-1) := by
  change min (directionKey ⟨-2, -8, 2⟩) (directionKey ⟨-2, -2, -6⟩) = _
  rw [show (⟨-2, -8, 2⟩ : Triple) = vsmul (-2) ⟨1, 4, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, -2, -6⟩ : Triple) = vsmul (-2) ⟨1, 1, 3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s2_t1 : representativeEdgeKey s2 t1 = key41 5 1 (-1) 1 := by
  change min (directionKey ⟨-6, -8, 2⟩) (directionKey ⟨2, -2, 2⟩) = _
  rw [show (⟨-6, -8, 2⟩ : Triple) = vsmul (-2) ⟨3, 4, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, -2, 2⟩ : Triple) = vsmul 2 ⟨1, -1, 1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_neg_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s2_t2 : representativeEdgeKey s2 t2 = key41 20 1 (-4) 1 := by
  change min (directionKey ⟨-6, -2, 2⟩) (directionKey ⟨2, -8, 2⟩) = _
  rw [show (⟨-6, -2, 2⟩ : Triple) = vsmul (-2) ⟨3, 1, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, -8, 2⟩ : Triple) = vsmul 2 ⟨1, -4, 1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_neg_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s2_t3 : representativeEdgeKey s2 t3 = key41 20 1 4 1 := by
  change min (directionKey ⟨-2, -8, -2⟩) (directionKey ⟨-2, -2, 6⟩) = _
  rw [show (⟨-2, -8, -2⟩ : Triple) = vsmul (-2) ⟨1, 4, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, -2, 6⟩ : Triple) = vsmul (-2) ⟨1, 1, -3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s2_t4 : representativeEdgeKey s2 t4 = key41 5 1 1 1 := by
  change min (directionKey ⟨-2, -8, 6⟩) (directionKey ⟨-2, -2, -2⟩) = _
  rw [show (⟨-2, -8, 6⟩ : Triple) = vsmul (-2) ⟨1, 4, -3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, -2, -2⟩ : Triple) = vsmul (-2) ⟨1, 1, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s3_t1 : representativeEdgeKey s3 t1 = key41 20 1 4 (-1) := by
  change min (directionKey ⟨-6, 2, -2⟩) (directionKey ⟨2, 8, -2⟩) = _
  rw [show (⟨-6, 2, -2⟩ : Triple) = vsmul (-2) ⟨3, -1, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, 8, -2⟩ : Triple) = vsmul 2 ⟨1, 4, -1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s3_t2 : representativeEdgeKey s3 t2 = key41 5 1 1 (-1) := by
  change min (directionKey ⟨-6, 8, -2⟩) (directionKey ⟨2, 2, -2⟩) = _
  rw [show (⟨-6, 8, -2⟩ : Triple) = vsmul (-2) ⟨3, -4, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, 2, -2⟩ : Triple) = vsmul 2 ⟨1, 1, -1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s3_t3 : representativeEdgeKey s3 t3 = key41 20 1 (-4) (-1) := by
  change min (directionKey ⟨-2, 2, -6⟩) (directionKey ⟨-2, 8, 2⟩) = _
  rw [show (⟨-2, 2, -6⟩ : Triple) = vsmul (-2) ⟨1, -1, 3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, 8, 2⟩ : Triple) = vsmul (-2) ⟨1, -4, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s3_t4 : representativeEdgeKey s3 t4 = key41 5 1 (-1) (-1) := by
  change min (directionKey ⟨-2, 2, 2⟩) (directionKey ⟨-2, 8, -6⟩) = _
  rw [show (⟨-2, 2, 2⟩ : Triple) = vsmul (-2) ⟨1, -1, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, 8, -6⟩ : Triple) = vsmul (-2) ⟨1, -4, 3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s4_t1 : representativeEdgeKey s4 t1 = key41 20 1 4 1 := by
  change min (directionKey ⟨-6, 2, 2⟩) (directionKey ⟨2, 8, 2⟩) = _
  rw [show (⟨-6, 2, 2⟩ : Triple) = vsmul (-2) ⟨3, -1, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, 8, 2⟩ : Triple) = vsmul 2 ⟨1, 4, 1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_neg_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s4_t2 : representativeEdgeKey s4 t2 = key41 5 1 1 1 := by
  change min (directionKey ⟨-6, 8, 2⟩) (directionKey ⟨2, 2, 2⟩) = _
  rw [show (⟨-6, 8, 2⟩ : Triple) = vsmul (-2) ⟨3, -4, -1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨2, 2, 2⟩ : Triple) = vsmul 2 ⟨1, 1, 1⟩ by rfl,
    directionKey_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_z_neg_one_of_x_pos,
    primitiveDirection_x_one, qForm, DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s4_t3 : representativeEdgeKey s4 t3 = key41 5 1 (-1) 1 := by
  change min (directionKey ⟨-2, 2, -2⟩) (directionKey ⟨-2, 8, 6⟩) = _
  rw [show (⟨-2, 2, -2⟩ : Triple) = vsmul (-2) ⟨1, -1, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, 8, 6⟩ : Triple) = vsmul (-2) ⟨1, -4, -3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem edgeKey_s4_t4 : representativeEdgeKey s4 t4 = key41 20 1 (-4) 1 := by
  change min (directionKey ⟨-2, 2, 6⟩) (directionKey ⟨-2, 8, -2⟩) = _
  rw [show (⟨-2, 2, 6⟩ : Triple) = vsmul (-2) ⟨1, -1, -3⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num),
    show (⟨-2, 8, -2⟩ : Triple) = vsmul (-2) ⟨1, -4, 1⟩ by rfl,
    directionKey_neg_two_vsmul _ (by norm_num)]
  simp [key41, directionKey, primitiveDirection_x_one, qForm,
    DirectionKey.le_iff_ble, DirectionKey.ble, DirectionKey.blt]

theorem residual_key_table :
    representativeEdgeKey s1 t1 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s1 t3 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s1 t2 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s1 t4 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s2 t1 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s2 t4 = key41 5 1 1 1 ∧
      representativeEdgeKey s2 t2 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s2 t3 = key41 20 1 4 1 ∧
      representativeEdgeKey s3 t4 = key41 5 1 (-1) (-1) ∧
      representativeEdgeKey s3 t2 = key41 5 1 1 (-1) ∧
      representativeEdgeKey s3 t3 = key41 20 1 (-4) (-1) ∧
      representativeEdgeKey s3 t1 = key41 20 1 4 (-1) ∧
      representativeEdgeKey s4 t3 = key41 5 1 (-1) 1 ∧
      representativeEdgeKey s4 t2 = key41 5 1 1 1 ∧
      representativeEdgeKey s4 t4 = key41 20 1 (-4) 1 ∧
      representativeEdgeKey s4 t1 = key41 20 1 4 1 := by
  exact ⟨signed_orbit_edge_key, edgeKey_s1_t3, edgeKey_s1_t2, edgeKey_s1_t4,
    edgeKey_s2_t1, edgeKey_s2_t4, edgeKey_s2_t2, edgeKey_s2_t3,
    edgeKey_s3_t4, edgeKey_s3_t2, edgeKey_s3_t3, edgeKey_s3_t1,
    edgeKey_s4_t3, edgeKey_s4_t2, edgeKey_s4_t4, edgeKey_s4_t1⟩

theorem equal_key_edges_are_distinct :
    representativeEdgeKey s1 t1 = representativeEdgeKey s3 t4 ∧
      s1 ≠ s3 ∧ t1 ≠ t4 := by
  constructor
  · rw [signed_orbit_edge_key, edgeKey_s3_t4]
    rfl
  · constructor <;> intro h
    · have := congrArg (fun s : BResidual 41 => s.1.1.y) h
      norm_num [s1, s3] at this
    · have := congrArg (fun t : AResidual 41 => t.1.1.z) h
      norm_num [t1, t4] at this

end Examples41
end TunnellMap

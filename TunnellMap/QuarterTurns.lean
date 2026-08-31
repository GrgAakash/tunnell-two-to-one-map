import TunnellMap.Basic

/-!
# The direct quarter-turn layer

This file formalizes Theorem 3.2 of the paper in the original Tunnell
coordinates.  Divisibility conditions carry their quotient as data.  The
quotient is unique, so these structures are equivalent to the corresponding
congruence-defined subsets, while their maps avoid partial integer division.
-/

namespace TunnellMap

section Parity

theorem odd_y_of_bOdd {n : ℤ} (hn : Odd n) (p : BOddRep n) : Odd p.1.y := by
  rcases Int.even_or_odd p.1.y with hy | hy
  · rcases hy with ⟨ky, hky⟩
    have hform := p.2.1
    change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 = n at hform
    have heven : Even n := by
      refine ⟨p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2, ?_⟩
      calc
        n = 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 := hform.symm
        _ = (p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2) +
            (p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2) := by rw [hky]; ring
    exfalso
    exact (Int.not_even_iff_odd.mpr hn) heven
  · exact hy

theorem odd_y_of_aRep {n : ℤ} (hn : Odd n) (p : ARep n) : Odd p.1.y := by
  rcases Int.even_or_odd p.1.y with hy | hy
  · rcases hy with ⟨ky, hky⟩
    have hform := p.2
    change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at hform
    have heven : Even n := by
      refine ⟨p.1.x ^ 2 + 2 * ky ^ 2 + 16 * p.1.z ^ 2, ?_⟩
      calc
        n = 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 := hform.symm
        _ = (p.1.x ^ 2 + 2 * ky ^ 2 + 16 * p.1.z ^ 2) +
            (p.1.x ^ 2 + 2 * ky ^ 2 + 16 * p.1.z ^ 2) := by rw [hky]; ring
    exfalso
    exact (Int.not_even_iff_odd.mpr hn) heven
  · exact hy

end Parity

/-! ## The three source domains and target images -/

structure DirectDomain1 (n : ℤ) where
  rep : BOddRep n
  quotient : ℤ
  equation : rep.1.x + 2 * rep.1.z + rep.1.y = 8 * quotient

structure DirectImage1 (n : ℤ) where
  rep : ARep n
  quotient : ℤ
  equation : rep.1.x + 4 * rep.1.z - rep.1.y = 4 * quotient
  quotient_odd : Odd quotient

structure DirectDomain2 (n : ℤ) where
  rep : BOddRep n
  quotient : ℤ
  equation : rep.1.y - rep.1.x + 2 * rep.1.z = 8 * quotient

structure DirectImage2 (n : ℤ) where
  rep : ARep n
  quotient : ℤ
  equation : rep.1.x - 4 * rep.1.z + rep.1.y = 4 * quotient
  quotient_odd : Odd quotient

structure DirectDomain3 (n : ℤ) where
  rep : BOddRep n
  quotient : ℤ
  equation : rep.1.x = 4 * quotient

structure DirectImage3 (n : ℤ) where
  rep : ARep n
  quotient : ℤ
  equation : rep.1.x = 2 * quotient
  quotient_odd : Odd quotient

@[ext] theorem DirectDomain1.ext {n : ℤ} {p q : DirectDomain1 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

@[ext] theorem DirectImage1.ext {n : ℤ} {p q : DirectImage1 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

@[ext] theorem DirectDomain2.ext {n : ℤ} {p q : DirectDomain2 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

@[ext] theorem DirectImage2.ext {n : ℤ} {p q : DirectImage2 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

@[ext] theorem DirectDomain3.ext {n : ℤ} {p q : DirectDomain3 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

@[ext] theorem DirectImage3.ext {n : ℤ} {p q : DirectImage3 n}
    (hrep : p.rep = q.rep) (hquotient : p.quotient = q.quotient) : p = q := by
  cases p
  cases q
  cases hrep
  cases hquotient
  rfl

theorem DirectDomain1.quotient_unique {n : ℤ} (p : DirectDomain1 n)
    {q : ℤ} (hq : p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y = 8 * q) :
    q = p.quotient := by
  nlinarith [p.equation]

theorem DirectDomain2.quotient_unique {n : ℤ} (p : DirectDomain2 n)
    {q : ℤ} (hq : p.rep.1.y - p.rep.1.x + 2 * p.rep.1.z = 8 * q) :
    q = p.quotient := by
  nlinarith [p.equation]

theorem DirectDomain3.quotient_unique {n : ℤ} (p : DirectDomain3 n)
    {q : ℤ} (hq : p.rep.1.x = 4 * q) : q = p.quotient := by
  nlinarith [p.equation]

theorem DirectImage1.quotient_unique {n : ℤ} (p : DirectImage1 n)
    {q : ℤ} (hq : p.rep.1.x + 4 * p.rep.1.z - p.rep.1.y = 4 * q) :
    q = p.quotient := by
  nlinarith [p.equation]

theorem DirectImage2.quotient_unique {n : ℤ} (p : DirectImage2 n)
    {q : ℤ} (hq : p.rep.1.x - 4 * p.rep.1.z + p.rep.1.y = 4 * q) :
    q = p.quotient := by
  nlinarith [p.equation]

theorem DirectImage3.quotient_unique {n : ℤ} (p : DirectImage3 n)
    {q : ℤ} (hq : p.rep.1.x = 2 * q) : q = p.quotient := by
  nlinarith [p.equation]

/-! ## First quarter-turn -/

def branch1To {n : ℤ} (p : DirectDomain1 n) : DirectImage1 n := by
  let x := p.rep.1.x
  let y := p.rep.1.y
  let z := p.rep.1.z
  let q := p.quotient
  refine ⟨⟨⟨4 * q - y, x - 2 * z, q⟩, ?_⟩, z, ?_, p.rep.2.2⟩
  · have hform := p.rep.2.1
    have heq := p.equation
    change 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = n at hform
    change 2 * (4 * q - y) ^ 2 + (x - 2 * z) ^ 2 + 32 * q ^ 2 = n
    simp only [x, y, z, q] at hform heq ⊢
    have hy : p.rep.1.y = 8 * p.quotient - p.rep.1.x - 2 * p.rep.1.z := by
      linarith [heq]
    rw [hy] at hform ⊢
    ring_nf at hform ⊢
    exact hform
  · have heq := p.equation
    dsimp [x, y, z, q] at heq ⊢
    nlinarith [heq]

def branch1From {n : ℤ} (p : DirectImage1 n) : DirectDomain1 n := by
  let u := p.rep.1.x
  let v := p.rep.1.y
  let w := p.rep.1.z
  let r := p.quotient
  refine ⟨⟨⟨u + 4 * w - 2 * r, -u + 4 * w, r⟩, ?_, p.quotient_odd⟩,
    w, ?_⟩
  · have hform := p.rep.2
    have heq := p.equation
    change 2 * u ^ 2 + v ^ 2 + 32 * w ^ 2 = n at hform
    change 2 * (u + 4 * w - 2 * r) ^ 2 + (-u + 4 * w) ^ 2 + 8 * r ^ 2 = n
    simp only [u, v, w, r] at hform heq ⊢
    have hv : p.rep.1.y = p.rep.1.x + 4 * p.rep.1.z - 4 * p.quotient := by
      linarith [heq]
    rw [hv] at hform
    ring_nf at hform ⊢
    exact hform
  · have heq := p.equation
    dsimp [u, v, w, r] at heq ⊢
    nlinarith [heq]

def branch1Equiv (n : ℤ) : DirectDomain1 n ≃ DirectImage1 n where
  toFun := branch1To
  invFun := branch1From
  left_inv := by
    intro p
    apply DirectDomain1.ext
    · apply Subtype.ext
      apply Triple.ext
      · change (4 * p.quotient - p.rep.1.y) + 4 * p.quotient -
          2 * p.rep.1.z = p.rep.1.x
        nlinarith [p.equation]
      · change -(4 * p.quotient - p.rep.1.y) + 4 * p.quotient = p.rep.1.y
        ring
      · rfl
    · rfl
  right_inv := by
    intro p
    apply DirectImage1.ext
    · apply Subtype.ext
      apply Triple.ext
      · change 4 * p.rep.1.z - (-p.rep.1.x + 4 * p.rep.1.z) = p.rep.1.x
        ring
      · change p.rep.1.x + 4 * p.rep.1.z - 2 * p.quotient -
          2 * p.quotient = p.rep.1.y
        nlinarith [p.equation]
      · rfl
    · rfl

theorem branch1_paper_formula {n : ℤ} (p : DirectDomain1 n) :
    2 * (branch1Equiv n p).rep.1.x =
        p.rep.1.x + 2 * p.rep.1.z - p.rep.1.y ∧
      (branch1Equiv n p).rep.1.y = p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch1Equiv n p).rep.1.z =
        p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y := by
  dsimp [branch1Equiv, branch1To]
  constructor
  · nlinarith [p.equation]
  · constructor
    · rfl
    · nlinarith [p.equation]

/-! ## Second quarter-turn -/

def branch2To {n : ℤ} (p : DirectDomain2 n) : DirectImage2 n := by
  let x := p.rep.1.x
  let y := p.rep.1.y
  let z := p.rep.1.z
  let q := p.quotient
  refine ⟨⟨⟨x - 2 * z + 4 * q, -x - 2 * z, q⟩, ?_⟩, -z, ?_,
    p.rep.2.2.neg⟩
  · have hform := p.rep.2.1
    have heq := p.equation
    change 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = n at hform
    change 2 * (x - 2 * z + 4 * q) ^ 2 + (-x - 2 * z) ^ 2 + 32 * q ^ 2 = n
    simp only [x, y, z, q] at hform heq ⊢
    have hy : p.rep.1.y = 8 * p.quotient + p.rep.1.x - 2 * p.rep.1.z := by
      linarith [heq]
    rw [hy] at hform
    ring_nf at hform ⊢
    exact hform
  · have heq := p.equation
    dsimp [x, y, z, q] at heq ⊢
    nlinarith [heq]

def branch2From {n : ℤ} (p : DirectImage2 n) : DirectDomain2 n := by
  let u := p.rep.1.x
  let v := p.rep.1.y
  let w := p.rep.1.z
  let r := p.quotient
  refine ⟨⟨⟨u - 4 * w - 2 * r, u + 4 * w, -r⟩, ?_, p.quotient_odd.neg⟩,
    w, ?_⟩
  · have hform := p.rep.2
    have heq := p.equation
    change 2 * u ^ 2 + v ^ 2 + 32 * w ^ 2 = n at hform
    change 2 * (u - 4 * w - 2 * r) ^ 2 + (u + 4 * w) ^ 2 + 8 * (-r) ^ 2 = n
    simp only [u, v, w, r] at hform heq ⊢
    have hv : p.rep.1.y = 4 * p.quotient - p.rep.1.x + 4 * p.rep.1.z := by
      linarith [heq]
    rw [hv] at hform
    ring_nf at hform ⊢
    exact hform
  · have heq := p.equation
    dsimp [u, v, w, r] at heq ⊢
    nlinarith [heq]

def branch2Equiv (n : ℤ) : DirectDomain2 n ≃ DirectImage2 n where
  toFun := branch2To
  invFun := branch2From
  left_inv := by
    intro p
    apply DirectDomain2.ext
    · apply Subtype.ext
      apply Triple.ext
      · change p.rep.1.x - 2 * p.rep.1.z + 4 * p.quotient -
          4 * p.quotient - 2 * (-p.rep.1.z) = p.rep.1.x
        ring
      · change p.rep.1.x - 2 * p.rep.1.z + 4 * p.quotient +
          4 * p.quotient = p.rep.1.y
        nlinarith [p.equation]
      · change -(-p.rep.1.z) = p.rep.1.z
        ring
    · rfl
  right_inv := by
    intro p
    apply DirectImage2.ext
    · apply Subtype.ext
      apply Triple.ext
      · change p.rep.1.x - 4 * p.rep.1.z - 2 * p.quotient -
          2 * (-p.quotient) + 4 * p.rep.1.z = p.rep.1.x
        ring
      · change -(p.rep.1.x - 4 * p.rep.1.z - 2 * p.quotient) -
          2 * (-p.quotient) = p.rep.1.y
        nlinarith [p.equation]
      · rfl
    · change -(-p.quotient) = p.quotient
      ring

theorem branch2_paper_formula {n : ℤ} (p : DirectDomain2 n) :
    2 * (branch2Equiv n p).rep.1.x =
        p.rep.1.x - 2 * p.rep.1.z + p.rep.1.y ∧
      (branch2Equiv n p).rep.1.y = -p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch2Equiv n p).rep.1.z =
        p.rep.1.y - p.rep.1.x + 2 * p.rep.1.z := by
  dsimp [branch2Equiv, branch2To]
  constructor
  · nlinarith [p.equation]
  · constructor
    · rfl
    · nlinarith [p.equation]

/-! ## Third quarter-turn -/

def branch3To {n : ℤ} (p : DirectDomain3 n) : DirectImage3 n := by
  let y := p.rep.1.y
  let z := p.rep.1.z
  let q := p.quotient
  refine ⟨⟨⟨2 * z, y, -q⟩, ?_⟩, z, rfl, p.rep.2.2⟩
  have hform := p.rep.2.1
  have heq := p.equation
  change 2 * p.rep.1.x ^ 2 + y ^ 2 + 8 * z ^ 2 = n at hform
  change 2 * (2 * z) ^ 2 + y ^ 2 + 32 * (-q) ^ 2 = n
  simp only [y, z, q] at hform heq ⊢
  rw [heq] at hform
  ring_nf at hform ⊢
  exact hform

def branch3From {n : ℤ} (p : DirectImage3 n) : DirectDomain3 n := by
  let v := p.rep.1.y
  let w := p.rep.1.z
  let r := p.quotient
  refine ⟨⟨⟨-4 * w, v, r⟩, ?_, p.quotient_odd⟩, -w, by ring⟩
  have hform := p.rep.2
  have heq := p.equation
  change 2 * p.rep.1.x ^ 2 + v ^ 2 + 32 * w ^ 2 = n at hform
  change 2 * (-4 * w) ^ 2 + v ^ 2 + 8 * r ^ 2 = n
  simp only [v, w, r] at hform heq ⊢
  rw [heq] at hform
  ring_nf at hform ⊢
  exact hform

def branch3Equiv (n : ℤ) : DirectDomain3 n ≃ DirectImage3 n where
  toFun := branch3To
  invFun := branch3From
  left_inv := by
    intro p
    apply DirectDomain3.ext
    · apply Subtype.ext
      apply Triple.ext
      · change -4 * (-p.quotient) = p.rep.1.x
        nlinarith [p.equation]
      · rfl
      · rfl
    · change -(-p.quotient) = p.quotient
      ring
  right_inv := by
    intro p
    apply DirectImage3.ext
    · apply Subtype.ext
      apply Triple.ext
      · change 2 * p.quotient = p.rep.1.x
        nlinarith [p.equation]
      · rfl
      · change -(-p.rep.1.z) = p.rep.1.z
        ring
    · rfl

theorem branch3_paper_formula {n : ℤ} (p : DirectDomain3 n) :
    (branch3Equiv n p).rep.1 =
      ⟨2 * p.rep.1.z, p.rep.1.y, -(p.rep.1.x / 4)⟩ := by
  apply Triple.ext <;> dsimp [branch3Equiv, branch3To]
  have hdiv : p.rep.1.x / 4 = p.quotient := by
    rw [p.equation]
    norm_num
  rw [hdiv]

/-! ## Disjointness and the combined direct partial bijection -/

def DirectPredicate1 {n : ℤ} (p : BOddRep n) : Prop :=
  ∃ q : ℤ, p.1.x + 2 * p.1.z + p.1.y = 8 * q

def DirectPredicate2 {n : ℤ} (p : BOddRep n) : Prop :=
  ∃ q : ℤ, p.1.y - p.1.x + 2 * p.1.z = 8 * q

def DirectPredicate3 {n : ℤ} (p : BOddRep n) : Prop :=
  ∃ q : ℤ, p.1.x = 4 * q

theorem direct_domains_pairwise_disjoint {n : ℤ} (hn : Odd n) (p : BOddRep n) :
    ¬ (DirectPredicate1 p ∧ DirectPredicate2 p) ∧
      ¬ (DirectPredicate1 p ∧ DirectPredicate3 p) ∧
      ¬ (DirectPredicate2 p ∧ DirectPredicate3 p) := by
  have hy := odd_y_of_bOdd hn p
  rcases hy with ⟨ky, hky⟩
  rcases p.2.2 with ⟨kz, hkz⟩
  constructor
  · rintro ⟨⟨q₁, h₁⟩, ⟨q₂, h₂⟩⟩
    omega
  · constructor
    · rintro ⟨⟨q₁, h₁⟩, ⟨q₃, h₃⟩⟩
      omega
    · rintro ⟨⟨q₂, h₂⟩, ⟨q₃, h₃⟩⟩
      omega

def ImagePredicate1 {n : ℤ} (p : ARep n) : Prop :=
  ∃ q : ℤ, Odd q ∧ p.1.x + 4 * p.1.z - p.1.y = 4 * q

def ImagePredicate2 {n : ℤ} (p : ARep n) : Prop :=
  ∃ q : ℤ, Odd q ∧ p.1.x - 4 * p.1.z + p.1.y = 4 * q

def ImagePredicate3 {n : ℤ} (p : ARep n) : Prop :=
  ∃ q : ℤ, Odd q ∧ p.1.x = 2 * q

theorem direct_images_pairwise_disjoint {n : ℤ} (hn : Odd n) (p : ARep n) :
    ¬ (ImagePredicate1 p ∧ ImagePredicate2 p) ∧
      ¬ (ImagePredicate1 p ∧ ImagePredicate3 p) ∧
      ¬ (ImagePredicate2 p ∧ ImagePredicate3 p) := by
  have hy := odd_y_of_aRep hn p
  rcases hy with ⟨ky, hky⟩
  constructor
  · rintro ⟨⟨q₁, hq₁, h₁⟩, ⟨q₂, hq₂, h₂⟩⟩
    rcases hq₁ with ⟨k₁, hk₁⟩
    rcases hq₂ with ⟨k₂, hk₂⟩
    omega
  · constructor
    · rintro ⟨⟨q₁, hq₁, h₁⟩, ⟨q₃, hq₃, h₃⟩⟩
      rcases hq₁ with ⟨k₁, hk₁⟩
      rcases hq₃ with ⟨k₃, hk₃⟩
      omega
    · rintro ⟨⟨q₂, hq₂, h₂⟩, ⟨q₃, hq₃, h₃⟩⟩
      rcases hq₂ with ⟨k₂, hk₂⟩
      rcases hq₃ with ⟨k₃, hk₃⟩
      omega

abbrev DirectDomain (n : ℤ) :=
  DirectDomain1 n ⊕ (DirectDomain2 n ⊕ DirectDomain3 n)

abbrev DirectImage (n : ℤ) :=
  DirectImage1 n ⊕ (DirectImage2 n ⊕ DirectImage3 n)

/-- The disjoint union of the three direct quarter-turn branches. -/
def directEquiv (n : ℤ) : DirectDomain n ≃ DirectImage n :=
  Equiv.sumCongr (branch1Equiv n)
    (Equiv.sumCongr (branch2Equiv n) (branch3Equiv n))

end TunnellMap

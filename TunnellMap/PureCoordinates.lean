import TunnellMap.Basic

/-!
# Sum-of-three-squares coordinates

This file formalizes the two coordinate equivalences in Lemma 2.1 of the
manuscript. The predicates below state the manuscript's congruence and parity
conditions directly.
-/

namespace TunnellMap

def pureNorm (p : Triple) : ℤ := p.x ^ 2 + p.y ^ 2 + p.z ^ 2

def LOneRep (n : ℤ) :=
  {p : Triple //
    pureNorm p = n ∧ (4 : ℤ) ∣ p.x - p.y ∧ Odd ((p.x - p.y) / 4)}

def LZeroRep (n : ℤ) :=
  {p : Triple //
    pureNorm p = n ∧ (4 : ℤ) ∣ p.x - p.y ∧ Even ((p.x - p.y) / 4)}

/-- The paper's map `e_B(x,y,z) = (x+2z,x-2z,y)`. -/
def eB {n : ℤ} (p : BOddRep n) : LOneRep n := by
  refine ⟨⟨p.1.x + 2 * p.1.z, p.1.x - 2 * p.1.z, p.1.y⟩, ?_⟩
  constructor
  · have h := p.2.1
    simp only [pureNorm, bForm] at h ⊢
    nlinarith
  · constructor
    · use p.1.z
      ring
    · convert p.2.2 using 1
      dsimp
      rw [show (p.1.x + 2 * p.1.z) - (p.1.x - 2 * p.1.z) =
          4 * p.1.z by ring]
      exact Int.mul_ediv_cancel_left p.1.z (by norm_num)

/-- The displayed inverse of `e_B`. -/
def eBInv {n : ℤ} (p : LOneRep n) : BOddRep n := by
  let x := (p.1.x + p.1.y) / 2
  let z := (p.1.x - p.1.y) / 4
  refine ⟨⟨x, p.1.z, z⟩, ?_, p.2.2.2⟩
  obtain ⟨k, hk⟩ := p.2.2.1
  have hz : z = k := by
    dsimp [z]
    omega
  have hx : x = p.1.x - 2 * k := by
    dsimp [x]
    omega
  have hy : p.1.y = p.1.x - 4 * k := by omega
  have hnorm := p.2.1
  simp only [pureNorm] at hnorm
  rw [hy] at hnorm
  simp only [bForm]
  rw [hx, hz]
  nlinarith

def eBEquiv (n : ℤ) : BOddRep n ≃ LOneRep n where
  toFun := eB
  invFun := eBInv
  left_inv := by
    intro p
    apply Subtype.ext
    apply Triple.ext <;> dsimp [eBInv, eB] <;> omega
  right_inv := by
    intro p
    apply Subtype.ext
    obtain ⟨k, hk⟩ := p.2.2.1
    have hz : (p.1.x - p.1.y) / 4 = k := by omega
    have hx : (p.1.x + p.1.y) / 2 = p.1.x - 2 * k := by omega
    apply Triple.ext
    · dsimp [eBInv, eB]
      rw [hz, hx]
      omega
    · dsimp [eBInv, eB]
      rw [hz, hx]
      omega
    · rfl

/-- The paper's map `e_A(u,v,w) = (u+4w,u-4w,v)`. -/
def eA {n : ℤ} (p : ARep n) : LZeroRep n := by
  refine ⟨⟨p.1.x + 4 * p.1.z, p.1.x - 4 * p.1.z, p.1.y⟩, ?_⟩
  constructor
  · have h := p.2
    simp only [pureNorm, aForm] at h ⊢
    nlinarith
  · constructor
    · use 2 * p.1.z
      ring
    · use p.1.z
      dsimp
      rw [show (p.1.x + 4 * p.1.z) - (p.1.x - 4 * p.1.z) =
          4 * (p.1.z + p.1.z) by ring]
      exact Int.mul_ediv_cancel_left (p.1.z + p.1.z) (by norm_num)

/-- The displayed inverse of `e_A`. -/
def eAInv {n : ℤ} (p : LZeroRep n) : ARep n := by
  let x := (p.1.x + p.1.y) / 2
  let w := (p.1.x - p.1.y) / 8
  refine ⟨⟨x, p.1.z, w⟩, ?_⟩
  obtain ⟨q, hq⟩ := p.2.2.1
  obtain ⟨k, hk⟩ := p.2.2.2
  have hqValue : (p.1.x - p.1.y) / 4 = q := by omega
  have hqEven : q = 2 * k := by omega
  have hw : w = k := by
    dsimp [w]
    omega
  have hx : x = p.1.x - 4 * k := by
    dsimp [x]
    omega
  have hy : p.1.y = p.1.x - 8 * k := by omega
  have hnorm := p.2.1
  simp only [pureNorm] at hnorm
  rw [hy] at hnorm
  simp only [aForm]
  rw [hx, hw]
  nlinarith

def eAEquiv (n : ℤ) : ARep n ≃ LZeroRep n where
  toFun := eA
  invFun := eAInv
  left_inv := by
    intro p
    apply Subtype.ext
    apply Triple.ext <;> dsimp [eAInv, eA] <;> omega
  right_inv := by
    intro p
    apply Subtype.ext
    obtain ⟨q, hq⟩ := p.2.2.1
    obtain ⟨k, hk⟩ := p.2.2.2
    have hqValue : (p.1.x - p.1.y) / 4 = q := by omega
    have hqEven : q = 2 * k := by omega
    have hw : (p.1.x - p.1.y) / 8 = k := by omega
    have hx : (p.1.x + p.1.y) / 2 = p.1.x - 4 * k := by omega
    apply Triple.ext
    · dsimp [eAInv, eA]
      rw [hw, hx]
      omega
    · dsimp [eAInv, eA]
      rw [hw, hx]
      omega
    · rfl

end TunnellMap

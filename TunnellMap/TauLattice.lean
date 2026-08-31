import TunnellMap.AffineLattice

/-!
# The index-two lattice of the `tau` embedding

This file proves equation (5.1): the image of `tau` consists exactly of
triples whose first and third coordinates have the same parity, with the
displayed division-by-two inverse.
-/

namespace TunnellMap

def InTauLattice (r : Triple) : Prop := (2 : ℤ) ∣ r.x - r.z

instance inTauLatticeDecidable (r : Triple) : Decidable (InTauLattice r) := by
  unfold InTauLattice
  infer_instance

def tauInv (r : Triple) : Triple :=
  ⟨(r.x + r.z) / 2, r.y, (r.x - r.z) / 2⟩

theorem tau_mem (d : Triple) : InTauLattice (tau d) := by
  refine ⟨d.z, ?_⟩
  simp [InTauLattice, tau]
  ring

@[simp] theorem tauInv_tau (d : Triple) : tauInv (tau d) = d := by
  apply Triple.ext
  · simp only [tauInv, tau]
    rw [show (d.x + d.z + (d.x - d.z)) = 2 * d.x by ring]
    exact Int.mul_ediv_cancel_left d.x (by norm_num)
  · rfl
  · simp only [tauInv, tau]
    rw [show (d.x + d.z - (d.x - d.z)) = 2 * d.z by ring]
    exact Int.mul_ediv_cancel_left d.z (by norm_num)

theorem tau_tauInv {r : Triple} (hr : InTauLattice r) : tau (tauInv r) = r := by
  have hdiff : (2 : ℤ) ∣ r.x - r.z := hr
  have hsum : (2 : ℤ) ∣ r.x + r.z := by
    obtain ⟨k, hk⟩ := hdiff
    refine ⟨k + r.z, ?_⟩
    linarith
  have hdiffDiv : 2 * ((r.x - r.z) / 2) = r.x - r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiff
  have hsumDiv : 2 * ((r.x + r.z) / 2) = r.x + r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hsum
  apply Triple.ext
  · simp only [tau, tauInv]
    omega
  · rfl
  · simp only [tau, tauInv]
    omega

def tauEquiv : Triple ≃ {r : Triple // InTauLattice r} where
  toFun d := ⟨tau d, tau_mem d⟩
  invFun r := tauInv r.1
  left_inv := tauInv_tau
  right_inv := by
    intro r
    apply Subtype.ext
    exact tau_tauInv r.2

theorem tau_injective : Function.Injective tau := by
  intro d e h
  simpa using congrArg tauInv h

end TunnellMap

import TunnellMap.Examples41Residual

/-!
# The `n = 41` affine-lattice and generator examples

This file checks the complete arithmetic reconstruction in the manuscript,
including the short interval, discriminant, roots, and four retained records
in the preference row of `s2`.
-/

namespace TunnellMap
namespace Examples41

open OrderedGenerator

set_option maxRecDepth 10000

def frame41 : OrthogonalFrame (tau (residualSourceLift s2)) where
  e₁ := ⟨1, 0, 0⟩
  e₂ := ⟨0, -4, 5⟩
  z := ⟨0, -1, 1⟩
  cross_eq := by
    norm_num [s2, midpointSource, residualSourceLift, bLift, tau, cross]
  bezout := by
    norm_num [s2, midpointSource, residualSourceLift, bLift, tau, dot]

theorem lattice_frame_example :
    tau (residualSourceLift s2) = ⟨0, -5, -4⟩ ∧
      frame41.e₁ = ⟨1, 0, 0⟩ ∧
      frame41.e₂ = ⟨0, -4, 5⟩ ∧
      frame41.z = ⟨0, -1, 1⟩ ∧
      cross frame41.e₁ frame41.e₂ = tau (residualSourceLift s2) ∧
      dot (tau (residualSourceLift s2)) frame41.z = 1 := by
  norm_num [frame41, s2, midpointSource, residualSourceLift, bLift, tau, cross, dot]

theorem lattice_scalar_data :
    alpha frame41 = 1 ∧
      beta frame41 = 0 ∧
      dot frame41.e₂ frame41.e₂ = 41 ∧
      delta frame41 = 0 ∧
      epsilon frame41 = 9 ∧
      dot frame41.z frame41.z = 2 ∧
      K frame41 = -9 := by
  norm_num [frame41, alpha, beta, delta, epsilon, K, dot]

theorem short_interval_example :
    qForm ⟨1, -4, 1⟩ = 20 ∧
      qBilinear (residualSourceLift s2) ⟨1, -4, 1⟩ = 20 ∧
      M 41 20 1 = 420 ∧
      Int.sqrt 420 = 20 ∧
      bLower 41 frame41 20 1 = -4 ∧
      bUpper 41 frame41 20 1 = -4 ∧
      frame41.halfDiscriminant 20 1 (-4) = 4 := by
  norm_num [qForm, qBilinear, s2, midpointSource, residualSourceLift, bLift,
    M, bLower, bUpper, alpha, beta, delta, epsilon, K, frame41,
    OrthogonalFrame.halfDiscriminant, dot]

theorem short_interval_unique_integer (b : ℤ)
    (hb : bLower 41 frame41 20 1 ≤ b ∧ b ≤ bUpper 41 frame41 20 1) :
    b = -4 := by
  have hlo : bLower 41 frame41 20 1 = -4 := short_interval_example.2.2.2.2.1
  have hhi : bUpper 41 frame41 20 1 = -4 := short_interval_example.2.2.2.2.2.1
  rw [hlo, hhi] at hb
  omega

theorem lattice_roots_example :
    rootValues frame41 20 1 (-4) = ({2, -2} : Finset ℤ) := by
  decide +kernel

def latticeIndex : GeneratorIndex := ⟨20, 1, -4, 2⟩

theorem lattice_reconstruction_example :
    aValue frame41 latticeIndex = 2 ∧
      rValue frame41 latticeIndex = ⟨2, -4, 0⟩ ∧
      dValue frame41 latticeIndex = ⟨1, -4, 1⟩ ∧
      targetValue s2 frame41 latticeIndex = ⟨4, -3, 0⟩ := by
  norm_num [latticeIndex, aValue, rValue, dValue, targetValue, frame41,
    alpha, beta, delta, linComb3, vadd, vsmul, tauInv, s2, midpointSource,
    residualSourceLift, bLift, negTriple, dot, reconstructedTarget]

def rowIndex1 : GeneratorIndex := ⟨5, 1, -1, 2⟩
def rowIndex2 : GeneratorIndex := ⟨5, -1, 1, 2⟩
def rowIndex3 : GeneratorIndex := latticeIndex
def rowIndex4 : GeneratorIndex := ⟨20, -1, 4, 2⟩

theorem generated_row_affine_data :
    (rowIndex1.A, rowIndex1.q, rowIndex1.u, rowIndex1.b) = (5, 1, 2, -1) ∧
      (rowIndex2.A, rowIndex2.q, rowIndex2.u, rowIndex2.b) = (5, -1, 2, 1) ∧
      (rowIndex3.A, rowIndex3.q, rowIndex3.u, rowIndex3.b) = (20, 1, 2, -4) ∧
      (rowIndex4.A, rowIndex4.q, rowIndex4.u, rowIndex4.b) = (20, -1, 2, 4) := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex]

theorem generated_row_directions :
    dValue frame41 rowIndex1 = ⟨1, -1, 1⟩ ∧
      dValue frame41 rowIndex2 = ⟨1, 1, 1⟩ ∧
      dValue frame41 rowIndex3 = ⟨1, -4, 1⟩ ∧
      dValue frame41 rowIndex4 = ⟨1, 4, 1⟩ := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex,
    dValue, rValue, aValue, frame41, alpha, beta, delta, linComb3, vadd,
    vsmul, tauInv, dot]

theorem generated_row_targets :
    targetValue s2 frame41 rowIndex1 = ⟨4, 3, 0⟩ ∧
      targetValue s2 frame41 rowIndex2 = ⟨0, 3, -4⟩ ∧
      targetValue s2 frame41 rowIndex3 = ⟨4, -3, 0⟩ ∧
      targetValue s2 frame41 rowIndex4 = ⟨0, -3, -4⟩ := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex,
    targetValue, dValue, rValue, aValue, frame41, alpha, beta, delta,
    linComb3, vadd, vsmul, tauInv, s2, midpointSource, residualSourceLift,
    bLift, negTriple, dot, reconstructedTarget]

theorem generated_row_key_order :
    representativeEdgeKey s2 t1 < representativeEdgeKey s2 t4 ∧
      representativeEdgeKey s2 t4 < representativeEdgeKey s2 t2 ∧
      representativeEdgeKey s2 t2 < representativeEdgeKey s2 t3 := by
  rw [edgeKey_s2_t1, edgeKey_s2_t4, edgeKey_s2_t2, edgeKey_s2_t3]
  simp [key41, DirectionKey.lt_iff_blt, DirectionKey.blt]

end Examples41
end TunnellMap

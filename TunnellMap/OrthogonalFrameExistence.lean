import TunnellMap.AffineLattice

/-!
# Existence of the oriented orthogonal frame

The manuscript obtains the frame by extended gcd and Smith reduction.  In
dimension three an explicit extended-gcd completion is enough: a Bezout
vector for a primitive normal vector is completed to two kernel vectors whose
cross product is that normal vector.
-/

namespace TunnellMap

/-- The gcd of all three coordinates of an integer triple. -/
def tripleGCD (p : Triple) : ℕ := Int.gcd (Int.gcd p.x p.y : ℤ) p.z

/-- A deterministic Bezout vector assembled from two extended-gcd calls. -/
def tripleBezout (p : Triple) : Triple :=
  let g : ℤ := Int.gcd p.x p.y
  let c := g.gcdA p.z
  ⟨p.x.gcdA p.y * c, p.x.gcdB p.y * c, g.gcdB p.z⟩

theorem dot_tripleBezout_of_gcd_eq_one {p : Triple} (hp : tripleGCD p = 1) :
    dot p (tripleBezout p) = 1 := by
  have hxy := Int.gcd_eq_gcd_ab p.x p.y
  have hall := Int.gcd_eq_gcd_ab (Int.gcd p.x p.y : ℤ) p.z
  calc
    dot p (tripleBezout p) =
        (p.x * p.x.gcdA p.y + p.y * p.x.gcdB p.y) *
            (Int.gcd p.x p.y : ℤ).gcdA p.z +
          p.z * (Int.gcd p.x p.y : ℤ).gcdB p.z := by
            simp [dot, tripleBezout]
            ring
    _ = (Int.gcd p.x p.y : ℤ) * (Int.gcd p.x p.y : ℤ).gcdA p.z +
          p.z * (Int.gcd p.x p.y : ℤ).gcdB p.z := by rw [← hxy]
    _ = (tripleGCD p : ℤ) := hall.symm
    _ = 1 := by exact_mod_cast hp

/-- A squarefree squared norm forces the coordinate gcd to be one. -/
theorem tripleGCD_eq_one_of_squarefree_norm {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) : tripleGCD p = 1 := by
  let g : ℤ := tripleGCD p
  have hgxy : (tripleGCD p : ℤ) ∣ (Int.gcd p.x p.y : ℤ) :=
    Int.gcd_dvd_left (Int.gcd p.x p.y : ℤ) p.z
  have hgx : g ∣ p.x := hgxy.trans (Int.gcd_dvd_left p.x p.y)
  have hgy : g ∣ p.y := hgxy.trans (Int.gcd_dvd_right p.x p.y)
  have hgz : g ∣ p.z := Int.gcd_dvd_right (Int.gcd p.x p.y : ℤ) p.z
  have hgxx : g * g ∣ p.x * p.x := mul_dvd_mul hgx hgx
  have hgyy : g * g ∣ p.y * p.y := mul_dvd_mul hgy hgy
  have hgzz : g * g ∣ p.z * p.z := mul_dvd_mul hgz hgz
  have hgnorm : g * g ∣ dot p p := by
    simpa [dot] using dvd_add (dvd_add hgxx hgyy) hgzz
  have hunit : IsUnit g := hn g (by simpa [hnorm] using hgnorm)
  have hgCases : g = 1 ∨ g = -1 := Int.isUnit_iff.mp hunit
  have hgNonneg : 0 ≤ g := by
    dsimp [g]
    exact Int.natCast_nonneg _
  rcases hgCases with hg | hg
  · have hg' : (tripleGCD p : ℤ) = 1 := by simpa [g] using hg
    exact Int.ofNat_inj.mp (by simpa using hg')
  · omega

/-- Any integral Bezout vector can be completed explicitly to an oriented
orthogonal frame. -/
theorem orthogonalFrame_exists_of_bezout {p z : Triple} (hz : dot p z = 1) :
    Nonempty (OrthogonalFrame p) := by
  by_cases hg0 : Int.gcd p.x p.y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hg0
    have hpz : p.z = 1 ∨ p.z = -1 := by
      apply Int.eq_one_or_neg_one_of_mul_eq_one
      simpa [dot, hx, hy] using hz
    rcases hpz with hpz | hpz
    · refine ⟨OrthogonalFrame.mk ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ z ?_ hz⟩
      apply Triple.ext <;> simp [cross, hx, hy, hpz]
    · refine ⟨OrthogonalFrame.mk ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ z ?_ hz⟩
      apply Triple.ext <;> simp [cross, hx, hy, hpz]
  · let G : ℤ := Int.gcd p.x p.y
    let A : ℤ := p.x.gcdA p.y
    let B : ℤ := p.x.gcdB p.y
    let a : ℤ := p.x / G
    let b : ℤ := p.y / G
    have hGne : G ≠ 0 := by
      intro h
      apply hg0
      dsimp [G] at h
      exact_mod_cast h
    have hxDiv : G * a = p.x := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_left p.x p.y)
    have hyDiv : G * b = p.y := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_right p.x p.y)
    have hBezout : G = p.x * A + p.y * B := Int.gcd_eq_gcd_ab p.x p.y
    have hAB : A * a + B * b = 1 := by
      apply mul_left_cancel₀ hGne
      calc
        G * (A * a + B * b) = (G * a) * A + (G * b) * B := by ring
        _ = p.x * A + p.y * B := by rw [hxDiv, hyDiv]
        _ = G := hBezout.symm
        _ = G * 1 := by ring
    let e₁ : Triple := ⟨-b, a, 0⟩
    let e₂ : Triple := ⟨-A * p.z, -B * p.z, G⟩
    refine ⟨OrthogonalFrame.mk e₁ e₂ z ?_ hz⟩
    apply Triple.ext
    · dsimp [e₁, e₂, cross]
      simpa [mul_comm] using hxDiv
    · dsimp [e₁, e₂, cross]
      simpa [mul_comm] using hyDiv
    · dsimp [e₁, e₂, cross]
      calc
        -b * (-B * p.z) - a * (-A * p.z) = b * B * p.z + a * A * p.z := by ring
        _ = (A * a + B * b) * p.z := by ring
        _ = p.z := by rw [hAB]; ring

/-- Lemma 5.1: a squarefree norm admits an oriented kernel basis and Bezout
vector. -/
theorem orthogonalFrame_exists_of_squarefree_norm {p : Triple} {n : ℤ}
    (hn : Squarefree n) (hnorm : dot p p = n) :
    Nonempty (OrthogonalFrame p) := by
  have hgcd := tripleGCD_eq_one_of_squarefree_norm hn hnorm
  exact orthogonalFrame_exists_of_bezout (dot_tripleBezout_of_gcd_eq_one hgcd)

end TunnellMap

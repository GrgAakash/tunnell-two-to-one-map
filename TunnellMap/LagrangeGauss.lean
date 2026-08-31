import TunnellMap.DeterministicFrame
import TunnellMap.ReducedBasisBound
import TunnellMap.ResidualTargetTest

/-!
# Executable Lagrange-Gauss reduction of the kernel basis

The kernel lattice of a primitive source vector is a rank-two positive
definite integral lattice.  This file implements the Lagrange-Gauss reduction
algorithm on the ordered basis `(e₁, e₂)` of `TunnellMap.OrthogonalFrame`,
with every convention fixed:

* the *first* vector of the pair is the one whose square length is required to
  be the smaller one; the loop swaps as `(u, v) ↦ (v, -u)`, which has
  determinant `+1`, so the cross product — hence the source vector — is
  preserved;
* the reduction quotient is the *nearest integer* to `⟨u,v⟩/⟨u,u⟩`; at an
  exact half-integer tie it rounds *toward zero*, exactly as the manuscript
  prescribes;
* the loop stops as soon as the second vector is no shorter than the first;
* the sign is then normalized: if the first vector is lexicographically
  smaller than its own negative, both vectors are negated (determinant
  `(-1)(-1) = +1`);
* finally, if the two reduced vectors have equal norm, the oriented swap
  `(u,v) ↦ (v,-u)` — which also has determinant `+1` and is again a reduced
  pair — is a second admissible oriented reduced basis, and the
  lexicographically smaller of the two (compared as a pair: first vector
  first, second vector as tie-break) is selected, again as the manuscript
  prescribes.  The output pair is therefore uniquely determined.

Termination uses the well-founded measure `(⟨u,u⟩).toNat`, which strictly
decreases at every swap.

Everything here is a plain `def`; the reduced frame is computed, never
selected from an existence theorem.
-/

namespace TunnellMap

open OrderedGenerator

/-! ## Elementary facts about the integral dot product -/

theorem dot_self_nonneg (v : Triple) : 0 ≤ dot v v := by
  simp only [dot]
  nlinarith [mul_self_nonneg v.x, mul_self_nonneg v.y, mul_self_nonneg v.z]

theorem eq_zero_of_dot_self_eq_zero {v : Triple} (h : dot v v = 0) :
    v = ⟨0, 0, 0⟩ := by
  simp only [dot] at h
  have h1 := mul_self_nonneg v.x
  have h2 := mul_self_nonneg v.y
  have h3 := mul_self_nonneg v.z
  have hx : v.x = 0 := by nlinarith
  have hy : v.y = 0 := by nlinarith
  have hz : v.z = 0 := by nlinarith
  exact Triple.ext hx hy hz

@[simp] theorem dot_negTriple_left (u v : Triple) :
    dot (negTriple u) v = - dot u v := by simp only [dot, negTriple]; ring

@[simp] theorem dot_negTriple_right (u v : Triple) :
    dot u (negTriple v) = - dot u v := by simp only [dot, negTriple]; ring

theorem dot_negTriple_self (u : Triple) : dot (negTriple u) (negTriple u) = dot u u := by
  simp

theorem dot_vsub_vsmul (u v : Triple) (q : ℤ) :
    dot u (vsub v (vsmul q u)) = dot u v - q * dot u u := by
  simp only [dot, vsub, vsmul]; ring

theorem cross_vsub_vsmul (u v : Triple) (q : ℤ) :
    cross u (vsub v (vsmul q u)) = cross u v := by
  apply Triple.ext <;> simp only [cross, vsub, vsmul] <;> ring

theorem cross_swap_neg (u v : Triple) : cross v (negTriple u) = cross u v := by
  apply Triple.ext <;> simp only [cross, negTriple] <;> ring

theorem cross_neg_neg (u v : Triple) :
    cross (negTriple u) (negTriple v) = cross u v := by
  apply Triple.ext <;> simp only [cross, negTriple] <;> ring

/-! ## The reduction step -/

/-- **The nearest integer to `b / a`, with exact half-integer ties rounded
toward zero.**  For `a > 0` this is the unique integer `q` with
`|2 * (b - q * a)| ≤ a` which, at a tie, is the one of smaller absolute
value. -/
def nearestQuot (b a : ℤ) : ℤ :=
  if 0 ≤ b then (2 * b + a - 1) / (2 * a) else -((-(2 * b) + a - 1) / (2 * a))

/-- The nearest-integer quotient of `⟨u,v⟩` by `⟨u,u⟩`, with exact
half-integer ties rounded toward zero. -/
def lgQuot (u v : Triple) : ℤ := nearestQuot (dot u v) (dot u u)

/-- One size-reduction of the second vector against the first. -/
def lgNext (u v : Triple) : Triple := vsub v (vsmul (lgQuot u v) u)

/-- The nearest-integer rounding bound, with ties rounded toward zero. -/
theorem round_bound {a b : ℤ} (ha : 0 < a) :
    -a ≤ 2 * (b - nearestQuot b a * a) ∧ 2 * (b - nearestQuot b a * a) ≤ a := by
  unfold nearestQuot
  by_cases hb : 0 ≤ b
  · rw [if_pos hb]
    have hdiv := Int.mul_ediv_add_emod (2 * b + a - 1) (2 * a)
    have hlo : 0 ≤ (2 * b + a - 1) % (2 * a) := Int.emod_nonneg _ (by omega)
    have hhi : (2 * b + a - 1) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
    generalize (2 * b + a - 1) / (2 * a) = Q at *
    generalize (2 * b + a - 1) % (2 * a) = R at *
    constructor <;> nlinarith
  · rw [if_neg hb]
    have hdiv := Int.mul_ediv_add_emod (-(2 * b) + a - 1) (2 * a)
    have hlo : 0 ≤ (-(2 * b) + a - 1) % (2 * a) := Int.emod_nonneg _ (by omega)
    have hhi : (-(2 * b) + a - 1) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ (by omega)
    generalize (-(2 * b) + a - 1) / (2 * a) = Q at *
    generalize (-(2 * b) + a - 1) % (2 * a) = R at *
    constructor <;> nlinarith

/-- **Exact half-integer ties round toward zero.**  If `2 * b = (2 * k + 1) * a`
then `b / a` is the half-integer `k + 1/2`, and `nearestQuot b a` is `k` for a
nonnegative `b` and `k + 1` for a negative one — in both cases the nearer
integer to zero. -/
theorem nearestQuot_tie {a b k : ℤ} (ha : 0 < a) (h : 2 * b = (2 * k + 1) * a) :
    nearestQuot b a = if 0 ≤ b then k else k + 1 := by
  have hstep : ∀ m : ℤ, (2 * a * m - 1) / (2 * a) = m - 1 := by
    intro m
    have : 2 * a * m - 1 = (2 * a - 1) + 2 * a * (m - 1) := by ring
    rw [this, Int.add_mul_ediv_left _ _ (by omega : (2 * a : ℤ) ≠ 0),
      Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  unfold nearestQuot
  by_cases hb : 0 ≤ b
  · rw [if_pos hb, if_pos hb]
    have : 2 * b + a - 1 = 2 * a * (k + 1) - 1 := by linarith
    rw [this, hstep]
    ring
  · rw [if_neg hb, if_neg hb]
    have : -(2 * b) + a - 1 = 2 * a * (-k) - 1 := by linarith
    rw [this, hstep]
    ring

/-- **The Lagrange-Gauss size-reduction inequality.**  After one reduction
step the mixed term is at most half the first square length. -/
theorem lgNext_bound (u v : Triple) : |2 * dot u (lgNext u v)| ≤ dot u u := by
  rcases eq_or_lt_of_le (dot_self_nonneg u) with h0 | hpos
  · have hu : u = ⟨0, 0, 0⟩ := eq_zero_of_dot_self_eq_zero h0.symm
    subst hu
    simp [lgNext, dot, vsub, vsmul]
  · have hval : dot u (lgNext u v) =
        dot u v - nearestQuot (dot u v) (dot u u) * dot u u := by
      rw [lgNext, dot_vsub_vsmul, lgQuot]
    obtain ⟨h₁, h₂⟩ := round_bound (a := dot u u) (b := dot u v) hpos
    rw [abs_le, hval]
    exact ⟨h₁, h₂⟩

/-- The core reduction loop: reduce, and swap with a sign as long as the
second vector is strictly shorter than the first. -/
def lgReduceAux (u v : Triple) : Triple × Triple :=
  if _h : dot (lgNext u v) (lgNext u v) < dot u u then
    lgReduceAux (lgNext u v) (negTriple u)
  else (u, lgNext u v)
termination_by (dot u u).toNat
decreasing_by
  have hnn := dot_self_nonneg (lgNext u v)
  omega

/-- The sign normalization: the first vector of the output is never
lexicographically smaller than its own negative. -/
def lgNormalize (uv : Triple × Triple) : Triple × Triple :=
  if tripleLexLtExec uv.1 (negTriple uv.1) then
    (negTriple uv.1, negTriple uv.2)
  else uv

/-- The oriented swap `(u, v) ↦ (v, -u)`.  Its determinant is `+1`, so it
preserves the cross product; when the two vectors have equal norm it turns a
reduced pair into a reduced pair. -/
def lgSwap (uv : Triple × Triple) : Triple × Triple := (uv.2, negTriple uv.1)

/-- Lexicographic comparison of two oriented bases: the first vectors are
compared lexicographically, the second vectors break a tie. -/
def pairLexLtExec (uv wz : Triple × Triple) : Bool :=
  tripleLexLtExec uv.1 wz.1 ||
    (decide (uv.1 = wz.1) && tripleLexLtExec uv.2 wz.2)

/-- **The manuscript's selection between equal-norm oriented reduced bases.**
The sign-normalized pair and the sign-normalized oriented swap are both
admissible outputs when the two reduced vectors have equal norm; the
lexicographically smaller one is chosen. -/
def lgSelect (uv : Triple × Triple) : Triple × Triple :=
  if decide (dot uv.1 uv.1 = dot uv.2 uv.2) &&
      pairLexLtExec (lgNormalize (lgSwap uv)) (lgNormalize uv) then
    lgNormalize (lgSwap uv)
  else lgNormalize uv

/-- **The executable Lagrange-Gauss reduction** of an ordered pair of lattice
vectors. -/
def lgReduce (u v : Triple) : Triple × Triple := lgSelect (lgReduceAux u v)

/-! ## The loop preserves the cross product -/

theorem lgReduceAux_cross (u v : Triple) :
    cross (lgReduceAux u v).1 (lgReduceAux u v).2 = cross u v := by
  induction u, v using lgReduceAux.induct with
  | case1 u v h ih =>
      rw [lgReduceAux, dif_pos h, ih, cross_swap_neg, lgNext, cross_vsub_vsmul]
  | case2 u v h =>
      rw [lgReduceAux, dif_neg h]
      show cross u (lgNext u v) = cross u v
      rw [lgNext, cross_vsub_vsmul]

theorem lgNormalize_cross (uv : Triple × Triple) :
    cross (lgNormalize uv).1 (lgNormalize uv).2 = cross uv.1 uv.2 := by
  unfold lgNormalize
  split
  · exact cross_neg_neg _ _
  · rfl

theorem lgSwap_cross (uv : Triple × Triple) :
    cross (lgSwap uv).1 (lgSwap uv).2 = cross uv.1 uv.2 :=
  cross_swap_neg uv.1 uv.2

theorem lgSelect_cross (uv : Triple × Triple) :
    cross (lgSelect uv).1 (lgSelect uv).2 = cross uv.1 uv.2 := by
  unfold lgSelect
  split
  · rw [lgNormalize_cross, lgSwap_cross]
  · exact lgNormalize_cross uv

theorem lgReduce_cross (u v : Triple) :
    cross (lgReduce u v).1 (lgReduce u v).2 = cross u v := by
  rw [lgReduce, lgSelect_cross, lgReduceAux_cross]

/-! ## The output of the loop is reduced -/

/-- The Lagrange-Gauss inequalities on a pair of vectors. -/
def IsReducedPair (uv : Triple × Triple) : Prop :=
  |2 * dot uv.1 uv.2| ≤ dot uv.1 uv.1 ∧ dot uv.1 uv.1 ≤ dot uv.2 uv.2

theorem lgReduceAux_reduced (u v : Triple) : IsReducedPair (lgReduceAux u v) := by
  induction u, v using lgReduceAux.induct with
  | case1 u v h ih =>
      rw [lgReduceAux, dif_pos h]
      exact ih
  | case2 u v h =>
      rw [lgReduceAux, dif_neg h]
      exact ⟨lgNext_bound u v, not_lt.mp h⟩

theorem lgNormalize_reduced {uv : Triple × Triple} (h : IsReducedPair uv) :
    IsReducedPair (lgNormalize uv) := by
  unfold lgNormalize
  split
  · obtain ⟨h₁, h₂⟩ := h
    refine ⟨?_, ?_⟩ <;>
      simp only [dot_negTriple_left, dot_negTriple_right, neg_neg] at * <;>
      [exact h₁; exact h₂]
  · exact h

/-- When the two vectors of a reduced pair have equal norm, the oriented swap
is again a reduced pair. -/
theorem lgSwap_reduced {uv : Triple × Triple} (h : IsReducedPair uv)
    (heq : dot uv.1 uv.1 = dot uv.2 uv.2) : IsReducedPair (lgSwap uv) := by
  obtain ⟨h₁, -⟩ := h
  refine ⟨?_, ?_⟩
  · show |2 * dot uv.2 (negTriple uv.1)| ≤ dot uv.2 uv.2
    rw [dot_negTriple_right, dot_comm uv.2 uv.1, ← heq, mul_neg, abs_neg]
    exact h₁
  · show dot uv.2 uv.2 ≤ dot (negTriple uv.1) (negTriple uv.1)
    rw [dot_negTriple_self]
    exact le_of_eq heq.symm

theorem lgSelect_reduced {uv : Triple × Triple} (h : IsReducedPair uv) :
    IsReducedPair (lgSelect uv) := by
  unfold lgSelect
  split
  · rename_i hcond
    have heq : dot uv.1 uv.1 = dot uv.2 uv.2 := by
      simpa using (Bool.and_eq_true _ _).mp hcond |>.1
    exact lgNormalize_reduced (lgSwap_reduced h heq)
  · exact lgNormalize_reduced h

theorem lgReduce_reduced (u v : Triple) : IsReducedPair (lgReduce u v) :=
  lgSelect_reduced (lgReduceAux_reduced u v)

/-! ## The reduced frame -/

variable {p : Triple}

/-- **The deterministically reduced orthogonal frame.**  The kernel basis of
the given frame is replaced by its Lagrange-Gauss reduction; the Bezout vector
is unchanged, and the reduction is unimodular of determinant one, so the frame
property is preserved. -/
def reduceFrame (F : OrthogonalFrame p) : OrthogonalFrame p where
  e₁ := (lgReduce F.e₁ F.e₂).1
  e₂ := (lgReduce F.e₁ F.e₂).2
  z := F.z
  cross_eq := by rw [lgReduce_cross]; exact F.cross_eq
  bezout := F.bezout

@[simp] theorem reduceFrame_e₁ (F : OrthogonalFrame p) :
    (reduceFrame F).e₁ = (lgReduce F.e₁ F.e₂).1 := rfl

@[simp] theorem reduceFrame_e₂ (F : OrthogonalFrame p) :
    (reduceFrame F).e₂ = (lgReduce F.e₁ F.e₂).2 := rfl

@[simp] theorem reduceFrame_z (F : OrthogonalFrame p) :
    (reduceFrame F).z = F.z := rfl

/-- **The computed frame satisfies the manuscript's reducedness
predicate.** -/
theorem isLagrangeGaussReduced_reduceFrame (F : OrthogonalFrame p) :
    IsLagrangeGaussReduced (reduceFrame F) :=
  lgReduce_reduced F.e₁ F.e₂

/-- **The reduced-basis size bound applies to the computed frame.** -/
theorem reduceFrame_alpha_square_bound (F : OrthogonalFrame p) :
    3 * alpha (reduceFrame F) ^ 2 ≤ 4 * dot p p :=
  reduced_alpha_square_bound _ (isLagrangeGaussReduced_reduceFrame F)

/-- **The real form of the reduced-basis bound for the computed frame.** -/
theorem reduceFrame_alpha_le_two_sqrt_div_three (F : OrthogonalFrame p) :
    (alpha (reduceFrame F) : ℝ) ≤ 2 * Real.sqrt ((dot p p : ℝ) / 3) :=
  reduced_alpha_le_two_sqrt_div_three _ (isLagrangeGaussReduced_reduceFrame F)

/-- **The reduction is unimodular** of determinant one. -/
theorem reduceFrame_unimodular (F : OrthogonalFrame p) (hp : p ≠ ⟨0, 0, 0⟩) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      (reduceFrame F).e₁ = span2 a b F.e₁ F.e₂ ∧
      (reduceFrame F).e₂ = span2 c d F.e₁ F.e₂ :=
  frame_change_unimodular F (reduceFrame F) hp

/-- **The reduction spans the same lattice.** -/
theorem reduceFrame_same_lattice (F : OrthogonalFrame p) (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔
      (∃ a b : ℤ, r = span2 a b (reduceFrame F).e₁ (reduceFrame F).e₂) :=
  frame_same_lattice F (reduceFrame F) r

/-- The Gram determinant is unchanged by the reduction. -/
theorem reduceFrame_gram_det (F : OrthogonalFrame p) :
    dot (reduceFrame F).e₁ (reduceFrame F).e₁ * dot (reduceFrame F).e₂ (reduceFrame F).e₂ -
        dot (reduceFrame F).e₁ (reduceFrame F).e₂ ^ 2 = dot p p :=
  (reduceFrame F).gram_det

/-- **Determinism.**  The reduction is a function of the input pair alone: no
choice, ordering or auxiliary data enters, so any two executions on equal
inputs return equal outputs. -/
theorem lgReduce_deterministic {u v u' v' : Triple} (hu : u = u') (hv : v = v') :
    lgReduce u v = lgReduce u' v' := by rw [hu, hv]

/-- **Determinism of the reduced frame.**  The reduced basis depends only on
the input basis vectors — not on the Bezout vector, the ambient source vector,
or the proofs carried by the frame. -/
theorem reduceFrame_deterministic {p q : Triple} (F : OrthogonalFrame p)
    (G : OrthogonalFrame q) (h₁ : F.e₁ = G.e₁) (h₂ : F.e₂ = G.e₂) :
    ((reduceFrame F).e₁, (reduceFrame F).e₂) =
      ((reduceFrame G).e₁, (reduceFrame G).e₂) := by
  rw [reduceFrame_e₁, reduceFrame_e₂, reduceFrame_e₁, reduceFrame_e₂, h₁, h₂]

end TunnellMap

import TunnellMap.FallbackFreeMap

/-!
# The branch specification of the public map

`paperTunnellMapTotal` is assembled from four branches, and this file pins
each of them by an explicit coordinate formula, so that the public map is not
merely *some* two-to-one map:

* `paperTunnellMapTotal_even` — the even branch `(x, y, 2w) ↦ (x, y, w)`;
* `paperTunnellMapTotal_quarterTurn_one/two/three` — the three integral
  quarter-turns, on the congruence-defined subsets of the odd part, in the
  manuscript's priority order;
* `paperTunnellMapTotal_residual_target` — a source in none of those three
  classes is sent to a *residual* target, i.e. to a target that no
  quarter-turn branch produces.  This is the branch computed by the generator
  and the deferred-acceptance loop; the value of the map there is determined
  by the stable matching, which these formulas do not restate.
-/

namespace TunnellMap

variable {n : ℤ}

/-- Reading a value off the `Option` computation. -/
theorem paperTunnellMapTotal_val_eq (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    {p : BRep n} {v : Triple}
    (h : Option.map (fun a : ARep n => a.1) (paperTunnellMapExecOpt hnpos hsq p) =
      some v) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 = v := by
  rw [← some_paperTunnellMapTotal hn hnpos hsq hbal p, Option.map_some] at h
  exact Option.some.inj h

/-! ## The even branch -/

/-- **The even branch.**  A source with even third coordinate is halved in
that coordinate. -/
theorem paperTunnellMapTotal_even (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.z % 2 = 0) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨p.1.x, p.1.y, p.1.z / 2⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  rw [paperTunnellMapExecOpt, dif_pos hz]
  rfl

/-! ## The three quarter-turn branches -/

/-- **The first quarter-turn.**  If the third coordinate is odd and
`8 ∣ x + 2z + y`, with quotient `q`, then the image is `(4q - y, x - 2z, q)`. -/
theorem paperTunnellMapTotal_quarterTurn_one (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y)) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨4 * ((p.1.x + 2 * p.1.z + p.1.y) / 8) - p.1.y, p.1.x - 2 * p.1.z,
        (p.1.x + 2 * p.1.z + p.1.y) / 8⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  have hd : SourceUsedTriple p.1 := Or.inl h₁
  let q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
  rw [paperTunnellMapExecOpt, dif_neg hz]
  change Option.map (fun a : ARep n => a.1) (oddMapExecOpt hnpos hsq q) = _
  rw [oddMapExecOpt, dif_pos hd,
    directMapExec, directDomainExec, dif_pos h₁]
  rfl

/-- **The second quarter-turn.**  If the third coordinate is odd,
`8 ∤ x + 2z + y` and `8 ∣ y - x + 2z`, with quotient `q`, then the image is
`(x - 2z + 4q, -x - 2z, q)`. -/
theorem paperTunnellMapTotal_quarterTurn_two (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y))
    (h₂ : (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z)) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨p.1.x - 2 * p.1.z + 4 * ((p.1.y - p.1.x + 2 * p.1.z) / 8),
        -p.1.x - 2 * p.1.z, (p.1.y - p.1.x + 2 * p.1.z) / 8⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  have hd : SourceUsedTriple p.1 := Or.inr (Or.inl h₂)
  let q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
  rw [paperTunnellMapExecOpt, dif_neg hz]
  change Option.map (fun a : ARep n => a.1) (oddMapExecOpt hnpos hsq q) = _
  rw [oddMapExecOpt, dif_pos hd,
    directMapExec, directDomainExec, dif_neg h₁, dif_pos h₂]
  rfl

/-- **The third quarter-turn.**  If the third coordinate is odd, neither of
the first two congruences holds and `4 ∣ x`, with quotient `q`, then the image
is `(2z, y, -q)`. -/
theorem paperTunnellMapTotal_quarterTurn_three (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0)
    (h₁ : ¬ (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y))
    (h₂ : ¬ (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z))
    (h₃ : (4 : ℤ) ∣ p.1.x) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨2 * p.1.z, p.1.y, -(p.1.x / 4)⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  have hd : SourceUsedTriple p.1 := Or.inr (Or.inr h₃)
  let q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
  rw [paperTunnellMapExecOpt, dif_neg hz]
  change Option.map (fun a : ARep n => a.1) (oddMapExecOpt hnpos hsq q) = _
  rw [oddMapExecOpt, dif_pos hd,
    directMapExec, directDomainExec, dif_neg h₁, dif_neg h₂, dif_pos h₃]
  rfl

/-! ## The residual branch -/

/-- **The residual branch lands in the residual targets.**  A source whose
third coordinate is odd and which satisfies none of the three congruences is
mapped to a target that no quarter-turn branch produces; the value there is
the one computed by the generator and the deferred-acceptance loop. -/
theorem paperTunnellMapTotal_residual_target (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : ¬ p.1.z % 2 = 0) (hd : ¬ SourceUsedTriple p.1) :
    ¬ DirectTargetUsed (paperTunnellMapTotal hn hnpos hsq hbal p) := by
  classical
  set q : BOddRep n := ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩ with hq
  set x : BResidual n := ⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩ with hx
  have hcard := residual_orbit_card_eq hn hnpos
    (odd_card_eq_of_full_balance (fintype_balance_of_nat_card hbal))
  have hres := RecordDA.residualMapExecOpt_eq_some hn hnpos hsq hcard x
  have hopt : paperTunnellMapExecOpt hnpos hsq p =
      some (canonicalResidualMapOf hnpos
        (residualOrbitMatching hnpos hcard) x).1 := by
    rw [paperTunnellMapExecOpt, dif_neg hz]
    change oddMapExecOpt hnpos hsq q = _
    rw [oddMapExecOpt, dif_neg hd, hres]
    rfl
  have hval : paperTunnellMapTotal hn hnpos hsq hbal p =
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x).1 :=
    Option.some.inj
      ((some_paperTunnellMapTotal hn hnpos hsq hbal p).trans hopt)
  rw [hval]
  exact (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x).2

end TunnellMap

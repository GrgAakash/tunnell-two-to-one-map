import TunnellMap.OrbitLift
import TunnellMap.Finiteness

/-!
# Assembly from the paper's full balance hypothesis

The full source set is split by parity of its third coordinate.  The even
part is equivalent to the target set, while the odd part is the `BOddRep`
used by the direct and residual construction.  Thus
`card BRep = 2 * card ARep` implies `card BOddRep = card ARep`.
-/

namespace TunnellMap

def BEvenRep (n : ℤ) := {p : BRep n // Even p.1.z}

theorem BEvenParam.extensionality {n : ℤ} {p q : BEvenParam n}
    (hx : p.x = q.x) (hy : p.y = q.y) (hw : p.w = q.w) : p = q := by
  cases p
  cases q
  simp_all

def evenRepToParam {n : ℤ} (p : BEvenRep n) : BEvenParam n := by
  refine ⟨p.1.1.x, p.1.1.y, p.1.1.z / 2, ?_⟩
  have hform := p.1.2
  change bForm ⟨p.1.1.x, p.1.1.y, 2 * (p.1.1.z / 2)⟩ = n
  have hdiv : (2 : ℤ) ∣ p.1.1.z := even_iff_two_dvd.mp p.2
  have hz' : 2 * (p.1.1.z / 2) = p.1.1.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  rw [hz']
  exact hform

def evenParamToRep {n : ℤ} (p : BEvenParam n) : BEvenRep n :=
  ⟨p.asBRep, ⟨p.w, by dsimp [BEvenParam.asBRep]; omega⟩⟩

def evenRepParamEquiv (n : ℤ) : BEvenRep n ≃ BEvenParam n := by
  refine
    { toFun := evenRepToParam
      invFun := evenParamToRep
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Triple.ext
    · rfl
    · rfl
    · change 2 * (p.1.1.z / 2) = p.1.1.z
      rw [mul_comm]
      exact Int.ediv_mul_cancel (even_iff_two_dvd.mp p.2)
  · intro p
    apply BEvenParam.extensionality
    · rfl
    · rfl
    · change (2 * p.w) / 2 = p.w
      exact Int.mul_ediv_cancel_left p.w (by norm_num)

def bOddSubtypeEquiv (n : ℤ) :
    {p : BRep n // Odd p.1.z} ≃ BOddRep n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl

noncomputable def bRepParityEquiv (n : ℤ) :
    BRep n ≃ BEvenParam n ⊕ BOddRep n := by
  classical
  exact (Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm.trans
    (Equiv.sumCongr (evenRepParamEquiv n)
      ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
        (bOddSubtypeEquiv n)))

noncomputable instance bOddRepFintype {n : ℤ} [Fintype (BRep n)] :
    Fintype (BOddRep n) := by
  classical
  letI : Fintype {p : BRep n // Odd p.1.z} := Fintype.ofFinite _
  exact Fintype.ofEquiv _ (bOddSubtypeEquiv n)

noncomputable instance bEvenParamFintype {n : ℤ} [Fintype (ARep n)] :
    Fintype (BEvenParam n) := Fintype.ofEquiv _ (evenEquiv n).symm

theorem odd_card_eq_of_full_balance {n : ℤ}
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    Fintype.card (BOddRep n) = Fintype.card (ARep n) := by
  classical
  have hsplit := Fintype.card_congr (bRepParityEquiv n)
  have heven := Fintype.card_congr (evenEquiv n)
  rw [Fintype.card_sum] at hsplit
  omega

noncomputable def paperOddEquiv {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    BOddRep n ≃ ARep n :=
  oddEquivOfBalance hn hnpos (odd_card_eq_of_full_balance hbalance)

/-- The map in the paper's balanced construction theorem, on the literal full source representation set. -/
noncomputable def paperTunnellMap {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n)) :
    BRep n → ARep n := fun p =>
  conditionalTunnellMap (paperOddEquiv hn hnpos hbalance) (bRepParityEquiv n p)

theorem paperTunnellMap_exactly_two {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMap hn hnpos hbalance p₁ = a ∧
      paperTunnellMap hn hnpos hbalance p₂ = a ∧
      ∀ p, paperTunnellMap hn hnpos hbalance p = a ↔ p = p₁ ∨ p = p₂ := by
  let odd := paperOddEquiv hn hnpos hbalance
  obtain ⟨x₁, x₂, hne, hx₁, hx₂, hfiber⟩ :=
    conditionalTunnellMap_exactly_two odd a
  refine ⟨(bRepParityEquiv n).symm x₁, (bRepParityEquiv n).symm x₂,
    ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    exact (bRepParityEquiv n).symm.injective h
  · simpa [paperTunnellMap, odd] using hx₁
  · simpa [paperTunnellMap, odd] using hx₂
  · intro p
    rw [show paperTunnellMap hn hnpos hbalance p =
        conditionalTunnellMap odd (bRepParityEquiv n p) by rfl, hfiber]
    constructor
    · rintro (h | h)
      · left
        exact (bRepParityEquiv n).injective (by simpa using h)
      · right
        exact (bRepParityEquiv n).injective (by simpa using h)
    · rintro (rfl | rfl) <;> simp

end TunnellMap

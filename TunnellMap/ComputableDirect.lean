import TunnellMap.ResidualBalance
import TunnellMap.ComputableRoster

/-!
# The executable direct branch

`TunnellMap.directSubsetEquiv` is `noncomputable`: the equivalences
`domain1SubtypeEquiv`, … recover the branch quotient with `Classical.choose`.
The quotient is however *determined* by the coordinates, so it can simply be
divided out.  This file rebuilds the direct branch as a computable function

* `directDomainExec` — the branch datum of a direct source, with the quotient
  obtained by exact integer division;
* `directMapExec` — the resulting target representation.

`directMapExec_eq` proves that the computable function agrees with the value
of the structural equivalence `directSubsetEquiv`.
-/

namespace TunnellMap

/-- The source representation underlying a direct branch datum. -/
def directDomainRep {n : ℤ} : DirectDomain n → BOddRep n
  | Sum.inl d => d.rep
  | Sum.inr (Sum.inl d) => d.rep
  | Sum.inr (Sum.inr d) => d.rep

/-- The target representation underlying a direct image datum. -/
def directImageRep {n : ℤ} : DirectImage n → ARep n
  | Sum.inl d => d.rep
  | Sum.inr (Sum.inl d) => d.rep
  | Sum.inr (Sum.inr d) => d.rep

/-- **The executable branch datum of a direct source.**  The branch is chosen
by the manuscript's priority order 1, 2, 3, and the quotient is the exact
integer division. -/
def directDomainExec {n : ℤ} (p : BOddRep n) : Option (DirectDomain n) :=
  if h₁ : (8 : ℤ) ∣ (p.1.x + 2 * p.1.z + p.1.y) then
    some (Sum.inl ⟨p, (p.1.x + 2 * p.1.z + p.1.y) / 8,
      (Int.mul_ediv_cancel' h₁).symm⟩)
  else if h₂ : (8 : ℤ) ∣ (p.1.y - p.1.x + 2 * p.1.z) then
    some (Sum.inr (Sum.inl ⟨p, (p.1.y - p.1.x + 2 * p.1.z) / 8,
      (Int.mul_ediv_cancel' h₂).symm⟩))
  else if h₃ : (4 : ℤ) ∣ p.1.x then
    some (Sum.inr (Sum.inr ⟨p, p.1.x / 4, (Int.mul_ediv_cancel' h₃).symm⟩))
  else none

/-- **The executable direct map.** -/
def directMapExec {n : ℤ} (p : BOddRep n) : Option (ARep n) :=
  (directDomainExec p).map fun d => directImageRep (directEquiv n d)

theorem directDomainExec_rep {n : ℤ} {p : BOddRep n} {d : DirectDomain n}
    (h : directDomainExec p = some d) : directDomainRep d = p := by
  unfold directDomainExec at h
  split_ifs at h <;> rw [← Option.some.inj h] <;> rfl

theorem directDomainExec_isSome {n : ℤ} {p : BOddRep n} (h : DirectSourceUsed p) :
    ∃ d : DirectDomain n, directDomainExec p = some d := by
  rw [directSourceUsed_iff] at h
  unfold directDomainExec
  split_ifs with h₁ h₂ h₃
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact absurd h (by
      unfold SourceUsedTriple
      push_neg
      exact ⟨h₁, h₂, h₃⟩)

/-! ## Agreement with the structural direct equivalence -/

theorem directSourceUnionEquiv_val {n : ℤ} (hn : Odd n) (d : DirectDomain n) :
    (directSourceUnionEquiv hn d).1 = directDomainRep d := by
  rcases d with d | d | d <;> rfl

theorem directTargetUnionEquiv_val {n : ℤ} (hn : Odd n) (i : DirectImage n) :
    (directTargetUnionEquiv hn i).1 = directImageRep i := by
  rcases i with i | i | i <;> rfl

/-- **The computable direct map agrees with the structural equivalence.** -/
theorem directMapExec_eq {n : ℤ} (hn : Odd n) (p : BOddRep n)
    (h : DirectSourceUsed p) :
    directMapExec p = some ((directSubsetEquiv hn ⟨p, h⟩).1) := by
  obtain ⟨d, hd⟩ := directDomainExec_isSome h
  have hrep : directDomainRep d = p := directDomainExec_rep hd
  have hsym : (directSourceUnionEquiv hn).symm ⟨p, h⟩ = d := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext (by rw [directSourceUnionEquiv_val, hrep])
  rw [directMapExec, hd, Option.map_some]
  congr 1
  show directImageRep (directEquiv n d) = _
  rw [directSubsetEquiv]
  simp only [Equiv.trans_apply, hsym]
  rw [directTargetUnionEquiv_val]

end TunnellMap

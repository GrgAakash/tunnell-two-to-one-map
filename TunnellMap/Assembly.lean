import TunnellMap.Basic

/-!
# Assembly of two bijective branches

The final construction in the paper is the disjoint union of an even branch
and an odd branch, each bijective with the target.  The theorems below prove
that this assembly has exactly two preimages at every target.
-/

namespace TunnellMap

section AbstractAssembly

variable {E O A : Type*}

def assemble (even : E ≃ A) (odd : O ≃ A) : E ⊕ O → A
  | Sum.inl e => even e
  | Sum.inr o => odd o

@[simp] theorem assemble_inl (even : E ≃ A) (odd : O ≃ A) (e : E) :
    assemble even odd (Sum.inl e) = even e :=
  rfl

@[simp] theorem assemble_inr (even : E ≃ A) (odd : O ≃ A) (o : O) :
    assemble even odd (Sum.inr o) = odd o :=
  rfl

theorem assemble_surjective (even : E ≃ A) (odd : O ≃ A) :
    Function.Surjective (assemble even odd) := by
  intro a
  exact ⟨Sum.inl (even.symm a), by simp⟩

theorem assemble_fiber_iff (even : E ≃ A) (odd : O ≃ A) (a : A)
    (x : E ⊕ O) :
    assemble even odd x = a ↔
      x = Sum.inl (even.symm a) ∨ x = Sum.inr (odd.symm a) := by
  cases x with
  | inl e =>
      simpa [assemble] using
        (even.apply_eq_iff_eq_symm_apply : even e = a ↔ e = even.symm a)
  | inr o =>
      simpa [assemble] using
        (odd.apply_eq_iff_eq_symm_apply : odd o = a ↔ o = odd.symm a)

theorem assemble_two_distinct_preimages (even : E ≃ A) (odd : O ≃ A)
    (a : A) :
    assemble even odd (Sum.inl (even.symm a)) = a ∧
      assemble even odd (Sum.inr (odd.symm a)) = a ∧
      Sum.inl (even.symm a) ≠ Sum.inr (odd.symm a) := by
  simp

theorem assemble_exactly_two (even : E ≃ A) (odd : O ≃ A) (a : A) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      assemble even odd x₁ = a ∧
      assemble even odd x₂ = a ∧
      ∀ x, assemble even odd x = a ↔ x = x₁ ∨ x = x₂ := by
  refine ⟨Sum.inl (even.symm a), Sum.inr (odd.symm a), ?_, by simp,
    by simp, ?_⟩
  · simp
  · intro x
    exact assemble_fiber_iff even odd a x

end AbstractAssembly

/-- The conditional map after an odd-branch equivalence has been constructed. -/
def conditionalTunnellMap {n : ℤ} (odd : BOddRep n ≃ ARep n) :
    BEvenParam n ⊕ BOddRep n → ARep n :=
  assemble (evenEquiv n) odd

theorem conditionalTunnellMap_exactly_two {n : ℤ}
    (odd : BOddRep n ≃ ARep n) (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap odd x₁ = a ∧
      conditionalTunnellMap odd x₂ = a ∧
      ∀ x, conditionalTunnellMap odd x = a ↔ x = x₁ ∨ x = x₂ :=
  assemble_exactly_two (evenEquiv n) odd a

end TunnellMap

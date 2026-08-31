import Mathlib

/-!
# Stable matchings with globally ranked pairs

This file isolates the combinatorial core of Proposition 4.3 in the paper.
Every edge has a natural-number rank.  Incident ranks are distinct at both
ends, so the global ranking induces strict preferences.  We prove that two
stable perfect matchings must coincide.
-/

namespace TunnellMap

structure GloballyRanked (K S T : Type*) where
  rank : S → T → K
  source_injective : ∀ s, Function.Injective (rank s)
  target_injective : ∀ t, Function.Injective (fun s => rank s t)

namespace GloballyRanked

variable {K S T : Type*}

def Blocks [LT K] (I : GloballyRanked K S T) (M : S ≃ T) (s : S) (t : T) : Prop :=
  I.rank s t < I.rank s (M s) ∧
    I.rank s t < I.rank (M.symm t) t

def Stable [LT K] (I : GloballyRanked K S T) (M : S ≃ T) : Prop :=
  ∀ s t, ¬ I.Blocks M s t

section Finite

variable [LinearOrder K] [Fintype S] [Fintype T]

def InMatchingSymmDiff (M N : S ≃ T) (e : S × T) : Prop :=
  (M e.1 = e.2 ∧ N e.1 ≠ e.2) ∨
    (N e.1 = e.2 ∧ M e.1 ≠ e.2)

noncomputable def matchingSymmDiff (M N : S ≃ T) : Finset (S × T) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (InMatchingSymmDiff M N)

theorem stable_unique (I : GloballyRanked K S T) (M N : S ≃ T)
    (hM : I.Stable M) (hN : I.Stable N) : M = N := by
  classical
  by_contra hne
  have hfun : ∃ s, M s ≠ N s := by
    by_contra hnone
    apply hne
    apply Equiv.ext
    intro s
    by_contra hs
    exact hnone ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := hfun
  let D := matchingSymmDiff M N
  have hD : D.Nonempty := by
    refine ⟨(s₀, M s₀), ?_⟩
    simp [D, matchingSymmDiff, InMatchingSymmDiff, Ne.symm hs₀]
  let R : Finset K := D.image (fun e => I.rank e.1 e.2)
  have hR : R.Nonempty := hD.image _
  let k := R.min' hR
  have hkR : k ∈ R := Finset.min'_mem R hR
  obtain ⟨e, heD, hek⟩ := Finset.mem_image.mp hkR
  have hmin {e' : S × T} (he' : e' ∈ D) :
      I.rank e.1 e.2 ≤ I.rank e'.1 e'.2 := by
    have hr' : I.rank e'.1 e'.2 ∈ R := Finset.mem_image.mpr ⟨e', he', rfl⟩
    rw [hek]
    change R.min' hR ≤ I.rank e'.1 e'.2
    exact Finset.min'_le R (I.rank e'.1 e'.2) hr'
  have heCases : InMatchingSymmDiff M N e := by
    simpa [D, matchingSymmDiff] using (Finset.mem_filter.mp heD).2
  rcases heCases with heM | heN
  · rcases heM with ⟨hMe, hNe⟩
    have hsourceD : (e.1, N e.1) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, hMe, Ne.symm hNe]
    have htarget_ne : M (N.symm e.2) ≠ e.2 := by
      intro h
      have hs : N.symm e.2 = e.1 := M.injective (h.trans hMe.symm)
      have : N e.1 = e.2 := by
        rw [← hs]
        simp
      exact hNe this
    have htargetD : (N.symm e.2, e.2) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, htarget_ne]
    have hle_source := hmin hsourceD
    have hle_target := hmin htargetD
    have hlt_source : I.rank e.1 e.2 < I.rank e.1 (N e.1) := by
      apply lt_of_le_of_ne hle_source
      intro h
      exact hNe (I.source_injective e.1 h).symm
    have hlt_target : I.rank e.1 e.2 < I.rank (N.symm e.2) e.2 := by
      apply lt_of_le_of_ne hle_target
      intro h
      have hs := I.target_injective e.2 h
      exact htarget_ne (by simpa [hs] using hMe)
    exact hN e.1 e.2 ⟨hlt_source, hlt_target⟩
  · rcases heN with ⟨hNe, hMe⟩
    have hsourceD : (e.1, M e.1) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, hNe, Ne.symm hMe]
    have htarget_ne : N (M.symm e.2) ≠ e.2 := by
      intro h
      have hs : M.symm e.2 = e.1 := N.injective (h.trans hNe.symm)
      have : M e.1 = e.2 := by
        rw [← hs]
        simp
      exact hMe this
    have htargetD : (M.symm e.2, e.2) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, htarget_ne]
    have hle_source := hmin hsourceD
    have hle_target := hmin htargetD
    have hlt_source : I.rank e.1 e.2 < I.rank e.1 (M e.1) := by
      apply lt_of_le_of_ne hle_source
      intro h
      exact hMe (I.source_injective e.1 h).symm
    have hlt_target : I.rank e.1 e.2 < I.rank (M.symm e.2) e.2 := by
      apply lt_of_le_of_ne hle_target
      intro h
      have hs := I.target_injective e.2 h
      exact htarget_ne (by simpa [hs] using hNe)
    exact hM e.1 e.2 ⟨hlt_source, hlt_target⟩

end Finite

end GloballyRanked

end TunnellMap

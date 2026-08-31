import TunnellMap.OrderedGenerator
import TunnellMap.DeferredAcceptanceStability
import TunnellMap.OrbitLift

/-!
# Deferred acceptance on the Tunnell residual orbits

This file identifies the finite arithmetic incident stream with the abstract
preference list used by deferred acceptance.  It then instantiates the FIFO
algorithm on the residual orbit graph and proves that its output is the
paper's unique stable orbit matching.
-/

namespace TunnellMap

open OrderedGenerator

section SourceOrder

variable {n : ℤ} [Fintype (BOddRep n)]

/-- The lexicographic key of a residual source orbit, evaluated on its
canonical signed representative. -/
def residualSourceOrbitKey
    (s : (bResidualInvolution n).Orbit) : TripleLexKey :=
  bResidualLexKey (canonicalBResidualRepresentative s)

theorem residualSourceOrbitKey_injective :
    Function.Injective (residualSourceOrbitKey (n := n)) := by
  intro s₁ s₂ hkey
  have hrep : canonicalBResidualRepresentative s₁ =
      canonicalBResidualRepresentative s₂ :=
    bResidualLexKey_injective hkey
  let BI := bResidualInvolution n
  calc
    s₁ = BI.orbit (canonicalBResidualRepresentative s₁) :=
      (BI.orbit_canonicalRepresentative bResidualLexKey
        bResidualLexKey_injective s₁).symm
    _ = BI.orbit (canonicalBResidualRepresentative s₂) := by rw [hrep]
    _ = s₂ := BI.orbit_canonicalRepresentative bResidualLexKey
      bResidualLexKey_injective s₂

/-- The initial FIFO queue prescribed in the manuscript: all residual source
orbits in the lexicographic order of their canonical representatives. -/
noncomputable def residualSourceOrder :
    List (bResidualInvolution n).Orbit := by
  classical
  letI : LinearOrder (bResidualInvolution n).Orbit :=
    LinearOrder.lift' residualSourceOrbitKey residualSourceOrbitKey_injective
  exact (Finset.univ : Finset (bResidualInvolution n).Orbit).sort

theorem residualSourceOrder_nodup :
    (residualSourceOrder (n := n)).Nodup := by
  classical
  unfold residualSourceOrder
  exact Finset.sort_nodup _ _

@[simp] theorem mem_residualSourceOrder
    (s : (bResidualInvolution n).Orbit) :
    s ∈ residualSourceOrder (n := n) := by
  classical
  simp [residualSourceOrder]

end SourceOrder

section GeneratedPreferences

variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- The generated arithmetic stream is pairwise ordered by the same global
projective key as the abstract preference list. -/
theorem incidentStream_pairwise (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Pairwise fun t₁ t₂ =>
      (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₁ ≤
        (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₂ := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact (incidentStream_key_strict hnpos s F hij).le

/-- The arithmetic generator and the abstract finite sort define literally
the same preference list. -/
theorem incidentStream_eq_preferenceList (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    incidentStream hnpos s F =
      (residualOrbitRanking hnpos).preferenceList
        ((bResidualInvolution n).orbit s) := by
  let I := residualOrbitRanking hnpos
  let q := (bResidualInvolution n).orbit s
  have hperm : (incidentStream hnpos s F).Perm (I.preferenceList q) := by
    apply (List.perm_ext_iff_of_nodup
      (incidentStream_nodup hnpos s F)
      (I.preferenceList_nodup q)).2
    intro t
    constructor
    · intro _
      exact I.mem_preferenceList q t
    · intro _
      exact mem_incidentStream hn hnpos s F t
  apply hperm.eq_of_pairwise
  · intro t₁ t₂ _ _ h₁₂ h₂₁
    exact I.source_injective q (le_antisymm h₁₂ h₂₁)
  · exact incidentStream_pairwise hnpos s F
  · exact I.preferenceList_pairwise q

/-- A squarefree source norm supplies the oriented frame required by the
finite arithmetic generator. -/
noncomputable def residualSourceFrame (hsquarefree : Squarefree n)
    (s : BResidual n) :
    OrthogonalFrame (tau (residualSourceLift s)) := by
  have hnorm : dot (tau (residualSourceLift s))
      (tau (residualSourceLift s)) = n := by
    rw [qForm_tau]
    simp [residualSourceLift]
  exact Classical.choice
    (orthogonalFrame_exists_of_squarefree_norm hsquarefree hnorm)

theorem canonicalIncidentStream_eq_preferenceList
    (hn : Odd n) (hnpos : 0 < n) (hsquarefree : Squarefree n)
    (q : (bResidualInvolution n).Orbit) :
    incidentStream hnpos (canonicalBResidualRepresentative q)
        (residualSourceFrame hsquarefree
          (canonicalBResidualRepresentative q)) =
      (residualOrbitRanking hnpos).preferenceList q := by
  rw [incidentStream_eq_preferenceList hn hnpos]
  congr 1
  simpa [canonicalBResidualRepresentative] using
    (bResidualInvolution n).orbit_canonicalRepresentative
      bResidualLexKey bResidualLexKey_injective q

end GeneratedPreferences

section AlgorithmicMatching

variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- The orbit matching returned by the terminating FIFO algorithm started in
the manuscript's canonical source order. -/
noncomputable def algorithmicResidualOrbitMatching
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (bResidualInvolution n).Orbit ≃
      (aResidualInvolution n hnpos).Orbit := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching
    (residualOrbitRanking hnpos) hcard residualSourceOrder
      residualSourceOrder_nodup mem_residualSourceOrder

theorem algorithmicResidualOrbitMatching_stable
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (algorithmicResidualOrbitMatching hnpos hcard) := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching_stable
    (residualOrbitRanking hnpos) hcard residualSourceOrder
      residualSourceOrder_nodup mem_residualSourceOrder

/-- The executable FIFO construction agrees with the abstract matching used
elsewhere in the paper. -/
theorem algorithmicResidualOrbitMatching_eq
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualOrbitMatching hnpos hcard =
      residualOrbitMatching hnpos hcard := by
  classical
  exact residualOrbitMatching_unique hnpos hcard _
    (algorithmicResidualOrbitMatching_stable hnpos hcard)

/-- Any complete duplicate-free rerun order produces the same orbit
matching.  In particular, the inverse can be regenerated without retaining a
proposal transcript. -/
theorem residualDeferredAcceptance_rerun
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (sourceOrder : List (bResidualInvolution n).Orbit)
    (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    GloballyRanked.DAState.deferredAcceptanceMatching
        (residualOrbitRanking hnpos) hcard sourceOrder hnodup hcomplete =
      algorithmicResidualOrbitMatching hnpos hcard := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching_order_independent
    (residualOrbitRanking hnpos) hcard sourceOrder residualSourceOrder
      hnodup residualSourceOrder_nodup hcomplete mem_residualSourceOrder

/-- Lift the algorithmic orbit matching through the paper's deterministic
sign rule to obtain the residual signed correspondence. -/
noncomputable def algorithmicResidualEquiv
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    BResidual n ≃ AResidual n := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let M := algorithmicResidualOrbitMatching hnpos hcard
  exact BI.liftOrbitEquiv AI M (fun s => orbitSignEquiv hnpos s (M s))

/-- The executable lift is extensionally the residual equivalence used in the
assembled Tunnell map. -/
theorem algorithmicResidualEquiv_eq
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualEquiv hnpos hcard =
      residualEquivOfOrbitCard hnpos hcard := by
  classical
  unfold algorithmicResidualEquiv residualEquivOfOrbitCard
  rw [algorithmicResidualOrbitMatching_eq hnpos hcard]

/-- The regenerated reverse interface is the inverse equivalence; both
pointwise inverse identities follow without retaining the proposal history. -/
theorem algorithmicResidualEquiv_inverse_identities
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (∀ s, (algorithmicResidualEquiv hnpos hcard).symm
        (algorithmicResidualEquiv hnpos hcard s) = s) ∧
      (∀ t, algorithmicResidualEquiv hnpos hcard
        ((algorithmicResidualEquiv hnpos hcard).symm t) = t) := by
  constructor <;> intro x <;> simp

end AlgorithmicMatching

end TunnellMap

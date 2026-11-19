import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre
import Hironaka.Resolution.HironakaG8NativePrefixWindowRestriction
import Hironaka.Invariant.StepOneTangentChange

/-! Transport the same simultaneous native maximum through literal
shrinking and actual stagewise biholomorphic identification. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeSimultaneousTransport

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaStageCenters MaxLocusLocal StepOneTangentChange
  HironakaOriginalTerminalOverlapComparison HironakaG8NativePrefixWindowRestriction
  HironakaG8NativeSimultaneousCentre

variable {n k : ℕ} {X Y X' Y' : CMfd.{0} n} {I Λ : Type} [LinearOrder Λ]

/-- The literal old window on the restricted common base. -/
abbrev shrunkWindow (O U : Opens X) : Opens O := nestedOpens O (O ⊓ U)

/-- The original local powered record on the actual overlap, in the
coordinates of the newly restricted ambient. -/
abbrev shrunkRecord (O U : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U)) :
    MarkedIdeal n (CMfd.of (n := n) (shrunkWindow O U)) :=
  MarkedIdeal.pullback
    (overlapBaseEquiv (n := n) (show O ⊓ U ≤ O from inf_le_left) (show O ⊓ U ≤ U from inf_le_right))
    (MarkedIdeal.pullback (Subtype.val : nestedOpens U (O ⊓ U) → U) P)

private theorem shrunk_window_iff (T : BlowupTower X Y) (O U : Opens X) (z : openPreimage T O) :
    z ∈ openPreimage (restrict O T) (shrunkWindow O U) ↔ z.val ∈ openPreimage T U := by
  rw [mem_openPreimage_restrict_nestedOpens O (O ⊓ U) T]
  exact ⟨fun h => h.2,fun h => ⟨z.property,h⟩⟩

theorem NativeSimultaneousCentre.restrictAmbient
    {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ}
    {U : I → Opens X} {P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))}
    {T : BlowupTower X Y} {C : Set Y} {m : Λ}
    (h : NativeSimultaneousCentre R U P T C m)
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (O : Opens X) :
    NativeSimultaneousCentre R (fun i => shrunkWindow O (U i)) (fun i => shrunkRecord O (U i) (P i))
      (restrict O T) ((Subtype.val : openPreimage T O → Y) ⁻¹' C) m := by
  choose f hPoint hCos _ hValue using fun i =>
    (native_prefix_values_on_shrunk_ambient R (U i) O (P i) (hP i) T (hCan i)).2.2
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi⟩ := h.covered z.val hz
    exact ⟨i,(shrunk_window_iff T O _ z).mpr hi⟩
  · intro i z hz
    have hz' := (Set.ext_iff.mp (hCos i) z).mp hz
    exact (hValue i z hz).trans_le (h.upper i (f i z) hz')
  · intro i
    ext z
    have hAt : (f i z).val ∈ C ↔ z.val.val ∈ C := iff_of_eq (congrArg (· ∈ C) (hPoint i z))
    have hTrace := Set.ext_iff.mp (h.trace i) (f i z)
    have hState := Set.ext_iff.mp (hCos i) z
    constructor
    · intro hz
      obtain ⟨hzOld,hm⟩ := hTrace.mp (hAt.mpr hz)
      have hzNew := hState.mpr hzOld
      exact ⟨hzNew,(hValue i z hzNew).trans hm⟩
    · rintro ⟨hz,hm⟩
      exact hAt.mp (hTrace.mpr ⟨hState.mp hz,(hValue i z hz).symm.trans hm⟩)

theorem native_simultaneous_stages_restrictAmbient
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i)) (O : Opens X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      (∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T)) →
      NativeSimultaneousStages R U P T →
      NativeSimultaneousStages R (fun i => shrunkWindow O (U i))
        (fun i => shrunkRecord O (U i) (P i)) (restrict O T)
  | _, .refl, _, _ => trivial
  | _, .step T C _ _, hCan, h => by
    have hCanPrev (i : I) := (hCan i).1
    refine ⟨native_simultaneous_stages_restrictAmbient R U P hP O T hCanPrev h.1,?_⟩
    rcases h.2 with hEmpty | ⟨m,hm⟩
    · exact Or.inl (hEmpty ▸ preimage_empty)
    · exact Or.inr ⟨m,NativeSimultaneousCentre.restrictAmbient hm hP hCanPrev O⟩

variable (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)

/-- The actual window pulled back by the ambient identification. -/
abbrev transportedWindow (U : Opens X) : Opens X' :=
  ⟨φ ⁻¹' (U : Set X),U.isOpen.preimage φ.continuous⟩

/-- Its literal marked record, with the original boundary positions. -/
abbrev transportedRecord (U : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U)) :
    MarkedIdeal n (CMfd.of (n := n) (transportedWindow φ U)) :=
  MarkedIdeal.pullback (diffeoOpens φ (transportedWindow φ U) U (fun _ => Iff.rfl)) P

theorem NativeSimultaneousCentre.of_isTowerIso
    {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ}
    {U : I → Opens X} {P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) {C : Set Y} {m : Λ}
    (h : NativeSimultaneousCentre R U P T C m)
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T)) :
    NativeSimultaneousCentre R (fun i => transportedWindow φ (U i))
      (fun i => transportedRecord φ (U i) (P i)) T' (χ ⁻¹' C) m := by
  let U₀ (i : I) := transportedWindow φ (U i)
  let P₀ (i : I) := transportedRecord φ (U i) (P i)
  let hU (i : I) : ∀ z : X', z ∈ U₀ i ↔ φ z ∈ U i := fun _ => Iff.rfl
  let e (i : I) := diffeoOpens φ (U₀ i) (U i) (hU i)
  let hV (i : I) := isTowerIso_mem_openPreimage_iff hIso (hU i)
  let f (i : I) := diffeoOpens χ (openPreimage T' (U₀ i)) (openPreimage T (U i)) (hV i)
  have hTower (i : I) := isTowerIso_restrictOpens (hU i) hIso (hV i)
  have hTest (i : I) := R.isInvValue.isGeoTestTower_of_isCanonical (hP i) (restrict (U i) T) (hCan i)
  have hCos (i : I) : (geoTransformAlong (P₀ i) (restrict (U₀ i) T')).cosupp =
      f i ⁻¹' (geoTransformAlong (P i) (restrict (U i) T)).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong (e i) (hP i).isWellFormed.isClosedSubmanifold_N
      (hP i).isWellFormed.isCoherent (hTower i) (hTest i)
  have hValue (i : I) (z : openPreimage T' (U₀ i))
      (hz : f i z ∈ (geoTransformAlong (P i) (restrict (U i) T)).cosupp) :
      R.inv (P₀ i) (restrict (U₀ i) T') z = R.inv (P i) (restrict (U i) T) (f i z) :=
    R.isInvValue.towerIso (e i) (P i) (hP i) _ _ (f i) (hTower i) (hCan i) z hz
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi⟩ := h.covered (χ z) hz
    exact ⟨i,(hV i z).mpr hi⟩
  · intro i z hz
    have hz' := (Set.ext_iff.mp (hCos i) z).mp hz
    exact (hValue i z hz').trans_le (h.upper i (f i z) hz')
  · intro i
    ext z
    have hTrace := Set.ext_iff.mp (h.trace i) (f i z)
    have hState := Set.ext_iff.mp (hCos i) z
    constructor
    · intro hz
      obtain ⟨hzOld,hm⟩ := hTrace.mp hz
      exact ⟨hState.mpr hzOld,(hValue i z hzOld).trans hm⟩
    · rintro ⟨hz,hm⟩
      have hz' := hState.mp hz
      exact hTrace.mpr ⟨hz',(hValue i z hz').symm.trans hm⟩

theorem native_simultaneous_stages_of_isTowerIso
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ)
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) T))
    (h : NativeSimultaneousStages R U P T) :
    NativeSimultaneousStages R (fun i => transportedWindow φ (U i))
      (fun i => transportedRecord φ (U i) (P i)) T' := by
  induction hIso with
  | refl => trivial
  | @step Y' Y Z' Z T' T χ hIso C' π' hπ' C π hπ χ₁ hπComm hC ih =>
    have hPrev (i : I) := (hCan i).1
    refine ⟨ih hPrev h.1,?_⟩
    rw [← hC]
    rcases h.2 with hEmpty | ⟨m,hm⟩
    · exact Or.inl (hEmpty ▸ preimage_empty)
    · exact Or.inr ⟨m,NativeSimultaneousCentre.of_isTowerIso φ hIso hm hP hPrev⟩

end
end Hironaka.HironakaG8NativeSimultaneousTransport

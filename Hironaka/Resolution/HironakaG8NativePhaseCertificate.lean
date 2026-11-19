import Hironaka.Resolution.HironakaG8NativeRelativePhase
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-! The certified actual phase of a labelled relative singular history
is stable under literal open restriction and actual tower isomorphisms. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativePhaseCertificate

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaG8NativeRelativeClearing HironakaG8NativeRelativePhase
  HironakaG8NativePrefixWindowRestriction HironakaResolutionSpaceLocal
  HironakaEmbeddedBoundary HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaActualVanishingIntrinsicHSTransport HironakaActualOpenEmbeddingVanishingIdeal
  HironakaNormalCrossingsSeparationChoiceComparison HironakaG8FiniteSingularTowerMerge
  HironakaG8SingularFootprintExtension HironakaG3CentresOverGenericFactor
  HironakaStageCenters ResolutionInvariantSpec HironakaG11PresLineState
  NormalCrossings RestrictEmptyTower CanonicalCentres HomogenizedGlueingTower

variable {n : ℕ} {X X' Y Y' : CMfd.{0} n}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

private abbrev original {B : CMfd.{0} n} (W : Set B) (E : List (Set B)) : MarkedIdeal n B :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

/-- The exact original Hilbert--Samuel level supporting a native phase. -/
def phaseLevel (W : Set X) (H : ℕ → ℕ) : Set X := {x | HS[W] x = H}

/-- The actual finite phase and the native terminal certificates on its
literal windows. Every centre lies over the indicated original profile. -/
structure ActualNativePhase (W : Set X) (E : List (Set X)) (H : ℕ → ℕ)
    (T : BlowupTower X Y) : Prop where
  test : IsGeoTestTower (original W E) T
  singular : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  supports : CentresOver (phaseLevel W H) T
  nativeStages : ∃ I : Type, TerminalWindowsRemembering True I (canonicalInvariant n) T W (phaseLevel W H) E H
  nonincrease : ∀ z ℓ, HS[strictTransform n T.proj W] z ℓ ≤ HS[W] (T.proj z) ℓ
  strictDrop : ∀ z ∈ T.proj ⁻¹' phaseLevel W H, toLex (HS[strictTransform n T.proj W] z) < toLex H

/-- The complete phase exposes the original terminal native records
with the previous readout type. -/
theorem ActualNativePhase.native {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y} (h : ActualNativePhase W E H T) :
    ∃ I : Type, TerminalWindows I (canonicalInvariant n) T W (phaseLevel W H) E H := by
  obtain ⟨I,A,hEnd,_⟩ := h.nativeStages
  exact ⟨I,A,hEnd⟩

private theorem terminalWindows_restrictOpen {I Λ : Type} [LinearOrder Λ]
    {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ}
    {T : BlowupTower X Y} {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (hEnd : TerminalWindowsRemembering True I R T W D E H) (O : Opens X) :
    TerminalWindowsRemembering True I R (restrict O T)
      ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H := by
  obtain ⟨A,hA,hSync⟩ := hEnd
  refine ⟨A.restrictAmbient O, (fun i => ?_),?_⟩
  swap
  · exact fun hKeep => A.simultaneous_restrictAmbient R T (fun i => (hA i).1) (hSync hKeep) O
  rw [A.restrictAmbient_powered O i]
  obtain ⟨hDom,hCan,f,_,hCos,_,_⟩ := native_prefix_values_on_shrunk_ambient
    R (A.openSet i) O (A.powered i) (A.powered_domain i) T (hA i).1
  exact ⟨hCan,R.isInvValue.isGeoTestTower_of_isCanonical hDom _ hCan,
    hCos.trans ((congrArg (f ⁻¹' ·) (hA i).2.2).trans preimage_empty)⟩

private theorem phaseLevel_preimage_val (W : Set X) (H : ℕ → ℕ) (O : Opens X) :
    phaseLevel (X := CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W) H =
      (Subtype.val : O → X) ⁻¹' phaseLevel W H := by
  ext y
  change HS[(Subtype.val : O → X) ⁻¹' W] y = H ↔ HS[W] y.val = H
  rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W y)]

/-- The entire certified phase restricts to the literal blowups on any
ambient open, including all possibly empty centre positions. -/
theorem ActualNativePhase.restrictOpen {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y} (h : ActualNativePhase W E H T)
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens X) :
    ActualNativePhase ((Subtype.val : O → X) ⁻¹' W)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H (restrict O T) := by
  have hProfile := phaseLevel_preimage_val W H O
  have hStrict := strictTransform_restricted_tower O T W
  refine ⟨?_,singular_stages_restrict W O T h.singular,?_,?_,?_,?_⟩
  · have hRestricted := MarkedIdealRestrictOpen.isGeoTestTower_restrict O isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) T h.test
    have hPull : MarkedIdeal.pullback (Subtype.val : O → X) (original W E) =
        original (B := CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) := pullback_val_mk_vanishingIdeal O E W
    rw [hPull] at hRestricted
    exact hRestricted
  · rw [hProfile]
    exact centresOver_restrict O _ T h.supports
  · obtain ⟨I,hEnd⟩ := h.nativeStages
    rw [hProfile]
    exact ⟨I,terminalWindows_restrictOpen hEnd O⟩
  · intro z ℓ
    rw [hStrict, hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ z ℓ,
      hilbertSamuelAt_vanishing_actual_open_any O W ((restrict O T).proj z) ℓ, proj_restrict]
    exact h.nonincrease z.val ℓ
  · intro z hz
    rw [hProfile] at hz
    change ((restrict O T).proj z).val ∈ phaseLevel W H at hz
    rw [proj_restrict] at hz
    rw [hStrict, funext (hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ z)]
    exact h.strictDrop z.val hz

/-- Transport a certified phase through the supplied actual isomorphism
of the same towers, keeping all native terminal window certificates. -/
theorem ActualNativePhase.of_isTowerIso {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} (h : ActualNativePhase W E H T)
    (hW : IsComplexAnalyticSubset (n := n) W)
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) :
    ActualNativePhase (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) H T' := by
  have hProfile : phaseLevel (n := n) (φ ⁻¹' W) H = φ ⁻¹' phaseLevel W H := by
    ext z
    change HS[φ ⁻¹' W] z = H ↔ HS[W] (φ z) = H
    rw [funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W z)]
  have hStrict := strictTransform_preimage_of_square φ χ T'.contMDiff_proj T.contMDiff_proj
    W hW.isClosed (fun z => (hIso.proj_comm z).symm)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hRecord : MarkedIdeal.pullback φ (original W E) = original (B := X') (φ ⁻¹' W)
        (E.map (φ ⁻¹' ·)) := by
      change (MarkedIdeal.mk (φ ⁻¹' univ) (E.map (φ ⁻¹' ·))
        (GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) W)) 1 : MarkedIdeal n X') = _
      rw [preimage_univ, pullback_vanishingIdeal_of_biholomorphism]
    rw [← hRecord]
    exact (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) hIso).mpr h.test
  · apply singular_stages_of_tower_iso (φ ⁻¹' W) (hW.isClosed.preimage φ.continuous) φ.symm hIso.symm
    have hDouble : φ.symm ⁻¹' (φ ⁻¹' W) = W := by
      ext z
      change φ (φ.symm z) ∈ W ↔ z ∈ W
      rw [φ.apply_symm_apply]
    rw [hDouble]
    exact h.singular
  · rw [hProfile]
    exact centresOver_of_isTowerIso hIso _ h.supports
  · obtain ⟨I,A,hA,hSync⟩ := h.nativeStages
    rw [hProfile]
    exact ⟨I,A.transportBase φ,(fun i => A.terminal_transportBase φ _ hIso hA i),
      fun hKeep => A.simultaneous_transportBase φ _ hIso (fun i => (hA i).1) (hSync hKeep)⟩
  · intro z ℓ
    rw [hStrict,hilbertSamuelAt_vanishing_actual_biholomorphic_any χ,
      hilbertSamuelAt_vanishing_actual_biholomorphic_any φ,hIso.proj_comm]
    exact h.nonincrease (χ z) ℓ
  · intro z hz
    rw [hProfile] at hz
    change φ (T'.proj z) ∈ phaseLevel W H at hz
    rw [hIso.proj_comm] at hz
    rw [hStrict,funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any χ _ z)]
    exact h.strictDrop (χ z) hz

/-- A genuinely covered native phase has a singular exact level. -/
theorem ActualNativePhase.level_subset_singular {W : Set X} {E : List (Set X)}
    {H : ℕ → ℕ} {T : BlowupTower X Y} (h : ActualNativePhase W E H T) :
    phaseLevel W H ⊆ singularSet (n := n) W := by
  obtain ⟨I,A,_⟩ := h.native
  intro x hx
  obtain ⟨i,hi⟩ := A.covers x hx
  let y : A.openSet i := ⟨x,hi⟩
  have hAt : HS[(Subtype.val : A.openSet i → X) ⁻¹' W] y = H :=
    (funext (hilbertSamuelAt_vanishing_actual_open_any (A.openSet i) W y)).trans hx
  have hy : y ∈ (A.record i).cosupp := by
    rw [(A.native i).cosupp_eq]
    exact fun ℓ => congrFun hAt ℓ
  have h0 := (A.native i).hsTowerState (.refl : BlowupTower (CMfd.of (n := n) (A.openSet i)) _) trivial
  have hS := h0.2.2.2.2 hy
  change y ∈ singularSet (n := n) ((Subtype.val : A.openSet i → X) ⁻¹' W) at hS
  rw [singularSet_preimage_val] at hS
  exact hS

/-- A phase with higher label restricts to an empty tower on a window
whose original singular profile is everywhere strictly below that label. -/
theorem ActualNativePhase.empty_restrict_of_smaller_profile {W : Set X} {E : List (Set X)}
    {H : ℕ → ℕ} {T : BlowupTower X Y} (h : ActualNativePhase W E H T)
    (O : Opens X)
    (hBound : ∀ x ∈ (O : Set X) ∩ singularSet (n := n) W, toLex (HS[W] x) < toLex H) :
    ResolutionInvariantExt.IsEmptyTower (restrict O T) := by
  apply isEmptyTower_restrict_of_centresOver O _ _ h.supports
  apply Set.disjoint_left.mpr
  intro x hx hx'
  exact (hBound x ⟨hx,h.level_subset_singular hx'⟩).ne (congrArg toLex hx')

/-- The compact native producer supplies a complete certificate at its
attained profile on the very same physical tower. -/
theorem exists_actual_native_phase_near_compact (hn : 0 < n)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (K : Set X) (hK : IsCompact K) (a : X) (ha : a ∈ K ∩ singularSet (n := n) W)
    (hMax : ∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex (HS[W] a)) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      ActualNativePhase ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) (HS[W] a) T := by
  obtain ⟨I,U,hKU,Y,T,hTest,hStage,hBound,hDrop,hOver,hNative⟩ :=
    exists_finite_relative_native_phase_with_maximal_stages hn hW E hE hDense K hK a ha hMax
  exact ⟨U,hKU,Y,T,hTest,hStage,hOver,⟨I,hNative⟩,hBound,hDrop⟩

end
end Hironaka.HironakaG8NativePhaseCertificate

import Hironaka.Resolution.HironakaG8LabelledNativeHead
import Hironaka.Resolution.HironakaG8FilteredBoundaryTerminalOverlap
import Hironaka.Resolution.HironakaG8NativeFilteredSimultaneousTerminal
import Hironaka.Resolution.HironakaG8DenseBoundaryRestart
import Hironaka.Resolution.HironakaG3BiholomorphicFirstMeeting

/-! Compare whole labelled finite native histories on their common
saturated open through their retained simultaneous native phases. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LabelledNativeOverlap

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealTowerTransport NormalCrossings ResolutionInvariantSpec CanonicalCentres
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaG8NativePhaseCertificate HironakaG8LabelledNativeHistory HironakaG8LabelledNativeHead
  HironakaG8FilteredBoundaryTerminalOverlap HironakaG8DenseBoundaryRestart
  HironakaG8NativeFilteredSimultaneousTerminal HironakaG8NativeSimultaneousTerminal
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareFilteredBoundary HironakaG3EmptyAwareBornSlots
  HironakaG3BiholomorphicFirstMeeting HironakaG8IntrinsicSingularBlockSchedule
  HironakaNormalCrossingsSeparationChoiceComparison HironakaActualVanishingIntrinsicHSTransport
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG8LocalHistory
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaOriginalCanonicalDimensionList
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaResolutionSpaceLocal RestrictEmptyTower HironakaAdmissibleSequence
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ}

private abbrev original {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

private theorem emptyTower_of_centresOver_empty {X : CMfd.{0} n} :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver ∅ T → IsEmptyTower T
  | _, .refl, _ => trivial
  | _, .step P C π hπ, h => ⟨emptyTower_of_centresOver_empty P h.1,
    eq_empty_of_subset_empty (by simpa only [preimage_empty] using h.2)⟩

private theorem actual_phase_empty_of_lower_bound {X Y : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} {T : BlowupTower X Y} {H : ℕ → ℕ}
    (h : ActualNativePhase W E H T)
    (hBound : ∀ x ∈ singularSet (n := n) W, toLex (HS[W] x) < toLex H) :
    IsEmptyTower T := by
  have hEmpty : phaseLevel W H = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
    (hBound x (h.level_subset_singular hx)).ne (congrArg toLex hx)
  exact emptyTower_of_centresOver_empty T (hEmpty ▸ h.supports)

private theorem singular_tower_empty_of_smooth_source {X Y : CMfd.{0} n}
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower n W E K T L) (hSmooth : IsClosedSubmanifold n W) :
    IsEmptyTower T := by
  have hEmpty : singularSet (n := n) W = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxW,hxSing⟩ := mem_singularSet_iff.mp hx
    obtain ⟨d,hd⟩ := hSmooth.2 x hxW
    exact hxSing d hd
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,
    (isClosed_singularSet h.source_analytic.isClosed).isOpen_compl⟩
  have hOver : CentresOver (singularSet (n := n) W) T := by
    simpa [O] using centresOver_compl_of_centresAvoid O T
      (intrinsic_singular_history_avoids_regular_open h.source_analytic O disjoint_compl_right
        T h.test_and_singular.2)
  exact emptyTower_of_centresOver_empty T (hEmpty ▸ hOver)

private theorem transfer_singular_upper_bound {X X' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} (hCarrier : W' = φ ⁻¹' W) {H : ℕ → ℕ}
    (hBound : ∀ x ∈ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex H) :
    ∀ x ∈ singularSet (n := n) W', toLex (HS[W'] x) ≤ toLex H := by
  subst W'
  intro x hx
  rw [singularSet_preimage_eq (isSubmersion_biholomorphism φ)] at hx
  rw [funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W x)]
  exact hBound (φ x) hx

private theorem simultaneous_same_profile_compare {X X' Y Y' : CMfd.{0} n} (hn : 0 < n)
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')} {H : ℕ → ℕ}
    {P : BlowupTower X Y} {P' : BlowupTower X' Y'}
    (hW' : IsComplexAnalyticSubset (n := n) W') (hW : IsComplexAnalyticSubset (n := n) W)
    (hE' : IsSNCDivisor n E') (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B))
    (hCarrier : W' = φ ⁻¹' W)
    (hE : E'.filter (fun B => decide B.Nonempty) = (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hPhase' : ActualNativePhase W' E' H P') (hPhase : ActualNativePhase W E H P) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, EmptyAwareTowerIso φ P' P χ := by
  let tr := transport φ P
  have hTr := transport_isTowerIso φ P
  have hAligned := hPhase.of_isTowerIso hW hTr
  rw [← hCarrier] at hAligned
  obtain ⟨I,A,hEndA,hSyncA⟩ := hPhase'.nativeStages
  obtain ⟨J,B,hEndB,hSyncB⟩ := hAligned.nativeStages
  have hNon := boundary_noncontainment_at_current_singular_of_dense_complement hn hW' E' hE' hDense'
    (BlowupTower.refl : BlowupTower X' X') trivial trivial
  have hNot : ∀ B ∈ E', ∀ x ∈ singularSet (n := n) W', x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ W' := by
    simpa only [geoTransformAlong_refl,BlowupTower.proj_refl,strictTransform_id hW'.isClosed] using hNon
  have hLevel : phaseLevel W' H = {x | ∀ ℓ, HS[W'] x ℓ = H ℓ} := by
    ext x
    exact ⟨fun hx ℓ => congrFun hx ℓ,fun hx => funext hx⟩
  have hActiveNot : ∀ B ∈ E', ∀ x ∈ phaseLevel W' H, x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ W' :=
    fun B hB x hx => hNot B hB x (hPhase'.level_subset_singular hx)
  have hTerminalA : NativeSynchronizedTerminal A P' :=
    ⟨hPhase'.test,hPhase'.singular,fun i => (hEndA i).1,hSyncA trivial,fun i => (hEndA i).2.2⟩
  have hTerminalB : NativeSynchronizedTerminal B tr.tower :=
    ⟨hAligned.test,hAligned.singular,fun i => (hEndB i).1,hSyncB trivial,fun i => (hEndB i).2.2⟩
  obtain ⟨χ,hMatch⟩ := native_simultaneous_terminal_emptyAware_of_filtered_boundary hn hW' hE'
    hLevel hActiveNot hE hTerminalA hTerminalB
  refine ⟨χ.trans tr.back,?_⟩
  simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans
    hMatch (emptyAware_of_isTowerIso hTr)

/-- An actual prefix comparison carries the strict carriers, nonempty
ordered boundaries and dense complements into the next phase. -/
theorem aligned_after_prefixes {X X' Y Y' : CMfd.{0} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    {P : BlowupTower X Y} {P' : BlowupTower X' Y'}
    (hW' : IsComplexAnalyticSubset (n := n) W') (hW : IsComplexAnalyticSubset (n := n) W)
    (hE' : IsSNCDivisor n E') (hE : IsSNCDivisor n E)
    (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B)) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (hCarrier : W' = φ ⁻¹' W)
    (hBoundary : E'.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hTest' : IsGeoTestTower (original W' E') P') (hTest : IsGeoTestTower (original W E) P)
    (hSing' : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W')) P')
    (hSing : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) P)
    (hIso : EmptyAwareTowerIso φ P' P ψ) :
    let A' := strictTransform n P'.proj W'
    let A := strictTransform n P.proj W
    let F' := (geoTransformAlong (original W' E') P').E
    let F := (geoTransformAlong (original W E) P).E
    A' = ψ ⁻¹' A ∧ F'.filter (fun B => decide B.Nonempty) =
      (F.map (ψ ⁻¹' ·)).filter (fun B => decide B.Nonempty) ∧
    A' ⊆ closure (A' \ ⋃ B ∈ F', B) ∧ A ⊆ closure (A \ ⋃ B ∈ F, B) := by
  have hStrict : strictTransform n P'.proj W' = ψ ⁻¹' strictTransform n P.proj W := by
    rw [hCarrier]
    exact strictTransform_preimage_of_square φ ψ P'.contMDiff_proj P.contMDiff_proj
      W hW.isClosed (emptyAware_proj_comm hIso)
  have hFilter := full_boundary_transport_of_filtered_initial hIso (original W' E') (original W E) hBoundary hE.1
  rw [← filter_map_bijection ψ ψ.surjective] at hFilter
  exact ⟨hStrict,hFilter,
    strict_transform_dense_off_accumulated_boundary hW' E' hE' hDense' P' hTest' hSing',
    strict_transform_dense_off_accumulated_boundary hW E hE hDense P hTest hSing⟩

/-- Compose an empty-aware comparison with two actual factorizations. -/
theorem compare_from_factors {X X' A A' Y Y' : CMfd.{0} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {P : BlowupTower X A} {P' : BlowupTower X' A'}
    {e : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {e' : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A'}
    {ψ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    (h₀ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X' ∞) T' P' e')
    (h₁ : EmptyAwareTowerIso φ P' P ψ)
    (h₂ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T P e) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ := by
  refine ⟨e'.trans (ψ.trans e.symm), ?_⟩
  have hc := HironakaG3EmptyAwareComposition.trans (emptyAware_of_isTowerIso h₀)
    (HironakaG3EmptyAwareComposition.trans h₁ (emptyAware_of_isTowerIso h₂.symm))
  simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using hc

/-- Compare whole labelled histories already restricted to their common
task. Unequal highest phases disappear there; equal phases compare by
their simultaneous native window certificates. -/
theorem labelled_native_history_overlap (hn : 0 < n)
    {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    (hCarrier : W' = φ ⁻¹' W)
    (hBoundary : E'.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B)) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L L' : List (ℕ → ℕ)}
    (hLeft : LabelledNativeTower n W' E' univ T' L') (hRight : LabelledNativeTower n W E univ T L) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ := by
  have go : ∀ m : ℕ, ∀ {X X' Y Y' : CMfd.{0} n}
      (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
      {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')},
      W' = φ ⁻¹' W →
      E'.filter (fun B => decide B.Nonempty) = (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty) →
      W' ⊆ closure (W' \ ⋃ B ∈ E', B) → W ⊆ closure (W \ ⋃ B ∈ E, B) →
      ∀ {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L L' : List (ℕ → ℕ)},
        LabelledNativeTower n W' E' univ T' L' → LabelledNativeTower n W E univ T L →
        L'.length + L.length ≤ m →
        ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro X X' Y Y' φ W W' E E' hCarrier hBoundary hDense' hDense T T' L L' hLeft hRight hSize
      have hWL := hLeft.source_analytic
      have hWR := hRight.source_analytic
      have hEL := hLeft.source_snc
      have hER := hRight.source_snc
      cases L' with
      | nil =>
        have hSmoothL := (finished_of_empty_labels hLeft rfl).2
        have hSmoothR := (isClosedSubmanifold_preimage_iff φ).mp (hCarrier ▸ hSmoothL)
        exact emptyAware_of_empty_towers φ T' T (singular_tower_empty_of_smooth_source hLeft hSmoothL)
          (singular_tower_empty_of_smooth_source hRight hSmoothR)
      | cons H' L' =>
        cases L with
        | nil =>
          have hSmoothR := (finished_of_empty_labels hRight rfl).2
          have hSmoothL := hCarrier.symm ▸ (isClosedSubmanifold_preimage_iff φ).mpr hSmoothR
          exact emptyAware_of_empty_towers φ T' T (singular_tower_empty_of_smooth_source hLeft hSmoothL)
            (singular_tower_empty_of_smooth_source hRight hSmoothR)
        | cons H L =>
          obtain ⟨A',Z',P',Q',e',hPhase',hTop',_,hTail',hFactor'⟩ := exists_head_phase hLeft H' L' rfl
          obtain ⟨A,Z,P,Q,e,hPhase,hTop,_,hTail,hFactor⟩ := exists_head_phase hRight H L rfl
          simp only [univ_inter,preimage_univ] at hTop' hTop hTail' hTail
          rcases lt_trichotomy (toLex H') (toLex H) with hSmall | hEqual | hLarge
          · have hCarrierInv : W = φ.symm ⁻¹' W' := by
              rw [hCarrier,symm_preimage_preimage φ W]
            have hTooSmall := transfer_singular_upper_bound φ.symm hCarrierInv hTop'
            have hEmpty := actual_phase_empty_of_lower_bound hPhase (fun x hx => (hTooSmall x hx).trans_lt hSmall)
            obtain ⟨ψ,hPrefix⟩ := emptyAware_of_empty_towers φ (BlowupTower.refl : BlowupTower X' X') P trivial hEmpty
            obtain ⟨hc,hE,hDL,hDR⟩ := aligned_after_prefixes (P' := (BlowupTower.refl : BlowupTower X' X')) hWL hWR hEL hER hDense' hDense
              hCarrier hBoundary trivial hPhase.test trivial hPhase.singular hPrefix
            have hKeep : LabelledNativeTower n (strictTransform n (BlowupTower.refl : BlowupTower X' X').proj W')
                (geoTransformAlong (original W' E') (BlowupTower.refl : BlowupTower X' X')).E univ T' (H' :: L') := by
              simpa only [BlowupTower.proj_refl,strictTransform_id hWL.isClosed,geoTransformAlong_refl] using hLeft
            have hSmaller : (H' :: L').length + L.length < m := by simp only [List.length_cons] at hSize ⊢; omega
            obtain ⟨χ,hPost⟩ := ih _ hSmaller ψ hc hE hDL hDR hKeep hTail le_rfl
            have hBody : EmptyAwareTowerIso φ T' (P.append Q) χ := by
              simpa only [BlowupTower.refl_append] using emptyAware_append_same_base_transport hPrefix hPost
            exact compare_from_factors (IsTowerIso.refl_self T') hBody hFactor
          · have hLabels : H' = H := congrArg ofLex hEqual
            subst H'
            obtain ⟨ψ,hPrefix⟩ := simultaneous_same_profile_compare hn φ hWL hWR hEL hDense'
              hCarrier hBoundary hPhase' hPhase
            obtain ⟨hc,hE,hDL,hDR⟩ := aligned_after_prefixes hWL hWR hEL hER hDense' hDense
              hCarrier hBoundary hPhase'.test hPhase.test hPhase'.singular hPhase.singular hPrefix
            have hSmaller : L'.length + L.length < m := by simp only [List.length_cons] at hSize; omega
            obtain ⟨χ,hPost⟩ := ih _ hSmaller ψ hc hE hDL hDR hTail' hTail le_rfl
            exact compare_from_factors hFactor' (emptyAware_append_same_base_transport hPrefix hPost) hFactor
          · have hTooSmall := transfer_singular_upper_bound φ hCarrier hTop
            have hEmpty := actual_phase_empty_of_lower_bound hPhase' (fun x hx => (hTooSmall x hx).trans_lt hLarge)
            obtain ⟨ψ,hPrefix⟩ := emptyAware_of_empty_towers φ P' (BlowupTower.refl : BlowupTower X X) hEmpty trivial
            obtain ⟨hc,hE,hDL,hDR⟩ := aligned_after_prefixes (P := (BlowupTower.refl : BlowupTower X X)) hWL hWR hEL hER hDense' hDense
              hCarrier hBoundary hPhase'.test trivial hPhase'.singular trivial hPrefix
            have hKeep : LabelledNativeTower n (strictTransform n (BlowupTower.refl : BlowupTower X X).proj W)
                (geoTransformAlong (original W E) (BlowupTower.refl : BlowupTower X X)).E univ T (H :: L) := by
              simpa only [BlowupTower.proj_refl,strictTransform_id hWR.isClosed,geoTransformAlong_refl] using hRight
            have hSmaller : L'.length + (H :: L).length < m := by simp only [List.length_cons] at hSize ⊢; omega
            obtain ⟨χ,hPost⟩ := ih _ hSmaller ψ hc hE hDL hDR hTail' hKeep le_rfl
            have hBody : EmptyAwareTowerIso φ (P'.append Q') T χ := by
              simpa only [BlowupTower.refl_append] using emptyAware_append_same_base_transport hPrefix hPost
            exact compare_from_factors hFactor' hBody (IsTowerIso.refl_self T)
  exact go (L'.length + L.length) φ hCarrier hBoundary hDense' hDense hLeft hRight le_rfl

end
end Hironaka.HironakaG8LabelledNativeOverlap

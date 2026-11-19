import Hironaka.Resolution.HironakaActualSmoothCleanupPhysicalComparison
import Hironaka.Resolution.HironakaG8DisjointPhaseMerge
import Hironaka.Resolution.HironakaG3EmptyAwareFilteredBoundary
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaSharpActualFiniteChronologicalHistory
import Hironaka.Resolution.HironakaG4BoundaryRestrict
import Hironaka.Resolution.HironakaActualGeometricCleanupComposition

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG8OrderedSmoothSuffix

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts HironakaOriginalCanonicalDimensionList
  HironakaActualSmoothBoundaryCleanup HironakaActualSmoothCleanupPhysicalComparison
  HironakaSharpActualFiniteChronologicalHistory HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareFilteredBoundary HironakaG3EmptyAwareBornSlots
  HironakaSharpActualCurveComparisonRestriction HironakaNormalCrossingsOpenRestrictionSeparation
  NormalCrossingsInvariance MarkedIdealBiholomorphism MarkedIdealTowerTransport

/-- One actual smooth cleanup rank with the retained pure stopping certificate, or the literal
identity at ambient rank. -/
inductive SmoothRankPhase {n : ℕ} {X : CMfd.{u} n} (W : Set X) (E : List (Set X))
    (hE : IsSNCDivisor n E) (d : Fin (n + 1)) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | proper {Y : CMfd.{u} n} {T : BlowupTower X Y}
      (hd : (d : ℕ) < n) (hA : IsClosedSubmanifold n (dimensionPart (n := n) W d))
      (hPure : ∀ x ∈ dimensionPart (n := n) W d, RegularAtDim (n := n) (dimensionPart (n := n) W d) x d)
      (hDense : dimensionPart (n := n) W d ⊆ closure (dimensionPart (n := n) W d \ ⋃ H ∈ E, H))
      (h : ActualSmoothBoundaryCleanupResult (dimensionPart (n := n) W d) E d hE T) :
      SmoothRankPhase W E hE d T
  | ambient (hd : (d : ℕ) = n) : SmoothRankPhase W E hE d (.refl : BlowupTower X X)

/-- The actual towers of each rank are retained inside their exact concatenation. The suffix
updates the unprocessed closed carrier and the full ordered boundary after each rank. -/
inductive OrderedSmoothSuffix {n : ℕ} : (ranks : List (Fin (n + 1))) →
    {X Y : CMfd.{u} n} → Set X → List (Set X) → BlowupTower X Y → Prop
  | nil {X : CMfd.{u} n} (W : Set X) (E : List (Set X)) :
      OrderedSmoothSuffix [] W E (.refl : BlowupTower X X)
  | cons {d : Fin (n + 1)} {ds : List (Fin (n + 1))} {X Y Z V : CMfd.{u} n}
      {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {Q : BlowupTower Y Z}
      {T : BlowupTower X V} {η : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
      (hE : IsSNCDivisor n E) (hRem : IsClosed (W \ dimensionPart (n := n) W d))
      (head : SmoothRankPhase W E hE d P)
      (tail : OrderedSmoothSuffix ds (strictTransform n P.proj (W \ dimensionPart (n := n) W d))
        (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E Q)
      (iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T (P.append Q) η) :
      OrderedSmoothSuffix (d :: ds) W E T

/-- Every compact window uses the same increasing list of ambient ranks, including absent ranks. -/
abbrev AscendingSmoothSuffix {n : ℕ} {X Y : CMfd.{u} n} (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) : Prop :=
  OrderedSmoothSuffix (List.finRange (n + 1)) W E T

private theorem dimensionPart_pullback {n : ℕ} {X' X : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (W : Set X) (d : ℕ) :
    dimensionPart (n := n) (Φ ⁻¹' W) d = Φ ⁻¹' dimensionPart (n := n) W d := by
  simpa only [Nat.sub_self, Nat.add_zero] using
    dimensionPart_preimage_eq_shift
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) W d

/-- A specified rank compares across distinct base charts and empty original boundary slots. -/
theorem smooth_rank_emptyAware {n : ℕ} {X' X Y' Y : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} {E' : List (Set X')}
    {hE : IsSNCDivisor n E} {hE' : IsSNCDivisor n E'} {d : Fin (n + 1)}
    {P' : BlowupTower X' Y'} {P : BlowupTower X Y}
    (hB : E'.filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (h' : SmoothRankPhase (Φ ⁻¹' W) E' hE' d P') (h : SmoothRankPhase W E hE d P) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso Φ P' P ψ := by
  have hp := dimensionPart_pullback Φ W d
  cases h with
  | proper hd hA hPure hDense hP =>
    cases h' with
    | proper hd' hA' hPure' hDense' hP' =>
      rw [hp] at hA' hPure' hDense' hP'
      exact actual_smooth_cleanup_emptyAware_over_filtered_boundary Φ hA hA' hd hPure hPure'
        hE hE' hDense hDense' hB P' P hP' hP
    | ambient hd' => exact (Nat.ne_of_lt hd hd').elim
  | ambient hd =>
    cases h' with
    | proper hd' _ _ _ _ => exact (Nat.ne_of_lt hd' hd).elim
    | ambient _ => exact ⟨Φ, .refl⟩

/-- Actual rank-by-rank comparisons give one empty-aware comparison of the entire supplied
ordered smooth suffixes. The base map can be the comparison of the preceding singular prefixes. -/
theorem ordered_smooth_suffix_emptyAware {n : ℕ} {X' X Z' Z : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {ds : List (Fin (n + 1))} {W : Set X} {E : List (Set X)} {E' : List (Set X')}
    {T' : BlowupTower X' Z'} {T : BlowupTower X Z}
    (hB : E'.filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (h' : OrderedSmoothSuffix ds (Φ ⁻¹' W) E' T') (h : OrderedSmoothSuffix ds W E T) :
    ∃ ψ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso Φ T' T ψ := by
  induction h generalizing X' Z' with
  | nil W E =>
    cases h'
    exact ⟨Φ, .refl⟩
  | @cons d ds X Y Z V W E P Q T η hE hRem hP hQ hIso ih =>
    cases h' with
    | @cons _ _ _ Y' _ _ _ _ P' Q' _ η' hE' _ hP' hQ' hIso' =>
      obtain ⟨β, hβ⟩ := smooth_rank_emptyAware Φ hB hP' hP
      have hCarrier :
          strictTransform n P'.proj ((Φ ⁻¹' W) \ dimensionPart (n := n) (Φ ⁻¹' W) d) =
            β ⁻¹' strictTransform n P.proj (W \ dimensionPart (n := n) W d) := by
        rw [dimensionPart_pullback Φ W d, ← preimage_sdiff]
        exact HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
          Φ β P'.contMDiff_proj P.contMDiff_proj _ hRem (emptyAware_proj_comm hβ)
      have hBInitial : E'.filter (fun H => decide H.Nonempty) =
          (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
        rw [filter_map_bijection Φ Φ.surjective]
        exact hB
      let M' : MarkedIdeal n X' := geometricTemplate (univ : Set X') E'
      let M : MarkedIdeal n X := geometricTemplate (univ : Set X) E
      have hClosed : ∀ H ∈ M.E, IsClosed H := hE.1
      have hBNext := full_boundary_transport_of_filtered_initial hβ M' M hBInitial hClosed
      rw [hCarrier] at hQ'
      obtain ⟨ψ, hψ⟩ := ih β hBNext hQ'
      refine ⟨η'.trans (ψ.trans η.symm), ?_⟩
      simpa only [Diffeomorph.symm_refl, Diffeomorph.refl_trans, Diffeomorph.trans_refl] using
        G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hIso')
          (G3UniverseEmptyAwareCore.trans (HironakaG8DisjointPhaseMerge.emptyAware_append hβ hψ)
            (emptyAware_of_isTowerIso hIso.symm))

theorem dimensionPart_restrict {n : ℕ} {X : CMfd.{u} n}
    (U : Opens X) (W : Set X) (d : ℕ) :
    dimensionPart (n := n) ((Subtype.val : U → X) ⁻¹' W) d =
      (Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W d := by
  simpa only [Nat.sub_self, Nat.add_zero] using
    dimensionPart_preimage_eq_shift (X := X) (Y := CMfd.of (n := n) U)
      (HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val U) W d

theorem smooth_rank_restrict {n : ℕ} {X Y : CMfd.{u} n}
    {W : Set X} {E : List (Set X)} {hE : IsSNCDivisor n E} {d : Fin (n + 1)}
    {P : BlowupTower X Y} (h : SmoothRankPhase W E hE d P) (U : Opens X)
    (hEU : IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·))) :
    SmoothRankPhase ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))
      hEU d (restrict U P) := by
  cases h with
  | ambient hd => exact .ambient hd
  | proper hd hA hPure hDense hP =>
    obtain ⟨_, hPU⟩ := actual_smooth_cleanup_restrict hA hd hPure hE hDense P hP U
    have hPart := dimensionPart_restrict U W d
    apply SmoothRankPhase.proper hd
    · rw [hPart]
      exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val hA U
    · rw [hPart]
      intro x hx
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hPure x.val hx)
    · rw [hPart]
      exact HironakaOriginalSmoothIntrinsicRegularLoci.boundary_density_preimage
        (HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val U) _ _ hDense
    · rw [hPart]
      exact hPU

/-- The decomposition on a common open comes from the actual restriction and retains the complete
ordered boundary on every constituent phase. -/
theorem ordered_smooth_suffix_restrict {n : ℕ} {X Y : CMfd.{u} n}
    {ds : List (Fin (n + 1))} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : OrderedSmoothSuffix ds W E T) : ∀ U : Opens X,
    OrderedSmoothSuffix ds ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))
      (restrict U T) := by
  induction h with
  | nil W E => intro U; exact .nil _ _
  | @cons d ds X Y Z V W E P Q T η hE hRem hP hQ hIso ih =>
    intro U
    let A := CMfd.of (n := n) U
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let WU : Set A := (Subtype.val : U → X) ⁻¹' W
    let J := openPreimage P U
    let L := restrict U P
    have hEU : IsSNCDivisor n EU :=
      isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
    have hRemU : WU \ dimensionPart (n := n) WU d =
        (Subtype.val : U → X) ⁻¹' (W \ dimensionPart (n := n) W d) := by
      exact (congrArg (fun B => WU \ B) (dimensionPart_restrict U W d)).trans (preimage_sdiff (Subtype.val : U → X) W (dimensionPart (n := n) W d)).symm
    have hCarrier :
        strictTransform n L.proj (WU \ dimensionPart (n := n) WU d) =
          (Subtype.val : J → Y) ⁻¹' strictTransform n P.proj (W \ dimensionPart (n := n) W d) := by
      rw [hRemU]
      exact strictTransform_restricted_tower U P _
    have hB :
        (geoTransformAlong (geometricTemplate (univ : Set A) EU) L).E =
          (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E.map
            ((Subtype.val : J → Y) ⁻¹' ·) :=
      (HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
        (𝔍 := geometricTemplate (univ : Set A) EU)
        (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate (univ : Set X) E)) rfl L).trans
        (HironakaG4BoundaryRestrict.boundary_geoTransformAlong_restrict
          (geometricTemplate (univ : Set X) E) U P)
    have hTail := ih J
    have hIsoU := IsTowerIso.open_restriction hIso U
    have hSplit := BlowupTowerIsoTail.isTowerIso_restrict_append U P Q
    have hOutIso := BlowupTowerSplitIso.IsTowerIso.congr_base (hIsoU.trans hSplit)
      (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) fun _ => rfl
    refine .cons (P := L) (Q := restrict J Q) hEU ?_ (smooth_rank_restrict hP U hEU) ?_ hOutIso
    · rw [hRemU]
      exact hRem.preimage continuous_subtype_val
    · rw [hCarrier, hB]
      exact hTail

private theorem smooth_rank_transport {n : ℕ} {X' X Y : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} {hE : IsSNCDivisor n E} {d : Fin (n + 1)}
    {P : BlowupTower X Y} (h : SmoothRankPhase W E hE d P)
    (hE' : IsSNCDivisor n (E.map (Φ ⁻¹' ·))) :
    SmoothRankPhase (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) hE' d (transport Φ P).tower := by
  cases h with
  | ambient hd => exact .ambient hd
  | proper hd hA hPure hDense hP =>
    obtain ⟨_, hP'⟩ := actual_smooth_cleanup_transport Φ hA hd hPure hE hDense P hP
    apply SmoothRankPhase.proper hd
    · rw [dimensionPart_pullback Φ W d]
      exact (isClosedSubmanifold_preimage_iff Φ).mpr hA
    · rw [dimensionPart_pullback Φ W d]
      intro x hx
      exact (CodimOnePartCanonical.regularAtDim_preimage_iff Φ).mpr (hPure (Φ x) hx)
    · rw [dimensionPart_pullback Φ W d]
      exact HironakaOriginalSmoothIntrinsicRegularLoci.boundary_density_preimage
        (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) _ _ hDense
    · rw [dimensionPart_pullback Φ W d]
      exact hP'

private theorem smooth_rank_test {n : ℕ} {X Y : CMfd.{u} n}
    {W : Set X} {E : List (Set X)} {hE : IsSNCDivisor n E} {d : Fin (n + 1)}
    {P : BlowupTower X Y} (h : SmoothRankPhase W E hE d P) :
    IsGeoTestTower (geometricTemplate (univ : Set X) E) P := by
  cases h with
  | ambient _ => trivial
  | proper _ _ _ _ hP =>
    exact HironakaActualGeometricCleanupComposition.geometric_test_of_test
      (actualSmoothBoundaryMarked (dimensionPart (n := n) W d) E) E (.refl E) P hP.2.1

/-- A strict tower isomorphism on the full chart preserves all ranked certificates over the
literal pulled-back carrier and full boundary records. -/
theorem ordered_smooth_suffix_of_isTowerIso {n : ℕ} {X Y : CMfd.{u} n}
    {ds : List (Fin (n + 1))} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    (h : OrderedSmoothSuffix ds W E T) {X' Y' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso Φ T' T χ) :
    OrderedSmoothSuffix ds (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) T' := by
  induction h generalizing X' Y' with
  | nil W E =>
    cases hIso
    exact .nil _ _
  | @cons d ds X Y Z V W E P Q T η hE hRem hP hQ hSplit ih =>
    let P' := transport Φ P
    let Q' := transport P'.back Q
    let W' : Set X' := Φ ⁻¹' W
    let E' : List (Set X') := E.map (Φ ⁻¹' ·)
    let M : MarkedIdeal n X := geometricTemplate (univ : Set X) E
    let M' : MarkedIdeal n X' := geometricTemplate (univ : Set X') E'
    have hE' : IsSNCDivisor n E' :=
      isSNCDivisor_map_preimage (pullsBackCoordinates Φ) Φ.continuous hE
    have hRem' : W' \ dimensionPart (n := n) W' d = Φ ⁻¹' (W \ dimensionPart (n := n) W d) := by
      rw [show W' = Φ ⁻¹' W from rfl, dimensionPart_pullback Φ W d, preimage_sdiff]
    have hHeadIso := transport_isTowerIso Φ P
    have hQIso := transport_isTowerIso P'.back Q
    have hCarrier :
        strictTransform n P'.tower.proj (W' \ dimensionPart (n := n) W' d) =
          P'.back ⁻¹' strictTransform n P.proj (W \ dimensionPart (n := n) W d) := by
      rw [hRem']
      exact HironakaNormalCrossingsSeparationChoiceComparison.strictTransform_preimage_of_square
        Φ P'.back P'.tower.contMDiff_proj P.contMDiff_proj _ hRem (fun z => (hHeadIso.proj_comm z).symm)
    have hB : (geoTransformAlong M' P'.tower).E =
        (geoTransformAlong M P).E.map (P'.back ⁻¹' ·) := by
      have hh := hHeadIso.geoTransformAlong_eq Φ HomogenizedGlueingTower.isClosedSubmanifold_univ
        IdealWeightPowers.isCoherent_unitIdeal (smooth_rank_test hP)
      have hr := HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
        (𝔍 := M') (𝔪 := MarkedIdeal.pullback Φ M) rfl P'.tower
      exact hr.trans (congrArg MarkedIdeal.E hh)
    have hTail := ih P'.back hQIso
    have hAppend := hHeadIso.append hQIso
    have hOutIso := BlowupTowerSplitIso.IsTowerIso.congr_base ((hIso.trans hSplit).trans hAppend.symm)
      (Φ' := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X' ∞) (fun x => (Φ.symm_apply_apply x).symm)
    refine .cons (P := P'.tower) (Q := Q'.tower) hE' ?_ (smooth_rank_transport Φ hP hE') ?_ hOutIso
    · rw [hRem']
      exact hRem.preimage Φ.continuous
    · rw [hCarrier, hB]
      exact hTail

end
end Hironaka.HironakaG8OrderedSmoothSuffix

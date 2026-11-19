import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCanonicalOpenRestriction
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumAdmissibleLevels
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumStepDrop
import Hironaka.Resolution.HironakaLocalPrincipalization

/-!
# Finite prescribed-H canonical resolutions near compact sets

The natural input is original native M-domain, the SAME prescribed-H
adaptation and a compact K. WHOLE cosupport, X, N and H need not be compact.
Properness makes only the current cosupport over K compact. Its attained
NEW maximum, native USC and proper closed-image shrinking give a genuine
whole maximum on an actual open. Its actual blowup strictly lowers all
new values; well-founded induction on WithTop of the NEW value constructs
a finite history. Every shrink keeps the full accumulated history.

Actual nested-open biholomorphisms transport the WHOLE native marked
record and literal preimage H. Target raw CAN and ALLbranch/terminal pair
are internal outputs. There is no H-free Seq replacement, compact-cosupp
fiction after restriction, nonempty-head rebase or infinite intersection.

Mathematics/API first: work/hironaka-g9-marked-stratum-local-driver-20261024/
(math cffcf29f, complete real API a973af6e). SOURCE ONLY: no Lean/kernel
check, Blueprint credit, public principalization/embedded output, G3
global scheduler or complete original G9 closure is asserted.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCMarkedStratumLocalDriver

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen ResolutionDriver ResolutionInvariantOrder ResolutionInvariantDriver
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalNCMarkedStratumNaturality HironakaOriginalNCMarkedStratumNativeFields
  HironakaOriginalNCMarkedStratumAdmissibleLevels HironakaOriginalNCMarkedStratumStepDrop
  HironakaOriginalNCMarkedStratumCanonicalOpenRestriction
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ}

/-- Raw NEW canonicality through a GIVEN actual tower isomorphism. The
source prefix CAN, not an assumed target CAN, supplies every value field. -/
private theorem canonical_of_given_towerIso {X X' : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) :
    IsCanonical M (markedStratumHistoryValue M H) T →
      IsCanonical (MarkedIdeal.pullback φ M)
        (markedStratumHistoryValue (MarkedIdeal.pullback φ M) (φ ⁻¹' H)) T' := by
  induction hIso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hIso C' π' hπ' C π hπ χ₁ hComm hC ih =>
    intro hCan
    obtain ⟨hT, hCc⟩ : IsCanonical M (markedStratumHistoryValue M H) T ∧
        (C = ∅ ∨ C = maxLocus (markedStratumHistoryValue M H T)
          (geoTransformAlong M T).cosupp) := hCan
    have hTest : IsGeoTestTower M T :=
      (markedStratum_canonical_history_joint_interpretation M hM h T hT).1
    show IsCanonical (MarkedIdeal.pullback φ M)
        (markedStratumHistoryValue (MarkedIdeal.pullback φ M) (φ ⁻¹' H)) T' ∧
      (C' = ∅ ∨ C' = maxLocus
        (markedStratumHistoryValue (MarkedIdeal.pullback φ M) (φ ⁻¹' H) T')
        (geoTransformAlong (MarkedIdeal.pullback φ M) T').cosupp)
    refine ⟨ih hT, ?_⟩
    subst hC
    rcases hCc with rfl | rfl
    · exact Or.inl preimage_empty
    · right
      rw [IsTowerIso.cosupp_geoTransformAlong φ hM.isWellFormed.isClosedSubmanifold_N
        hM.isWellFormed.isCoherent hIso hTest]
      exact (ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective
        (fun p hp => markedStratum_history_value_towerIso M hM h φ T' T χ hIso hT p hp)).symm

/-- The entire computed maximum is admissible by the true all-open level
field; native testness/coherence are internally produced from source CAN. -/
private theorem whole_maximum_admissible {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    (geoTransformAlong M T).IsAdmissibleCentre
      (maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp) := by
  by_cases hNe : (maxLocus (markedStratumHistoryValue M H T)
      (geoTransformAlong M T).cosupp).Nonempty
  · obtain ⟨x, hx⟩ := hNe
    have hLevel := markedStratum_history_value_levels_admissible M hM h T hCan
      ⊤ (markedStratumHistoryValue M H T x) (fun y hy _ => hx.2 y hy)
    rw [← maxLocus_eq_level hx] at hLevel
    have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCurrent.isWellFormed.isCoherent hg) hLevel
  · rw [Set.not_nonempty_iff_eq_empty.mp hNe]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- The actual nested open change transports BOTH the whole native datum
and literal prescribed H, and retains the given accumulated finite tower. -/
private theorem flatten_nested_resolution {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (A : Opens X) (B : Opens (CMfd.of (n := n) A)) (D : Opens X)
    (hBD : ∀ q : A, q ∈ B ↔ (q : X) ∈ D) (hDA : D ≤ A)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) B) Y)
    (hCan : IsCanonical
      (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → X) M))
      (markedStratumHistoryValue
        (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → X) M))
        ((Subtype.val : B → A) ⁻¹' ((Subtype.val : A → X) ⁻¹' H))) T)
    (hRes : IsGeoResolution
      (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → X) M)) T) :
    ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) D) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : D → X) M)
        (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : D → X) M)
          ((Subtype.val : D → X) ⁻¹' H)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : D → X) M) T' := by
  have hMA := InvDomainTowerAlong.isInvDomain_pullback_val A hM
  have hMB := InvDomainTowerAlong.isInvDomain_pullback_val B hMA
  have hHA := boundaryAdapted_open A h
  have hHB := boundaryAdapted_open B hHA
  let φ := (MaxLocusLocal.nestedDiffeo (n := n) A B D hBD hDA).symm
  have hIso := transport_isTowerIso φ T
  have hRes' := (IsTowerIso.isGeoResolution_iff φ
    hMB.isWellFormed.isClosedSubmanifold_N hMB.isWellFormed.isCoherent hIso).mpr hRes
  have hCan' := canonical_of_given_towerIso
    (X := CMfd.of (n := n) B)
    (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → X) M))
    hMB hHB φ hIso hCan
  have hWhole := HironakaLocalPrincipalization.pullback_symm_nestedDiffeo
    (𝔫 := M) hM.isWellFormed.isCoherent A B D hBD hDA
  have hH : φ ⁻¹' ((Subtype.val : B → A) ⁻¹' ((Subtype.val : A → X) ⁻¹' H)) =
      (Subtype.val : D → X) ⁻¹' H := by
    ext x
    rfl
  change MarkedIdeal.pullback φ
    (MarkedIdeal.pullback (Subtype.val : B → A) (MarkedIdeal.pullback (Subtype.val : A → X) M)) =
      MarkedIdeal.pullback (Subtype.val : D → X) M at hWhole
  rw [hWhole, hH] at hCan'
  rw [hWhole] at hRes'
  exact ⟨_, _, hCan', hRes'⟩

/-- If no survivor lies over K, proper closed-image shrinking makes the
SAME actually restricted raw-canonical accumulated tower a resolution. -/
private theorem local_resolution_of_disjoint {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (hNe : ¬ ((geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
        (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
          ((Subtype.val : U → X) ⁻¹' H)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) M) T' := by
  have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest
  have hClosed : IsClosed (geoTransformAlong M T).cosupp :=
    GiraudAlong.isClosed_cosupport_along hCurrent.isWellFormed.isCoherent
      hCurrent.isWellFormed.isClosedSubmanifold_N _
  let O : Opens X := ⟨(T.proj '' (geoTransformAlong M T).cosupp)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hClosed).isOpen_compl⟩
  have hKO : K ⊆ O := by
    rintro x hx ⟨y, hyS, rfl⟩
    exact hNe ⟨y, hyS, hx⟩
  refine ⟨O, hKO, _, restrict O T, markedStratum_canonical_restrictOpen M hM h O T hCan,
    isGeoTestTower_restrict O hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent T hTest, ?_⟩
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent O T hTest]
  refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  exact p.property ⟨p, hp, rfl⟩

/-- A genuine compact part, not the WHOLE cosupport, supplies its attained
maximum. USC plus proper closed-image shrinking bounds the entire actual
restricted cosupport, then a real whole-maximum blowup strictly lowers it. -/
theorem exists_markedStratum_maximum_step_near_compact {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (hK : IsCompact K) (O₀ : Opens X) (hKO₀ : K ⊆ O₀) (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (hNe : ((geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ (z₀ : Y) (hz₀ : z₀ ∈ (geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K)
      (O : Opens X) (hKO : K ⊆ O), O ≤ O₀ ∧
      ∃ (Y₁ : CMfd.{u} n) (C : Set (openPreimage T O)) (π : Y₁ → openPreimage T O)
        (hπ : IsBlowupAlong n C π),
        (⟨z₀, hKO hz₀.2⟩ : openPreimage T O) ∈ C ∧
        let T₁ : BlowupTower (CMfd.of (n := n) O) Y₁ := .step (restrict O T) C π hπ
        IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) M)
          (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : O → X) M)
            ((Subtype.val : O → X) ⁻¹' H)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) M) T₁).cosupp,
          T₁.proj z ∈ (Subtype.val : O → X) ⁻¹' K →
          markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : O → X) M)
            ((Subtype.val : O → X) ⁻¹' H) T₁ z < markedStratumHistoryValue M H T z₀ := by
  have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest
  have hClosed : IsClosed (geoTransformAlong M T).cosupp :=
    GiraudAlong.isClosed_cosupport_along hCurrent.isWellFormed.isCoherent
      hCurrent.isWellFormed.isClosedSubmanifold_N _
  have hCompact : IsCompact ((geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K) :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).inter_left hClosed
  have hUSC := markedStratum_history_value_isInvUSCOn M hM h T hCan
  obtain ⟨z₀, hz₀, hMax⟩ := (hUSC.mono inter_subset_left).exists_isMaxOn hCompact hNe
  refine ⟨z₀, hz₀, ?_⟩
  obtain ⟨W, hWDef⟩ : ∃ W : Set Y,
      W = {y | y ∈ (geoTransformAlong M T).cosupp →
        markedStratumHistoryValue M H T y ≤ markedStratumHistoryValue M H T z₀} := ⟨_, rfl⟩
  have hW : IsOpen W := by
    rw [hWDef, isOpen_iff_mem_nhds]
    intro y hy
    by_cases hyS : y ∈ (geoTransformAlong M T).cosupp
    · filter_upwards [hUSC y hyS] with y' hy' hy'S
      exact (hy' hy'S).trans (hy hyS)
    · filter_upwards [hClosed.isOpen_compl.mem_nhds hyS] with y' hy' hy'S
      exact absurd hy'S hy'
  let O' : Opens X := ⟨(T.proj '' Wᶜ)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hW.isClosed_compl).isOpen_compl⟩
  let O := O' ⊓ O₀
  have hKO : K ⊆ O := by
    intro x hx
    refine ⟨?_, hKO₀ hx⟩
    rintro ⟨y, hyW, rfl⟩
    rw [hWDef] at hyW
    exact hyW fun hyS => hMax y ⟨hyS, hx⟩
  have hOW : ∀ y : Y, T.proj y ∈ O → y ∈ W := fun y hy => by
    by_contra hyW
    exact hy.1 ⟨y, hyW, rfl⟩
  refine ⟨O, hKO, inf_le_right, ?_⟩
  let MO : MarkedIdeal n O := MarkedIdeal.pullback (Subtype.val : O → X) M
  let HO : Set O := (Subtype.val : O → X) ⁻¹' H
  have hMO : IsInvDomain n MO := InvDomainTowerAlong.isInvDomain_pullback_val O hM
  have hHO : IsBoundaryAdaptedCarrier (n := n) HO MO.E := boundaryAdapted_open O h
  have hCanO : IsCanonical MO (markedStratumHistoryValue MO HO) (restrict O T) :=
    markedStratum_canonical_restrictOpen M hM h O T hCan
  have hTestO := (markedStratum_canonical_history_joint_interpretation
    (X := CMfd.of (n := n) O) MO hMO hHO (restrict O T) hCanO).1
  have hCosO : (geoTransformAlong MO (restrict O T)).cosupp =
      (Subtype.val : openPreimage T O → Y) ⁻¹' (geoTransformAlong M T).cosupp :=
    ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent O T hTest
  have hValO : ∀ p ∈ (geoTransformAlong MO (restrict O T)).cosupp,
      markedStratumHistoryValue MO HO (restrict O T) p = markedStratumHistoryValue M H T p.val :=
    fun p hp => markedStratum_history_value_restrictOpen M hM h O T hCan p (by
      rw [hCosO] at hp
      exact hp)
  have hLe : ∀ p ∈ (geoTransformAlong MO (restrict O T)).cosupp,
      markedStratumHistoryValue MO HO (restrict O T) p ≤ markedStratumHistoryValue M H T z₀ := by
    intro p hp
    rw [hValO p hp]
    have hpS : p.val ∈ (geoTransformAlong M T).cosupp := by rw [hCosO] at hp; exact hp
    have hpW := hOW p.val p.property
    rw [hWDef] at hpW
    exact hpW hpS
  have hp₀ : (⟨z₀, hKO hz₀.2⟩ : openPreimage T O) ∈
      (geoTransformAlong MO (restrict O T)).cosupp := by
    rw [hCosO]
    exact hz₀.1
  obtain ⟨C, hCDef⟩ : ∃ C, C = maxLocus (markedStratumHistoryValue MO HO (restrict O T))
      (geoTransformAlong MO (restrict O T)).cosupp := ⟨_, rfl⟩
  have hp₀C : (⟨z₀, hKO hz₀.2⟩ : openPreimage T O) ∈ C := by
    rw [hCDef]
    exact ⟨hp₀, fun p hp => (hLe p hp).trans (hValO _ hp₀).ge⟩
  have hAdm := whole_maximum_admissible (X := CMfd.of (n := n) O) MO hMO hHO (restrict O T) hCanO
  have hInterior := interior_maxLocus_eq_empty hMO (restrict O T) hTestO
    (markedStratumHistoryValue MO HO (restrict O T))
  rw [← hCDef] at hAdm hInterior
  obtain ⟨Z, π, hπ⟩ := exists_blowup C hAdm.1 hInterior
  refine ⟨Z, C, π, hπ, hp₀C, ⟨hCanO, Or.inr hCDef⟩, ?_⟩
  have hCurrentO := InvDomainTowerAlong.isInvDomain_geoTransformAlong hMO (restrict O T) hTestO
  intro z hz _hzK
  have hzS : π z ∈ (geoTransformAlong MO (restrict O T)).cosupp :=
    TransformOffCentre.cosupp_geoTransform_subset_preimage _ hCurrentO.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCurrentO.isWellFormed.isCoherent hg) hπ
      (fun p hp => by rw [hCDef] at hp; exact hp.1) hz
  obtain ⟨hDrop, hEq⟩ := markedStratum_history_value_decrease
    (X := CMfd.of (n := n) O) MO hMO hHO (restrict O T) C π hπ hCanO ⟨_, hp₀C⟩ hCDef z hz
  by_cases hzC : π z ∈ C
  · exact (hDrop hzC).trans_le (hLe _ hzS)
  · rw [hEq hzC]
    refine lt_of_le_of_ne (hLe _ hzS) fun he => hzC ?_
    rw [hCDef]
    exact ⟨hzS, fun p hp => (hLe p hp).trans he.ge⟩

private theorem shrink_step {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (hK : IsCompact K) (T : BlowupTower X Y)
    (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (hNe : ((geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ z₀ ∈ (geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K,
      ∃ O : Opens X, K ⊆ O ∧
        ∃ (Y₁ : CMfd.{u} n) (T₁ : BlowupTower (CMfd.of (n := n) O) Y₁),
          IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) M)
            (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : O → X) M)
              ((Subtype.val : O → X) ⁻¹' H)) T₁ ∧
          ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) M) T₁).cosupp,
            T₁.proj z ∈ (Subtype.val : O → X) ⁻¹' K →
            markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : O → X) M)
              ((Subtype.val : O → X) ⁻¹' H) T₁ z < markedStratumHistoryValue M H T z₀ := by
  obtain ⟨z₀, hz₀, O, hKO, _, Y₁, C, π, hπ, _, hCan₁, hLt₁⟩ :=
    exists_markedStratum_maximum_step_near_compact M hM h K hK ⊤ (subset_univ K) T hCan hNe
  exact ⟨z₀, hz₀, O, hKO, Y₁, .step (restrict O T) C π hπ, hCan₁, hLt₁⟩

/-- Flatten the actual output open of the inductive call, with the SAME
prescribed H and the WHOLE native marked pullback. -/
private theorem local_resolution_of_nested {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (O : Opens X) (hKO : K ⊆ O)
    (U₁ : Opens (CMfd.of (n := n) O)) (hKU₁ : (Subtype.val : O → X) ⁻¹' K ⊆ U₁)
    {Y₁ : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (hCan₁ : IsCanonical
      (MarkedIdeal.pullback (Subtype.val : U₁ → O) (MarkedIdeal.pullback (Subtype.val : O → X) M))
      (markedStratumHistoryValue
        (MarkedIdeal.pullback (Subtype.val : U₁ → O) (MarkedIdeal.pullback (Subtype.val : O → X) M))
        ((Subtype.val : U₁ → O) ⁻¹' ((Subtype.val : O → X) ⁻¹' H))) T₁)
    (hRes₁ : IsGeoResolution
      (MarkedIdeal.pullback (Subtype.val : U₁ → O) (MarkedIdeal.pullback (Subtype.val : O → X) M)) T₁) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
        (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
          ((Subtype.val : U → X) ⁻¹' H)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) M) T' := by
  obtain ⟨U, hUDef⟩ : ∃ U : Opens X, (U : Set X) = (Subtype.val : O → X) '' (U₁ : Set O) :=
    ⟨⟨_, O.isOpen.isOpenMap_subtype_val _ U₁.isOpen⟩, rfl⟩
  have hBD : ∀ q : O, q ∈ U₁ ↔ (q : X) ∈ U := fun q => by
    rw [← SetLike.mem_coe (x := (q : X)), hUDef]
    exact ⟨fun hq => ⟨q, hq, rfl⟩, fun ⟨q', hq', heq⟩ => (Subtype.ext heq : q' = q) ▸ hq'⟩
  have hDA : U ≤ O := by
    intro x hx
    rw [← SetLike.mem_coe, hUDef] at hx
    obtain ⟨q, _hq, rfl⟩ := hx
    exact q.property
  have hKU : K ⊆ U := fun x hx => (hBD ⟨x, hKO hx⟩).mp (hKU₁ hx)
  obtain ⟨Y', T', hCan', hRes'⟩ := flatten_nested_resolution M hM h O U₁ U hBD hDA T₁ hCan₁ hRes₁
  exact ⟨U, hKU, Y', T', hCan', hRes'⟩

/-- Well-founded finite local induction on the actual NEW value with top.
The state retains the entire accumulated T, not a rebased nonempty suffix. -/
private theorem local_resolution_of_lt
    (μ : WithTop (ℕ ×ₗ WithBot (CanonicalCentres.ValTy n))) :
    ∀ {X : CMfd.{u} n} (M : MarkedIdeal n X), IsInvDomain n M →
      ∀ (H : Set X), IsBoundaryAdaptedCarrier (n := n) H M.E →
      ∀ (K : Set X), IsCompact K →
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
        IsCanonical M (markedStratumHistoryValue M H) T →
        (∀ z ∈ (geoTransformAlong M T).cosupp, T.proj z ∈ K →
          (markedStratumHistoryValue M H T z : WithTop (ℕ ×ₗ WithBot (CanonicalCentres.ValTy n))) < μ) →
        ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
          IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
            (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
              ((Subtype.val : U → X) ⁻¹' H)) T' ∧
          IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) M) T' := by
  induction μ using WellFoundedLT.induction with
  | _ μ ih => ?_
  intro X M hM H h K hK Y T hCan hLt
  by_cases hNe : ((geoTransformAlong M T).cosupp ∩ T.proj ⁻¹' K).Nonempty
  · obtain ⟨z₀, hz₀, O, hKO, Y₁, T₁, hCan₁, hLt₁⟩ := shrink_step M hM h K hK T hCan hNe
    have hK₁ : IsCompact ((Subtype.val : O → X) ⁻¹' K) :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
        (fun x hx => ⟨⟨x, hKO hx⟩, rfl⟩)).mpr hK
    have hMO := InvDomainTowerAlong.isInvDomain_pullback_val O hM
    have hHO := boundaryAdapted_open O h
    obtain ⟨U₁, hKU₁, Y₂, T₂, hCan₂, hRes₂⟩ := ih _ (hLt z₀ hz₀.1 hz₀.2)
      (MarkedIdeal.pullback (Subtype.val : O → X) M) hMO
      ((Subtype.val : O → X) ⁻¹' H) hHO ((Subtype.val : O → X) ⁻¹' K) hK₁ T₁ hCan₁
      (fun z hz hzK => WithTop.coe_lt_coe.mpr (hLt₁ z hz hzK))
    exact local_resolution_of_nested M hM h K O hKO U₁ hKU₁ T₂ hCan₂ hRes₂
  · exact local_resolution_of_disjoint M hM h K T hCan hNe

/-- Original local domain: only native M, prescribed adapted H and compact
K. The whole cosupport may be noncompact. Actual raw CAN, resolution,
ALL original localbranch histories and the terminal adapted pair are outputs. -/
theorem exists_markedStratum_local_canonical_resolving_tower {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) M) T ∧
        IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
          (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
            ((Subtype.val : U → X) ⁻¹' H)) T ∧
        IsOriginalBranchTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M)
          ((Subtype.val : U → X) ⁻¹' H) T ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T ((Subtype.val : U → X) ⁻¹' H))
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) T).E := by
  obtain ⟨U, hKU, Y, T, hCan, hRes⟩ := local_resolution_of_lt ⊤ M hM H h K hK
    (.refl : BlowupTower X X) trivial (fun _ _ _ => WithTop.coe_lt_top _)
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hHU := boundaryAdapted_open U h
  obtain ⟨hTest, hHistory, _hBirths, _hFrame⟩ := markedStratum_canonical_history_joint_interpretation
    (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) M) hMU hHU T hCan
  have hPair := (current_old_strata_eq_strict (X := CMfd.of (n := n) U)
    (MarkedIdeal.pullback (Subtype.val : U → X) M) hHU T hTest hHistory).1
  exact ⟨U, hKU, Y, T, hRes, hCan, hHistory, hPair⟩

/-- The original relatively compact open domain: an actual D contained in
compact K gets a finite canonical resolution over EXACTLY D, with H retained.
No compactness of the cosupport inside the open D is manufactured. -/
theorem exists_markedStratum_resolution_of_subset_isCompact {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (hK : IsCompact K) (D : Opens X) (hDK : (D : Set X) ⊆ K) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) D) Y),
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : D → X) M) T ∧
        IsCanonical (MarkedIdeal.pullback (Subtype.val : D → X) M)
          (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : D → X) M)
            ((Subtype.val : D → X) ⁻¹' H)) T ∧
        IsOriginalBranchTestTower (MarkedIdeal.pullback (Subtype.val : D → X) M)
          ((Subtype.val : D → X) ⁻¹' H) T ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T ((Subtype.val : D → X) ⁻¹' H))
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : D → X) M) T).E := by
  obtain ⟨A, hKA, Y, T, hRes, hCan, _hHistory, _hPair⟩ :=
    exists_markedStratum_local_canonical_resolving_tower M hM h K hK
  have hDA : D ≤ A := fun x hx => hKA (hDK hx)
  let B : Opens (CMfd.of (n := n) A) :=
    ⟨(Subtype.val : A → X) ⁻¹' D, D.isOpen.preimage continuous_subtype_val⟩
  have hBD : ∀ q : A, q ∈ B ↔ (q : X) ∈ D := fun _ => Iff.rfl
  have hMA := InvDomainTowerAlong.isInvDomain_pullback_val A hM
  have hHA := boundaryAdapted_open A h
  have hCanB := markedStratum_canonical_restrictOpen (X := CMfd.of (n := n) A)
    (MarkedIdeal.pullback (Subtype.val : A → X) M) hMA hHA B T hCan
  have hResB := isGeoResolution_restrict B hMA.isWellFormed.isClosedSubmanifold_N
    hMA.isWellFormed.isCoherent hRes
  obtain ⟨Y', T', hCan', hRes'⟩ := flatten_nested_resolution M hM h A B D hBD hDA
    (restrict B T) hCanB hResB
  have hMD := InvDomainTowerAlong.isInvDomain_pullback_val D hM
  have hHD := boundaryAdapted_open D h
  obtain ⟨hTest', hHistory', _hBirths', _hFrame'⟩ := markedStratum_canonical_history_joint_interpretation
    (X := CMfd.of (n := n) D) (MarkedIdeal.pullback (Subtype.val : D → X) M) hMD hHD T' hCan'
  have hPair' := (current_old_strata_eq_strict (X := CMfd.of (n := n) D)
    (MarkedIdeal.pullback (Subtype.val : D → X) M) hHD T' hTest' hHistory').1
  exact ⟨Y', T', hRes', hCan', hHistory', hPair'⟩

/-- A relatively compact neighbourhood of each GIVEN compact K, with the
same finite canonical native resolution/ALLbranch/terminal pair. -/
theorem exists_markedStratum_relativelyCompact_local_resolution {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (K : Set X) (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) M) T ∧
          IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
            (markedStratumHistoryValue (MarkedIdeal.pullback (Subtype.val : U → X) M)
              ((Subtype.val : U → X) ⁻¹' H)) T ∧
          IsOriginalBranchTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M)
            ((Subtype.val : U → X) ⁻¹' H) T ∧
          IsBoundaryAdaptedCarrier (n := n) (strictAlong T ((Subtype.val : U → X) ⁻¹' H))
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) T).E := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUOpen, hKU, hUCompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUOpen⟩, hKU, hUCompact,
    exists_markedStratum_resolution_of_subset_isCompact M hM h
      (closure U) hUCompact ⟨U, hUOpen⟩ subset_closure⟩

end
end Hironaka.HironakaOriginalNCMarkedStratumLocalDriver

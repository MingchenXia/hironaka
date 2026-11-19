import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Resolution.HironakaAdmissibleCalculus

/-! Natural compact/local cleanup AFTER the whole source is smooth.
The ordinary native invariant is used with the SAME full ordered E.
Every prefix has the literal controlled mark-one vanishing ideal, remains
smooth and pure d, and every cleanup centre lies in CURRENT W intersect E.
The returned prefix stops BEFORE blowing up its whole next maximum W.

Source-facing mathematics/API: work/hironaka-g8-constant-hs-phase-20261024/
smooth-boundary-cleanup-consumer/. Source-only initial draft, no Lean run.
This does not identify ordinary and NEW prescribed-H values, assert the
nonsmooth Sing-centre stage, or close the historical phase, G4 or G8. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualSmoothBoundaryCleanup
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaEmbeddedBoundary HironakaAdmissibleSequence
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ} {X : CMfd.{u} n}

/-- The literal native source record, retaining every original boundary slot. -/
def actualSmoothBoundaryMarked (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ, E, vanishingIdeal (n := n) W, 1⟩

/-- The true good open is the complement of the ENTIRE initial boundary. -/
def actualSmoothBoundaryOpen (E : List (Set X)) (hE : IsSNCDivisor n E) : Opens X :=
  ⟨(⋃ H ∈ E, H)ᶜ, (isClosed_biUnion_of_forall_isClosed hE.1).isOpen_compl⟩

/-- Concrete OUTPUT data at every actual step; no future centre is an input. -/
def ActualSmoothBoundarySteps (W : Set X) (E : List (Set X)) (d : ℕ) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
      ActualSmoothBoundarySteps W E d T ∧
      geoTransformAlong (actualSmoothBoundaryMarked W E) T =
        (⟨univ, (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E,
          vanishingIdeal (n := n) (strictAlong T W), 1⟩ : MarkedIdeal n _) ∧
      IsClosedSubmanifold n (strictAlong T W) ∧
      (∀ x ∈ strictAlong T W, RegularAtDim (n := n) (strictAlong T W) x d) ∧
      C ⊆ strictAlong T W ∩ ⋃ H ∈ (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E, H

/-- The actual geometric endpoint on the SAME retained native tower. -/
def ActualSmoothBoundaryCleanupResult (W : Set X) (E : List (Set X)) (d : ℕ)
    (hE : IsSNCDivisor n E) {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  let M := actualSmoothBoundaryMarked W E
  let S := strictAlong T W
  let MT := geoTransformAlong M T
  IsCanonical M ((CanonicalCentres.canonicalInvariant.{u} n).inv M) T ∧
    IsGeoTestTower M T ∧ CentresAvoid (actualSmoothBoundaryOpen E hE) T ∧
    ActualSmoothBoundarySteps W E d T ∧
    MT = (⟨univ, MT.E, vanishingIdeal (n := n) S, 1⟩ : MarkedIdeal n Y) ∧
    IsClosedSubmanifold n S ∧ (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧
    S = strictTransform n T.proj W ∧
    maxLocus ((CanonicalCentres.canonicalInvariant.{u} n).inv M T) MT.cosupp = S ∧
    HasNormalCrossings n S MT.E ∧ IsSNCDivisor n MT.E ∧
    IsAdmissibleBlowupSequence n X E (W ∩ ⋃ H ∈ E, H) Y T.proj MT.E

/-- ANY actual test tower preserves the ENTIRE smooth mark-one ideal and
the actual common dimension. No canonical, density or boundary-avoidance
premise is needed for this source state. -/
theorem actual_smooth_mark_one_test_tower_state (W : Set X) (E : List (Set X))
    (hW : IsClosedSubmanifold n W) (d : ℕ)
    (hpure : ∀ x ∈ W, RegularAtDim (n := n) W x d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower (actualSmoothBoundaryMarked W E) T →
      geoTransformAlong (actualSmoothBoundaryMarked W E) T =
        (⟨univ, (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E,
          vanishingIdeal (n := n) (strictAlong T W), 1⟩ : MarkedIdeal n Y) ∧
      IsClosedSubmanifold n (strictAlong T W) ∧
      (∀ x ∈ strictAlong T W, RegularAtDim (n := n) (strictAlong T W) x d)
  | _, .refl, _ => ⟨rfl, hW, hpure⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hMT, hWT, hpureT⟩ := actual_smooth_mark_one_test_tower_state W E hW d hpure T hT.1
      have hCos : (geoTransformAlong (actualSmoothBoundaryMarked W E) T).cosupp = strictAlong T W := by
        rw [hMT]
        exact cosupp_mk_vanishingIdeal hWT.1 _
      have hCW : C ⊆ strictAlong T W := by
        intro x hx
        have hc := hT.2.2.1 hx
        rwa [hCos] at hc
      have hNext : geoTransformAlong (actualSmoothBoundaryMarked W E) (.step T C π hπ) =
          (⟨univ, (geoTransformAlong (actualSmoothBoundaryMarked W E) (.step T C π hπ)).E,
            vanishingIdeal (n := n) (strictAlong (.step T C π hπ) W), 1⟩ : MarkedIdeal n _) := by
        change (geoTransformAlong (actualSmoothBoundaryMarked W E) T).geoTransform C π =
          (⟨univ, ((geoTransformAlong (actualSmoothBoundaryMarked W E) T).geoTransform C π).E,
            vanishingIdeal (n := n) (geoStrictTransform π C (strictAlong T W)), 1⟩ : MarkedIdeal n _)
        rw [hMT]
        apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
        · exact geoTransform_N_eq_univ rfl hπ
        · rfl
        · rw [geoTransform_ideal_eq_controlledTransform rfl
            (VanishingIdealCoherent.isCoherent_vanishingIdeal hWT) hπ]
          exact BlowupStrictIdeal.controlledTransform_vanishingIdeal hπ hWT hCW
        · rfl
      refine ⟨hNext, ?_, ?_⟩
      · exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hWT hCW
      · intro x hx
        exact regularAtDim_geoStrictTransform hπ hWT.1 hpureT hCW hx

/-- This inclusion holds for EVERY native tower before any centre-location
claim: the born member catches any part lost from an old strict member. -/
private theorem initial_boundary_preimage_subset (M : MarkedIdeal n X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      T.proj ⁻¹' (⋃ H ∈ M.E, H) ⊆ ⋃ H ∈ (geoTransformAlong M T).E, H
  | _, .refl => fun _ hx => hx
  | _, .step T C π hπ => by
      intro y hy
      have hOld := initial_boundary_preimage_subset M T hy
      obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hOld
      change y ∈ ⋃ D ∈ ((geoTransformAlong M T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]), D
      by_cases hyC : π y ∈ C
      · exact mem_iUnion₂.mpr ⟨π ⁻¹' C,
          List.mem_append_right _ (List.mem_singleton.mpr rfl), hyC⟩
      · exact mem_iUnion₂.mpr ⟨geoStrictTransform π C H,
          List.mem_append_left _ (List.mem_map.mpr ⟨H, hH, rfl⟩), subset_closure ⟨hyH, hyC⟩⟩

theorem strictAlong_eq_library_of_avoid (W : Set X) (hW : IsClosed W)
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresAvoid O T →
      strictAlong T W = strictTransform n T.proj W
  | _, .refl, _ => by simp [strictAlong, strictTransform, exceptionalLocus_id]
  | _, .step T C π hπ, hAvoid => by
      have hCE : C ⊆ T.proj ⁻¹' (O : Set X)ᶜ := by
        intro x hx hxO
        exact Set.disjoint_left.mp hAvoid.2 hx hxO
      have hD : strictTransform n T.proj W ⊆
          closure (strictTransform n T.proj W \ T.proj ⁻¹' (O : Set X)ᶜ) :=
        HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hW
          (by simpa only [sdiff_compl] using hdense)
      have hNowhere : strictTransform n T.proj W ⊆ closure (strictTransform n T.proj W \ C) :=
        hD.trans (closure_mono (sdiff_subset_sdiff_right hCE))
      calc
        strictAlong (.step T C π hπ) W = geoStrictTransform π C (strictAlong T W) := rfl
        _ = geoStrictTransform π C (strictTransform n T.proj W) := by
          rw [strictAlong_eq_library_of_avoid W hW O hdense T hAvoid.1]
        _ = strictTransform n π (strictTransform n T.proj W) :=
          BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hNowhere
        _ = strictTransform n (T.proj ∘ π) W :=
          (StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff W).symm

theorem boundary_steps_of_test_avoid (W : Set X) (E : List (Set X))
    (hW : IsClosedSubmanifold n W) (d : ℕ)
    (hpure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower (actualSmoothBoundaryMarked W E) T →
      CentresAvoid (actualSmoothBoundaryOpen E hE) T → ActualSmoothBoundarySteps W E d T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hTest, hAvoid => by
      obtain ⟨hMT, hWT, hPureT⟩ := actual_smooth_mark_one_test_tower_state W E hW d hpure T hTest.1
      refine ⟨boundary_steps_of_test_avoid W E hW d hpure hE T hTest.1 hAvoid.1,
        hMT, hWT, hPureT, ?_⟩
      intro x hx
      have hxCos := hTest.2.2.1 hx
      have hxW : x ∈ strictAlong T W := by
        rw [hMT, cosupp_mk_vanishingIdeal hWT.1] at hxCos
        exact hxCos
      have hxF : T.proj x ∈ ⋃ H ∈ E, H := by
        by_contra hxF
        exact Set.disjoint_left.mp hAvoid.2 hx hxF
      exact ⟨hxW, initial_boundary_preimage_subset (actualSmoothBoundaryMarked W E) T hxF⟩

private theorem admissible_sequence_of_test_avoid (W : Set X) (E : List (Set X))
    (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hM : IsInvDomain n (actualSmoothBoundaryMarked W E))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (actualSmoothBoundaryMarked W E) T)
    (hAvoid : CentresAvoid (actualSmoothBoundaryOpen E hE) T) :
    IsAdmissibleBlowupSequence n X E (W ∩ ⋃ H ∈ E, H) Y T.proj
      (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E := by
  have hCos : (actualSmoothBoundaryMarked W E).cosupp = W := cosupp_mk_vanishingIdeal hW E
  have hOverW := centresOver_cosupp (actualSmoothBoundaryMarked W E)
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest
  rw [hCos] at hOverW
  have hOverE : CentresOver (⋃ H ∈ E, H) T := by
    have h := centresOver_compl_of_centresAvoid (actualSmoothBoundaryOpen E hE) T hAvoid
    change CentresOver (((⋃ H ∈ E, H)ᶜ)ᶜ) T at h
    simpa only [compl_compl] using h
  have hOver := centresOver_of_inter_subset (Subset.refl (W ∩ ⋃ H ∈ E, H)) T hOverW hOverE
  exact isAdmissibleBlowupSequence_proj (actualSmoothBoundaryMarked W E) _ T hTest hOver

/-- Actual resolving input is internal to the two public constructors below.
The next maximum, its equality with W and its NC are PRODUCED here. -/
private theorem exists_cleanup_prefix_of_resolution (W : Set X) (E : List (Set X))
    (hW : IsClosedSubmanifold n W) (d : ℕ)
    (hpure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hM : IsInvDomain n (actualSmoothBoundaryMarked W E))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hCan₀ : IsCanonical (actualSmoothBoundaryMarked W E)
      ((CanonicalCentres.canonicalInvariant.{u} n).inv (actualSmoothBoundaryMarked W E)) T₀)
    (hRes₀ : IsGeoResolution (actualSmoothBoundaryMarked W E) T₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), ActualSmoothBoundaryCleanupResult W E d hE T := by
  let M := actualSmoothBoundaryMarked W E
  let O := actualSmoothBoundaryOpen E hE
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  have hDenseO : W ⊆ closure (W ∩ (O : Set X)) := hdense
  have hEO : ∀ H ∈ E, Disjoint H (O : Set X) := by
    intro H hH
    exact disjoint_left.mpr fun x hxH hxO => hxO (mem_biUnion hH hxH)
  have hPrefix : ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical M (R.inv M) T ∧ CentresAvoid O T ∧
        maxLocus (R.inv M T) (geoTransformAlong M T).cosupp = strictAlong T W := by
    by_cases hAvoid₀ : CentresAvoid O T₀
    · obtain ⟨hMT, hWT, _hPure⟩ := actual_smooth_mark_one_test_tower_state W E hW d hpure T₀ hRes₀.1
      have hCos : (geoTransformAlong M T₀).cosupp = strictAlong T₀ W := by
        rw [hMT]
        exact cosupp_mk_vanishingIdeal hWT.1 _
      have hS0 : strictAlong T₀ W = ∅ := hCos.symm.trans hRes₀.2
      refine ⟨Y₀, T₀, hCan₀, hAvoid₀, ?_⟩
      rw [hRes₀.2, hS0]
      ext x
      exact ⟨fun hx => False.elim hx.1, fun hx => False.elim hx⟩
    · obtain ⟨Y, T, _tail, _hAppend, hCan, hAvoid, c, hc, hcO⟩ :=
        EmbeddedFromResolution.exists_first_centre M (R.inv M) O T₀ hCan₀ hAvoid₀
      have hTest := hF.isGeoTestTower_of_isCanonical hM T hCan
      obtain ⟨hMT, hWT, _hPure⟩ := actual_smooth_mark_one_test_tower_state W E hW d hpure T hTest
      have hCos : (geoTransformAlong M T).cosupp = strictAlong T W := by
        rw [hMT]
        exact cosupp_mk_vanishingIdeal hWT.1 _
      have hAdm := hF.isAdmissibleCentre_maxLocus hM T hCan hTest
      have hMaxO := fun y (hy : T.proj y ∈ O) =>
        HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim
          hF hW.1 O hEO (d := d) (fun x hx => hpure x hx) hM T hCan hAvoid hc hcO hy
      have hStrict := strictAlong_eq_library_of_avoid W hW.1 O hDenseO T hAvoid
      have hD : strictAlong T W ⊆ closure (strictAlong T W \ T.proj ⁻¹' (⋃ H ∈ E, H)) := by
        rw [hStrict]
        exact HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hW.1 hdense
      have hTrace : strictAlong T W \ T.proj ⁻¹' (⋃ H ∈ E, H) ⊆
          maxLocus (R.inv M T) (geoTransformAlong M T).cosupp := by
        rintro y ⟨hyS, hyF⟩
        have hyO : T.proj y ∈ O := hyF
        have hyCos : y ∈ (geoTransformAlong M T).cosupp := hCos.symm ▸ hyS
        have hyW := (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid
          hW.1 hM O T hTest hAvoid hyO).mp hyCos
        exact (hMaxO y hyO).mpr hyW
      have hSMax := hD.trans (closure_minimal hTrace hAdm.1.1)
      refine ⟨Y, T, hCan, hAvoid, ?_⟩
      apply Subset.antisymm ?_ hSMax
      intro y hy
      exact hCos ▸ hy.1
  obtain ⟨Y, T, hCan, hAvoid, hMax⟩ := hPrefix
  have hTest := hF.isGeoTestTower_of_isCanonical hM T hCan
  obtain ⟨hMT, hWT, hPure⟩ := actual_smooth_mark_one_test_tower_state W E hW d hpure T hTest
  have hAdm := hF.isAdmissibleCentre_maxLocus hM T hCan hTest
  have hNC : HasNormalCrossings n (strictAlong T W) (geoTransformAlong M T).E := by
    rw [← hMax]
    exact hAdm.2.2
  exact ⟨Y, T, hCan, hTest, hAvoid,
    boundary_steps_of_test_avoid W E hW d hpure hE T hTest hAvoid,
    hMT, hWT, hPure, strictAlong_eq_library_of_avoid W hW.1 O hDenseO T hAvoid,
    hMax, hNC, (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest).isWellFormed.isSNCDivisor,
    admissible_sequence_of_test_avoid W E hW.1 hE hM T hTest hAvoid⟩

/-- Compact WHOLE W suffices on an arbitrary ambient manifold. The real
finite resolving tower and the stopping maximum are constructed internally. -/
theorem exists_actual_smooth_boundary_cleanup_of_isCompact (W : Set X) (E : List (Set X))
    (hW : IsClosedSubmanifold n W) (hK : IsCompact W) (d : ℕ) (hd : d < n)
    (hpure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), ActualSmoothBoundaryCleanupResult W E d hE T := by
  have hWa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW
  have hpure' : W ⊆ closure (regularLocus (n := n) W d) :=
    fun x hx => subset_closure (hpure x hx)
  have hM : IsInvDomain n (actualSmoothBoundaryMarked W E) :=
    isInvDomain_boundary hWa (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure') hE
  have hCos : (actualSmoothBoundaryMarked W E).cosupp = W := cosupp_mk_vanishingIdeal hW.1 E
  obtain ⟨Y₀, T₀, hCan₀, hRes₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hM (by rw [hCos]; exact hK)
  exact exists_cleanup_prefix_of_resolution W E hW d hpure hE hdense hM T₀ hCan₀ hRes₀

/-- A compact original K gives an ACTUAL source open and finite cleanup;
no compactness of the open, W or its whole restricted cosupport is assumed. -/
theorem exists_actual_local_smooth_boundary_cleanup (W : Set X) (E : List (Set X))
    (hW : IsClosedSubmanifold n W) (d : ℕ) (hd : d < n)
    (hpure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧
      ∃ (hEU : IsSNCDivisor n (E.map ((Subtype.val : U → X) ⁻¹' ·)))
        (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        ActualSmoothBoundaryCleanupResult ((Subtype.val : U → X) ⁻¹' W)
          (E.map ((Subtype.val : U → X) ⁻¹' ·)) d hEU T := by
  have hWa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW
  have hpure' : W ⊆ closure (regularLocus (n := n) W d) :=
    fun x hx => subset_closure (hpure x hx)
  have hM : IsInvDomain n (actualSmoothBoundaryMarked W E) :=
    isInvDomain_boundary hWa (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure') hE
  obtain ⟨U, hKU, Y₀, T₀, hCan₀, hRes₀⟩ :=
    HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical
      (CanonicalCentres.canonicalInvariant.{u} n) hM hK
  let WU : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' W
  let EU : List (Set (CMfd.of (n := n) U)) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  dsimp only [actualSmoothBoundaryMarked] at hMU hCan₀ hRes₀
  rw [pullback_val_mk_vanishingIdeal U E W] at hMU hCan₀ hRes₀
  have hEU : IsSNCDivisor n EU := hMU.isWellFormed.isSNCDivisor
  have hPureU : ∀ x ∈ WU, RegularAtDim (n := n) WU x d := by
    intro x hx
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hpure x hx)
  have hWU : IsClosedSubmanifold n WU :=
    ⟨hW.1.preimage continuous_subtype_val, fun x hx => ⟨d, hPureU x hx⟩⟩
  have hSupp : (⋃ H ∈ EU, H) = (Subtype.val : U → X) ⁻¹' (⋃ H ∈ E, H) := by
    ext x
    simp only [EU, mem_iUnion, List.mem_map, mem_preimage]
    constructor
    · rintro ⟨A, ⟨H, hH, rfl⟩, hx⟩
      exact ⟨H, hH, hx⟩
    · rintro ⟨H, hH, hx⟩
      exact ⟨_, ⟨H, hH, rfl⟩, hx⟩
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU, H) := by
    intro x hx
    have h := hdense hx
    have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E, H)
    have h' : x ∈ closure ((Subtype.val : U → X) ⁻¹' (W \ ⋃ H ∈ E, H)) :=
      (Set.ext_iff.mp he x).mp h
    simpa only [preimage_sdiff, ← hSupp] using h'
  obtain ⟨Y, T, hResult⟩ := exists_cleanup_prefix_of_resolution WU EU hWU d hPureU hEU hDenseU hMU T₀ hCan₀ hRes₀
  exact ⟨U, hKU, hEU, Y, T, hResult⟩

end
end Hironaka.HironakaActualSmoothBoundaryCleanup

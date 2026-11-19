import Hironaka.Resolution.HironakaCompactFootprintJointTests
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase

/-! The SAME actual compact-footprint extension retains both original tests
and genuine CURRENT sharp-centre avoidance. Complete source-first proof:
hironaka-compact-footprint-sharp-extension.tex. Native whole-record,
strict-transform and coordinate transport are reused. -/

set_option autoImplicit false

open Set TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaCompactFootprintSharpExtension

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen MarkedIdealTowerTransport HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  NormalCrossings NormalCrossingsInvariance IdealWeightPowers

variable {n : ℕ} {X X' Y Z : CMfd.{u} n}

private theorem pullback_template (f : Y → X) (E : List (Set X)) :
    MarkedIdeal.pullback f (geometricTemplate (univ : Set X) E) =
      geometricTemplate (univ : Set Y) (E.map (f ⁻¹' ·)) := by
  simp [MarkedIdeal.pullback, geometricTemplate, BlowupExceptionalDivisor.pullback_unitIdeal]

private theorem normalCrossingsAt_preimage_diffeo
    (Φ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {E : List (Set X)} {y : Y}
    (hNC : normalCrossingsAt (n := n) N E (Φ y)) :
    normalCrossingsAt (n := n) (Φ ⁻¹' N) (E.map (Φ ⁻¹' ·)) y := by
  obtain ⟨S₀,S,hcoord,hcard⟩ := hNC
  let c : Fin (E.map (Φ ⁻¹' ·)).length → Fin E.length := Fin.cast (List.length_map _)
  refine ⟨S₀,fun i => S (c i),?_,?_⟩
  · exact IsCoordinateFamilyAt.reindex ((pullsBackCoordinates Φ) _ _ y hcoord)
      (Option.map c) (by rintro (_|i); rfl; exact get_map_preimage E i)
      (by rintro (_|i) <;> rfl)
  · intro i hi
    rw [get_map_preimage] at hi
    exact hcard (c i) hi

theorem currentSharp_of_isTowerIso (N : Set X) (E : List (Set X))
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {Y' : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) :
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
    CurrentSharpCentres (Φ ⁻¹' N) (E.map (Φ ⁻¹' ·)) T' →
      CurrentSharpCentres N E T := by
  induction hiso with
  | refl => exact fun _ _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hTest hSharp
    refine ⟨ih hTest.1 hSharp.1,?_⟩
    intro c hc
    let c' : Y' := χ.symm c
    have hc' : c' ∈ C' := by
      rw [←hC]
      change χ (χ.symm c) ∈ C
      simpa only [χ.apply_symm_apply] using hc
    have hbad := hSharp.2 hc'
    have hN := hiso.strictAlong_eq N
    have hRecord := IsTowerIso.geoTransformAlong_eq Φ isClosedSubmanifold_univ
      isCoherent_unitIdeal hiso hTest.1
    rw [pullback_template] at hRecord
    have hE : (geoTransformAlong
        (geometricTemplate (univ : Set X') (E.map (Φ ⁻¹' ·))) T').E =
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E.map (χ ⁻¹' ·) := by
      simpa only [MarkedIdeal.pullback] using congrArg MarkedIdeal.E hRecord
    rw [hN,hE] at hbad
    refine ⟨?_,?_⟩
    · simpa only [mem_preimage,c',χ.apply_symm_apply] using hbad.1
    · intro hNC
      apply hbad.2
      apply normalCrossingsAt_preimage_diffeo χ
      simpa only [c',χ.apply_symm_apply] using hNC

private theorem currentSharp_of_restrict (N : Set X) (E : List (Set X))
    (U : Opens X) (K : Set X) (hKU : K ⊆ U) :
    ∀ {Y : CMfd.{u} n} (Q : BlowupTower X Y), CentresOver K Q →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q →
      CurrentSharpCentres ((Subtype.val : U → X) ⁻¹' N)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U Q) →
      CurrentSharpCentres N E Q
  | _,.refl,_hOver,_hTest,_hSharp => trivial
  | _,.step P C π hπ,hOver,hTest,hSharp => by
    refine ⟨currentSharp_of_restrict N E U K hKU P hOver.1 hTest.1 hSharp.1,?_⟩
    intro c hc
    let v : openPreimage P U := ⟨c,hKU (hOver.2 hc)⟩
    have hbad := hSharp.2 (show v ∈ (Subtype.val : openPreimage P U → _) ⁻¹' C from hc)
    rw [strictAlong_restrict] at hbad
    have hRecord := geoTransformAlong_restrict U isClosedSubmanifold_univ
      isCoherent_unitIdeal P hTest.1
    rw [pullback_template (Y := CMfd.of (n := n) U) (Subtype.val : U → X) E] at hRecord
    have hE : (geoTransformAlong (geometricTemplate (univ : Set U)
        (E.map ((Subtype.val : U → X) ⁻¹' ·))) (restrict U P)).E =
        (geoTransformAlong (geometricTemplate (univ : Set X) E) P).E.map
          ((Subtype.val : openPreimage P U → _) ⁻¹' ·) := by
      simpa only [MarkedIdeal.pullback] using congrArg MarkedIdeal.E hRecord
    rw [hE] at hbad
    refine ⟨hbad.1,fun hNC => hbad.2 ?_⟩
    exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mpr hNC

/-- The prescribed ACTUAL closed-footprint local history constructs ONE
global history with BOTH original tests and genuine CURRENT sharp centres,
retaining the entire actual comparison, every position and original footprint. -/
theorem exists_current_sharp_joint_test_extension_of_closed
    (N : Set X) (E : List (Set X)) (M : MarkedIdeal n X)
    (hNM : IsClosedSubmanifold n M.N) (hIM : M.ideal.IsCoherent)
    (U : Opens X) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : CentresOver ((Subtype.val : U → X) ⁻¹' K) T)
    (hFull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X)
      (geometricTemplate (univ : Set X) E)) T)
    (hM : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T)
    (hSharp : CurrentSharpCentres ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      IsGeoTestTower M Q ∧ CurrentSharpCentres N E Q ∧ CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  obtain ⟨Y,Q,hOver,e,he,hLength,hProj⟩ :=
    HironakaClosedFootprintOpenTowerExtension.exists_closed_footprint_extension U K hK hKU T hT
  have hFullQ := HironakaCompactFootprintJointTests.isGeoTestTower_of_supported_open_iso
    (geometricTemplate (univ : Set X) E) isClosedSubmanifold_univ isCoherent_unitIdeal
    U K hK hKU Q hOver T e he hFull
  have hMQ := HironakaCompactFootprintJointTests.isGeoTestTower_of_supported_open_iso
    M hNM hIM U K hK hKU Q hOver T e he hM
  have hFullU := isGeoTestTower_restrict U isClosedSubmanifold_univ
    isCoherent_unitIdeal Q hFullQ
  rw [pullback_template (Y := CMfd.of (n := n) U) (Subtype.val : U → X) E] at hFullU
  have hSharpU : CurrentSharpCentres ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U Q) :=
    currentSharp_of_isTowerIso (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) U)
      (Y := CMfd.of (n := n) (openPreimage Q U)) (Y' := Z)
      (T' := T) (T := restrict U Q) (χ := e) ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) he hFullU
      (by simpa [Function.comp_def] using hSharp)
  exact ⟨Y,Q,hFullQ,hMQ,currentSharp_of_restrict N E U K hKU Q hOver hFullQ hSharpU,
    hOver,e,he,hLength,hProj⟩

/-- The prescribed ACTUAL compact-footprint local history constructs ONE
global history with BOTH original tests and genuine CURRENT sharp centres,
retaining the entire actual comparison, every position and original footprint. -/
theorem exists_current_sharp_joint_test_extension
    (N : Set X) (E : List (Set X)) (M : MarkedIdeal n X)
    (hNM : IsClosedSubmanifold n M.N) (hIM : M.ideal.IsCoherent)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : CentresOver ((Subtype.val : U → X) ⁻¹' K) T)
    (hFull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X)
      (geometricTemplate (univ : Set X) E)) T)
    (hM : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T)
    (hSharp : CurrentSharpCentres ((Subtype.val : U → X) ⁻¹' N)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      IsGeoTestTower M Q ∧ CurrentSharpCentres N E Q ∧ CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val :=
  exists_current_sharp_joint_test_extension_of_closed N E M hNM hIM U K hK.isClosed hKU T hT hFull hM hSharp

end
end Hironaka.HironakaCompactFootprintSharpExtension

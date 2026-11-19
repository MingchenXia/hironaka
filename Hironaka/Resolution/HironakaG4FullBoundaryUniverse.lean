import Hironaka.Resolution.HironakaG4FullBoundaryCompactCleanup
import Hironaka.Resolution.HironakaG4SharpTerminalOpen
import Hironaka.Resolution.HironakaG3UniverseShrinkManifold
import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Resolution.HironakaG3UniverseOrderedBoundary
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Resolution.HironakaG3UniverseStrictAlong
import Hironaka.Resolution.HironakaG34SurfaceSharpCleanup
import Hironaka.Blowup.BlowupTowerIsoTail

/-!
# Compact full-boundary cleanup in arbitrary dimensions and universes

The literal shrink and lift preserve the pointwise normal crossings condition.
The resulting actual tower retains the complete compact cleanup contract on
the original manifold. In dimension zero the identity tower suffices.

Blueprint: `hironaka-g4-compact-full-boundary-universe.tex`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4FullBoundaryUniverse

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaG34NonPureLowDim HironakaG3UniverseChartTransport HironakaG3UniverseCoordinateTransport
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseLiftedTestHistory
  HironakaG3UniverseLiftedMarkedHistory G3UniverseStrictAlong
  HironakaSmoothSubmersionCoefficientIdeals SimultaneousNormalCrossings
  HironakaG3UniverseShrinkManifold HironakaG3UniverseCarrierGeometry HironakaG3UniverseOrderedBoundary
  HironakaG4FullBoundaryCompactCleanup HironakaCompactFootprintSharpExtension
  HironakaEmbeddedAnalytic HironakaG4SharpBadFootprint HironakaG34SurfaceSharpCleanup
  MarkedIdealBiholomorphism MarkedIdealTowerTransport RestrictEmptyTower
  HironakaG4SharpTerminalAtlas HironakaG4SharpTerminalOpen

/-- The literal ordered normal crossings condition is equivalent on an
actual transported complex atlas, across universes. -/
theorem transported_normalCrossingsAt_iff {n : ℕ} {X : CMfd.{u} n} {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) (A : Set X) (E : List (Set X)) (y : Y) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    normalCrossingsAt (n := n) (e.symm ⁻¹' A) (E.map (e.symm ⁻¹' ·)) y ↔
      normalCrossingsAt (n := n) A E (e.symm y) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  let G := E.map (e.symm ⁻¹' ·)
  let cast : Fin G.length ≃ Fin E.length := finCongr (List.length_map _)
  have hGet (j : Fin G.length) : G.get j = e.symm ⁻¹' E.get (cast j) := by
    simp only [G, List.get_eq_getElem, List.getElem_map]
    rfl
  constructor
  · rintro ⟨S₀, S, hFam, hCard⟩
    let S' : Fin E.length → Finset (Fin n) := S ∘ cast.symm
    refine ⟨S₀, S', ?_, ?_⟩
    · apply transported_coordinate_family_reverse e
      apply IsCoordinateFamilyAt.reindex hFam (Option.map cast.symm)
      · rintro (_ | j)
        · rfl
        · change e.symm ⁻¹' E.get j = G.get (cast.symm j)
          rw [hGet, cast.apply_symm_apply]
      · rintro (_ | _) <;> rfl
    · intro j hj
      apply hCard (cast.symm j)
      rwa [hGet, cast.apply_symm_apply]
  · rintro ⟨S₀, S, hFam, hCard⟩
    have hTransport := transported_coordinate_family e (fun j : Option (Fin E.length) =>
      j.elim A E.get) (fun j => j.elim S₀ S) y hFam
    refine ⟨S₀, S ∘ cast, ?_, ?_⟩
    · apply IsCoordinateFamilyAt.reindex hTransport (Option.map cast)
      · rintro (_ | j)
        · rfl
        · exact hGet j
      · rintro (_ | _) <;> rfl
    · intro j hj
      apply hCard (cast j)
      rwa [hGet] at hj

private theorem markedPullback_template {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (f : Y → X) (A : Set X) (E : List (Set X)) :
    markedPullback (m := n) f (geometricTemplate A E) =
      geometricTemplate (f ⁻¹' A) (E.map (f ⁻¹' ·)) := by
  simp [markedPullback, geometricTemplate, HironakaSmoothSubmersionCoefficientIdeals.pullback_unitIdeal]

private theorem ambient_template_wellFormed {n : ℕ} {X : CMfd.{u} n}
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    (geometricTemplate (univ : Set X) E).IsWellFormed :=
  ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
    isTransverse_univ_of_isSNCDivisor hE⟩

private theorem carrier_template_wellFormed {n : ℕ} {X : CMfd.{u} n}
    {W : Set X} (hW : IsClosedSubmanifold n W) :
    (geometricTemplate W []).IsWellFormed :=
  ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hW⟩

/-- The actual sharp bad locus uses the same coordinates on every prefix
of a literal lifted tower. -/
theorem liftTower_sharp_bad_iff {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (y : liftCMfd.{u} Y) :
    y ∈ originalSharpBadLocus (n := n)
        (strictAlong (liftTower.{u} T) ((liftDiffeomorph.{u} X).symm ⁻¹' W))
        (geoTransformAlong (geometricTemplate (univ : Set (liftCMfd.{u} X))
          (E.map ((liftDiffeomorph.{u} X).symm ⁻¹' ·))) (liftTower.{u} T)).E ↔
    (liftDiffeomorph.{u} Y).symm y ∈ originalSharpBadLocus (n := n) (strictAlong T W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
  let M := geometricTemplate (univ : Set X) E
  have hRec := congrArg MarkedIdeal.E
    (liftTower_geoTransformAlong M (ambient_template_wellFormed hE) T hTest)
  rw [markedPullback_template ((liftDiffeomorph.{u} X).symm : liftCMfd.{u} X → X)
    (univ : Set X) E, preimage_univ] at hRec
  rw [strictAlong_liftTower W T, hRec]
  change (y ∈ (liftDiffeomorph.{u} Y).symm ⁻¹' strictAlong T W ∧
      ¬normalCrossingsAt (n := n) _ _ y) ↔
    ((liftDiffeomorph.{u} Y).symm y ∈ strictAlong T W ∧
      ¬normalCrossingsAt (n := n) _ _ ((liftDiffeomorph.{u} Y).symm y))
  exact and_congr Iff.rfl (not_congr
    (transported_normalCrossingsAt_iff (Homeomorph.ulift.symm : Y ≃ₜ ULift.{u} Y)
      (strictAlong T W) (geoTransformAlong M T).E y))

/-- A literal lifted finite tower keeps the stagewise sharp centres on its
actual original carrier and ordered boundary. -/
theorem liftTower_currentSharpCentres {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T → CurrentSharpCentres W E T →
      CurrentSharpCentres ((liftDiffeomorph.{u} X).symm ⁻¹' W)
        (E.map ((liftDiffeomorph.{u} X).symm ⁻¹' ·)) (liftTower.{u} T)
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hTest, hSharp => by
    refine ⟨liftTower_currentSharpCentres hE T hTest.1 hSharp.1, ?_⟩
    intro y hy
    exact (liftTower_sharp_bad_iff hE T hTest.1 y).mpr (hSharp.2 hy)


/-- Carry a given small sharp terminal tower back to a biholomorphic
ambient manifold, with the full chronological ordered boundary. -/
theorem sharpTerminal_transportLift {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₀)
    (W : Set X) (E : List (Set X))
    (hW₀ : IsClosedSubmanifold n (e.symm ⁻¹' W)) (hE₀ : IsSNCDivisor n (E.map (e.symm ⁻¹' ·)))
    (T : BlowupTower X₀ Y₀) (hT : IsSharpTerminalTower (e.symm ⁻¹' W) (E.map (e.symm ⁻¹' ·)) T) :
    IsSharpTerminalTower W E (transport (e.trans (liftDiffeomorph.{u} X₀)) (liftTower.{u} T)).tower := by
  let W₀ : Set X₀ := e.symm ⁻¹' W
  let E₀ := E.map (e.symm ⁻¹' ·)
  obtain ⟨hTCarrier, hTAmbient, hTSharp, hTNC⟩ := hT
  let β := e.trans (liftDiffeomorph.{u} X₀)
  let L := liftTower.{u} T
  let WL : Set (liftCMfd.{u} X₀) := (liftDiffeomorph.{u} X₀).symm ⁻¹' W₀
  let EL := E₀.map ((liftDiffeomorph.{u} X₀).symm ⁻¹' ·)
  have hWL : WL = β.symm ⁻¹' W := rfl
  have hEL : EL = E.map (β.symm ⁻¹' ·) := by
    unfold EL E₀
    rw [List.map_map]
    rfl
  have hWBack : β ⁻¹' WL = W := by rw [hWL]; ext x; simp
  have hEBack : EL.map (β ⁻¹' ·) = E := by
    rw [hEL, List.map_map]
    have hfun : ((β ⁻¹' ·) ∘ (β.symm ⁻¹' ·) : Set X → Set X) = id := by
      funext H
      ext x
      simp
    rw [hfun, List.map_id]
  have hLCarrier := liftTower_isGeoTestTower.{u} _ (carrier_template_wellFormed hW₀) T hTCarrier
  have hLAmbient := liftTower_isGeoTestTower.{u} _ (ambient_template_wellFormed hE₀) T hTAmbient
  rw [markedPullback_template ((liftDiffeomorph.{u} X₀).symm :
    liftCMfd.{u} X₀ → X₀) W₀ ([] : List (Set X₀)), List.map_nil] at hLCarrier
  rw [markedPullback_template ((liftDiffeomorph.{u} X₀).symm : liftCMfd.{u} X₀ → X₀)
    (univ : Set X₀) E₀, preimage_univ] at hLAmbient
  have hLSharp : CurrentSharpCentres WL EL L := liftTower_currentSharpCentres hE₀ T hTAmbient hTSharp
  have hWLSmooth : IsClosedSubmanifold n WL :=
    transported_closedSubmanifold (Homeomorph.ulift.symm : X₀ ≃ₜ ULift.{u} X₀) W₀ hW₀
  have hELSNC : IsSNCDivisor n EL :=
    transported_list_snc X₀ (Homeomorph.ulift.symm : X₀ ≃ₜ ULift.{u} X₀) E₀ hE₀
  have hLNC : HasNormalCrossings n (strictAlong L WL)
      (geoTransformAlong (geometricTemplate (univ : Set (liftCMfd.{u} X₀)) EL) L).E := by
    intro y hy
    by_contra hNC
    have hBad := (liftTower_sharp_bad_iff hE₀ T hTAmbient y).mp ⟨hy, hNC⟩
    exact hBad.2 (hTNC ((liftDiffeomorph.{u} Y₀).symm y) hBad.1)
  let R := transport β L
  let Q := R.tower
  have hIso : IsTowerIso β Q L R.back := transport_isTowerIso β L
  have hLCarrierWF := carrier_template_wellFormed hWLSmooth
  have hLAmbientWF := ambient_template_wellFormed hELSNC
  have hQCarrier := (IsTowerIso.isGeoTestTower_iff β hLCarrierWF.isClosedSubmanifold_N
    hLCarrierWF.isCoherent hIso).mpr hLCarrier
  have hQAmbient := (IsTowerIso.isGeoTestTower_iff β hLAmbientWF.isClosedSubmanifold_N
    hLAmbientWF.isCoherent hIso).mpr hLAmbient
  rw [template_pullback (β : X → liftCMfd.{u} X₀) WL [], List.map_nil, hWBack] at hQCarrier
  rw [template_pullback (β : X → liftCMfd.{u} X₀) univ EL, preimage_univ, hEBack] at hQAmbient
  have hQSharp : CurrentSharpCentres W E Q := by
    change CurrentSharpCentres WL EL L at hLSharp
    rw [hWL, hEL] at hLSharp
    exact currentSharp_of_isTowerIso W E β.symm hIso.symm hQAmbient hLSharp
  have hQN := hIso.strictAlong_eq WL
  rw [hWBack] at hQN
  have hQE := congrArg MarkedIdeal.E (IsTowerIso.geoTransformAlong_eq β
    hLAmbientWF.isClosedSubmanifold_N hLAmbientWF.isCoherent hIso hLAmbient)
  rw [template_pullback (β : X → liftCMfd.{u} X₀) univ EL, preimage_univ, hEBack] at hQE
  refine ⟨hQCarrier, hQAmbient, hQSharp, ?_⟩
  change (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E =
    (geoTransformAlong (geometricTemplate (univ : Set (liftCMfd.{u} X₀)) EL) L).E.map
      (R.back ⁻¹' ·) at hQE
  rw [hQN, hQE]
  intro z hz
  exact normalCrossingsAt_preimage_diffeo R.back (hLNC (R.back z) hz)

/-- Carry a given small sharp terminal tower back to a biholomorphic
ambient manifold, with the full chronological ordered boundary. -/
theorem sharpTerminal_of_small_biholomorphism {n : ℕ} {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₀)
    (W : Set X) (E : List (Set X))
    (hW₀ : IsClosedSubmanifold n (e.symm ⁻¹' W)) (hE₀ : IsSNCDivisor n (E.map (e.symm ⁻¹' ·)))
    (T : BlowupTower X₀ Y₀) (hT : IsSharpTerminalTower (e.symm ⁻¹' W) (E.map (e.symm ⁻¹' ·)) T) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y), IsSharpTerminalTower W E Q := by
  let R := transport (e.trans (liftDiffeomorph.{u} X₀)) (liftTower.{u} T)
  exact ⟨R.target, R.tower, sharpTerminal_transportLift e W E hW₀ hE₀ T hT⟩

/-- In ambient dimension zero the identity gives a full sharp terminal history. -/
theorem sharpTerminal_zero {X : CMfd.{u} 0} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold 0 W) (hE : IsSNCDivisor 0 E) :
    IsSharpTerminalTower W E (BlowupTower.refl (X := X)) := by
  refine ⟨trivial,trivial,trivial,?_⟩
  exact hasNormalCrossings_of_regularAtDim_zero hE fun x hx => by
    obtain ⟨d, hd⟩ := hW.2 x hx
    obtain rfl : d = 0 := Nat.eq_zero_of_le_zero hd.1
    exact hd

/-- Compact sharp cleanup for arbitrary ambient universes and dimensions. -/
theorem exists_compact_full_boundary_sharp_cleanup {n : ℕ} {X : CMfd.{u} n}
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      let WQ := geoTransformAlong (geometricTemplate W []) Q
      let FQ := (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E
      IsGeoTestTower (geometricTemplate W []) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧ CurrentSharpCentres W E Q ∧
      CentresOver (originalSharpBadLocus (n := n) W E) Q ∧
      IsClosedSubmanifold n WQ.N ∧ IsSNCDivisor n FQ ∧ HasNormalCrossings n WQ.N FQ ∧
      IsProperMap Q.proj ∧ IsIsomorphismOver n Q.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  classical
  by_cases hn : 0 < n
  · let X₀ := shrinkCMfd X
    let e := shrinkDiffeomorph X
    let W₀ : Set X₀ := e.symm ⁻¹' W
    let E₀ := E.map (e.symm ⁻¹' ·)
    have hW₀ : IsClosedSubmanifold n W₀ := transported_closedSubmanifold e.toHomeomorph W hW
    have hE₀ : IsSNCDivisor n E₀ := transported_list_snc X e.toHomeomorph E hE
    have hBadEq : originalSharpBadLocus (n := n) W₀ E₀ =
        e '' originalSharpBadLocus (n := n) W E := by
      ext z
      change z ∈ originalSharpBadLocus (n := n) W₀ E₀ ↔
        z ∈ e.toEquiv '' originalSharpBadLocus (n := n) W E
      rw [e.toEquiv.image_eq_preimage_symm]
      change (z ∈ W₀ ∧ ¬normalCrossingsAt (n := n) W₀ E₀ z) ↔
        (e.symm z ∈ W ∧ ¬normalCrossingsAt (n := n) W E (e.symm z))
      exact and_congr Iff.rfl (not_congr (transported_normalCrossingsAt_iff e.toHomeomorph W E z))
    have hK₀ : IsCompact (originalSharpBadLocus (n := n) W₀ E₀) := by
      rw [hBadEq]
      exact hK.image e.continuous
    obtain ⟨Y₀, T, hTCarrier, hTAmbient, hTSharp, _, _, _, hTNC, _, _⟩ :=
      exists_actual_compact_sharp_cleanup_full_boundary hn hW₀ hE₀ hK₀
    rw [N_geoTransformAlong] at hTNC
    obtain ⟨Y, Q, hQ⟩ := sharpTerminal_of_small_biholomorphism e W E hW₀ hE₀ T
      ⟨hTCarrier, hTAmbient, hTSharp, hTNC⟩
    obtain ⟨hOver, hSmooth, hSNC, hProper, hIso⟩ := sharpTerminal_full_geometry hW hE Q hQ
    exact ⟨Y, Q, hQ.carrierTest, hQ.boundaryTest, hQ.sharp, hOver,
      by simpa only [N_geoTransformAlong, show (geometricTemplate W []).N = W from rfl] using hSmooth, hSNC,
      by simpa only [N_geoTransformAlong, show (geometricTemplate W []).N = W from rfl] using hQ.normalCrossings, hProper, hIso⟩
  · have hn0 : n = 0 := by omega
    subst n
    have h := sharpTerminal_zero hW hE
    obtain ⟨hOver, _, _, hProper, hIso⟩ := sharpTerminal_full_geometry hW hE (.refl : BlowupTower X X) h
    exact ⟨X, .refl, trivial, trivial, trivial, hOver, hW, hE, h.normalCrossings, hProper, hIso⟩

end
end Hironaka.HironakaG4FullBoundaryUniverse

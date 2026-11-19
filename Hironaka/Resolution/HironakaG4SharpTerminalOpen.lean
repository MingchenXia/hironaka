import Hironaka.Resolution.HironakaG4SharpTerminalAtlas
import Hironaka.Resolution.HironakaActualProtectedGammaOpenCompatibility
import Hironaka.Resolution.HironakaCompactFootprintSharpExtension
import Hironaka.Resolution.HironakaG4BoundaryRestrict
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes

/-! Open restriction and physical rebasing of the full sharp terminal tower. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SharpTerminalOpen

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HomogenizedGlueingTower HironakaSharpActualFiniteChronologicalHistory HironakaG4SharpTerminalAtlas
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport NormalCrossings NormalCrossingsInvariance IdealWeightPowers
  HironakaG34NonPureLowDim HironakaActualProtectedGammaOpenCompatibility
  HironakaCompactFootprintSharpExtension HironakaG4BoundaryRestrict MaxLocusLocal RestrictEmptyTower
  HironakaG4SharpBadFootprint HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalDynamicGoodPrefixes
  SimultaneousNormalCrossings

/-- Each literal sharp terminal tower has its centres over the original
bad locus, with smooth strict carrier, full SNC boundary and good-locus isomorphism. -/
theorem sharpTerminal_full_geometry {n : ℕ} {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsSharpTerminalTower W E T) :
    CentresOver (originalSharpBadLocus (n := n) W E) T ∧
    IsClosedSubmanifold n (strictAlong T W) ∧
    IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E ∧
    IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  have hC : (geometricTemplate W []).IsWellFormed :=
    ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hM : (geometricTemplate (univ : Set X) E).IsWellFormed := ⟨isClosedSubmanifold_univ,
    IdealWeightPowers.isCoherent_unitIdeal, hE, isTransverse_univ_of_isSNCDivisor hE⟩
  have hOver := (currentSharpCentres_original_footprint hW.1 hE.1 T hT.sharp).2
  have hSmooth :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hC T hT.carrierTest).isClosedSubmanifold_N
  rw [N_geoTransformAlong] at hSmooth
  exact ⟨hOver, hSmooth,
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.boundaryTest).isSNCDivisor,
    HironakaLocalPrincipalization.isProperMap_proj T,
    isIsomorphismOver_proj_of_centresOver _ T hOver⟩

/-- The actual restricted tower retains both tests, current sharpness and
the final normal crossings against the literal restricted boundary. -/
theorem sharpTerminal_restrict {n : ℕ} {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (V : Opens X) (T : BlowupTower X Y)
    (hT : IsSharpTerminalTower W E T) :
    IsSharpTerminalTower ((Subtype.val : V → X) ⁻¹' W) (E.map ((Subtype.val : V → X) ⁻¹' ·))
      (restrict V T) := by
  let XV := CMfd.of (n := n) V
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let M := geometricTemplate (univ : Set X) E
  have hMG : MarkedIdeal.pullback (Subtype.val : V → X) M = geometricTemplate (univ : Set XV) EV := by
    rw [template_pullback (Y := XV), preimage_univ]
  have hCG : MarkedIdeal.pullback (Subtype.val : V → X) (geometricTemplate W []) =
      geometricTemplate (X := XV) WV [] := by rw [template_pullback (Y := XV), List.map_nil]
  have hCarrier := isGeoTestTower_restrict V hW isCoherent_unitIdeal T hT.carrierTest
  have hAmbient := isGeoTestTower_restrict V isClosedSubmanifold_univ isCoherent_unitIdeal T hT.boundaryTest
  rw [hCG] at hCarrier
  rw [hMG] at hAmbient
  refine ⟨hCarrier, hAmbient, currentSharp_restrict V T hT.boundaryTest hT.sharp, ?_⟩
  have hE := boundary_geoTransformAlong_restrict M V T
  rw [hMG] at hE
  rw [strictAlong_restrict V T W, hE]
  exact hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T V)) hT.normalCrossings

/-- A given biholomorphism of source manifolds transports the entire
terminal tower, including its literal chronological boundary. -/
theorem sharpTerminal_rebase {n : ℕ} {X X' Y : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (hT : IsSharpTerminalTower W E T) :
    IsSharpTerminalTower (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower := by
  let A := e ⁻¹' W
  let F := E.map (e ⁻¹' ·)
  let R := transport e T
  let M := geometricTemplate (univ : Set X) E
  have hIso := transport_isTowerIso e T
  have hC := (isGeoTestTower_transport_iff e isCoherent_unitIdeal T).mpr hT.carrierTest
  have hF := (isGeoTestTower_transport_iff e isCoherent_unitIdeal T).mpr hT.boundaryTest
  have hPull : MarkedIdeal.pullback e M = geometricTemplate (univ : Set X') F := by
    rw [template_pullback (Y := X'), preimage_univ]
  rw [template_pullback (Y := X'), List.map_nil] at hC
  rw [hPull] at hF
  have hBackW : e.symm ⁻¹' A = W := by
    ext x
    change e (e.symm x) ∈ W ↔ x ∈ W
    rw [e.apply_symm_apply]
  have hBackE : F.map (e.symm ⁻¹' ·) = E := by
    dsimp only [F]
    rw [List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id E)
    intro H _
    ext x
    change e (e.symm x) ∈ H ↔ x ∈ H
    rw [e.apply_symm_apply]
  have hSharp := currentSharp_of_isTowerIso A F e.symm hIso.symm hF
  rw [hBackW, hBackE] at hSharp
  have hE := congrArg MarkedIdeal.E (IsTowerIso.geoTransformAlong_eq e
    isClosedSubmanifold_univ isCoherent_unitIdeal hIso hT.boundaryTest)
  rw [hPull] at hE
  refine ⟨hC, hF, hSharp hT.sharp, ?_⟩
  rw [hIso.strictAlong_eq W, hE]
  exact hasNormalCrossings_preimage (pullsBackCoordinates R.back) hT.normalCrossings

set_option backward.isDefEq.respectTransparency false in
/-- A containing source open can be replaced by any prescribed smaller
original open using the literal restriction and the nested-open isomorphism. -/
theorem sharpTerminal_on_smaller_open {n : ℕ} {X Y : CMfd.{u} n}
    {W : Set X} (hW : IsClosedSubmanifold n W) (E : List (Set X))
    (V U : Opens X) (hUV : U ≤ V) (T : BlowupTower (CMfd.of (n := n) V) Y)
    (hT : IsSharpTerminalTower ((Subtype.val : V → X) ⁻¹' W) (E.map ((Subtype.val : V → X) ⁻¹' ·)) T) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) U) Z),
      IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) R := by
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hUV).symm
  let R := transport e (restrict D T)
  let WD := (Subtype.val : D → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W)
  let ED := (E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : D → V) ⁻¹' ·)
  have hWV := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW V
  have hD := sharpTerminal_restrict hWV D T hT
  have hR := sharpTerminal_rebase e WD ED (restrict D T) hD
  have hList : ED.map (e ⁻¹' ·) = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    dsimp only [ED]
    rw [List.map_map, List.map_map]
    rfl
  rw [hList] at hR
  exact ⟨R.target, R.tower, hR⟩

end
end Hironaka.HironakaG4SharpTerminalOpen

import Hironaka.Resolution.HironakaG4UnitTemplate
import Hironaka.Resolution.HironakaActualFullBoundaryCurveEndpointHistories

/-! Lift an actual-member unit template from a nested source window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4AmbientUnitTemplate
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsInvariance MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupRestrictOpen
  HironakaSharpActualFiniteChronologicalHistory IdealWeightPowers GermIdealPullbackCalculus
  HironakaActualFullBoundaryCurveEndpointHistories DivisorExponentAlong MonomialPartAlong
  NonmonomialTransformAlong RestrictedIdealExtension RelativePrincipalizationSpan

variable {n : ℕ} {X : CMfd.{u} n}

/-- A well-formed actual-member template on a nested open can be read as an
ambient template on its open image, with the slice identity preserved. -/
theorem ambient_actual_member_template_of_nested_open
    (U : Opens X) (V : Opens (CMfd.of (n := n) U)) (N H S : Set X) (F : List (Set X))
    (hN : IsClosedSubmanifold n N)
    (hD : (MarkedIdeal.pullback (Subtype.val : V → U)
      (geometricTemplate ((Subtype.val : U → X) ⁻¹' N)
        ((Subtype.val : U → X) ⁻¹' H :: F.map ((Subtype.val : U → X) ⁻¹' ·)))).IsWellFormed)
    (hSlice : (Subtype.val : V → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' S) =
      (Subtype.val : V → U) ⁻¹' (((Subtype.val : U → X) ⁻¹' N) ∩ ((Subtype.val : U → X) ⁻¹' H))) :
    let W := ambientOpen U V
    (MarkedIdeal.pullback (Subtype.val : W → X) (geometricTemplate N (H :: F))).IsWellFormed ∧
      (Subtype.val : W → X) ⁻¹' S = (Subtype.val : W → X) ⁻¹' (N ∩ H) := by
  dsimp only
  let W := ambientOpen U V
  let χ := (flattenOpenEquiv U V).symm
  have hχ : ∀ w : W, ((χ w : V) : U).val = w.val := fun w => flattenOpenEquiv_symm_apply U V w
  have hSNC := isSNCDivisor_map_preimage (MarkedIdealTowerTransport.pullsBackCoordinates χ)
    χ.continuous hD.isSNCDivisor
  have hTr := isTransverse_preimage (MarkedIdealTowerTransport.pullsBackCoordinates χ) hD.isTransverse
  have hPre (A : Set X) : χ ⁻¹' ((Subtype.val : V → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' A)) =
      (Subtype.val : W → X) ⁻¹' A := by
    ext w
    exact Iff.of_eq (congrArg (fun z => z ∈ A) (hχ w))
  have hList : (((H :: F).map ((Subtype.val : U → X) ⁻¹' ·)).map
      ((Subtype.val : V → U) ⁻¹' ·)).map (χ ⁻¹' ·) =
      (H :: F).map ((Subtype.val : W → X) ⁻¹' ·) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro A hA
    exact hPre A
  refine ⟨?_,?_⟩
  · refine ⟨isClosedSubmanifold_preimage_val hN W,
      isCoherent_pullback contMDiff_subtype_val (isCoherent_unitIdeal (n := n) (M := X)), ?_, ?_⟩
    · change IsSNCDivisor n ((H :: F).map ((Subtype.val : W → X) ⁻¹' ·))
      change IsSNCDivisor n ((((H :: F).map ((Subtype.val : U → X) ⁻¹' ·)).map
        ((Subtype.val : V → U) ⁻¹' ·)).map (χ ⁻¹' ·)) at hSNC
      rw [hList] at hSNC
      exact hSNC
    · change IsTransverse n ((Subtype.val : W → X) ⁻¹' N) ((H :: F).map ((Subtype.val : W → X) ⁻¹' ·))
      change IsTransverse n (χ ⁻¹' ((Subtype.val : V → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' N)))
        ((((H :: F).map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : V → U) ⁻¹' ·)).map (χ ⁻¹' ·)) at hTr
      rw [hPre N,hList] at hTr
      exact hTr
  · ext w
    have hh := Set.ext_iff.mp hSlice (χ w)
    simpa only [Set.mem_preimage,Set.mem_inter_iff,hχ] using hh

/-- The unit residual data on the original protected open window construct
the well-formed actual-member template on a smaller ambient open. -/
theorem exists_ambient_unit_member_template (hn : 0 < n)
    (U : Opens X) (x : U) (N H S : Set X) (F : List (Set X)) (Haux : Set U)
    (B L : List (Set U)) (hN : IsClosedSubmanifold n N)
    (hEF : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTF : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (Haux :: F.map ((Subtype.val : U → X) ⁻¹' ·)))
    (hL : IsSNCDivisor n L) (hHL : (Subtype.val : U → X) ⁻¹' H ∈ L)
    (hxN : x ∈ (Subtype.val : U → X) ⁻¹' N) (hxHaux : x ∈ Haux)
    (hI : (RestrictedIdealExtension.restrictOn n ((Subtype.val : U → X) ⁻¹' N)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))).IsCoherent)
    (hnz : IsNonzeroAlongAt ((Subtype.val : U → X) ⁻¹' N)
      (RestrictedIdealExtension.restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) x)
    (hunit : (MonomialPartAlong.monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (RestrictedIdealExtension.restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mem x 1)
    (hJZ : ∀ g, (nonmonomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
      (RestrictedIdealExtension.restrictOn n ((Subtype.val : U → X) ⁻¹' N)
        (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))) B).mem x g ↔
      (vanishingIdeal (n := n) (((Subtype.val : U → X) ⁻¹' N) ∩ Haux)).mem x g)
    (hSlice : (Subtype.val : U → X) ⁻¹' S = ((Subtype.val : U → X) ⁻¹' N) ∩ Haux) :
    ∃ W : Opens X, (x : X) ∈ W ∧ (W : Set X) ⊆ U ∧
      (MarkedIdeal.pullback (Subtype.val : W → X) (geometricTemplate N (H :: F))).IsWellFormed ∧
      (Subtype.val : W → X) ⁻¹' S = (Subtype.val : W → X) ⁻¹' (N ∩ H) := by
  obtain ⟨V,hxV,hDV,hSliceV⟩ := HironakaG4UnitTemplate.exists_unit_member_template
    (X := CMfd.of (n := n) U) hn (isClosedSubmanifold_preimage_val hN U)
      hEF hTF hL hHL hxN hxHaux hI hnz hunit hJZ
  let W := ambientOpen U V
  have hS : (Subtype.val : V → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' S) =
      (Subtype.val : V → U) ⁻¹' (((Subtype.val : U → X) ⁻¹' N) ∩ ((Subtype.val : U → X) ⁻¹' H)) := by
    rw [hSlice]
    exact hSliceV
  have hW := ambient_actual_member_template_of_nested_open U V N H S F hN hDV hS
  refine ⟨W,⟨x,hxV,rfl⟩,?_,hW.1,hW.2⟩
  rintro y ⟨z,hz,rfl⟩
  exact z.property

end
end Hironaka.HironakaG4AmbientUnitTemplate

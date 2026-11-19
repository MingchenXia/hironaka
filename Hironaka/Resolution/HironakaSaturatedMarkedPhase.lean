import Hironaka.Resolution.HironakaSaturatedTowerAppend
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Test and full boundary readback on a saturated, geometrically appended
phase. The prefix and suffix records may have different ideals and marks. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaSaturatedMarkedPhase

open BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MaxLocusLocal HironakaCoherentTransformExtension

/-- Read both test records and the whole ordered terminal boundary on the
same saturated restriction, when the original suffix boundary is the actual
final prefix list. -/
theorem saturated_marked_phase_restrict {n : ℕ} {X Y Z : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (N : MarkedIdeal n Y) (hN : N.IsWellFormed) (hE : N.E = (geoTransformAlong M T).E)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hS : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → Y) N) S)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let U := openPreimage T O
    let D := nestedOpens V U
    let e := (nestedOpensDiffeo (n := n) hOV).symm
    let tail := transport e (restrict D S)
    let A := (restrict O T).append tail.tower
    let MO := MarkedIdeal.pullback (Subtype.val : O → X) M
    let NU := MarkedIdeal.pullback (Subtype.val : U → Y) N
    let NV := MarkedIdeal.pullback (Subtype.val : V → Y) N
    let b : tail.target → Z := fun z => (tail.back z).val
    IsGeoTestTower MO (restrict O T) ∧ IsGeoTestTower NU tail.tower ∧
    (geoTransformAlong MO (restrict O T)).E = NU.E ∧
    (geoTransformAlong MO A).E = (geoTransformAlong NV S).E.map (b ⁻¹' ·) := by
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let tail := transport e (restrict D S)
  let A := (restrict O T).append tail.tower
  let MO := MarkedIdeal.pullback (Subtype.val : O → X) M
  let NU := MarkedIdeal.pullback (Subtype.val : U → Y) N
  let NV := MarkedIdeal.pullback (Subtype.val : V → Y) N
  let ND := MarkedIdeal.pullback (Subtype.val : D → V) NV
  let b : tail.target → Z := fun z => (tail.back z).val
  have hNV := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN V
  have hND := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hNV D
  have hRec : MarkedIdeal.pullback e ND = NU := pullback_symm_nestedOpensDiffeo hN.isCoherent hOV
  have hL : IsGeoTestTower MO (restrict O T) :=
    isGeoTestTower_restrict O hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hR : IsGeoTestTower ND (restrict D S) :=
    isGeoTestTower_restrict D hNV.isClosedSubmanifold_N hNV.isCoherent S hS
  have hTail : IsGeoTestTower NU tail.tower := hRec ▸
    (IsTowerIso.isGeoTestTower_iff e hND.isClosedSubmanifold_N hND.isCoherent
      (transport_isTowerIso e (restrict D S))).mpr hR
  have hCurrentE : (geoTransformAlong MO (restrict O T)).E = NU.E := by
    rw [geoTransformAlong_restrict O hM.isClosedSubmanifold_N hM.isCoherent T hT]
    change (geoTransformAlong M T).E.map ((Subtype.val : U → Y) ⁻¹' ·) = N.E.map ((Subtype.val : U → Y) ⁻¹' ·)
    rw [hE]
  refine ⟨hL, hTail, hCurrentE, ?_⟩
  have hTailEq := IsTowerIso.geoTransformAlong_eq e hND.isClosedSubmanifold_N hND.isCoherent
    (transport_isTowerIso e (restrict D S)) hR
  rw [hRec, geoTransformAlong_restrict D hNV.isClosedSubmanifold_N hNV.isCoherent S hS] at hTailEq
  change (geoTransformAlong MO A).E = _
  rw [geoTransformAlong_append, geoTransformAlong_E_eq_of_E_eq hCurrentE tail.tower, hTailEq]
  change (((geoTransformAlong NV S).E.map ((Subtype.val : openPreimage S D → Z) ⁻¹' ·)).map
      (tail.back ⁻¹' ·)) = (geoTransformAlong NV S).E.map (b ⁻¹' ·)
  rw [List.map_map]
  rfl

end Hironaka.HironakaSaturatedMarkedPhase

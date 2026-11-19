import Hironaka.Resolution.HironakaG8RestrictedBirthTest
import Hironaka.Resolution.HironakaG11RestrictedHistoryExponent
import Hironaka.Resolution.HironakaG11PositiveBornHistoryOrder
/-! # Positive born history above mark on a domain open -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PositiveBornDomainOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal GermIdealOrder DivisorExponentAlong ResolutionInvariantSpec
  HironakaG8RestrictedBirthTest HironakaG11RestrictedHistoryExponent HironakaG11PositiveBornHistoryOrder

/-- A positive born exponent along an actual suffix forces above-mark source
order near the centre whenever the original record is in the invariant
domain on a source open around the birth projection. -/
theorem above_mark_of_positive_born_on_domain_open
    {n : ℕ} {X Y Z : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (T : BlowupTower Y Z) (hT : IsGeoTestTower (M.geoTransform C π) T)
    (G : Opens X) {k : ℕ} (hMG : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : G → X) M))
    {z : Z} (hzG : π (T.proj z) ∈ G)
    (hzN : z ∈ (geoTransformAlong (M.geoTransform C π) T).N)
    (hzD : z ∈ strictAlong T (π ⁻¹' C))
    (hpos : 0 < divExpAlong n (geoTransformAlong (M.geoTransform C π) T).N
      (geoTransformAlong (M.geoTransform C π) T).ideal (strictAlong T (π ⁻¹' C)) z) :
    ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ cosupport n M.N M.ideal (M.d+1) := by
  let V : Opens Y := ⟨π ⁻¹' (G : Set X), G.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → G := fun p => ⟨π p.val,p.2⟩
  let C' : Set G := (Subtype.val : G → X) ⁻¹' C
  let M' := MarkedIdeal.pullback (Subtype.val : G → X) M
  let z' : openPreimage T V := ⟨z,hzG⟩
  let p' : G := ⟨π (T.proj z),hzG⟩
  have hρ : IsBlowupAlong n C' ρ := BlowupRestrictOpen.isBlowupAlong_restrict hπ G V.isOpen
  obtain ⟨hC',heq,hT'⟩ := restrict_birth_and_suffix M hM hC hπ T hT G
  let One : BlowupTower X Y := .step .refl C π hπ
  have hOne : IsGeoTestTower M One := ⟨trivial,hC⟩
  have hPost : (M.geoTransform C π).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM One hOne
  have hzN' : z' ∈ (geoTransformAlong (M'.geoTransform C' ρ) (restrict V T)).N := by
    rw [heq, geoTransformAlong_restrict V hPost.isClosedSubmanifold_N hPost.isCoherent T hT]
    exact hzN
  have hzD' : z' ∈ strictAlong (restrict V T) (ρ ⁻¹' C') := by
    change z' ∈ strictAlong (restrict V T) ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' C))
    rw [strictAlong_restrict V T]
    exact hzD
  have hexp := divExpAlong_restricted_test_history (M.geoTransform C π) hPost V T hT (π ⁻¹' C) z'
  have hpos' : 0 < divExpAlong n (geoTransformAlong (M'.geoTransform C' ρ) (restrict V T)).N
      (geoTransformAlong (M'.geoTransform C' ρ) (restrict V T)).ideal
      (strictAlong (restrict V T) (ρ ⁻¹' C')) z' := by
    rw [heq]
    change 0 < divExpAlong n (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Y) (M.geoTransform C π)) (restrict V T)).N
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Y) (M.geoTransform C π)) (restrict V T)).ideal
      (strictAlong (restrict V T) ((Subtype.val : V → Y) ⁻¹' (π ⁻¹' C))) z'
    rw [hexp]
    exact hpos
  have h := above_mark_on_centre_of_positive_born_history
    (X := CMfd.of (n := n) G) (Y := CMfd.of (n := n) V) (Z := CMfd.of (n := n) (openPreimage T V)) M' hMG hC' hρ (restrict V T) hT' hzN' hzD' hpos'
  have hpoint : ρ ((restrict V T).proj z') = p' := by
    apply Subtype.ext
    change π (((restrict V T).proj z' : V) : Y) = π (T.proj z)
    rw [proj_restrict V T z']
  rw [hpoint] at h
  have hcos : cosupport n ((Subtype.val : G → X) ⁻¹' M.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) M.ideal) (M.d+1) =
      (Subtype.val : G → X) ⁻¹' cosupport n M.N M.ideal (M.d+1) :=
    cosupp_pullback_val (⟨M.N,[],M.ideal,M.d+1⟩ : MarkedIdeal n X) (hol_of_isCoherent hM.isCoherent) G
  have hevent : ∀ᶠ x : G in 𝓝 p', x.val ∈ C → x.val ∈ cosupport n M.N M.ideal (M.d+1) := by
    filter_upwards [h] with x hx hxC
    have hx' := hx hxC
    change x ∈ cosupport n ((Subtype.val : G → X) ⁻¹' M.N)
      (GermIdeal.pullback (m := n) (Subtype.val : G → X) M.ideal) (M.d+1) at hx'
    rw [hcos] at hx'
    exact hx'
  have hmap : Filter.map (Subtype.val : G → X) (𝓝 p') = 𝓝 (π (T.proj z)) :=
    map_nhds_subtype_coe_eq_nhds p'.2 (G.isOpen.mem_nhds p'.2)
  have hh : ∀ᶠ x in Filter.map (Subtype.val : G → X) (𝓝 p'),
      x ∈ C → x ∈ cosupport n M.N M.ideal (M.d+1) := Filter.eventually_map.mpr hevent
  rwa [hmap] at hh

end
end Hironaka.HironakaG8PositiveBornDomainOpen

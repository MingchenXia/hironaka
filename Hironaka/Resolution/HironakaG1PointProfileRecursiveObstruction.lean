import Hironaka.Resolution.HironakaG1CartierTwoAnchors
import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile
import Hironaka.Resolution.HironakaG8BFamilyEmptyMember

/-! The reduced point profile does not encode the recursive padded letter. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1PointProfileRecursiveObstruction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HironakaG1CartierTwoAnchors HironakaG1TwoZeroBornCounts
  HironakaG1LaterPositiveNormalExample HironakaActualOpenZeroSectionDifferentials
  HironakaG8LocalHistory HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalContact
  HironakaActualRegularIntrinsicHSProfile HironakaHolomorphicJetChartInvariance
  BlowupFlatCoordinates HironakaActualRelativeNormalGeometry BlowupStrictSubmanifold NormalCrossings

private abbrev K : Set Y := (geoTransformAlong P B).cosupp
private abbrev paddedValue := Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P B
private abbrev sectionValue := Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S B

/-- Both actual marked records have the same whole controlled cosupport. -/
theorem cartier_controlled_cut_eq : K = (geoTransformAlong S B).cosupp := by
  have hTest : P.IsGeoTestTower B :=
    (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
      (invFamily (by decide : 0 < 3) 2) P (properNormalMarked_isInvDomain record record_domain)
      (properNormalMarked_maximalOrder record record_domain.isWellFormed.isCoherent)
      (by decide) B cartier_common_first_canonical.1).2.1
  exact ((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 B).2 hTest

private def axes : Finset (Fin 3) := {0,2}

private theorem line_eq_coordinate_preimage :
    linearLine = (Subtype.val : productOpen HironakaG1TwoZeroBornCounts.U → ComplexModel 3) ⁻¹'
      coordSubspace axes := by
  ext x
  change (x.val 0 = 0 ∧ x.val 2 = 0) ↔ ∀ i ∈ axes, x.val i = 0
  simp [axes]

private theorem cartier_line_regular (x : HironakaG1TwoZeroBornCounts.X) (hx : x ∈ linearLine) :
    RegularAtDim (n := 3) linearLine x 1 := by
  have hx' : x.val ∈ coordSubspace axes := by
    rw [line_eq_coordinate_preimage] at hx
    exact hx
  have hdim : 3 - axes.card = 1 := by decide
  have hModel := HironakaG8BFamilyEmptyMember.regularAtDim_coordSubspace axes hx'
  rw [hdim] at hModel
  rw [line_eq_coordinate_preimage]
  exact (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (x := x)).mpr hModel

private theorem cartier_centre_subset : ({p₀} : Set HironakaG1TwoZeroBornCounts.X) ⊆ linearLine := by
  intro x hx
  have he : x = p₀ := mem_singleton_iff.mp hx
  subst x
  have h0 : p₀.val = 0 := map_zero (HironakaRelativeNormalIdeal.tangentInclusion 2 1)
  exact ⟨congrArg (fun w : ComplexModel 3 => w 0) h0,congrArg (fun w : ComplexModel 3 => w 2) h0⟩

set_option maxHeartbeats 500000 in
private theorem cartier_controlled_cut_regular (y : Y) (hy : y ∈ K) :
    RegularAtDim (n := 3) K y 1 := by
  have hClosed : IsClosed linearLine := by
    rw [line_eq_coordinate_preimage]
    exact (HironakaG8BFamilyEmptyMember.isClosed_coordSubspace axes).preimage continuous_subtype_val
  have hK : K = geoStrictTransform π {p₀} linearLine := cartier_endpoint_cosupport
  have hy' : y ∈ geoStrictTransform π {p₀} linearLine := hK ▸ hy
  exact hK.symm ▸ regularAtDim_geoStrictTransform hπ hClosed cartier_line_regular cartier_centre_subset hy'

/-- Every endpoint point on the common cut has the same whole reduced
profile, in every degree, namely that of a regular complex curve. -/
theorem cartier_controlled_cut_profile (y : Y) (hy : y ∈ K) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) K) y ℓ = (1+ℓ).choose 1 :=
  hilbertSamuelAt_actual_regular (by decide) (cartier_controlled_cut_regular y hy) ℓ

/-- Even the complete section Step One value together with the entire
reduced profile cannot determine the padded Step One value on this
genuine common canonical prefix. -/
theorem cartier_no_stepOne_recode_from_profile :
    ¬ ∃ ρ : (ℕ → ℕ) → (ℕ ×ₗ WithTop (ValTy 1)) → (ℕ ×ₗ WithTop (ValTy 2)),
      ∀ y ∈ K,
        ρ (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := 3) K) y ℓ) (sectionValue y) =
          paddedValue y := by
  rintro ⟨ρ,hρ⟩
  have hEqCut := cartier_controlled_cut_eq
  have hMax : maxLocus sectionValue K = K := by
    rw [hEqCut]
    exact cartier_section_maximum_eq_cosupport
  have hTie (x y : Y) (hx : x ∈ K) (hy : y ∈ K) : sectionValue x = sectionValue y := by
    have hxm : x ∈ maxLocus sectionValue K := hMax.symm ▸ hx
    have hym : y ∈ maxLocus sectionValue K := hMax.symm ▸ hy
    exact le_antisymm (hym.2 x hx) (hxm.2 y hy)
  have hAll : maxLocus paddedValue K = K := by
    ext x
    refine ⟨fun h => h.1,fun hx => ⟨hx,?_⟩⟩
    intro y hy
    have hp : (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := 3) K) y ℓ) =
        (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := 3) K) x ℓ) := by
      funext ℓ
      exact (cartier_controlled_cut_profile y hy ℓ).trans
        (cartier_controlled_cut_profile x hx ℓ).symm
    rw [← hρ y hy,← hρ x hx,hp,hTie y x hy hx]
  exact cartier_common_prefix_maximum_discrepancy (hAll.trans (hMax.symm.trans (by rw [hEqCut])))


/-- The discrepancy is a strict padded order between two actual points
tied by both the section value and the entire reduced profile. -/
theorem cartier_tied_profiles_strict_padded_order :
    ∃ x ∈ K, ∃ y ∈ K,
      (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := 3) K) x ℓ =
        hilbertSamuelAt (vanishingIdeal (n := 3) K) y ℓ) ∧
      sectionValue x = sectionValue y ∧ paddedValue x < paddedValue y := by
  classical
  have hEqCut := cartier_controlled_cut_eq
  have hMax : maxLocus sectionValue K = K := by
    rw [hEqCut]
    exact cartier_section_maximum_eq_cosupport
  have hNon : ¬ K ⊆ maxLocus paddedValue K := by
    intro hIncl
    have hAll := Set.Subset.antisymm (fun _ hx => hx.1) hIncl
    exact cartier_common_prefix_maximum_discrepancy (hAll.trans (hMax.symm.trans (by rw [hEqCut])))
  obtain ⟨x,hx,hxm⟩ := Set.not_subset.mp hNon
  have hNot : ¬ ∀ y ∈ K, paddedValue y ≤ paddedValue x := fun h => hxm ⟨hx,h⟩
  push Not at hNot
  obtain ⟨y,hy,hLess⟩ := hNot
  have hxs : x ∈ maxLocus sectionValue K := hMax.symm ▸ hx
  have hys : y ∈ maxLocus sectionValue K := hMax.symm ▸ hy
  exact ⟨x,hx,y,hy,
    fun ℓ => (cartier_controlled_cut_profile x hx ℓ).trans (cartier_controlled_cut_profile y hy ℓ).symm,
    le_antisymm (hys.2 x hx) (hxs.2 y hy),hLess⟩

end
end Hironaka.HironakaG1PointProfileRecursiveObstruction

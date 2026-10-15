/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalWholeContactRemainderDomain
/-! One actual chosen contact model, uniform over every genuine extension of
an ANY original maximal-order test prefix. Retains the entire ordered boundary.
No automatic transversality or nonzero lower-domain assertion is made. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalNoncanonicalUniformContactPresentation
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  HomogenizedGlueingTower ContactStageKept ContactStageInvDomain
  ContactIndependenceAlong StepOneLowerDomain StepOneValue TangentDirectionAlong
  MaximalContactAlongTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaCoherentTransformExtension
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- Original maximal-order domain and ANY actual original test prefix internally
supply the fixed chosen tangent open and genuine coefficient contact geometry. -/
theorem exists_original_test_chosen_contact_geometry
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower M T₀)
    (y : Y) (hy : y ∈ (geoTransformAlong M T₀).cosupp) :
    let w := (tangentChoice M (T₀.proj y)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice M (T₀.proj y)).1 ∧ T₀.proj y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U w ∧
      let V := openPreimage T₀ U
      let L := contactMarkedKept M w T₀ V
      IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧
        ResolutionInvariantSpec.DimLE n L.N k ∧ 1 ≤ L.d ∧
        L.E = (geoTransformAlong M T₀).E.map (fun H => (Subtype.val : V → Y) ⁻¹' H) ∧
        L.cosupp = (Subtype.val : V → Y) ⁻¹' (geoTransformAlong M T₀).cosupp := by
  dsimp only
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hbar : IsGeoTestTower (barMarked M) T₀ := (he.2 T₀).1.mpr hT₀
  have hcs := (he.2 T₀).2 hbar
  have hybar : y ∈ (geoTransformAlong (barMarked M) T₀).cosupp := by rw [hcs]; exact hy
  obtain ⟨hyU, hw⟩ := tangentChoice_spec M (exists_tangent_of_mem_cosupp M
    hM.isWellFormed hM.one_le_d hmax T₀ hbar hybar)
  let U : Opens X := ⟨_, hw.isOpen⟩
  have hN := isClosedSubmanifold_strictAlong_stage_of_le M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
    U hw T₀ hT₀ (openPreimage T₀ U) subset_rfl
  have hI : (contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀
      (openPreimage T₀ U)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff M hM.isWellFormed.isCoherent
        hM.isWellFormed.isClosedSubmanifold_N _ T₀ hbar)
  have hdim0 := dimLE_strictAlong_stage M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d U hw T₀ hT₀ hM.dimLE
  have hdim : ResolutionInvariantSpec.DimLE n
      (contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀ (openPreimage T₀ U)).N k := by
    change ResolutionInvariantSpec.DimLE n ((Subtype.val : openPreimage T₀ U → Y) ⁻¹'
      strictAlong T₀ (M.N ∩ {x | (tangentChoice M (T₀.proj y)).2 x = 0})) k
    simpa only [show (k+1)-1=k by omega] using hdim0
  have hd : 1 ≤ (contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀
      (openPreimage T₀ U)).d := one_le_coeffMarkedAlong_d _
  have hE := geoTransformAlong_E_eq_of_E_eq (𝔍 := barMarked M) (𝔪 := M) rfl T₀
  have htail := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
    U hw T₀ (.refl : BlowupTower Y Y) hbar (openPreimage T₀ U) subset_rfl
  refine ⟨U, rfl, hyU, hw, hN, hI, hdim, hd, ?_, ?_⟩
  · change (geoTransformAlong (barMarked M) T₀).E.map _ = _
    rw [hE]
  · have hh := htail.2
    change (contactMarkedKept M (tangentChoice M (T₀.proj y)).2 T₀ (openPreimage T₀ U)).cosupp =
      (Subtype.val : openPreimage T₀ U → Y) ⁻¹' (geoTransformAlong (barMarked M) T₀).cosupp at hh
    exact hh.trans (congrArg (fun S => (Subtype.val : openPreimage T₀ U → Y) ⁻¹' S) hcs)

/-- ONE internally chosen coefficient contact model works for every genuine
original extension, preserving all actual maps, positions and cosupports. -/
theorem exists_original_test_uniform_contact_presentation
    (M : MarkedIdeal n X) (hM : IsInvDomain (k+1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower M T₀)
    (y : Y) (hy : y ∈ (geoTransformAlong M T₀).cosupp) :
    let w := (tangentChoice M (T₀.proj y)).2
    ∃ U : Opens X, (U : Set X) = (tangentChoice M (T₀.proj y)).1 ∧ T₀.proj y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U w ∧
      let V := openPreimage T₀ U
      let L := contactMarkedKept M w T₀ V
      IsClosedSubmanifold n L.N ∧ L.ideal.IsCoherent ∧
        ResolutionInvariantSpec.DimLE n L.N k ∧ 1 ≤ L.d ∧
        L.E = (geoTransformAlong M T₀).E.map (fun H => (Subtype.val : V → Y) ⁻¹' H) ∧
        L.cosupp = (Subtype.val : V → Y) ⁻¹' (geoTransformAlong M T₀).cosupp ∧
        ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z), IsGeoTestTower M (T₀.append Q) →
          IsGeoTestTower L (restrict V Q) ∧
          (geoTransformAlong L (restrict V Q)).cosupp =
            (Subtype.val : openPreimage Q V → Z) ⁻¹' (geoTransformAlong M (T₀.append Q)).cosupp := by
  dsimp only
  obtain ⟨U, hU, hyU, hw, hN, hI, hdim, hd, hE, hcs⟩ :=
    exists_original_test_chosen_contact_geometry M hM hmax T₀ hT₀ y hy
  refine ⟨U, hU, hyU, hw, hN, hI, hdim, hd, hE, hcs, ?_⟩
  intro Z Q hQ
  have he := coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d
  have hbar : IsGeoTestTower (barMarked M) (T₀.append Q) := (he.2 _).1.mpr hQ
  have ht := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
    U hw T₀ Q hbar (openPreimage T₀ U) subset_rfl
  exact ⟨ht.1, ht.2.trans (congrArg (fun S => (Subtype.val : openPreimage Q
    (openPreimage T₀ U) → Z) ⁻¹' S) ((he.2 _).2 hbar))⟩

end
end Hironaka.HironakaOriginalNoncanonicalUniformContactPresentation

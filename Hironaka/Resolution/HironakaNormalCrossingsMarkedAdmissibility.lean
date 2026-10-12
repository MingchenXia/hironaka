/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsTotalIdeal
import Hironaka.Resolution.HironakaHypersurfaceStrictIdeal
import Hironaka.Resolution.HironakaControlledTransform

/-! # Actual marking-one admissibility of the original NC separation

Original genuine NC charts internally supply the WHOLE original vanishing ideal
and whole invariant domain. Joint actual tower induction derives original-test
admissibility and ENTIRE differential strict-original containment in the SAME
current controlled cosupport. Every literal prefix has actual full domain,
controlled iteration equality, entire original pullback factorization and
invertibility, without caller cosupport/order/tower/termination certificates.

On the real finite terminal tower the SAME controlled original ideal is supported
on the actual augmented SNC list containing all new exceptionals and the ENTIRE
final original. Its WHOLE monomial equality and COMPLETE nonmonomial unit are
produced. This augmented list differs from the marked datum's boundary. No empty
terminal marked cosupport or completed marked resolution is claimed. Unrelated
marked ideals and the old ordered colex algorithm remain separate; G9 is OPEN.
Blueprint: `hironaka-normal-crossings-marked-admissibility-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsMarkedAdmissibility
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsSeparationChoiceComparison
  BlowupStrictSubmanifold HironakaStageCenters NormalCrossings GermIdealOrder
  Hironaka.ResolutionInvariantSpec HironakaControlledTransform IdealWeightPowers
open Hironaka
noncomputable section
variable {n : ℕ} {A B D : CMfd.{u} n}

theorem isInvDomain_originalMarkedIdeal {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) : IsInvDomain n (originalMarkedIdeal H) := by
  have hcoh : (vanishingIdeal (n := n) H).IsCoherent :=
    DivisorMetric.isCoherent_of_isInvertible (originalDivisor hH).isInvertible
  have hHa : IsComplexAnalyticSubset (n := n) H := by
    have h := CodimOneSupport.isComplexAnalyticSubset_zeroLocus hcoh
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1] at h
  exact HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_interior_eq_empty
    le_rfl hHa (interior_normalCrossingsCarrier_eq_empty hH)

theorem geoStrictTransform_subset_cosupp (M : MarkedIdeal n A) (hw : M.IsWellFormed)
    {C K : Set A} {π : B → A} (hπ : IsBlowupAlong n C π)
    (hc : M.IsAdmissibleCentre C) (hK : K ⊆ M.cosupp) :
    geoStrictTransform π C K ⊆ (M.geoTransform C π).cosupp := by
  have hnew := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hc hπ
  apply closure_minimal
  · rintro y ⟨hyK,hyC⟩
    exact TransformOffCentre.mem_cosupp_geoTransform_of_mem_cosupp M
      hw.isClosedSubmanifold_N.1 hπ hyC (hK hyK)
  · exact GiraudAlong.isClosed_cosupport_along hnew.isCoherent hnew.isClosedSubmanifold_N _

theorem higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T →
      IsGeoTestTower (originalMarkedIdeal H) T ∧
        strictTransform n T.proj H ⊆ (geoTransformAlong (originalMarkedIdeal H) T).cosupp
  | _, .refl, _ => by
    refine ⟨trivial, ?_⟩
    have hcos : (originalMarkedIdeal H).cosupp = H :=
      HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
    simpa only [BlowupTower.proj_refl,geoTransformAlong_refl,strictTransform,
      exceptionalLocus_id,sdiff_empty,hH.1.closure_eq,hcos,preimage_id] using (Subset.refl H)
  | _, .step T C π hπ, hc => by
    obtain ⟨hT,hsub⟩ := higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH T hc.1
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isInvDomain_originalMarkedIdeal hH).isWellFormed T hT
    obtain ⟨hh,r,hr,hbound,hceq,hne⟩ := hc.2
    have hgeometry := higherSeparationCentre_geometry hc.2
    have hCadm : (geoTransformAlong (originalMarkedIdeal H) T).IsAdmissibleCentre C := by
      refine ⟨hgeometry.2.1, (higherSeparationCentre_subset hc.2).trans hsub, ?_⟩
      rw [hceq]
      exact hasNormalCrossings_highest_boundary hh hbound
    refine ⟨⟨hT,hCadm⟩, ?_⟩
    have hnext := geoStrictTransform_subset_cosupp _ hw hπ hCadm hsub
    have hgeo := geoStrictTransform_highest_eq_strictTransform
      (isNormalCrossingsCarrier_of_boundaryAdapted hh) hr hbound
      (hceq ▸ hπ)
    rw [← hceq] at hgeo
    rw [hgeo] at hnext
    rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp
      T.contMDiff_proj hπ.contMDiff]
    exact hnext

/-- The actual internally generated NC procedure is a true original-ideal test tower. -/
theorem originalSeparation_isGeoTestTower {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsGeoTestTower (originalMarkedIdeal H) (originalSeparation hH).T :=
  (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp
    hH (originalSeparation hH).T (originalSeparation hH).centres).1

/-- The ENTIRE actual current original lies in the SAME original controlled cosupport. -/
theorem originalSeparation_strict_subset_cosupp {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    strictTransform n (originalSeparation hH).T.proj H ⊆
      (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).cosupp :=
  (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp
    hH (originalSeparation hH).T (originalSeparation hH).centres).2

private theorem stageCentres_head
    (P : ∀ {D : CMfd.{u} n}, BlowupTower A D → Set D → Prop) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D), StageCentres P T →
      ∀ i : ℕ, StageCentres P (BlowupTowerSplit.head T i)
  | _, .refl, hT, 0 => hT
  | _, .step _ _ _ _, hT, 0 => hT
  | _, .refl, _, _+1 => trivial
  | _, .step T _ _ _, hT, i+1 => stageCentres_head P T hT.1 i

/-- Every literal original prefix internally has full domain and whole strict-cosupport containment. -/
theorem originalSeparation_prefix_domain_and_strict {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    IsGeoTestTower (originalMarkedIdeal H) T ∧
      IsInvDomain n (geoTransformAlong (originalMarkedIdeal H) T) ∧
      strictTransform n T.proj H ⊆ (geoTransformAlong (originalMarkedIdeal H) T).cosupp := by
  dsimp only
  have hc := stageCentres_head _ _ (originalSeparation hH).centres i
  obtain ⟨hT,hstrict⟩ := higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH _ hc
  exact ⟨hT, InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (isInvDomain_originalMarkedIdeal hH) _ hT, hstrict⟩

private theorem stage_admissible_of_test (M : MarkedIdeal n A) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D), IsGeoTestTower M T →
      StageCentres (fun R C => (geoTransformAlong M R).IsAdmissibleCentre C) T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, hT => ⟨stage_admissible_of_test M T hT.1,hT.2⟩

/-- Every actual recorded centre is admissible for the ACTUAL current controlled original ideal. -/
theorem originalSeparation_stage_admissible {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    StageCentres (fun R C => (geoTransformAlong (originalMarkedIdeal H) R).IsAdmissibleCentre C)
      (originalSeparation hH).T :=
  stage_admissible_of_test _ _ (originalSeparation_isGeoTestTower hH)

/-- The SAME whole controlled original ideal on the internally generated terminal tower. -/
def originalControlledIdeal {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    GermIdeal n (originalSeparation hH).D :=
  (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).ideal

/-- Actual whole marked transforms agree with the literal iterated marking-one controlled ideal. -/
theorem originalControlledIdeal_eq_literalControlledTransformAlong {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    originalControlledIdeal hH =
      controlledTransformAlong (vanishingIdeal (n := n) H) (originalSeparation hH).T := by
  exact (controlledTransformAlong_eq (originalMarkedIdeal H) rfl
    (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent
    (originalSeparation hH).T (originalSeparation_isGeoTestTower hH)).symm

/-- The COMPLETE original pullback equals actual exceptional factor times the SAME whole controlled ideal. -/
theorem pullback_eq_exceptional_mul_originalControlledIdeal {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    GermIdeal.pullback (m := n) (originalSeparation hH).T.proj (vanishingIdeal (n := n) H) =
      (BlowupTowerTransforms.exceptionalDivisor (originalSeparation hH).T).ideal.mul
        (originalControlledIdeal hH) := by
  have h := (pullback_eq_mul_geoTransformAlong (originalMarkedIdeal H) rfl
    (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent
    (originalSeparation hH).T (originalSeparation_isGeoTestTower hH)).2.2
  simpa only [originalMarkedIdeal,originalControlledIdeal,FactorizationFromResolution.idealPow_one_of_isCoherent
    (BlowupExceptionalDivisor.isCoherent_ideal _)] using h

/-- Actual admissible controlled transforms of the SAME invertible whole ideal stay invertible. -/
theorem isInvertible_geoTransformAlong_of_test (M : MarkedIdeal n A)
    (hN : M.N = univ) (hI : M.ideal.IsInvertible) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D), IsGeoTestTower M T →
      (geoTransformAlong M T).ideal.IsInvertible
  | _, .refl, _ => hI
  | _, .step T C π hπ, hT => by
    have hcoh := DivisorMetric.isCoherent_of_isInvertible hI
    obtain ⟨hNT,hIT,_⟩ := pullback_eq_mul_geoTransformAlong M hN hcoh T hT.1
    have hle := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hIT hT.2
    rw [geoTransformAlong_step,geoTransform_ideal_eq_controlledTransform hNT hIT hπ]
    exact HironakaHypersurfaceStrictIdeal.isInvertible_controlledTransform hπ
      (isInvertible_geoTransformAlong_of_test M hN hI T hT.1) _ hle

/-- Every literal generated prefix has the SAME whole controlled iteration, true original factorization and invertibility. -/
theorem originalSeparation_prefix_controlled_dictionary {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    let I := (geoTransformAlong (originalMarkedIdeal H) T).ideal
    I = controlledTransformAlong (vanishingIdeal (n := n) H) T ∧ I.IsInvertible ∧
      GermIdeal.pullback (m := n) T.proj (vanishingIdeal (n := n) H) =
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mul I := by
  dsimp only
  have hT := (originalSeparation_prefix_domain_and_strict hH i).1
  have hcoh := (isInvDomain_originalMarkedIdeal hH).isWellFormed.isCoherent
  refine ⟨(controlledTransformAlong_eq (originalMarkedIdeal H) rfl hcoh _ hT).symm,
    isInvertible_geoTransformAlong_of_test (originalMarkedIdeal H) rfl (originalDivisor hH).isInvertible _ hT, ?_⟩
  have h := (pullback_eq_mul_geoTransformAlong (originalMarkedIdeal H) rfl hcoh _ hT).2.2
  simpa only [originalMarkedIdeal,FactorizationFromResolution.idealPow_one_of_isCoherent
    (BlowupExceptionalDivisor.isCoherent_ideal _)] using h

/-- The actual terminal whole controlled original ideal is internally invertible. -/
theorem isInvertible_originalControlledIdeal {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) : (originalControlledIdeal hH).IsInvertible :=
  isInvertible_geoTransformAlong_of_test (originalMarkedIdeal H) rfl
    (originalDivisor hH).isInvertible _ (originalSeparation_isGeoTestTower hH)

/-- The actual SAME whole controlled original ideal as an effective divisor. -/
def controlledOriginalDivisor {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    EffectiveDivisor n (originalSeparation hH).D :=
  ⟨originalControlledIdeal hH,isInvertible_originalControlledIdeal hH⟩

/-- Support containment is produced from true whole factorization and actual total support, not input. -/
theorem controlledOriginalDivisor_support_subset {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (controlledOriginalDivisor hH).support ⊆ ⋃ F ∈ terminalBoundary hH, F := by
  intro y hy
  have hp := RestrictLeCalculus.zeroLocus_right_subset_mul
    (BlowupTowerTransforms.exceptionalDivisor (originalSeparation hH).T).ideal
    (originalControlledIdeal hH) hy
  rw [← pullback_eq_exceptional_mul_originalControlledIdeal hH] at hp
  exact (totalOriginalDivisor_support hH).subset hp

/-- The SAME COMPLETE actual original controlled ideal equals its monomial ideal on augmented actual SNC boundary. -/
theorem controlled_original_eq_monomialPart {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    originalControlledIdeal hH = MonomialPart.monomialPart n
      (originalControlledIdeal hH) (terminalBoundary hH) :=
  HironakaSNCSupportedMonomialIdeal.ideal_eq_monomialPart_of_support_subset
    (controlledOriginalDivisor hH) _ (originalSeparation_geometry hH).2.2.2.1
    (controlledOriginalDivisor_support_subset hH)

/-- Its COMPLETE nonmonomial residual on augmented actual SNC boundary is the unit ideal. -/
theorem controlled_original_nonmonomialPart_eq_unit {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    MonomialPart.nonmonomialPart n (originalControlledIdeal hH) (terminalBoundary hH) =
      IdealWeightPowers.unitIdeal n (originalSeparation hH).D :=
  HironakaSNCSupportedMonomialIdeal.nonmonomialPart_eq_unitIdeal_of_support_subset
    (controlledOriginalDivisor hH) _ (originalSeparation_geometry hH).2.2.2.1
    (controlledOriginalDivisor_support_subset hH)

end
end Hironaka.HironakaNormalCrossingsMarkedAdmissibility

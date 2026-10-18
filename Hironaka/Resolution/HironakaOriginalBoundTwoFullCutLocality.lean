/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveLocalReferenceComparison
import Hironaka.Resolution.HironakaOriginalFiniteFullCutSmoothHistory
/-! Original DOMAIN two plus genuine FULL-cut histories give actual
same-history locality without lower canonicality or global raw reference DOMAIN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalBoundTwoFullCutLocality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism BlowupTowerIsoTail
  CanonicalCentres InvDomainTowerAlong MaxLocusLocal
  HironakaOriginalSourceChoiceCartesian HironakaOriginalAllStepOneEtaleValues HironakaOriginalUntestedCurveSmoothValues
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFiniteOrderCutBoundTwoSmoothValues
  HironakaOriginalFiniteFullCutSmoothHistory
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private theorem family_value_cast_depth (hn : 0<n) {a b : ℕ} (hab : a=b)
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) :
    congrArg ValTy hab ▸ (invFamily hn a).inv M T z=(invFamily hn b).inv M T z := by
  cases hab
  rfl

/-- ONE actual given history before the genuine source full-cut recipe
and ALL same-ambient original values at every depth at least two. -/
theorem bound_two_full_cut_cartesian_values (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T)
    {f : X' → X} {g : Y' → Y} {Q : BlowupTower X' Y'}
    (h : IsActualTowerPullback f Q T g) :
    IsFullCutTower hn d (MarkedIdeal.pullback f M) Q ∧
      ∀ z : Y',g z∈(geoTransformAlong M T).cosupp → ∀ k : ℕ,
        (invFamily hn (k+2)).inv (MarkedIdeal.pullback f M) Q z=
          (invFamily hn (k+2)).inv M T (g z) := by
  have hSource := IsActualTowerPullback.fullCutTower_pullback hn hn d M hM h hT
  rw [Nat.sub_self,Nat.zero_add] at hSource
  refine ⟨hSource,?_⟩
  intro z hz k
  have hv := orderCutTower_bound_two_full_smooth_values hn hn M hM T
    (fullCutTower_orderCut hn d M T hT) h z hz k
  rw [Nat.sub_self] at hv
  have hc := congrArg (fun v : ValTy (0+(k+2)) => congrArg ValTy (Nat.zero_add (k+2)) ▸ v) hv
  have hl := family_value_cast_depth hn (Nat.zero_add (k+2)) (MarkedIdeal.pullback f M) Q z
  exact hl.symm.trans (hc.trans (familyDimensionMap_zero (k+2) ((invFamily hn (k+2)).inv M T (g z))))

/-- Genuine nested DOMAIN, full-cut history and whole cosupport precede
ALL original FULL comparisons of the SAME raw local reference. -/
theorem bound_two_full_cut_nested_open (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) {W V : Opens X} (hVW : V≤W)
    (hDom : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : W → X) M))
    (T : BlowupTower X Y)
    (hRecipe : IsFullCutTower hn d (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)) :
    IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : V → X) M) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ∧
      IsFullCutTower hn d (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ∧
      (∀ p : openPreimage T V,p∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp ↔
        (⟨p.val,openPreimage_mono T hVW p.property⟩ : openPreimage T W)∈
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)).cosupp) ∧
      ∀ p : openPreimage T V,p∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp →
        ∀ k : ℕ,(invFamily hn (k+2)).inv (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) p=
          (invFamily hn (k+2)).inv (MarkedIdeal.pullback (Subtype.val : W → X) M) (restrict W T)
            ⟨p.val,openPreimage_mono T hVW p.property⟩ := by
  have hTest := orderCutTower_geoTest _ _ (fullCutTower_orderCut hn d _ _ hRecipe)
  have hDom' := isInvDomain_pullback_val (nestedOpens W V) hDom
  have hTest' := isGeoTestTower_restrict (nestedOpens W V) hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent (restrict W T) hTest
  obtain ⟨hRecipe',hValues'⟩ := bound_two_full_cut_cartesian_values hn d _ hDom _ hRecipe
    (open_inclusion_actual_tower (nestedOpens W V) (restrict W T))
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := pullback_symm_nestedOpensDiffeo (M := X) hM hVW
  have hDomV := isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hDom'
  rw [heq] at hDomV
  obtain ⟨hRecipeV,hValuesV⟩ := bound_two_full_cut_cartesian_values hn d _ hDom' _ hRecipe'
    (IsTowerIso.actual_cartesian hiso)
  rw [heq] at hRecipeV hValuesV
  have hTestV := (IsTowerIso.isGeoTestTower_iff (nestedOpensDiffeo (n := n) hVW).symm
    hDom'.isWellFormed.isClosedSubmanifold_N hDom'.isWellFormed.isCoherent hiso).mpr hTest'
  rw [heq] at hTestV
  have hCos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hDom'.isWellFormed.isClosedSubmanifold_N hDom'.isWellFormed.isCoherent hiso hTest'
  rw [heq] at hCos
  have hCos' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent
    (nestedOpens W V) (restrict W T) hTest
  refine ⟨hDomV,hTestV,hRecipeV,?_,?_⟩
  · intro p
    rw [hCos,mem_preimage,hCos',mem_preimage]
    rfl
  · intro p hp k
    have hp' := hp
    rw [hCos,mem_preimage] at hp'
    have hp'' := hp'
    rw [hCos',mem_preimage] at hp''
    exact (hValuesV p hp' k).trans (hValues' _ hp'' k)

/-- TWO independently genuine local domains/recipes compare through the
SAME actual reference/history/current point on their real intersection. -/
theorem bound_two_full_cut_two_opens (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (U V : Opens X)
    (hU : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : U → X) M))
    (hV : IsInvDomain 2 (MarkedIdeal.pullback (Subtype.val : V → X) M))
    (T : BlowupTower X Y)
    (hTU : IsFullCutTower hn d (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T))
    (hTV : IsFullCutTower hn d (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T))
    (z : Y) (hzU : T.proj z∈U) (hzV : T.proj z∈V) :
    ((⟨z,hzU⟩ : openPreimage T U)∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp ↔
      (⟨z,hzV⟩ : openPreimage T V)∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)).cosupp) ∧
      ((⟨z,hzU⟩ : openPreimage T U)∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp →
        ∀ k : ℕ,(invFamily hn (k+2)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) ⟨z,hzU⟩=
          (invFamily hn (k+2)).inv (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T) ⟨z,hzV⟩) := by
  obtain ⟨_,_,_,hCosU,hValU⟩ := bound_two_full_cut_nested_open hn d M hM (W := U) (V := U⊓V) inf_le_left hU T hTU
  obtain ⟨_,_,_,hCosV,hValV⟩ := bound_two_full_cut_nested_open hn d M hM (W := V) (V := U⊓V) inf_le_right hV T hTV
  let q : openPreimage T (U⊓V) := ⟨z,⟨hzU,hzV⟩⟩
  refine ⟨(hCosU q).symm.trans (hCosV q),?_⟩
  intro hz k
  have hq := (hCosU q).mpr hz
  exact (hValU q hq k).symm.trans (hValV q hq k)

end
end Hironaka.HironakaOriginalBoundTwoFullCutLocality

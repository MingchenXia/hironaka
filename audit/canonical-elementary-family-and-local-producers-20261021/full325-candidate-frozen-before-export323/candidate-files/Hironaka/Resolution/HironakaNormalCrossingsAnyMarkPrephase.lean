/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsBoundaryAvoidance
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! # A genuine finite permitted NC boundary prephase at every marking

The SAME actual natural separation tower is a true test tower for the
original coherent ideal at its unchanged arbitrary marking. Actual stage
admissibility and double-locus cosupport are derived, not supplied.
Original D2(H) ⊆ cosupp and an actual SNC adapted E remain explicit;
this qualified prephase does not close arbitrary initial-NC G9.
Blueprint: `hironaka-normal-crossings-any-mark-prephase-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsAnyMarkPrephase

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsDoubleLocusSeparation
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsBoundaryAvoidance
  BlowupTowers BlowupStrictSubmanifold NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder HironakaStageCenters RestrictEmptyTower HironakaAdmissibleSequence

noncomputable section
variable {n : ℕ}

private theorem branchMultiplicity_congr {A : CMfd.{u} n} {H K : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (heq : H = K) (x : A) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

/-- Every genuine higher-old-branch history is an actual test history for
its SAME original whole-ambient datum, at ANY unchanged actual marking. -/
theorem higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
    {A : CMfd.{u} n} (M : MarkedIdeal n A) (hN : M.N = univ) (hw : M.IsWellFormed)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hD2 : {x | 2 ≤ branchMultiplicity hH x} ⊆ M.cosupp) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      (hp : IsNormalCrossingsCarrier (n := n) (strictTransform n T.proj H)) →
      IsGeoTestTower M T ∧
        {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M T).cosupp
  | _,.refl,_,hp => by
      refine ⟨trivial,?_⟩
      have hs : strictTransform n (id : A → A) H = H := by
        simp [strictTransform,exceptionalLocus_id,hH.1.closure_eq]
      intro x hx
      apply hD2
      change 2 ≤ branchMultiplicity hp x at hx
      rwa [branchMultiplicity_congr hp hH hs x] at hx
  | _,.step T C π hπ,hc,hp => by
      obtain ⟨hh,r,hr,hbound,hceq,_⟩ := hc.2
      subst C
      let hcur := isNormalCrossingsCarrier_of_boundaryAdapted hh
      obtain ⟨hT,hdouble⟩ := higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
        M hN hw hH hD2 T hc.1 hcur
      have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
      have hNT : (geoTransformAlong M T).N = univ :=
        (pullback_eq_mul_geoTransformAlong M hN hw.isCoherent T hT).1
      have hs : strictTransform n (BlowupTower.step T _ π hπ).proj H =
          strictTransform n π (strictTransform n T.proj H) := by
        rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp
          T.contMDiff_proj hπ.contMDiff]
      let hnew := isNormalCrossingsCarrier_of_boundaryAdapted
        (boundaryAdapted_strict_highest hh hbound hπ)
      have hwhole : geoStrictTransform π {x | r ≤ branchMultiplicity hcur x}
          (strictTransform n T.proj H) = strictTransform n (BlowupTower.step T _ π hπ).proj H :=
        (geoStrictTransform_highest_eq_strictTransform hcur hr hbound hπ).trans hs.symm
      obtain ⟨hadm,hnext⟩ := highest_step_doubleLocus_subset_controlled_cosupport
        (geoTransformAlong M T) hNT hwT hh hr hbound hπ hdouble
      refine ⟨⟨hT,hadm⟩,?_⟩
      intro z hz
      have hznew : 2 ≤ branchMultiplicity hnew z := by
        change 2 ≤ branchMultiplicity hp z at hz
        rwa [branchMultiplicity_congr hp hnew hwhole.symm z] at hz
      have hznext := hnext hznew
      change z ∈ cosupport n ((geoTransformAlong M T).geoTransform _ π).N
        ((geoTransformAlong M T).geoTransform _ π).ideal
        ((geoTransformAlong M T).geoTransform _ π).d
      rw [geoTransform_N_eq_univ hNT hπ,
        geoTransform_ideal_eq_controlledTransform hNT hwT.isCoherent hπ,geoTransform_d]
      exact hznext

private theorem stage_double_subset_cosupp
    {A : CMfd.{u} n} (M : MarkedIdeal n A) (hN : M.N = univ) (hw : M.IsWellFormed)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hD2 : {x | 2 ≤ branchMultiplicity hH x} ⊆ M.cosupp) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      StageCentres (fun R _ =>
        ∃ hp : IsNormalCrossingsCarrier (n := n) (strictTransform n R.proj H),
          {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M R).cosupp) T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,hc => by
      have hp := isNormalCrossingsCarrier_of_boundaryAdapted (Classical.choose hc.2)
      exact ⟨stage_double_subset_cosupp M hN hw hH hD2 T hc.1,
        hp,(higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
          M hN hw hH hD2 T hc.1 hp).2⟩

/-- Only the ORIGINAL coherent ideal, actual mark and adapted pair are given.
Their original D2 cosupport condition internally makes the SAME finite natural
separation a permitted test tower, with actual prefix inclusions and good-locus
isomorphism. No new-cosupport or admissibility certificate is supplied. -/
theorem naturalSeparation_isGeoTestTower_of_doubleLocus_subset_cosupp
    {A : CMfd.{u} n} (I : GermIdeal n A) (hI : I.IsCoherent) (d : ℕ)
    {H : Set A} {E : List (Set A)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    (hD2 : {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆
      cosupport n univ I d) :
    let M : MarkedIdeal n A := ⟨univ,E,I,d⟩
    let o := naturalSeparation M h
    IsGeoTestTower M o.T ∧
      StageCentres (fun R _ =>
        ∃ hp : IsNormalCrossingsCarrier (n := n) (strictTransform n R.proj H),
          {x | 2 ≤ branchMultiplicity hp x} ⊆ (geoTransformAlong M R).cosupp) o.T ∧
      o.T.length ≤ n-1 ∧ IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) (geoTransformAlong M o.T).E ∧
      IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      IsAdmissibleBlowupSequence n A E (cosupport n univ I d)
        o.D o.T.proj (geoTransformAlong M o.T).E ∧
      CentresOver (cosupport n univ I d) o.T ∧
      IsIsomorphismOver n o.T.proj (cosupport n univ I d)ᶜ := by
  let M : MarkedIdeal n A := ⟨univ,E,I,d⟩
  let o := naturalSeparation M h
  have hE := isSNCDivisor_of_boundaryAdapted h
  have hw : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hI,hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted o.pair
  obtain ⟨ht,_⟩ := higherSeparationCentres_isGeoTestTower_and_double_subset_cosupp
    M rfl hw hH hD2 o.T o.centres hp
  obtain ⟨hlen,hsm,htrans,hsnc,hadm,hcover,hiso⟩ := naturalSeparation_permitted_geometry M h
    (GiraudAlong.isClosed_cosupport_along hI hw.isClosedSubmanifold_N d) hD2
  exact ⟨ht,stage_double_subset_cosupp M rfl hw hH hD2 o.T o.centres,
    hlen,hsm,htrans,hsnc,hadm,hcover,hiso⟩

end
end Hironaka.HironakaNormalCrossingsAnyMarkPrephase

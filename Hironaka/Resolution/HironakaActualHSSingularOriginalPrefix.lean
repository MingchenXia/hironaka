/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSSingularBlowupRestart
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal

/-! Genuine HS singular centres extend a test prefix of the SAME original marked input. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHSSingularOriginalPrefix
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  AnalyticDimensionBasics MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings SimultaneousNormalCrossings BlowupTowers BlowupTowerTransforms ResolutionDriver
  HironakaActualReferenceHSSingularCentre HironakaActualHSSingularBlowupRestart
  HironakaHolomorphicJetChartInvariance HironakaStageCenters RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ}

/-- The ENTIRE current singular set is genuinely analytic from the EXISTING original first-HS dictionary. -/
theorem isComplexAnalyticSubset_actualCurrentSingular {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) :
    IsComplexAnalyticSubset (n := n) (W \ regularLocus (n := n) W d) := by
  rw [HironakaHilbertSamuelTangentValue.singularLocus_eq_first_hilbertSamuel_superlevel hW hd hpure]
  exact hW.inter (isComplexAnalyticSubset_hilbertSamuelAt_superlevel
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW) 1 (d+2))

/-- The literal ENTIRE original regular open includes all points outside the original carrier. -/
def actualCurrentRegularOpen {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) : Opens X :=
  ⟨(W \ regularLocus (n := n) W d)ᶜ,
    (isComplexAnalyticSubset_actualCurrentSingular hW hd hpure).isClosed.isOpen_compl⟩

/-- BOTH genuine original regular-open intersection membership directions. -/
theorem actualCurrentRegularOpen_inter {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) :
    W ∩ (actualCurrentRegularOpen hW hd hpure : Set X) = regularLocus (n := n) W d := by
  ext x
  constructor
  · rintro ⟨hxW,hxO⟩
    by_contra hr
    exact hxO ⟨hxW,hr⟩
  · intro hr
    exact ⟨hr.2.1,fun hs => hs.2 hr⟩

/-- Original analytic geometric purity independently makes the SAME entire preserved open dense in W. -/
theorem actualCurrentRegularOpen_dense {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) :
    W ⊆ closure (W ∩ (actualCurrentRegularOpen hW hd hpure : Set X)) := by
  rw [actualCurrentRegularOpen_inter hW hd hpure]
  exact actualPure_subset_closure_regularLocus hW hpure

/-- ANY genuine recorded singular prefix INTERNALLY avoids every original regular open in arbitrary codimension. -/
theorem centresAvoid_of_actual_singular_prefix {X : CMfd.{u} n} {W : Set X}
    (hW : IsClosed W) (O : Opens X) {d : ℕ}
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
        regularLocus (n := n) (strictTransform n P.proj W) d) T → CentresAvoid O T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hstage => by
      have havoid := centresAvoid_of_actual_singular_prefix hW O hreg T hstage.1
      refine ⟨havoid,disjoint_left.mpr fun c hc hcO => ?_⟩
      have hcW := HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous
        hW (hstage.2 hc).1
      have hcreg := (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW
        (EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T havoid c hcO) d).mpr
          (hreg _ hcW hcO)
      exact (hstage.2 hc).2 hcreg

/-- The actual recorded singular positions give the ENTIRE original regular-open inverse, with no caller avoidance certificate. -/
theorem actual_singular_prefix_regular_open_iso {X Y : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) (T : BlowupTower X Y)
    (hstage : StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
      regularLocus (n := n) (strictTransform n P.proj W) d) T) :
    CentresAvoid (actualCurrentRegularOpen hW hd hpure) T ∧
    IsIsomorphismOver n T.proj (actualCurrentRegularOpen hW hd hpure : Set X) := by
  have havoid := centresAvoid_of_actual_singular_prefix hW.isClosed (actualCurrentRegularOpen hW hd hpure)
    (fun x hxW hxO => by by_contra hr; exact hxO ⟨hxW,hr⟩) T hstage
  have hiso := HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence (EmbeddedFromResolution.image_exceptionalLocus_subset_compl _ T havoid)
  exact ⟨havoid,by simpa only [compl_compl] using hiso⟩

/-- Every actual singular prefix has genuine analytic compact geometrically pure CURRENT strict carrier. -/
theorem actual_singular_prefix_current_geometry {X Y : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ}
    (hpure : IsPureDim (n := n) W d) (T : BlowupTower X Y)
    (hstage : StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
      regularLocus (n := n) (strictTransform n P.proj W) d) T) :
    IsComplexAnalyticSubset (n := n) (strictTransform n T.proj W) ∧
    IsCompact (strictTransform n T.proj W) ∧ IsPureDim (n := n) (strictTransform n T.proj W) d := by
  have hdense := HironakaHypersurfaceMultiplicityDescent.strictTransform_subset_closure_regularLocus_of_stageCentres_singular
    hW.isClosed (actualPure_subset_closure_regularLocus hW hpure) T hstage
  exact ⟨HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW,
    HironakaAdmissibleCalculus.isCompact_strictTransform T.isBlowupSequence hK,
    actualPure_of_subset_closure_regularLocus hdense⟩

/-- True SAME-original-input controlled ideal comparison uses ONLY original geometry and actual test/singular history. -/
theorem actual_singular_prefix_original_controlled_comparison {X Y : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hstage : StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
      regularLocus (n := n) (strictTransform n P.proj W) d) T) :
    (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).ideal.Le
      (vanishingIdeal (n := n) (strictTransform n T.proj W)) ∧
    strictTransform n T.proj W ⊆
      (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).cosupp ∧
    IsSNCDivisor n (geoTransformAlong (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T).E := by
  have hdom : IsInvDomain n (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) :=
    HironakaEmbeddedBoundary.isInvDomain_boundary hW (currentPure_interior_empty hd hpure) hE
  let O := actualCurrentRegularOpen hW hd.le hpure
  have havoid := (actual_singular_prefix_regular_open_iso hW hd.le hpure T hstage).1
  have hdense := actualCurrentRegularOpen_dense hW hd.le hpure
  exact ⟨HironakaCurrentStrictTransformIdeal.controlledIdeal_le_currentStrictIdeal hW.isClosed hdom O hdense T hT havoid,
    HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid hW.isClosed hdom O hdense T hT havoid,
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hdom.isWellFormed T hT).isSNCDivisor⟩

/-- ONLY original current geometry extends an actual singular prefix as a genuine test tower of the SAME original P. -/
theorem exists_actual_hs_singular_same_original_prefix_extension {X Y : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hstage : StageCentres (fun P C => C ⊆ strictTransform n P.proj W \
      regularLocus (n := n) (strictTransform n P.proj W) d) T)
    (hns : ¬ IsClosedSubmanifold n (strictTransform n T.proj W)) :
    let m : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
    ∃ (a : Y) (C : Set Y) (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      a ∈ strictTransform n T.proj W \ regularLocus (n := n) (strictTransform n T.proj W) d ∧
      C.Nonempty ∧ C ⊆ actualReferenceHSLocus (vanishingIdeal (n := n) (strictTransform n T.proj W)) a ∧
      C ⊆ strictTransform n T.proj W \ regularLocus (n := n) (strictTransform n T.proj W) d ∧
      (geoTransformAlong m T).IsAdmissibleCentre C ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsGeoTestTower m (.step T C π hπ) ∧
      StageCentres (fun P D => D ⊆ strictTransform n P.proj W \
        regularLocus (n := n) (strictTransform n P.proj W) d) (.step T C π hπ) ∧
      IsIsomorphismOver n (BlowupTower.proj (.step T C π hπ)) (W \ regularLocus (n := n) W d)ᶜ ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) (strictTransform n T.proj W) (geoTransformAlong m T).E a)
        (.refl : BlowupTower Y Y))
        (actualReferenceHSMarked (n := n) (strictTransform n T.proj W) (geoTransformAlong m T).E a).cosupp := by
  let m : MarkedIdeal n X := ⟨univ,E,vanishingIdeal (n := n) W,1⟩
  obtain ⟨hSa,hSk,hSp⟩ := actual_singular_prefix_current_geometry hW hK hpure T hstage
  obtain ⟨_hIle,hScos,hEt⟩ := actual_singular_prefix_original_controlled_comparison hW hd hpure hE T hT hstage
  obtain ⟨a,C,Z,π,ha,hCne,hCSa,hCS,hCadm,hπ,hproper,hholo,_hiso,_hE',hCeq⟩ :=
    exists_actual_current_full_hs_singular_first_blowup hSa hSk hd hSp hns hEt
  have hOriginalAdm : (geoTransformAlong m T).IsAdmissibleCentre C :=
    ⟨hCadm.1,fun y hy => hScos (hCS hy).1,hCadm.2.2⟩
  have hNextTest : IsGeoTestTower m (.step T C π hπ) := ⟨hT,hOriginalAdm⟩
  have hNextStage : StageCentres (fun P D => D ⊆ strictTransform n P.proj W \
      regularLocus (n := n) (strictTransform n P.proj W) d) (.step T C π hπ) := ⟨hstage,hCS⟩
  have hWholeIso := (actual_singular_prefix_regular_open_iso hW hd.le hpure (.step T C π hπ) hNextStage).2
  exact ⟨a,C,Z,π,hπ,ha,hCne,hCSa,hCS,hOriginalAdm,hproper,hholo,hNextTest,hNextStage,hWholeIso,hCeq⟩

end
end Hironaka.HironakaActualHSSingularOriginalPrefix

import Hironaka.Resolution.HironakaG8QuadraticGeometricInitialConflict
import Hironaka.Resolution.HironakaG8ProperEmbeddedOriginalOverlap
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorGeometry
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Analytic.PointSupportedIdealPrincipalization

/-! One literal ambient analytic set with higher HS at one anchor and an
exact original mark-one tie with a second anchor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8QuadraticSingleAmbientInitial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan OkaRelationSheaf BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres InvDomainTowerAlong NormalCrossings
  HironakaActualOpenEmbeddingVanishingIdeal HironakaBaseChange
  HironakaG8QuadraticAxesVanishing HironakaG8QuadraticQuadVanishing
  HironakaG8QuadraticAxesRecoding HironakaG8QuadraticInitialTieCriterion
  HironakaG8QuadraticGeometricInitialConflict HironakaG8ProperEmbeddedOriginalOverlap
  HironakaUniformHistoricalSuccessorGeometry HironakaEmbeddedAnalyticLocal
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedBoundary

/-- The translated quadric vertex lies off all three axes. -/
def quadAnchor : ComplexModel 3 := WithLp.toLp 2 (fun _ : Fin 3 => (1 : ℂ))

abbrev shift := modelTranslation quadAnchor

def mixedQuadraticSet : Set (ComplexModel 3) := axesSet ∪ shift.symm ⁻¹' quadSet

abbrev orig (W : Set (ComplexModel 3)) : MarkedIdeal 3 model :=
  fullRecord (X := model) (vanishingIdeal (n := 3) W) 1

private theorem axDiff (i : Fin 3) : Differentiable ℂ (axesFunction i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (axesI i)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (axesJ i)).differentiable

private theorem qDiff : Differentiable ℂ quadFunction :=
  (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable)).add
    (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable.mul
      (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable))

theorem axes_analytic : IsComplexAnalyticSubset (n := 3) axesSet := fun z =>
  RemmertSteinFlat.nonempty_presentation_of_eqOn isOpen_univ (mem_univ z) axesFunction
    (fun i => (axDiff i).differentiableOn) (fun _ _ => Iff.rfl)

theorem quad_analytic : IsComplexAnalyticSubset (n := 3) quadSet := fun z =>
  RemmertSteinFlat.nonempty_presentation_of_eqOn isOpen_univ (mem_univ z) (fun _ : Fin 1 => quadFunction)
    (fun _ => qDiff.differentiableOn) (fun _ _ => ⟨fun h _ => h,fun h => h 0⟩)

theorem mixedQuadraticSet_analytic : IsComplexAnalyticSubset (n := 3) mixedQuadraticSet :=
  isComplexAnalyticSubset_union axes_analytic
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage shift.symm.contMDiff quad_analytic)

private theorem anchor_not_axes : quadAnchor ∉ axesSet := by
  intro h
  have h' := h (0 : Fin 3)
  change coord 0 quadAnchor * coord 1 quadAnchor = 0 at h'
  simp [quadAnchor,coord] at h'

private theorem zero_not_shift_quad : (0 : ComplexModel 3) ∉ shift.symm ⁻¹' quadSet := by
  intro h
  change quadFunction ((0 : ComplexModel 3)-quadAnchor) = 0 at h
  simp [quadFunction,quadAnchor,coord] at h

private theorem shift_zero : shift (0 : ComplexModel 3) = quadAnchor := zero_add _

theorem mixedQuadraticSet_original_domain : IsInvDomain 3 (orig mixedQuadraticSet) := by
  apply (original_vanishing_domain_iff_empty_interior (X := model)
    mixedQuadraticSet_analytic (isSNCDivisor_nil (n := 3))).mpr
  let f : ComplexModel 3 → ℂ := fun z => axesFunction 0 z * quadFunction (z-quadAnchor)
  have hf : AnalyticOnNhd ℂ f univ := by
    intro z _
    have ha : AnalyticAt ℂ (axesFunction 0) z :=
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt z).mul
        ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt z)
    have hq : AnalyticAt ℂ quadFunction (z-quadAnchor) :=
      (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt (z-quadAnchor)).mul
        ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt (z-quadAnchor))).add
        (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt (z-quadAnchor)).mul
          ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt (z-quadAnchor)))
    have hm : AnalyticAt ℂ (fun w : ComplexModel 3 => w-quadAnchor) z :=
      analyticAt_id.sub analyticAt_const
    exact ha.mul (AnalyticAt.comp (g := quadFunction) hq hm)
  have hZ : ∀ z ∈ mixedQuadraticSet, f z = 0 := by
    rintro z (hz | hz)
    · exact mul_eq_zero_of_left (hz 0) _
    · change axesFunction 0 z * quadFunction (z-quadAnchor) = 0
      rw [show quadFunction (z-quadAnchor) = 0 from hz,mul_zero]
  have hNZ : f (quadAnchor+quadAnchor) ≠ 0 := by
    change (coord 0 (quadAnchor+quadAnchor) * coord 1 (quadAnchor+quadAnchor)) *
      quadFunction ((quadAnchor+quadAnchor)-quadAnchor) ≠ 0
    simp [quadFunction,quadAnchor,coord]
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' : ∀ᶠ y in 𝓝 z, y ∈ mixedQuadraticSet := mem_interior_iff_mem_nhds.mp hz
  have hE : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := hz'.mono fun y hy => hZ y hy
  exact hNZ (congrFun (hf.eq_of_eventuallyEq analyticOnNhd_const hE) _)

private theorem wholeOpen_record (W : Set (ComplexModel 3)) (D : Opens (ComplexModel 3)) :
    MarkedIdeal.pullback (Subtype.val : D → ComplexModel 3) (orig W) = geometricRecord W D :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val D) W) rfl

private theorem moved_record :
    MarkedIdeal.pullback shift (orig mixedQuadraticSet) = orig (shift ⁻¹' mixedQuadraticSet) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (pullback_vanishingIdeal_of_biholomorphism shift mixedQuadraticSet) rfl

theorem mixedQuadraticSet_anchors :
    (0 : ComplexModel 3) ∈ (orig mixedQuadraticSet).cosupp ∧
      quadAnchor ∈ (orig mixedQuadraticSet).cosupp := by
  rw [cosupp_mk_vanishingIdeal mixedQuadraticSet_analytic.isClosed]
  constructor
  · left
    intro i
    simp [axesFunction,coord]
  · right
    change quadFunction (quadAnchor-quadAnchor) = 0
    simp [quadFunction,coord]

/-- At the two actual points in one literal source, HS strictly prefers
the quadric while the original mark-one canonical values are tied. -/
theorem mixedQuadraticSet_exact_initial_conflict :
    toLex (hilbertSamuelAt (orig mixedQuadraticSet).ideal 0) <
      toLex (hilbertSamuelAt (orig mixedQuadraticSet).ideal quadAnchor) ∧
    (canonicalInvariant 3).inv (orig mixedQuadraticSet) .refl 0 =
      (canonicalInvariant 3).inv (orig mixedQuadraticSet) .refl quadAnchor := by
  let W := mixedQuadraticSet
  let Wq := shift ⁻¹' W
  let P := orig W
  let Pq := orig Wq
  let Bₐ : Opens (ComplexModel 3) :=
    ⟨(shift.symm ⁻¹' quadSet)ᶜ,(quad_analytic.isClosed.preimage shift.symm.continuous).isOpen_compl⟩
  let Bq : Opens (ComplexModel 3) :=
    ⟨shift ⁻¹' axesSetᶜ,axes_analytic.isClosed.isOpen_compl.preimage shift.continuous⟩
  have hₐ : (0 : ComplexModel 3) ∈ Bₐ := zero_not_shift_quad
  have hq : (0 : ComplexModel 3) ∈ Bq := by
    change shift 0 ∉ axesSet
    rw [shift_zero]
    exact anchor_not_axes
  obtain ⟨Dₐ,Dq,haD,hqD,hIna,hInq,_,_,_,_,hHS,hVal⟩ :=
    exists_quadratic_geometric_initial_conflict Bₐ Bq hₐ hq
  have hSetA : (Subtype.val : Dₐ → ComplexModel 3) ⁻¹' W =
      (Subtype.val : Dₐ → ComplexModel 3) ⁻¹' axesSet := by
    ext z
    have hz : z.val ∉ shift.symm ⁻¹' quadSet := hIna z.property
    change (z.val ∈ axesSet ∨ z.val ∈ shift.symm ⁻¹' quadSet) ↔ _
    simp [hz]
  have hSetQ : (Subtype.val : Dq → ComplexModel 3) ⁻¹' Wq =
      (Subtype.val : Dq → ComplexModel 3) ⁻¹' quadSet := by
    ext z
    have hz : shift z.val ∉ axesSet := hInq z.property
    change (shift z.val ∈ axesSet ∨ shift.symm (shift z.val) ∈ quadSet) ↔ _
    simp [hz]
  have hmoved : MarkedIdeal.pullback shift P = Pq := moved_record
  have hD : IsInvDomain 3 P := mixedQuadraticSet_original_domain
  have hDq : IsInvDomain 3 Pq := by
    rw [← hmoved]
    exact isInvDomain_pullback shift hD
  have hP0 : (0 : ComplexModel 3) ∈ P.cosupp := mixedQuadraticSet_anchors.1
  have hPq : quadAnchor ∈ P.cosupp := mixedQuadraticSet_anchors.2
  have hQ0 : (0 : ComplexModel 3) ∈ Pq.cosupp := by
    rw [← hmoved, MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback shift.contMDiff
      shift.symm.contMDiff shift.apply_symm_apply shift.symm_apply_apply P
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hg)]
    change shift 0 ∈ P.cosupp
    rwa [shift_zero]
  have hIdA : MarkedIdeal.pullback (Subtype.val : Dₐ → ComplexModel 3) P = geometricRecord axesSet Dₐ := by
    rw [wholeOpen_record]
    unfold geometricRecord
    rw [hSetA]
  have hIdQ : MarkedIdeal.pullback (Subtype.val : Dq → ComplexModel 3) Pq = geometricRecord quadSet Dq := by
    rw [wholeOpen_record]
    unfold geometricRecord
    rw [hSetQ]
  let R := canonicalInvariant 3
  have hVa := R.isInvValue.restrictOpen (X := model) P hD Dₐ
    (.refl : BlowupTower model model) trivial ⟨0,haD⟩ hP0
  rw [hIdA] at hVa
  have hVq := R.isInvValue.restrictOpen (X := model) Pq hDq Dq
    (.refl : BlowupTower model model) trivial ⟨0,hqD⟩ hQ0
  rw [hIdQ] at hVq
  have hShift := R.isInvValue.towerIso (X := model) (X' := model)
    shift P hD .refl .refl shift (.refl) trivial 0 (by rw [shift_zero]; exact hPq)
  rw [hmoved,shift_zero] at hShift
  constructor
  · have hAHS (l : ℕ) : hilbertSamuelAt (geometricRecord axesSet Dₐ).ideal ⟨0,haD⟩ l =
        hilbertSamuelAt P.ideal 0 l := by
      change hilbertSamuelAt (vanishingIdeal (n := 3) ((Subtype.val : Dₐ → ComplexModel 3) ⁻¹' axesSet)) ⟨0,haD⟩ l = _
      rw [← hSetA]
      exact hilbertSamuelAt_vanishing_actual_open_any Dₐ W ⟨0,haD⟩ l
    have hQHS (l : ℕ) : hilbertSamuelAt (geometricRecord quadSet Dq).ideal ⟨0,hqD⟩ l =
        hilbertSamuelAt P.ideal quadAnchor l := by
      change hilbertSamuelAt (vanishingIdeal (n := 3) ((Subtype.val : Dq → ComplexModel 3) ⁻¹' quadSet)) ⟨0,hqD⟩ l = _
      rw [← hSetQ,hilbertSamuelAt_vanishing_actual_open_any]
      rw [hilbertSamuelAt_vanishing_actual_biholomorphic_any shift W 0 l,shift_zero]
    rw [← funext hAHS,← funext hQHS]
    exact hHS
  · exact hVa.symm.trans (hVal.trans (hVq.trans hShift))

/-- Any occupied first centre supported on the higher HS profile and
containing its anchor fails whole marked-one original canonicality. -/
theorem higher_HS_occupied_first_centre_not_original_canonical
    {C : Set (ComplexModel 3)}
    (hC : C ⊆ {z | hilbertSamuelAt (orig mixedQuadraticSet).ideal z =
      hilbertSamuelAt (orig mixedQuadraticSet).ideal quadAnchor}) (hq : quadAnchor ∈ C)
    {Y : CMfd.{0} 3} (π : Y → model) (hπ : IsBlowupAlong 3 C π) :
    ¬ IsCanonical (orig mixedQuadraticSet) ((canonicalInvariant 3).inv (orig mixedQuadraticSet))
      (.step (.refl : BlowupTower model model) C π hπ) := by
  intro h
  have hOutside : (0 : ComplexModel 3) ∉ C := by
    intro h0
    have he := hC h0
    exact (ne_of_lt mixedQuadraticSet_exact_initial_conflict.1) (congrArg toLex he)
  rcases h.2 with he | hMax
  · rw [he] at hq
    exact hq
  rw [geoTransformAlong_refl] at hMax
  have hqMax := hMax ▸ hq
  apply hOutside
  rw [hMax]
  refine ⟨mixedQuadraticSet_anchors.1,?_⟩
  intro y hy
  change (canonicalInvariant 3).inv (orig mixedQuadraticSet) .refl y ≤
    (canonicalInvariant 3).inv (orig mixedQuadraticSet) .refl 0
  rw [mixedQuadraticSet_exact_initial_conflict.2]
  exact hqMax.2 y hy

/-- The higher-profile singleton is an admissible actual first blowup with
a compact centre, and its one-step tower violates original canonicality. -/
theorem exists_higher_HS_occupied_noncanonical_first_test :
    ∃ (Y : CMfd.{0} 3) (π : Y → model)
      (hπ : IsBlowupAlong 3 ({quadAnchor} : Set (ComplexModel 3)) π),
      let T := BlowupTower.step (.refl : BlowupTower model model) {quadAnchor} π hπ
      IsGeoTestTower (orig mixedQuadraticSet) T ∧
        ¬ IsCanonical (orig mixedQuadraticSet) ((canonicalInvariant 3).inv (orig mixedQuadraticSet)) T := by
  have hC : IsClosedSubmanifold 3 ({quadAnchor} : Set (ComplexModel 3)) :=
    (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 3) quadAnchor).1
  have hsub : ({quadAnchor} : Set (ComplexModel 3)) ⊆ (orig mixedQuadraticSet).cosupp :=
    singleton_subset_iff.mpr mixedQuadraticSet_anchors.2
  have hint : interior ({quadAnchor} : Set (ComplexModel 3)) = ∅ :=
    eq_empty_of_subset_empty ((interior_mono hsub).trans
      (ResolutionInvariantDriver.interior_cosupp_eq_empty mixedQuadraticSet_original_domain).subset)
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup (Y := model) _ hC hint
  refine ⟨Y,π,hπ,⟨trivial,hC,hsub,hasNormalCrossings_nil_of_isClosedSubmanifold hC⟩,?_⟩
  apply higher_HS_occupied_first_centre_not_original_canonical
    (singleton_subset_iff.mpr rfl) (mem_singleton _) π hπ

end
end Hironaka.HironakaG8QuadraticSingleAmbientInitial

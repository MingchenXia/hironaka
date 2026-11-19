import Hironaka.Resolution.HironakaG8QuadraticAxesVanishing
import Hironaka.Resolution.HironakaG8QuadraticQuadVanishing
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Analytic.RemmertSteinFlatSetup

/-! The degree-two ordering mismatch occurs on literal geometric vanishing
records, on independent arbitrarily small physical opens. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8QuadraticGeometricInitialConflict
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  OkaRelationSheaf BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres InvDomainTowerAlong
  HironakaActualOpenEmbeddingVanishingIdeal HironakaBaseChange
  HironakaG8QuadraticAxesVanishing HironakaG8QuadraticQuadVanishing
  HironakaG8QuadraticAxesRecoding HironakaG8QuadraticAxesInitialHS
  HironakaG8QuadraticInitialTieCriterion HironakaActualPointGeometricBennett
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalDeformationInitialRelations
  HironakaActualVanishingIntrinsicHSTransport
  HironakaSmoothCentreRealDomainActualIdealPresheaf HironakaSmoothSubmersionGermIdealColon
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder
  HironakaActualCoherentWeightedCoefficientMarked
  HomogenizedGlueingTower AnalyticIrreducibleComponents NormalCrossings

private theorem origin_inclusion_eventually {A B : GermIdeal 3 (ComplexModel 3)}
    (hA : A.IsCoherent) (hB : B.IsCoherent)
    (h : originalCoherentOriginIdeal A ≤ originalCoherentOriginIdeal B) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel 3), ∀ f, A.mem z f → B.mem z f := by
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hA 0
  have hg (i : Fin s) : B.mem 0 (G i) := by
    have hh := CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hx
    have hAgen := (hgen 0 hx (G i)).mpr (isInSpanAt_self ⟨i,rfl⟩ hh)
    have hh' : HolAt (G i) 0 := hh.mono fun _ hh => mdifferentiableAt_iff_differentiableAt.mp hh
    exact (mk_mem_originalCoherentOriginIdeal_iff B hB hh').mp
      (h ((mk_mem_originalCoherentOriginIdeal_iff A hA hh').mpr hAgen))
  have hAll : ∀ᶠ z in 𝓝 (0 : ComplexModel 3), ∀ i, B.mem z (G i) :=
    eventually_all.mpr fun i => coherent_original_membership_eventually B hB 0 _ (hg i)
  filter_upwards [hU.mem_nhds hx,hAll] with z hz hall f hf
  apply HomogenizedIdeal.mem_of_isInSpanAt hB
  refine ((hgen z hz f).mp hf).mono ?_
  rintro _ ⟨i,rfl⟩
  exact hall i

private theorem read_geometric_initial_of_origin_eq
    (W : Set (ComplexModel 3)) (hW : IsComplexAnalyticSubset (n := 3) W)
    (I : GermIdeal 3 (ComplexModel 3)) (hI : IsInvDomain 3 (fullRecord (X := model) I 1))
    (hx : (0 : ComplexModel 3) ∈ (fullRecord (X := model) I 1).cosupp)
    (hEq : originalCoherentOriginIdeal (vanishingIdeal (n := 3) W) = originalCoherentOriginIdeal I)
    (B : Opens (ComplexModel 3)) (hB : (0 : ComplexModel 3) ∈ B) :
    ∃ (D : Opens (ComplexModel 3)) (hD : (0 : ComplexModel 3) ∈ D), D ≤ B ∧
      let J := fullRecord (X := CMfd.of (n := 3) D)
        (vanishingIdeal (n := 3) ((Subtype.val : D → ComplexModel 3) ⁻¹' W)) 1
      IsInvDomain 3 J ∧ (⟨0,hD⟩ : D) ∈ J.cosupp ∧
      (canonicalInvariant 3).inv (X := CMfd.of (n := 3) D) J .refl ⟨0,hD⟩ =
        (canonicalInvariant 3).inv (X := model) (fullRecord (X := model) I 1) .refl 0 := by
  let A := vanishingIdeal (n := 3) W
  have hA := CartanIrreducible.cartanCoherence W hW
  have hC := hI.isWellFormed.isCoherent
  obtain ⟨V,hV,hVO,hV0⟩ := mem_nhds_iff.mp
    ((origin_inclusion_eventually hA hC hEq.le).and
      (origin_inclusion_eventually hC hA hEq.symm.le))
  let D : Opens (ComplexModel 3) := ⟨V ∩ B,hVO.inter B.isOpen⟩
  have hD : (0 : ComplexModel 3) ∈ D := ⟨hV0,hB⟩
  have hP : GermIdeal.pullback (m := 3) (Subtype.val : D → ComplexModel 3) I =
      GermIdeal.pullback (m := 3) (Subtype.val : D → ComplexModel 3) A := by
    apply GermIdeal.ext
    funext z f
    apply propext
    rw [GermIdeal.mem_pullback_iff,GermIdeal.mem_pullback_iff]
    exact ⟨fun hh => hh.mono (by rintro _ ⟨g,hg,rfl⟩; exact ⟨g,(hV z.property.1).2 g hg,rfl⟩),
      fun hh => hh.mono (by rintro _ ⟨g,hg,rfl⟩; exact ⟨g,(hV z.property.1).1 g hg,rfl⟩)⟩
  rw [pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val D) W] at hP
  let J := fullRecord (X := CMfd.of (n := 3) D)
    (vanishingIdeal (n := 3) ((Subtype.val : D → ComplexModel 3) ⁻¹' W)) 1
  have hM : MarkedIdeal.pullback (Subtype.val : D → ComplexModel 3) (fullRecord (X := model) I 1) = J :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl hP rfl
  have hCos : (⟨0,hD⟩ : D) ∈ J.cosupp := by
    rw [← hM,MarkedIdealRestrictOpen.cosupp_pullback_val _ (fun _ _ hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem hC hg)]
    exact hx
  have hValue := (canonicalInvariant 3).isInvValue.restrictOpen (X := model) (fullRecord (X := model) I 1)
    hI D (.refl : BlowupTower model model) trivial ⟨0,hD⟩ hx
  rw [hM] at hValue
  have hDJ : IsInvDomain 3 J := by rw [← hM]; exact isInvDomain_pullback_val D hI
  exact ⟨D,hD,fun z hz => hz.2,hDJ,hCos,hValue⟩

private theorem axesDiff (i : Fin 3) : Differentiable ℂ (axesFunction i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (axesI i)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (axesJ i)).differentiable

private theorem quadDiff : Differentiable ℂ quadFunction :=
  (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable)).add
    (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable.mul
      (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable))

private theorem polynomialDomain {I : GermIdeal 3 (ComplexModel 3)} (hI : I.IsCoherent)
    (f : ComplexModel 3 → ℂ) (hf : ∀ z,I.mem z f)
    (hAnal : AnalyticOnNhd ℂ f univ) {b : ComplexModel 3} (hb : f b ≠ 0) :
    IsInvDomain 3 (fullRecord (X := model) I 1) := by
  have hN := HomogenizedGlueingTower.isClosedSubmanifold_univ (n := 3) (M := ComplexModel 3)
  refine ⟨⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun z _ => ⟨3,le_rfl,regularAtDim_univ z⟩,le_rfl,?_⟩
  intro z _
  refine ⟨f,hf z,?_⟩
  apply Frequently.mono (p := fun y => f y ≠ 0) _ (fun y hy => ⟨mem_univ y,hy⟩)
  by_contra hn
  have he : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    change ∀ᶠ y in 𝓝 z, f y = 0
    simpa using hn
  exact hb (congrFun (hAnal.eq_of_eventuallyEq analyticOnNhd_const he) b)

private theorem axesDom : IsInvDomain 3 (fullRecord (X := model) axesIdeal 1) := by
  let b : ComplexModel 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ) + EuclideanSpace.single (1 : Fin 3) 1
  refine polynomialDomain axesCoherent (axesFunction 0)
    (fun z => isInSpanAt_self ⟨0,rfl⟩ (Eventually.of_forall fun y => (axesDiff 0 y).mdifferentiableAt))
      (b := b) ?_ ?_
  · intro z _
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt z).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt z)
  · change coord 0 b * coord 1 b ≠ 0
    simp [b,coord]

private theorem quadDom : IsInvDomain 3 (fullRecord (X := model) quadIdeal 1) := by
  let b : ComplexModel 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  refine polynomialDomain quadCoherent quadFunction
    (fun z => isInSpanAt_self ⟨0,rfl⟩ (Eventually.of_forall fun y => (quadDiff y).mdifferentiableAt))
      (b := b) ?_ ?_
  · intro z _
    exact (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt z).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt z)).add
      (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt z).mul
        ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt z))
  · simp [quadFunction,b,coord]

private theorem at_origin {m : ℕ} (s : Fin m → ComplexModel 3 → ℂ)
    (hD : ∀ i,Differentiable ℂ (s i)) (hF : ∀ i, s i 0 = 0) :
    (0 : ComplexModel 3) ∈ (fullRecord (X := model) (finiteFunctionIdeal s) 1).cosupp := by
  change (0 : ComplexModel 3) ∈ cosupport 3 univ (finiteFunctionIdeal s) 1
  have hHol (i : Fin m) : HolomorphicAt 3 (s i) 0 :=
    Eventually.of_forall fun y => (hD i y).mdifferentiableAt
  rw [mem_cosupport_finiteFunctionIdeal_iff _ _ _ hHol]
  exact fun i => (vanishesToOrderOn_one_iff (mem_univ _) (hHol i)).mpr (hF i)

def geometricRecord (W : Set (ComplexModel 3)) (D : Opens (ComplexModel 3)) :
    MarkedIdeal 3 (CMfd.of (n := 3) D) :=
  fullRecord (vanishingIdeal (n := 3) ((Subtype.val : D → ComplexModel 3) ⁻¹' W)) 1

/-- Literal reduced geometric records of the axes and quadric, on
independent open windows, have different whole HS profiles but exactly
equal original mark-one canonical initial values. -/
theorem exists_quadratic_geometric_initial_conflict
    (Bₐ Bq : Opens (ComplexModel 3))
    (hₐ : (0 : ComplexModel 3) ∈ Bₐ) (hq : (0 : ComplexModel 3) ∈ Bq) :
    ∃ (Dₐ Dq : Opens (ComplexModel 3))
      (haD : (0 : ComplexModel 3) ∈ Dₐ) (hqD : (0 : ComplexModel 3) ∈ Dq),
      Dₐ ≤ Bₐ ∧ Dq ≤ Bq ∧
      let A := geometricRecord axesSet Dₐ
      let Q := geometricRecord quadSet Dq
      IsInvDomain 3 A ∧ IsInvDomain 3 Q ∧
      (⟨0,haD⟩ : Dₐ) ∈ A.cosupp ∧ (⟨0,hqD⟩ : Dq) ∈ Q.cosupp ∧
      toLex (hilbertSamuelAt A.ideal ⟨0,haD⟩) < toLex (hilbertSamuelAt Q.ideal ⟨0,hqD⟩) ∧
      (canonicalInvariant 3).inv A .refl ⟨0,haD⟩ = (canonicalInvariant 3).inv Q .refl ⟨0,hqD⟩ := by
  have hA : IsComplexAnalyticSubset (n := 3) axesSet := fun z =>
    RemmertSteinFlat.nonempty_presentation_of_eqOn isOpen_univ (mem_univ z) axesFunction
      (fun i => (axesDiff i).differentiableOn) (fun _ _ => Iff.rfl)
  have hQ : IsComplexAnalyticSubset (n := 3) quadSet := fun z =>
    RemmertSteinFlat.nonempty_presentation_of_eqOn isOpen_univ (mem_univ z) (fun _ : Fin 1 => quadFunction)
      (fun _ => quadDiff.differentiableOn) (fun _ _ => ⟨fun h _ => h,fun h => h 0⟩)
  obtain ⟨Dₐ,haD,hIa,haDom,haCos,haVal⟩ := read_geometric_initial_of_origin_eq axesSet hA axesIdeal
    axesDom (at_origin axesFunction axesDiff (fun i => by simp [axesFunction,coord])) axes_geometric_origin Bₐ hₐ
  obtain ⟨Dq,hqD,hIq,hqDom,hqCos,hqVal⟩ := read_geometric_initial_of_origin_eq quadSet hQ quadIdeal
    quadDom (at_origin (fun _ : Fin 1 => quadFunction) (fun _ => quadDiff)
      (fun _ => by simp [quadFunction,coord])) quad_geometric_origin Bq hq
  refine ⟨Dₐ,Dq,haD,hqD,hIa,hIq,haDom,hqDom,haCos,hqCos,?_,
    haVal.trans (axes_quad_original_mark_one_initial_value_eq.trans hqVal.symm)⟩
  have haHS (l : ℕ) : hilbertSamuelAt (geometricRecord axesSet Dₐ).ideal ⟨0,haD⟩ l =
      hilbertSamuelAt axesIdeal 0 l := by
    change hilbertSamuelAt (vanishingIdeal (n := 3) ((Subtype.val : Dₐ → ComplexModel 3) ⁻¹' axesSet))
      ⟨0,haD⟩ l = _
    rw [hilbertSamuelAt_vanishing_actual_open_any,hilbertSamuelAt_model_zero,axes_geometric_origin]
    exact (hilbertSamuelAt_model_zero axesIdeal l).symm
  have hqHS (l : ℕ) : hilbertSamuelAt (geometricRecord quadSet Dq).ideal ⟨0,hqD⟩ l =
      hilbertSamuelAt quadIdeal 0 l := by
    change hilbertSamuelAt (vanishingIdeal (n := 3) ((Subtype.val : Dq → ComplexModel 3) ⁻¹' quadSet))
      ⟨0,hqD⟩ l = _
    rw [hilbertSamuelAt_vanishing_actual_open_any,hilbertSamuelAt_model_zero,quad_geometric_origin]
    exact (hilbertSamuelAt_model_zero quadIdeal l).symm
  change toLex (hilbertSamuelAt (geometricRecord axesSet Dₐ).ideal ⟨0,haD⟩) <
    toLex (hilbertSamuelAt (geometricRecord quadSet Dq).ideal ⟨0,hqD⟩)
  rw [funext haHS,funext hqHS]
  exact axes_quad_HS_orders_original_tie.1

end
end Hironaka.HironakaG8QuadraticGeometricInitialConflict

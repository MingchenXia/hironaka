import Hironaka.Resolution.HironakaActualLocalHolomorphicOriginPullback
import Hironaka.Resolution.HironakaActualSelectedCentreStrictSaturation
import Hironaka.Coherence.CartanIrreducible

/-! Genuine SOURCE local finite generation suffices for the whole TRUE
strict saturation in ANY original selected centre chart. Analytic SET
GERMS produce that source finite generation through actual local Cartan;
no global analyticity at the model-chart boundary is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalFGStrictSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  OkaRelationSheaf OkaIdealOperations AnalyticGermDecomposition CartanIrreducibleReduction
  HironakaActualLocalStrictSaturation HironakaActualLocalHolomorphicOriginPullback
  HironakaActualSelectedCentreStrictSaturation HironakaActualStrictPullbackSaturation
  HironakaActualAnalyticBlowupTaylor HironakaActualPointExceptionalVanishing HironakaActualPointGeometricBennett
  HironakaActualAnalyticStrictGenerators HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalAnalyticGraphQuotient HironakaHolomorphicJetChartInvariance

variable {n : ℕ}

/-- Actual analytic SET GERM geometry supplies both nearby vanishing-stalk
generator directions, without analyticity of a global representative. -/
theorem actual_analytic_germ_vanishing_local_fg
    (W : Set (ComplexModel n)) (hW : IsAnalyticGerm W) :
    IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n) := by
  obtain ⟨N,f,hf,hSet⟩:=hW
  obtain ⟨Ω,hΩD,hΩ,h0Ω⟩:=eventually_nhds_iff.mp (eventually_all.mpr hf)
  have hLocal:=localCartan_of_irreducibleLocalCartan (CartanIrreducible.irreducibleLocalCartan n)
  have hFG:=hLocal Ω hΩ N f (fun i z hz=>(hΩD z hz i).differentiableWithinAt) 0 h0Ω
  apply hFG.congr
  filter_upwards [hSet.eventually_nhds] with y hy g
  constructor
  · rintro ⟨hg,hzero⟩
    refine ⟨hg.mono (fun _ h=>h.mdifferentiableAt),?_⟩
    filter_upwards [hzero,hy] with z hz hEq hzW
    exact hz (hEq.mp hzW)
  · rintro ⟨hg,hzero⟩
    refine ⟨hg.mono (fun _ h=>h.differentiableAt),?_⟩
    filter_upwards [hzero,hy] with z hz hEq hzF
    exact hz (hEq.mpr hzF)

/-- The ENTIRE true selected geometric strict ideal is the exceptional
saturation of the ENTIRE actual total pullback, from SOURCE local FG. -/
theorem mem_actual_selected_strict_ideal_iff_power_of_local_fg
    (A : Set (Fin n)) (e : Fin n) (hOther : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n))
    (hFG : IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n))
    (g : HolGerm (ComplexModel n)) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n:=n)
      (strictTransform n (actualAnalyticBlowupMap A e b) W)) ↔
      ∃N : ℕ,(coordinateGerm e)^N*g∈
        Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)) := by
  let π:=actualAnalyticBlowupMap A e b
  let I:=vanishingIdeal (n:=n) W
  let J:=GermIdeal.pullback (m:=n) π I
  have hπ : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ π z:=
    Eventually.of_forall fun _=>(differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have hπ0 : π 0=0:=actualAnalyticBlowupMap_zero A e b
  have hJ : IdealFGAt J.mem (0 : ComplexModel n):=
    local_fg_pullback_of_holomorphic_germ π hπ hπ0 I hFG
  have hMap : originalCoherentOriginIdeal J=
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I):=
    origin_pullback_eq_of_holomorphic_germ π hπ hπ0 I hFG
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩:=HolGerm.exists_eq_mk g
    have hzero:=(mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    obtain ⟨U,hUprop,hU,h0U⟩:=eventually_nhds_iff.mp (hG.and hzero)
    have hOff : ∀ᶠy in 𝓝 (0 : ComplexModel n),y e≠0 → J.mem y G := by
      filter_upwards [hU.mem_nhds h0U] with y hy hye
      apply (pullback_vanishingIdeal_mem_iff_off_coordinate A e b W y hye G).mpr
      have hGU : DifferentiableOn ℂ G U:=fun z hz=>(hUprop z hz).1.differentiableWithinAt
      refine ⟨(holAt_of_differentiableOn hU hGU hy).mono (fun _ h=>h.mdifferentiableAt),?_⟩
      filter_upwards [hU.mem_nhds hy,
        (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hye]
        with z hz hze hzW
      apply (hUprop z hz).2
      rw [strictTransform,exceptionalLocus_actual_selected_centre_blowup_eq A e hOther b]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩:=exists_power_of_local_fg_off_divisor J hJ G hG e hOff
    exact ⟨N,by rwa [hMap] at hN⟩
  · rintro ⟨N,hN⟩
    apply (coordinate_pow_mul_mem_actual_selected_strict_ideal_iff A e hOther b W N g).mp
    have hTotal : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
        (originalCoherentOriginIdeal I)≤originalCoherentOriginIdeal (vanishingIdeal (n:=n)
          (strictTransform n (actualAnalyticBlowupMap A e b) W)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro F hF
      apply actual_selected_normalized_ideal_le_geometric_strict_vanishing A e hOther b W
      apply Ideal.subset_span
      refine ⟨0,F,hF,?_,?_⟩
      · rw [pow_zero,Ideal.one_eq_top]
        exact Submodule.mem_top
      · simp only [pow_zero,one_mul]
        rfl
    exact hTotal hN

/-- An actual analytic set GERM internally produces all source local FG
needed for the same whole arbitrary-selected geometric strict dictionary. -/
theorem mem_actual_selected_strict_ideal_iff_power_of_analytic_germ
    (A : Set (Fin n)) (e : Fin n) (hOther : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hW : IsAnalyticGerm W)
    (g : HolGerm (ComplexModel n)) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n:=n)
      (strictTransform n (actualAnalyticBlowupMap A e b) W)) ↔
      ∃N : ℕ,(coordinateGerm e)^N*g∈
        Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)) :=
  mem_actual_selected_strict_ideal_iff_power_of_local_fg A e hOther b W
    (actual_analytic_germ_vanishing_local_fg W hW) g

end
end Hironaka.HironakaActualLocalFGStrictSaturation

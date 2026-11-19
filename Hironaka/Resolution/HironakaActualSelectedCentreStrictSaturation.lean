import Hironaka.Resolution.HironakaActualStrictPullbackSaturation

/-! True differential exceptional geometry and ENTIRE strict saturation for
ANY original selected normal subset. No historical index is permuted. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSelectedCentreStrictSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualAnalyticBlowupTaylor HironakaActualNormalBlowupExceptionalLocus
  HironakaActualStrictRadicalPullback HironakaActualStrictExceptionalRegularity
  HironakaActualStrictPullbackSaturation HironakaActualPointGeometricBennett
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations
  HironakaActualPointExceptionalVanishing HironakaActualAnalyticStrictGenerators
  HironakaRelativeNormalAnalyticGraphQuotient OkaRelationSheaf
  HironakaHolomorphicJetChartInvariance

variable {n : ℕ}

private theorem selected_exceptional_coordinate_zero
    (A : Set (Fin n)) (e : Fin n) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z e=0) :
    z∈exceptionalLocus n (actualAnalyticBlowupMap A e b) := by
  obtain ⟨f,hf,hfe⟩:=hA
  let v : ComplexModel n:=PiLp.single 2 f 1
  have hve : v e=0:=by simp [v,Ne.symm hfe]
  have hv : v≠0 := by
    intro h
    have hzero:=congrArg (fun w : ComplexModel n=>w f) h
    simp [v] at hzero
  have hKernel : mfderiv 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (actualAnalyticBlowupMap A e b) z v=0 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℂ (actualAnalyticBlowupMap A e b) z v=0
    ext i
    have hc:=mfderiv_actual_selected_blowup_apply A e b z v i
    rw [mfderiv_eq_fderiv] at hc
    by_cases hi : i∈A
    · simp only [if_pos hi,hve,hz,zero_mul,add_zero,ite_self] at hc
      exact hc
    · have hif : i≠f:=fun h=>hi (h ▸ hf)
      have hvi : v i=0:=by simp [v,hif]
      simp only [if_neg hi,hvi] at hc
      exact hc
  intro hBij
  exact hv (hBij.1 (hKernel.trans (map_zero _).symm))

/-- The genuine differential exceptional locus in ANY original selected
normal subset with a second actual normal direction. -/
theorem exceptionalLocus_actual_selected_centre_blowup_eq
    (A : Set (Fin n)) (e : Fin n) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ) :
    exceptionalLocus n (actualAnalyticBlowupMap A e b)={z : ComplexModel n | z e=0} := by
  ext z
  constructor
  · intro hz
    by_contra hne
    exact hz (mfderiv_actual_selected_blowup_bijective_of_coordinate_ne_zero A e b z hne)
  · exact selected_exceptional_coordinate_zero A e hA b z

/-- The full divisor/identity branch, in the SAME arbitrary original indices. -/
theorem actual_selected_divisor_blowup_eq_id
    (A : Set (Fin n)) (e : Fin n) (hA : A⊆{e}) (b : Fin n → ℂ) :
    actualAnalyticBlowupMap A e b=id := by
  funext z
  ext i
  by_cases hi : i∈A
  · have hie : i=e:=Set.mem_singleton_iff.mp (hA hi)
    subst i
    simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]
  · simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]

/-- Every actual coordinate power cancels in the ENTIRE true selected
geometric strict ideal, before any normalized division or target HS. -/
theorem coordinate_pow_mul_mem_actual_selected_strict_ideal_iff
    (A : Set (Fin n)) (e : Fin n) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (q : ℕ) (g : HolGerm (ComplexModel n)) :
    (coordinateGerm e)^q*g∈originalCoherentOriginIdeal (vanishingIdeal (n:=n)
      (strictTransform n (actualAnalyticBlowupMap A e b) W)) ↔
      g∈originalCoherentOriginIdeal (vanishingIdeal (n:=n)
        (strictTransform n (actualAnalyticBlowupMap A e b) W)) := by
  apply coordinate_pow_mul_mem_closure_ideal_iff
  intro z hz hze
  exact hz.2 (selected_exceptional_coordinate_zero A e hA b z hze)

private theorem contMDiff_selected_blowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n=>z i):=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((contDiff_const (c:=b i)).add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

private theorem selected_total_pullback_le_true_strict
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (W : Set (ComplexModel n)) :
    Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))≤
      originalCoherentOriginIdeal (vanishingIdeal (n:=n)
        (strictTransform n (actualAnalyticBlowupMap A e b) W)) := by
  let π:=actualAnalyticBlowupMap A e b
  have hπ : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ π z:=
    Eventually.of_forall fun _=>(differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have hπ0 : π 0=0:=actualAnalyticBlowupMap_zero A e b
  have ht : Tendsto π (𝓝 (0 : ComplexModel n)) (𝓝 (0 : ComplexModel n)) := by
    have h : Tendsto π (𝓝 (0 : ComplexModel n)) (𝓝 (π 0)):=
      (differentiable_actualAnalyticBlowupMap A e b).continuous.tendsto 0
    rwa [hπ0] at h
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨F,hF,hFW,rfl⟩
  change actualAnalyticBlowupPullback A e b (HolGerm.mk F hF)∈
    originalCoherentOriginIdeal (vanishingIdeal (n:=n) (strictTransform n π W))
  rw [actualAnalyticBlowupPullback,compAlgHom_mk]
  apply (mk_mem_original_vanishing_origin_ideal_iff _ (F∘π) _).mpr
  apply eventually_zero_on_closure_of_eventually_continuous (F∘π)
    (π ⁻¹' W\exceptionalLocus n π)
    ((holomorphic_comp π hπ hπ0 hF).mono fun _ h=>h.continuousAt)
  filter_upwards [ht.eventually hFW.2] with z hz hzS
  exact hz hzS.1

/-- Actual original geometry identifies the ENTIRE selected strict ideal
with actual exceptional saturation of the ENTIRE total pullback ideal. -/
theorem mem_actual_selected_analytic_strict_ideal_iff_exists_coordinate_power
    (A : Set (Fin n)) (e : Fin n) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hW : IsComplexAnalyticSubset (n:=n) W)
    (g : HolGerm (ComplexModel n)) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n:=n)
      (strictTransform n (actualAnalyticBlowupMap A e b) W)) ↔
      ∃N : ℕ,(coordinateGerm e)^N*g∈Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
        (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)) := by
  let π:=actualAnalyticBlowupMap A e b
  let I:=vanishingIdeal (n:=n) W
  let J:=GermIdeal.pullback (m:=n) π I
  have hI : I.IsCoherent:=CartanIrreducible.cartanCoherence W hW
  have hπ:=contMDiff_selected_blowup A e b
  have hπ0 : π 0=0:=actualAnalyticBlowupMap_zero A e b
  have hJ : J.IsCoherent:=GermIdealPullbackCalculus.isCoherent_pullback hπ hI
  have hMap : originalCoherentOriginIdeal J=Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (originalCoherentOriginIdeal I):=originalOriginIdeal_holomorphic_pullback_eq π hπ hπ0 I hI
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
      rw [strictTransform,exceptionalLocus_actual_selected_centre_blowup_eq A e hA b]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩:=exists_coordinate_power_mul_mem_of_off_divisor_membership J hJ G hG e hOff
    exact ⟨N,by rwa [hMap] at hN⟩
  · rintro ⟨N,hN⟩
    exact (coordinate_pow_mul_mem_actual_selected_strict_ideal_iff A e hA b W N g).mp
      (selected_total_pullback_le_true_strict A e b W hN)

/-- ENTIRE actual normalized-member ideal inclusion in the TRUE geometric
strict ideal. Neither original analyticity nor target HS is assumed. -/
theorem actual_selected_normalized_ideal_le_geometric_strict_vanishing
    (A : Set (Fin n)) (e : Fin n) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) :
    actualAnalyticNormalizedMemberIdeal (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)) A e b≤
      originalCoherentOriginIdeal (vanishingIdeal (n:=n)
        (strictTransform n (actualAnalyticBlowupMap A e b) W)) := by
  apply Ideal.span_le.mpr
  rintro H ⟨q,F,hF,_hCentre,hProduct⟩
  apply (coordinate_pow_mul_mem_actual_selected_strict_ideal_iff A e hA b W q H).mp
  rw [hProduct]
  exact selected_total_pullback_le_true_strict A e b W
    (Ideal.mem_map_of_mem (actualAnalyticBlowupPullback A e b).toRingHom hF)

end
end Hironaka.HironakaActualSelectedCentreStrictSaturation

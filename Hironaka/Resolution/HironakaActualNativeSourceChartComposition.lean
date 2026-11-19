import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison
import Hironaka.Analytic.RegularAtDimTransport

/-! The SAME whole native source ideals under a genuine compatible source
chart composition. No target ideal identity or coordinate model analyticity
is supplied; actual analytic inverse maps produce the entire germ action. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSourceChartComposition
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualControlledNeighborhoodGenerators HironakaSmoothSubmersionGermIdealColon
  HironakaActualFixedFlatteningHSComparison HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  BlowupFlatCoordinates MarkedIdeals RelativePrincipalizationSpan GermIdealOrder

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private def inverse_source_chart {p q : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n:=n) p) (hpq : Φ.toFun p=q) :
    LocalHolomorphicEquivAt (n:=n) q where
  source:=Φ.target
  target:=Φ.source
  isOpen_source:=Φ.isOpen_target
  isOpen_target:=Φ.isOpen_source
  center_mem_source:=hpq ▸ Φ.mapsTo_toFun Φ.center_mem_source
  toFun:=Φ.invFun
  invFun:=Φ.toFun
  toFun_holomorphic:=Φ.invFun_holomorphic
  invFun_holomorphic:=Φ.toFun_holomorphic
  mapsTo_toFun:=Φ.mapsTo_invFun
  mapsTo_invFun:=Φ.mapsTo_toFun
  left_inv:=Φ.right_inv
  right_inv:=Φ.left_inv

private theorem model_regular_iff (c : ℕ) (C : Set (ComplexModel n)) :
    RegularAtDim (n:=n) C 0 c ↔ c≤n ∧ (0 : ComplexModel n)∈C ∧
      ∃D : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n),
        D.toFun 0=0 ∧ ∀{z},z∈D.source → (z∈C ↔ D.toFun z∈complexCoordinatePlane n c) := by
  simp [RegularAtDim,complexChartAt,chartAt_self_eq]
  intro _ _
  rfl

omit [IsComplexManifold n X] in
/-- The genuine actual composition has the required ORIGINAL native source
domain and is centred. Both facts are outputs of the real source maps. -/
theorem actual_native_source_chart_comp_geometry (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (D : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hD0 : D.toFun 0=0) :
    (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0).source⊆
        (chartAt (ComplexModel n) x).target ∧
      (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0).toFun
        (chartAt (ComplexModel n) x x)=0 := by
  refine ⟨fun _ hz=>hΦsrc hz.1,?_⟩
  change D.toFun (Φ.toFun (chartAt (ComplexModel n) x x))=0
  rw [hΦ0,hD0]

/-- Actual inverse-coordinate composition gives the ENTIRE same source
function germ, rather than an equality only on finite jets. -/
theorem actual_native_source_chart_comp_germ (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (D : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hD0 : D.toFun 0=0)
    (F : X → ℂ) (hF : HolomorphicAt n F x) :
    adaptedGerm x (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0)
      (actual_native_source_chart_comp_geometry x Φ hΦsrc hΦ0 D hD0).2 F hF=
      (localGermAlgEquiv D hD0).symm (adaptedGerm x Φ hΦ0 F hF) := by
  have hOld:=(holomorphic_adapted_iff x Φ hΦ0 F).mpr hF
  have hComp:=holomorphic_comp D.invFun (local_invFun_holomorphic D hD0)
    (local_invFun_zero D hD0) hOld
  change HolGerm.mk (fun z=>F ((chartAt (ComplexModel n) x).symm (Φ.invFun (D.invFun z)))) hComp=
    HolGerm.mk ((fun z=>F ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))∘D.invFun) hComp
  rfl

/-- EVERY whole actual source ideal maps exactly under the SAME genuine
coordinate composition; no target generator or ideal certificate is an input. -/
theorem actual_native_source_chart_comp_ideal (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (D : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hD0 : D.toFun 0=0)
    (I : GermIdeal n X) :
    adaptedIdeal I x (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0)
      (actual_native_source_chart_comp_geometry x Φ hΦsrc hΦ0 D hD0).2=
      Ideal.map (localGermAlgEquiv D hD0).symm.toRingEquiv.toRingHom (adaptedIdeal I x Φ hΦ0) := by
  unfold adaptedIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨F,hF,hIF,rfl⟩
    exact ⟨adaptedGerm x Φ hΦ0 F hF,⟨F,hF,hIF,rfl⟩,
      (actual_native_source_chart_comp_germ x Φ hΦsrc hΦ0 D hD0 F hF).symm⟩
  · rintro ⟨h,⟨F,hF,hIF,rfl⟩,rfl⟩
    exact ⟨F,hF,hIF,(actual_native_source_chart_comp_germ x Φ hΦsrc hΦ0 D hD0 F hF).symm⟩

/-- The literal zero-translated flattened vanishing origin ideal is exactly
the whole native adapted ideal. Only ORIGINAL native coherence is required. -/
theorem actual_original_translated_flattened_vanishing_origin_eq_adapted
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (W : Set X) (hW : (vanishingIdeal (n:=n) W).IsCoherent) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0)=
      adaptedIdeal (vanishingIdeal (n:=n) W) x Φ hΦ0 := by
  have h0T:=actualFlattening_target_zero_mem x Φ hΦ0
  have hFlatOrigin : originalCoherentOriginIdeal
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ)=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Φ W)) := by
    unfold originalCoherentOriginIdeal
    apply congrArg Ideal.span
    ext g
    constructor
    · rintro ⟨f,hf,hIf,rfl⟩
      exact ⟨f,hf,(flattened_vanishing_mem_iff x Φ hΦsrc W 0 h0T f).mp hIf,rfl⟩
    · rintro ⟨f,hf,hIf,rfl⟩
      exact ⟨f,hf,(flattened_vanishing_mem_iff x Φ hΦsrc W 0 h0T f).mpr hIf,rfl⟩
  exact (originalFlattenedVanishingOriginIdeal_eq_model x Φ hΦsrc hΦ0 W).trans
    (hFlatOrigin.symm.trans (actual_flattened_origin_eq_adapted (vanishingIdeal (n:=n) W) hW x Φ hΦ0))

omit [IsComplexManifold n X] in
/-- Original native regularity produces the genuine source centre model in
ANY GIVEN actual coordinates, with the SAME dimension. No model regularity
certificate or freshly selected historical family is supplied. -/
theorem actual_native_given_chart_regular_model
    (C : Set X) (x : X) (c : ℕ) (hC : RegularAtDim (n:=n) C x c)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    RegularAtDim (n:=n) (actualFixedFlatteningSet x Φ C) 0 c := by
  obtain ⟨hcn,hxC,Ξ,_hΞsrc,hΞ0,hΞflat⟩:=hC
  have hInv0 : Φ.invFun 0=chartAt (ComplexModel n) x x := by
    rw [←hΦ0,Φ.left_inv _ Φ.center_mem_source]
  let D:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp (inverse_source_chart Φ hΦ0) Ξ hInv0
  apply (model_regular_iff c (actualFixedFlatteningSet x Φ C)).mpr
  refine ⟨hcn,?_,D,?_,?_⟩
  · refine ⟨actualFlattening_target_zero_mem x Φ hΦ0,?_⟩
    change actualFlatteningInverseMap x Φ 0∈C
    rw [actualFlatteningInverseMap_zero x Φ hΦ0]
    exact hxC
  · change Ξ.toFun (Φ.invFun 0)=0
    rw [hInv0]
    exact hΞ0
  · intro z hz
    change z∈Φ.target ∩ Φ.invFun ⁻¹' Ξ.source at hz
    have hInvTarget : Φ.invFun z∈(chartAt (ComplexModel n) x).target:=
      hΦsrc (Φ.mapsTo_invFun hz.1)
    have hNativeSource:=(chartAt (ComplexModel n) x).map_target hInvTarget
    have hCoord:=(chartAt (ComplexModel n) x).right_inv hInvTarget
    have hΞSource : chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm (Φ.invFun z))∈Ξ.source := by
      rw [hCoord]
      exact hz.2
    have hNative:=hΞflat hNativeSource hΞSource
    change ((chartAt (ComplexModel n) x).symm (Φ.invFun z)∈C ↔
      Ξ.toFun (chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))∈
        complexCoordinatePlane n c) at hNative
    rw [hCoord] at hNative
    change (z∈Φ.target ∩ actualFlatteningInverseMap x Φ ⁻¹' C ↔
      Ξ.toFun (Φ.invFun z)∈complexCoordinatePlane n c)
    exact ⟨fun h=>hNative.mp h.2,fun h=>⟨hz.1,hNative.mpr h⟩⟩

/-- The SAME actual native inverse coordinates form a genuine holomorphic
map on EVERY open contained in the true coordinate target. -/
theorem actual_native_source_inverse_on_open_contMDiff (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (U : TopologicalSpace.Opens (ComplexModel n))
    (hU : (U : Set (ComplexModel n))⊆Φ.target) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : U=>actualFlatteningInverseMap x Φ z) := by
  intro z
  have hmd : ∀ᶠa in 𝓝 (z : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
        (actualFlatteningInverseMap x Φ) a :=
    eventually_of_mem (Φ.isOpen_target.mem_nhds (hU z.property))
      (fun a ha=>actualFlatteningInverseMap_mdifferentiable x Φ hΦsrc a ha)
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
    (contMDiff_subtype_val z)

/-- TRUE original marked cosupport pulls into the literal ENTIRE native
pullback record under a genuine holomorphic map, retaining its actual mark. -/
theorem actual_marked_cosupport_pullback_forward
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (Q : MarkedIdeal n X) (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (y : Y) (hy : f y∈Q.cosupp) :
    y∈(MarkedIdealBiholomorphism.MarkedIdeal.pullback f Q).cosupp := by
  refine ⟨hy.1,fun g hg=>?_⟩
  refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
    (GermIdeal.mem_pullback_iff.mp hg) ?_
  rintro _ ⟨a,ha,rfl⟩
  exact MonomialPartEtale.vanishesToOrderOn_comp
    (Eventually.of_forall fun w=>(hf w).mdifferentiableAt (by simp)) (hy.2 a ha)

end
end Hironaka.HironakaActualNativeSourceChartComposition

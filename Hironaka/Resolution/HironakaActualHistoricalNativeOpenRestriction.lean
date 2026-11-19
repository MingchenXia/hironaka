import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep

/-! Restriction of actual SAME-chart/five-law point data to the LITERAL
native phase open. Whole ideals follow from actual source finite generation
and the genuine subtype inverse. No desired target data or new family. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeOpenRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualHistoricalInitialAffineDictionary HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision HironakaActualNativeSourceChartComposition
  HironakaSmoothSubmersionGermIdealColon HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedCoefficientCompression
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  MarkedIdeals

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The SAME given chart, restricted to the actual preferred chart target
of the true native open. Its functions and inverse are unchanged. -/
def actualNativeOpenChart (O : Opens X) (x : O)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x.val x.val)) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x) :=
  Φ.restrict (chartAt (ComplexModel n) x).target (chartAt (ComplexModel n) x).open_target
    (chartAt (ComplexModel n) x x)
    ⟨Φ.center_mem_source,(chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)⟩

omit [IsComplexManifold n X] in
/-- The actual restricted given chart is legal and centred on the native
open; its source/target geometry is derived from the actual restriction. -/
theorem actual_native_open_chart_geometry (O : Opens X) (x : O)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x.val x.val))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x.val x.val)=0) :
    (actualNativeOpenChart O x Φ).source⊆(chartAt (ComplexModel n) x).target ∧
      (actualNativeOpenChart O x Φ).toFun (chartAt (ComplexModel n) x x)=0 :=
  ⟨fun _ hz=>hz.2,hΦ0⟩

omit [IsComplexManifold n X] in
private theorem actual_native_open_inverse (O : Opens X) (x : O)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x.val x.val))
    (z : ComplexModel n) (hz : z∈(actualNativeOpenChart O x Φ).target) :
    (((chartAt (ComplexModel n) x).symm ((actualNativeOpenChart O x Φ).invFun z) : O) : X)=
      (chartAt (ComplexModel n) x.val).symm (Φ.invFun z) := by
  have ht : Φ.invFun z∈((chartAt (ComplexModel n) x.val).subtypeRestr ⟨x⟩).target := by
    simpa only [Opens.chartAt_eq,mem_preimage] using hz.2
  exact (chartAt (ComplexModel n) x.val).subtypeRestr_symm_apply (⟨x⟩ : Nonempty O) ht

/-- ENTIRE original functions have the SAME adapted germs on the literal
native open, in the restricted GIVEN original chart. -/
theorem actual_native_open_adapted_germ (O : Opens X) (x : O)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x.val x.val))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x.val x.val)=0)
    (F : X → ℂ) (hF : HolomorphicAt n F x.val) :
    adaptedGerm x (actualNativeOpenChart O x Φ) (actual_native_open_chart_geometry O x Φ hΦ0).2
      (F ∘ (Subtype.val : O → X))
      (hF.comp_contMDiff (Eventually.of_forall fun _=>contMDiff_subtype_val.contMDiffAt))=
      adaptedGerm x.val Φ hΦ0 F hF := by
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0 : (0 : ComplexModel n)∈(actualNativeOpenChart O x Φ).target := by
    simpa only [(actual_native_open_chart_geometry O x Φ hΦ0).2] using
      (actualNativeOpenChart O x Φ).mapsTo_toFun (actualNativeOpenChart O x Φ).center_mem_source
  filter_upwards [(actualNativeOpenChart O x Φ).isOpen_target.mem_nhds h0] with z hz
  exact congrArg F (actual_native_open_inverse O x Φ z hz)

/-- ANY coherent source ideal has the SAME ENTIRE adapted ideal after
the actual open pullback, in the restricted GIVEN chart. -/
theorem actual_native_open_adapted_ideal (J : GermIdeal n X) (hJ : J.IsCoherent)
    (O : Opens X) (x : O)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x.val x.val))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x.val x.val)=0) :
    adaptedIdeal (GermIdeal.pullback (m:=n) (Subtype.val : O → X) J) x
        (actualNativeOpenChart O x Φ) (actual_native_open_chart_geometry O x Φ hΦ0).2=
      adaptedIdeal J x.val Φ hΦ0 := by
  obtain ⟨U,hU,hx,s,f,hf,hgen⟩:=hJ x.val
  have hfh (i : Fin s) : HolomorphicAt n (f i) x.val:=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hf i) hx
  have hfo (i : Fin s) : HolomorphicAt n (f i ∘ (Subtype.val : O → X)) x:=
    (hfh i).comp_contMDiff (Eventually.of_forall fun _=>contMDiff_subtype_val.contMDiffAt)
  have hgo (F : O → ℂ):=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _=>contMDiff_subtype_val.contMDiffAt) J f hfh (hgen x.val hx) F
  rw [actual_native_adapted_ideal_of_whole_generation _ x _ _ _ hfo hgo,
    actual_native_adapted_ideal_of_whole_generation J x.val Φ hΦ0 f hfh (hgen x.val hx)]
  apply congrArg Ideal.span
  congr 1
  funext i
  exact actual_native_open_adapted_germ O x Φ hΦ0 (f i) (hfh i)

/-- The LITERAL open restriction of the existing full Q retains the SAME
member family/words/selector and every native five-law point field. -/
theorem actual_native_point_presentation_open_restriction
    {V : Finset (Fin n →₀ ℕ)} {k : ℕ} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (hW : (vanishingIdeal (n:=n) W).IsCoherent)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent) (O : Opens X) (x : O)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x.val) :
    ActualHistoricalNativePointPresentation S a w ((Subtype.val : O → X) ⁻¹' W)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) Q) x := by
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,hFive,hSpan,hCompression⟩:=hAt
  let Θ:=actualNativeOpenChart O x Φ
  have hΘsrc:=(actual_native_open_chart_geometry O x Φ hΦ0).1
  have hΘ0:=(actual_native_open_chart_geometry O x Φ hΦ0).2
  have hWOpen : (vanishingIdeal (n:=n) ((Subtype.val : O → X) ⁻¹' W)).IsCoherent := by
    rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hW
  have hWhole:=actual_native_open_adapted_ideal (vanishingIdeal (n:=n) W) hW O x Φ hΦ0
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hWhole
  have hOldOrigin:=actual_original_translated_flattened_vanishing_origin_eq_adapted
    x.val Φ hΦsrc hΦ0 W hW
  have hNewOrigin:=actual_original_translated_flattened_vanishing_origin_eq_adapted
    x Θ hΘsrc hΘ0 ((Subtype.val : O → X) ⁻¹' W) hWOpen
  refine ⟨Θ,hΘsrc,hΘ0,Γ,hFive,?_,?_⟩
  · exact hSpan.trans (hOldOrigin.trans (hWhole.symm.trans hNewOrigin.symm))
  · exact (actual_native_open_adapted_ideal Q.ideal hQI O x Φ hΦ0).trans hCompression

end
end Hironaka.HironakaActualHistoricalNativeOpenRestriction

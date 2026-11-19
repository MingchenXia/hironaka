import Hironaka.Resolution.HironakaActualNativeSectionRegularity
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicHS
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! The entire intrinsic Hilbert--Samuel profile of an actual native image.
Blueprint: hironaka-actual-native-section-hilbert-samuel-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualNativeSectionHilbertSamuel
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense SubmanifoldChartedSpace IsManifold
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence HironakaReducedComplexAnalyticSpaces
  HironakaActualNativeSectionRegularity HironakaActualAnalyticSubspaceIntrinsicHS
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance

/-- Every order of the TRUE entire vanishing-ideal profile is unchanged by
the actual native carrier inclusion, via a produced local intrinsic iso. -/
theorem hilbertSamuelAt_native_image {n k : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {W : Set X} (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(A : Set W)(p : W),p∈A → ∀ℓ,
      hilbertSamuelAt (vanishingIdeal (n:=n) ((Subtype.val : W→X) '' A)) p.val ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=k) A) p ℓ := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A p hpA ℓ
  obtain ⟨U,hpU,R,hR,hFix,hRU⟩:=exists_actual_native_retraction_window hk hW p
  let V : Opens W:=⟨(Subtype.val : W→X) ⁻¹' U,U.isOpen.preimage continuous_subtype_val⟩
  let f : U→V:=fun y=>⟨R y,hRU y⟩
  let g : V→U:=fun q=>⟨q.val.val,q.property⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ f:=
    (ContMDiff.subtypeVal_comp_iff V f).mp hR
  have hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ g:=
    (ContMDiff.subtypeVal_comp_iff U g).mp ((contMDiff_val hk hW).comp contMDiff_subtype_val)
  let C : Set U:=(Subtype.val : U→X) ⁻¹' ((Subtype.val : W→X) '' A)
  let D : Set V:=(Subtype.val : V→W) ⁻¹' A
  have hRq (y : U) (q : W) (hq : q.val=y.val) : R y=q := by
    have hqU : q.val∈U:=hq ▸ y.property
    have he : (⟨q.val,hqU⟩ : U)=y:=Subtype.ext hq
    rw [←he,hFix]
  have hCD : ∀y∈C,f y∈D:=by
    rintro y ⟨q,hqA,hq⟩
    change R y∈A
    rw [hRq y q hq]
    exact hqA
  have hDC : ∀q∈D,g q∈C:=by
    intro q hq
    exact ⟨q.val,hq,rfl⟩
  have hgf : ∀y∈C,g (f y)=y:=by
    rintro y ⟨q,_hqA,hq⟩
    apply Subtype.ext
    change (R y).val=y.val
    rw [hRq y q hq]
    exact hq
  have hfg : ∀q∈D,f (g q)=q:=by
    intro q _hq
    apply Subtype.ext
    exact hFix q.val q.property
  let e:=actualSubspaceMutualRestrictionIso hf hg hCD hDC hgf hfg
  let x : U:=⟨p.val,hpU⟩
  let y : V:=⟨p,hpU⟩
  have hxC : x∈C:=⟨p,hpA,rfl⟩
  have hxy : (e.hom.base ⟨x,hxC⟩).val=y:=by
    apply Subtype.ext
    exact hFix p hpU
  have hHS:=hilbertSamuelAt_vanishing_intrinsic_iso e (actualSubspaceMap_point hf hCD) ⟨x,hxC⟩ ℓ
  change hilbertSamuelAt (vanishingIdeal (n:=n) C) x ℓ=
    hilbertSamuelAt (vanishingIdeal (n:=k) D) (e.hom.base ⟨x,hxC⟩).val ℓ at hHS
  rw [hxy] at hHS
  exact (hilbertSamuelAt_vanishing_actual_open_any U ((Subtype.val : W→X) '' A) x ℓ).symm.trans
    (hHS.trans (hilbertSamuelAt_vanishing_actual_open_any V A y ℓ))

end
end Hironaka.HironakaActualNativeSectionHilbertSamuel

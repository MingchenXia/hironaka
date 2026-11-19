import Hironaka.Resolution.HironakaG3UniverseLiftedAtlas
import Hironaka.Resolution.HironakaG3UniverseSmallResolutionAtlas
import Hironaka.Resolution.HironakaG3UniverseLiftManifold
import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Resolution.HironakaG3UniverseIndexedSNC
import Hironaka.Resolution.HironakaG3UniversePureTransport
import Hironaka.Resolution.HironakaG3UniverseConjugateGeometry
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
namespace Hironaka.HironakaG3UniverseArbitraryGeometricEndpoint
open Set Function
open scoped Manifold ContDiff Topology
universe w
open Hironaka.BlowupSequences BlowupTowers HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3UniverseSmallManifold HironakaG3UniverseShrinkManifold
  HironakaG3UniverseLiftManifold HironakaG3UniverseSmallResolution HironakaG3UniverseDiffeoDerivative
  HironakaG3UniversePureTransport HironakaG3UniverseCarrierGeometry HironakaG3UniverseIndexedSNC
  HironakaG3UniverseCoordinateTransport
noncomputable section

/-- An actual geometric endpoint for an arbitrary-universe pure analytic target. -/
theorem conjugate_pure_endpoint_from_small_model {n d : ℕ} (X : CMfd.{u} n) {ι : Type w}
    (W : Set X) (D : ι → Set X) {κ ρ : Type}
    (D₀ : κ → Set (shrinkCMfd X))
    (hD₀supp : (⋃ i, D₀ i) = (shrinkDiffeomorph X).symm ⁻¹' (⋃ i, D i))
    {Y₀ : CMfd.{0} n} (P₀ : Y₀ → shrinkCMfd X) (B₀ : ρ → Set Y₀)
    (hSmall :
      let W₀ : Set (shrinkCMfd X) := (shrinkDiffeomorph X).symm ⁻¹' W
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P₀ ∧ IsProperMap P₀ ∧ Surjective P₀ ∧
      P₀ '' strictTransform n P₀ W₀ = W₀ ∧
      IsIsomorphismOver n P₀ (W₀ \ regularLocus (n := n) W₀ d ∪ W₀ ∩ ⋃ i, D₀ i)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P₀ W₀) ∧
      (∀ z ∈ strictTransform n P₀ W₀, RegularAtDim (n := n) (strictTransform n P₀ W₀) z d) ∧
      P₀ ⁻¹' (W₀ \ regularLocus (n := n) W₀ d) ⊆ exceptionalLocus n P₀ ∧
      IsLocallyFiniteSNCDivisor n B₀ ∧ (∀ j, (B₀ j).Nonempty) ∧
      (⋃ j, B₀ j) = P₀ ⁻¹' (⋃ i, D₀ i) ∪ exceptionalLocus n P₀ ∧
      (⋃ j, B₀ j) = P₀ ⁻¹' ((⋃ i, D₀ i) ∪ W₀ \ regularLocus (n := n) W₀ d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P₀ W₀) B₀) :
    let ex := shrinkDiffeomorph X
    let Y : CMfd.{u} n := liftCMfd.{u} Y₀
    let P : Y → X := ex.symm ∘ P₀ ∘ (liftDiffeomorph.{u} Y₀).symm
    let B : ρ → Set Y := fun i => (liftDiffeomorph.{u} Y₀).symm ⁻¹' B₀ i
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
    P '' strictTransform n P W = W ∧
    IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
    IsClosedSubmanifold n (strictTransform n P W) ∧
    (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
    P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
    IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
    (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
    (⋃ a, B a) = P ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
    HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  letI : Small.{0} X := complex_manifold_small X
  let ex := shrinkDiffeomorph X
  let W₀ : Set (shrinkCMfd X) := ex.symm ⁻¹' W
  obtain ⟨hP₀,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB₀,hB₀ne,hSupp,hSupp',hNC⟩ := hSmall
  let Y : CMfd.{u} n := liftCMfd.{u} Y₀
  let ey : Y₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y := liftDiffeomorph Y₀
  let P : Y → X := ex.symm ∘ P₀ ∘ ey.symm
  let B : ρ → Set Y := fun j => ey.symm ⁻¹' B₀ j
  have hReg₀ : regularLocus (n := n) W₀ d = ex.symm ⁻¹' regularLocus (n := n) W d := by
    have hh := transported_regularLocus (n := n) (Shrink.homeomorph X) W d
    exact hh
  have hWback : (ex.symm).symm ⁻¹' W₀ = W := by
    ext x
    simp [W₀,ex]
  have hRegback : (ex.symm).symm ⁻¹' regularLocus (n := n) W₀ d = regularLocus (n := n) W d := by
    rw [hReg₀]
    ext x
    simp [ex]
  have hDback : (ex.symm).symm ⁻¹' (⋃ i, D₀ i) = ⋃ i, D i := by
    rw [hD₀supp]
    ext x
    simp [ex]
  have hSback : (ex.symm).symm ⁻¹' (W₀ \ regularLocus (n := n) W₀ d) =
      W \ regularLocus (n := n) W d := by
    ext x
    have a := Set.ext_iff.mp hWback x
    have b := Set.ext_iff.mp hRegback x
    simpa only [Set.mem_preimage, Set.mem_sdiff] using and_congr a (not_congr b)
  have hGoodback : (ex.symm).symm ⁻¹' (W₀ \ regularLocus (n := n) W₀ d ∪ W₀ ∩ ⋃ i, D₀ i)ᶜ =
      (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ i, D i)ᶜ := by
    ext x
    have a := Set.ext_iff.mp hSback x
    have b := Set.ext_iff.mp hWback x
    have c := Set.ext_iff.mp hDback x
    simpa only [Set.mem_preimage,Set.mem_compl_iff,Set.mem_union,Set.mem_inter_iff] using not_congr (or_congr a (and_congr b c))
  have hSupportback : (ex.symm).symm ⁻¹' ((⋃ i, D₀ i) ∪ W₀ \ regularLocus (n := n) W₀ d) =
      (⋃ i, D i) ∪ W \ regularLocus (n := n) W d := by
    ext x
    have a := Set.ext_iff.mp hSback x
    have b := Set.ext_iff.mp hDback x
    simpa only [Set.mem_preimage,Set.mem_union] using or_congr b a
  have hStrict : strictTransform n P W = ey.symm ⁻¹' strictTransform n P₀ W₀ := by
    have hh := conjugate_strictTransform ey ex.symm P₀ hP₀ W₀
    rw [hWback] at hh
    exact hh
  have hMaps := conjugate_map_properties ey ex.symm P₀ hP₀ hProper hSurj
  have hImage' := conjugate_non_erasure ey ex.symm P₀ hP₀ W₀ hImage
  rw [hWback] at hImage'
  have hGood' := conjugate_isomorphismOver ey ex.symm P₀ hP₀ _ hGood
  rw [hGoodback] at hGood'
  have hSing' := conjugate_preimage_exceptional ey ex.symm P₀ hP₀ _ hSing
  rw [hSback] at hSing'
  have hSupp₁ := conjugate_boundary_support ey ex.symm P₀ hP₀ D₀ B₀ hSupp
  rw [hDback] at hSupp₁
  have hSupp₂ := conjugate_preimage_support ey ex.symm P₀ B₀ _ hSupp'
  rw [hSupportback] at hSupp₂
  have hB : IsLocallyFiniteSNCDivisor n B := by
    have hh := transported_indexed_snc Y₀ (Homeomorph.ulift.symm) B₀ hB₀
    exact hh
  have hBne : ∀ j, (B j).Nonempty := by
    intro j
    obtain ⟨z,hz⟩ := hB₀ne j
    exact ⟨ey z,by simpa [B] using hz⟩
  have hSmooth' : IsClosedSubmanifold n (strictTransform n P W) := by
    rw [hStrict]
    have hh := transported_closedSubmanifold (Homeomorph.ulift.symm) (strictTransform n P₀ W₀) hSmooth
    exact hh
  have hRegular' : ∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d := by
    intro z hz
    rw [hStrict] at hz ⊢
    have hh := transported_regularAtDim_iff (n := n) (Homeomorph.ulift.symm) (strictTransform n P₀ W₀) z d
    exact hh.mpr (hRegular (ey.symm z) hz)
  have hNC' : HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
    rw [hStrict]
    have hh := transported_normalCrossings Y₀ (Homeomorph.ulift.symm) (strictTransform n P₀ W₀) B₀ hNC
    exact hh
  exact ⟨hMaps.1,hMaps.2.1,hMaps.2.2,hImage',hGood',hSmooth',hRegular',hSing',hB,hBne,hSupp₁,hSupp₂,hNC'⟩

theorem exists_arbitrary_universe_pure_geometry_with_atlas {n d : ℕ} (X : CMfd.{u} n) {ι : Type w}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Y : CMfd.{u} n) (P : Y → X) (ρ : Type) (B : ρ → Set Y),
      HironakaG3RTowerClass.IsGluedFrom (fun _ _ _ => True) Y P ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P '' strictTransform n P W = W ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      (⋃ a, B a) = P ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  let ex := shrinkDiffeomorph X
  obtain ⟨κ,D₀,_hD₀,_hD₀ne,hD₀supp,Y₀,P₀,ρ,B₀,hAtlas,hSmall⟩ :=
    exists_small_model_pure_resolution X W hW hPure D hD
  have hGeo := conjugate_pure_endpoint_from_small_model (d := d) X W D D₀ hD₀supp P₀ B₀ hSmall
  exact ⟨liftCMfd.{u} Y₀,ex.symm ∘ P₀ ∘ (liftDiffeomorph.{u} Y₀).symm,ρ,
    (fun i => (liftDiffeomorph.{u} Y₀).symm ⁻¹' B₀ i),
    G3UniverseLiftedAtlas.lifted_universal_atlas ex hAtlas,hGeo⟩

theorem exists_arbitrary_universe_pure_geometry {n d : ℕ} (X : CMfd.{u} n) {ι : Type w}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Y : CMfd.{u} n) (P : Y → X) (ρ : Type) (B : ρ → Set Y),
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P '' strictTransform n P W = W ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      (⋃ a, B a) = P ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  obtain ⟨Y,P,ρ,B,_,hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB,hBne,hSupp,hSupp',hNC⟩ :=
    exists_arbitrary_universe_pure_geometry_with_atlas X W hW hPure D hD
  exact ⟨Y,P,ρ,B,hP,hProper,hSurj,hImage,hGood,hSmooth,hRegular,hSing,hB,hBne,hSupp,hSupp',hNC⟩
end
end Hironaka.HironakaG3UniverseArbitraryGeometricEndpoint

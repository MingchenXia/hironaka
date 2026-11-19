import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision
import Hironaka.Resolution.HironakaActualFreeProductFlattening
import Hironaka.Resolution.HironakaActualInheritedSmoothCentrePowers
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! Compatible ACTUAL charts for prescribed moving centres. The geometric
free-product change is conjugated back to the ORIGINAL coordinate indices;
historical labels and selectors are not replaced by a new monic family. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalMovingCentreChart
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
 HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
 HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
 HironakaActualFixedInheritedSelector HironakaActualFixedInheritedSelectorPermutation
 HironakaActualInheritedEssentialPriority HironakaActualFreeProductFlattening
 HironakaActualFreeProductGermTransport HironakaActualZeroSectionCentreGeometry
 HironakaActualAnalyticBlockGraphTranslation HironakaHolomorphicJetChartInvariance
 HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalMovingSelectedContact
 HironakaActualInheritedSmoothCentrePowers HironakaSmoothCentreCoherentDomain
 HironakaActualFreePlaneRegularity
 HironakaActualInheritedAnalyticBlockJacobian
 HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
 HironakaActualInheritedNeighborhoodMarkedHS HironakaActualHistoricalWholeJetFrames
 HironakaActualHistoricalPrefixJetFrames HironakaActualHistoricalFormalSupportedDivision
 HironakaActualCanonicalBlockJacobian HironakaActualAnalyticFormalNormalPowers
 HironakaActualCauchyMonomialDivision HironakaActualCauchyCoordinateDivision
 HolomorphicTaylorTail GermIdealOrder InvertibleIdealQuotient
 HironakaHolomorphicJetRankLoci HironakaRelativeNormalTaylorCoefficients
 HironakaRelativeNormalDeformationInitialRelations OrderTaylor IdealWeightPowers
 HironakaSmoothCentreNearbyStalks HironakaActualAnalyticBlowupTaylor
 MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen

variable {n : ℕ}

/-- Both source and target are transported by genuine global linear
equivalences, retaining the exact whole forward/inverse functions. -/
def linearChart (L R : ComplexModel n ≃L[ℂ] ComplexModel n)
    (Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) :
    LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n) where
  source:=L ⁻¹' Ψ.source
  target:=R ⁻¹' Ψ.target
  isOpen_source:=Ψ.isOpen_source.preimage L.continuous
  isOpen_target:=Ψ.isOpen_target.preimage R.continuous
  center_mem_source:=by simpa only [mem_preimage,map_zero] using Ψ.center_mem_source
  toFun:=R.symm ∘ Ψ.toFun ∘ L
  invFun:=L.symm ∘ Ψ.invFun ∘ R
  toFun_holomorphic:=R.symm.differentiable.comp_differentiableOn
    (Ψ.toFun_holomorphic.comp L.differentiable.differentiableOn (fun _ hz=>hz))
  invFun_holomorphic:=L.symm.differentiable.comp_differentiableOn
    (Ψ.invFun_holomorphic.comp R.differentiable.differentiableOn (fun _ hz=>hz))
  mapsTo_toFun:=by
    intro z hz
    change R (R.symm (Ψ.toFun (L z)))∈Ψ.target
    rw [R.apply_symm_apply]
    exact Ψ.mapsTo_toFun hz
  mapsTo_invFun:=by
    intro z hz
    change L (L.symm (Ψ.invFun (R z)))∈Ψ.source
    rw [L.apply_symm_apply]
    exact Ψ.mapsTo_invFun hz
  left_inv:=by
    intro z hz
    change L.symm (Ψ.invFun (R (R.symm (Ψ.toFun (L z)))))=z
    rw [R.apply_symm_apply,Ψ.left_inv (L z) hz,L.symm_apply_apply]
  right_inv:=by
    intro z hz
    change R.symm (Ψ.toFun (L (L.symm (Ψ.invFun (R z)))))=z
    rw [L.apply_symm_apply,Ψ.right_inv (R z) hz,R.symm_apply_apply]

theorem linearChart_zero (L R : ComplexModel n ≃L[ℂ] ComplexModel n)
    (Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0) :
    (linearChart L R Ψ).toFun 0=0 := by
  change R.symm (Ψ.toFun (L 0))=0
  rw [map_zero,hΨ0,map_zero]

private theorem model_regular_iff (r k : ℕ) (C : Set (ComplexModel r)) :
    RegularAtDim (n:=r) C 0 k ↔ k≤r ∧ (0 : ComplexModel r)∈C ∧
      ∃Φ : LocalHolomorphicEquivAt (n:=r) (0 : ComplexModel r),
        Φ.toFun 0=0 ∧ ∀{z},z∈Φ.source → (z∈C ↔ Φ.toFun z∈complexCoordinatePlane r k) := by
  simp [RegularAtDim,complexChartAt,chartAt_self_eq]
  intro _ _
  rfl

theorem regular_linear_preimage (L : ComplexModel n ≃L[ℂ] ComplexModel n)
    (C : Set (ComplexModel n)) (k : ℕ) (hreg : RegularAtDim (n:=n) C 0 k) :
    RegularAtDim (n:=n) (L ⁻¹' C) 0 k := by
  obtain ⟨hkn,h0C,Ψ,hΨ0,hFlat⟩:=(model_regular_iff n k C).mp hreg
  apply (model_regular_iff n k (L ⁻¹' C)).mpr
  refine ⟨hkn,?_,linearChart L (ContinuousLinearEquiv.refl ℂ (ComplexModel n)) Ψ,?_,?_⟩
  · simpa only [mem_preimage,map_zero] using h0C
  · exact linearChart_zero L _ Ψ hΨ0
  · intro z hz
    exact hFlat hz

private theorem regular_inter_open {k : ℕ} {C U : Set (ComplexModel n)}
    (hreg : RegularAtDim (n:=n) C 0 k) (hU : IsOpen U) (h0U : (0 : ComplexModel n)∈U) :
    RegularAtDim (n:=n) (C∩U) 0 k := by
  obtain ⟨hkn,h0C,Ψ,hΨ0,hFlat⟩:=(model_regular_iff n k C).mp hreg
  apply (model_regular_iff n k (C∩U)).mpr
  refine ⟨hkn,⟨h0C,h0U⟩,Ψ.restrict U hU 0 ⟨Ψ.center_mem_source,h0U⟩,hΨ0,?_⟩
  intro z hz
  change z∈Ψ.source∩U at hz
  exact ⟨fun h=>(hFlat hz.1).mp h.1,fun h=>⟨(hFlat hz.1).mpr h,hz.2⟩⟩

/-- Actual regularity inside the genuine free plane DERIVES the centre
dimension bound; no free-codimension premise is supplied. -/
theorem centre_dim_le_free (m e k : ℕ) (C : Set (ComplexModel (m+e)))
    (hreg : RegularAtDim (n:=m+e) C 0 k)
    (hPlane : ∀ᶠz in 𝓝 (0 : ComplexModel (m+e)),z∈C → z∈complexCoordinatePlane (m+e) m) :
    k≤m := by
  obtain ⟨U,hUsub,hU,h0U⟩:=mem_nhds_iff.mp hPlane
  let C₀:=C∩U
  let D:=(tangentInclusion m e) ⁻¹' C₀
  have hC₀plane : C₀⊆complexCoordinatePlane (m+e) m:=fun z hz=>hUsub hz.2 hz.1
  have hImage : (tangentInclusion m e) '' D=C₀ := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact hz
    · intro z hz
      refine ⟨tangentProjection m e z,?_,tangentInclusion_projection_eq_of_mem_plane m e (hC₀plane hz)⟩
      change tangentInclusion m e (tangentProjection m e z)∈C₀
      rw [tangentInclusion_projection_eq_of_mem_plane m e (hC₀plane hz)]
      exact hz
  have hRegC₀ : RegularAtDim (n:=m+e) C₀ 0 k:=regular_inter_open hreg hU h0U
  have hRegImage : RegularAtDim (n:=m+e) ((tangentInclusion m e) '' D) 0 k:=hImage.symm ▸ hRegC₀
  exact ((model_regular_iff m k D).mp (regularAtDim_zeroSection_reflects hRegImage)).1

/-- A sparse actual coordinate plane, retaining ORIGINAL variable indices. -/
def coordinateSubsetPlane (A : Set (Fin n)) : Set (ComplexModel n) :=
  {z | ∀i∈A,z i=0}

theorem actualPermutationLinearEquiv_symm_apply (p : Fin n ≃ Fin n)
    (z : ComplexModel n) (i : Fin n) : (actualPermutationLinearEquiv p).symm z i=z (p.symm i) := by
  have h:=congrArg (fun w : ComplexModel n=>w (p.symm i))
    ((actualPermutationLinearEquiv p).apply_symm_apply z)
  simpa only [actualPermutationLinearEquiv_apply,p.apply_symm_apply] using h

theorem permutation_inverse_projection (p : Fin n ≃ Fin n) (B : Set (Fin n)) (z : ComplexModel n) :
    (actualPermutationLinearEquiv p).symm (actualBlockCoordinateProjection B z)=
      actualBlockCoordinateProjection (p '' B) ((actualPermutationLinearEquiv p).symm z) := by
  ext i
  rw [actualPermutationLinearEquiv_symm_apply,actualBlockCoordinateProjection_apply,
    actualBlockCoordinateProjection_apply,actualPermutationLinearEquiv_symm_apply]
  have hMem : p.symm i∈B ↔ i∈p '' B:=by
    constructor
    · intro h
      exact ⟨p.symm i,h,p.apply_symm_apply i⟩
    · rintro ⟨j,hj,hji⟩
      simpa only [←hji,p.symm_apply_apply] using hj
  rw [hMem]

theorem coordinateSubsetPlane_permutation (p : Fin n ≃ Fin n) (k : ℕ) (z : ComplexModel n) :
    (actualPermutationLinearEquiv p).symm z∈complexCoordinatePlane n k ↔
      z∈coordinateSubsetPlane {i : Fin n | k≤(p i).val} := by
  constructor
  · intro h i hi
    have hz:=h (p i) hi
    simpa only [actualPermutationLinearEquiv_symm_apply,p.symm_apply_apply] using hz
  · intro h i hi
    rw [actualPermutationLinearEquiv_symm_apply]
    exact h (p.symm i) (by
      change k≤(p (p.symm i)).val
      simpa only [p.apply_symm_apply] using hi)

theorem actualFreeProduct_invFun_section (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (z : ComplexModel (m+e)) :
    (actual_zeroSection_localEquiv m e 0 χ).invFun
      (actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z)=
        actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z := by
  have hProjection : tangentProjection m e
      (actualBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} z)=0 := by
    ext i
    rw [tangentProjection_apply,actualBlockCoordinateProjection_apply]
    simp only [mem_ofPred_eq,Fin.val_castAdd,not_le.mpr i.isLt,if_false,PiLp.zero_apply]
  rw [actualFreeProduct_invFun_eq,hProjection,local_invFun_zero χ hχ0,map_zero,sub_zero,zero_add]

/-- The WHOLE fixed-section germ law is derived from the actual inverse
function on that section, not supplied as presentation data. -/
theorem actual_inverse_chart_fixed_section
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0)
    (B : Set (Fin n))
    (hInv : ∀z,Φ.invFun (actualBlockCoordinateProjection B z)=actualBlockCoordinateProjection B z) :
    ∀F,actualBlockProjectionGermHom B ((localGermAlgEquiv Φ hΦ0).symm F)=actualBlockProjectionGermHom B F := by
  intro F
  induction F using HolGerm.induction_on with
  | h f hf =>
      let hInvHol : HolAt (f ∘ Φ.invFun) 0:=holomorphic_comp Φ.invFun
        (local_invFun_holomorphic Φ hΦ0) (local_invFun_zero Φ hΦ0) hf
      change actualBlockProjectionGermHom B (HolGerm.mk (f ∘ Φ.invFun) hInvHol)=
        actualBlockProjectionGermHom B (HolGerm.mk f hf)
      unfold actualBlockProjectionGermHom
      rw [compAlgHom_mk,compAlgHom_mk]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z=>congrArg f (hInv z)

theorem actualFreeProduct_coordinate_pair (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) (i : Fin (m+e)) (hi : m ≤ i.val) :
    (actual_zeroSection_localEquiv m e 0 χ).toFun z i=z i ∧
      (actual_zeroSection_localEquiv m e 0 χ).invFun z i=z i := by
  let j : Fin e:=⟨i.val-m,by omega⟩
  have hji : j.natAdd m=i:=Fin.ext (by dsimp [j];omega)
  rw [←hji]
  exact ⟨actualFreeProduct_toFun_essentialCoordinate m e χ z j,
    actualFreeProduct_invFun_essentialCoordinate m e χ z j⟩

/-- Actual smooth-centre geometry produces a real free chart, conjugated
back to ORIGINAL indices. Its entire essential coordinates/section are
fixed and the SAME centre is flattened to a genuine coordinate-subset
plane containing those essential directions. The dimension bound is
derived internally; no compatible chart or target presentation is input. -/
theorem exists_actual_original_index_free_centre_chart (m e k : ℕ)
    (B : Set (Fin (m+e))) (p : Fin (m+e) ≃ Fin (m+e))
    (hImage : p '' B={i : Fin (m+e) | m ≤ i.val})
    (C : Set (ComplexModel (m+e))) (hreg : RegularAtDim (n:=m+e) C 0 k)
    (hPlane : ∀ᶠz in 𝓝 (0 : ComplexModel (m+e)),z∈C → z∈coordinateSubsetPlane B) :
    ∃(χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m))(_hχ0 : χ.toFun 0=0),
    ∃(Ψ : LocalHolomorphicEquivAt (n:=m+e) (0 : ComplexModel (m+e)))(_hΨ0 : Ψ.toFun 0=0),
      Ψ.toFun=(actual_zeroSection_localEquiv m e 0 χ).toFun ∧
      Ψ.invFun=(actual_zeroSection_localEquiv m e 0 χ).invFun ∧
    ∃(Φ : LocalHolomorphicEquivAt (n:=m+e) (0 : ComplexModel (m+e)))(hΦ0 : Φ.toFun 0=0),
      Φ=linearChart (actualPermutationLinearEquiv p).symm (actualPermutationLinearEquiv p).symm Ψ ∧
      k≤m ∧ B⊆{i : Fin (m+e) | k≤(p i).val} ∧
      (∀z∈Φ.source,z∈C ↔ Φ.toFun z∈coordinateSubsetPlane {i : Fin (m+e) | k≤(p i).val}) ∧
      (∀z : ComplexModel (m+e),∀i∈B,Φ.toFun z i=z i ∧ Φ.invFun z i=z i) ∧
      (∀z,Φ.invFun (actualBlockCoordinateProjection B z)=actualBlockCoordinateProjection B z) ∧
      ∀F,actualBlockProjectionGermHom B ((localGermAlgEquiv Φ hΦ0).symm F)=actualBlockProjectionGermHom B F := by
  let R:=actualPermutationLinearEquiv p
  let CP:=R ⁻¹' C
  have hRegP : RegularAtDim (n:=m+e) CP 0 k:=regular_linear_preimage R C k hreg
  have hRT : Tendsto R (𝓝 (0 : ComplexModel (m+e))) (𝓝 0):=by
    simpa only [map_zero] using R.continuous.tendsto (0 : ComplexModel (m+e))
  have hPlaneP : ∀ᶠz in 𝓝 (0 : ComplexModel (m+e)),z∈CP → z∈complexCoordinatePlane (m+e) m := by
    filter_upwards [hRT.eventually hPlane] with z hz hzC
    intro i hi
    have hiImage : i∈p '' B:=hImage.symm ▸ hi
    obtain ⟨j,hj,hji⟩:=hiImage
    have hZero:=hz hzC j hj
    change (R z) j=0 at hZero
    rw [actualPermutationLinearEquiv_apply,hji] at hZero
    exact hZero
  have hkm:=centre_dim_le_free m e k CP hRegP hPlaneP
  obtain ⟨χ,hχ0,Ψ,hΨ0,hTo,hInv,_hSrc,hFlat,_hFix,_hFixInv⟩:=
    exists_actual_same_centre_free_product_flattening m e k CP hRegP hPlaneP
  let Φ:=linearChart R.symm R.symm Ψ
  have hΦ0 : Φ.toFun 0=0:=linearChart_zero R.symm R.symm Ψ hΨ0
  have hFixedSection (z : ComplexModel (m+e)) : Φ.invFun (actualBlockCoordinateProjection B z)=
      actualBlockCoordinateProjection B z := by
    change R (Ψ.invFun (R.symm (actualBlockCoordinateProjection B z)))=actualBlockCoordinateProjection B z
    rw [permutation_inverse_projection,hImage,hInv,actualFreeProduct_invFun_section m e χ hχ0]
    rw [←hImage,←permutation_inverse_projection,R.apply_symm_apply]
  refine ⟨χ,hχ0,Ψ,hΨ0,hTo,hInv,Φ,hΦ0,rfl,hkm,?_,?_,?_,hFixedSection,
    actual_inverse_chart_fixed_section Φ hΦ0 B hFixedSection⟩
  · intro i hi
    have hpi : p i∈{j : Fin (m+e) | m ≤ j.val}:=hImage ▸ (show p i∈p '' B from ⟨i,hi,rfl⟩)
    exact hkm.trans hpi
  · intro z hz
    have hPriorFlat : z∈C ↔ Ψ.toFun (R.symm z)∈complexCoordinatePlane (m+e) k := by
      have h:=hFlat (R.symm z) hz
      change (R (R.symm z)∈C ↔ Ψ.toFun (R.symm z)∈complexCoordinatePlane (m+e) k) at h
      simpa only [R.apply_symm_apply] using h
    have hCoordinate:=coordinateSubsetPlane_permutation p k (Φ.toFun z)
    have hComposite : R.symm (Φ.toFun z)=Ψ.toFun (R.symm z) := by
      change R.symm (R (Ψ.toFun (R.symm z)))=Ψ.toFun (R.symm z)
      exact R.symm_apply_apply _
    rw [hComposite] at hCoordinate
    exact hPriorFlat.trans hCoordinate
  · intro z i hi
    have hpi : m ≤ (p i).val:=
      (congrArg (fun D : Set (Fin (m+e))=>p i∈D) hImage).mp ⟨i,hi,rfl⟩
    constructor
    · change R (Ψ.toFun (R.symm z)) i=z i
      rw [actualPermutationLinearEquiv_apply,hTo,(actualFreeProduct_coordinate_pair m e χ (R.symm z) (p i) hpi).1,
        actualPermutationLinearEquiv_symm_apply,p.symm_apply_apply]
    · change R (Ψ.invFun (R.symm z)) i=z i
      rw [actualPermutationLinearEquiv_apply,hInv,(actualFreeProduct_coordinate_pair m e χ (R.symm z) (p i) hpi).2,
        actualPermutationLinearEquiv_symm_apply,p.symm_apply_apply]

/-- The actual induced germ map is the literal permutation/product/inverse
permutation composition. The permutations are INTERNAL chart geometry;
no family, word or selector is renamed in the conclusion. -/
theorem actual_conjugate_free_chart_germ (m e : ℕ) (p : Fin (m+e) ≃ Fin (m+e))
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (Ψ : LocalHolomorphicEquivAt (n:=m+e) (0 : ComplexModel (m+e))) (hΨ0 : Ψ.toFun 0=0)
    (hInv : Ψ.invFun=(actual_zeroSection_localEquiv m e 0 χ).invFun) :
    let R:=actualPermutationLinearEquiv p
    let Φ:=linearChart R.symm R.symm Ψ
    let hΦ0:=linearChart_zero R.symm R.symm Ψ hΨ0
    (localGermAlgEquiv Φ hΦ0).symm=
      ((actualPermutationGermEquiv p).trans (actualFreeProductGermEquiv m e χ hχ0)).trans
        (actualPermutationGermEquiv p).symm := by
  dsimp only
  apply AlgEquiv.ext
  intro F
  induction F using HolGerm.induction_on with
  | h f hf =>
      let R:=actualPermutationLinearEquiv p
      have hRf : HolAt (f ∘ R) 0:=holomorphic_comp R
        (Eventually.of_forall fun _=>R.differentiableAt) (map_zero R) hf
      have hMid : HolAt ((f ∘ R) ∘ Ψ.invFun) 0:=holomorphic_comp Ψ.invFun
        (local_invFun_holomorphic Ψ hΨ0) (local_invFun_zero Ψ hΨ0) hRf
      have hMidR : HolAt ((f ∘ R) ∘ (actual_zeroSection_localEquiv m e 0 χ).invFun) 0:=by
        rw [←hInv]
        exact hMid
      have hLeft : HolAt (((f ∘ R) ∘ Ψ.invFun) ∘ R.symm) 0:=holomorphic_comp R.symm
        (Eventually.of_forall fun _=>R.symm.differentiableAt) (map_zero R.symm) hMid
      have hRight : HolAt (((f ∘ R) ∘ (actual_zeroSection_localEquiv m e 0 χ).invFun) ∘ R.symm) 0:=
        holomorphic_comp R.symm (Eventually.of_forall fun _=>R.symm.differentiableAt) (map_zero R.symm) hMidR
      change HolGerm.mk (fun z=>f (actualPermutationLinearEquiv p
          (Ψ.invFun ((actualPermutationLinearEquiv p).symm z)))) hLeft=
        HolGerm.mk (fun z=>f (actualPermutationLinearEquiv p
          ((actual_zeroSection_localEquiv m e 0 χ).invFun ((actualPermutationLinearEquiv p).symm z)))) hRight
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z=>congrArg (fun w=>f (actualPermutationLinearEquiv p w))
        (congrFun hInv ((actualPermutationLinearEquiv p).symm z))

/-- Whole essential multi-derivatives commute with the SAME conjugated
actual product map in the ORIGINAL indices, including arbitrary orders. -/
theorem actual_conjugate_free_product_multiDerivative (m e : ℕ)
    (p : Fin (m+e) ≃ Fin (m+e)) (B : Set (Fin (m+e)))
    (hImage : p '' B={i : Fin (m+e) | m ≤ i.val})
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (β : Fin (m+e) →₀ ℕ) (hβ : ∀i,i∉B → β i=0) (F : HolGerm (ComplexModel (m+e))) :
    let E:=((actualPermutationGermEquiv p).trans (actualFreeProductGermEquiv m e χ hχ0)).trans
      (actualPermutationGermEquiv p).symm
    actualAnalyticMultiDerivative β (E F)=E (actualAnalyticMultiDerivative β F) := by
  let P:=actualPermutationGermEquiv p
  let A:=actualFreeProductGermEquiv m e χ hχ0
  let βp:=Finsupp.domCongr p β
  have hPure (i : Fin (m+e)) (hi : ¬ m ≤ i.val) : βp i=0 := by
    change Finsupp.domCongr p β i=0
    simp only [Finsupp.domCongr_apply,Finsupp.equivMapDomain_eq_mapDomain,Finsupp.mapDomain_equiv_apply]
    apply hβ
    intro hB
    have hTail : i∈{j : Fin (m+e) | m ≤ j.val}:=hImage ▸
      (show i∈p '' B from ⟨p.symm i,hB,p.apply_symm_apply i⟩)
    exact hi hTail
  have hBack (H : HolGerm (ComplexModel (m+e))) :
      actualAnalyticMultiDerivative β (P.symm H)=P.symm (actualAnalyticMultiDerivative βp H) := by
    apply P.injective
    rw [P.apply_symm_apply]
    have h:=actualAnalyticMultiDerivative_permutation p β (P.symm H)
    change actualAnalyticMultiDerivative βp (P (P.symm H))=P (actualAnalyticMultiDerivative β (P.symm H)) at h
    rw [P.apply_symm_apply] at h
    exact h.symm
  change actualAnalyticMultiDerivative β (P.symm (A (P F)))=P.symm (A (P (actualAnalyticMultiDerivative β F)))
  rw [hBack,actualFreeProductGermEquiv_multiDerivative m e χ hχ0 βp hPure,
    actualAnalyticMultiDerivative_permutation p β F]

/-- OUTPUT geometry for the SAME centre, in the ORIGINAL variable labels.
The literal split functions are retained for subsequent history composition;
the section/derivative laws are produced from those actual functions. -/
structure ActualCompatibleMovingCentreChart (B : Set (Fin n))
    (C : Set (ComplexModel n)) (k : ℕ) where
  freeDimension : ℕ
  essentialDimension : ℕ
  dimension : freeDimension+essentialDimension=n
  priorityPermutation : Fin n ≃ Fin (freeDimension+essentialDimension)
  priorityLinear : ComplexModel n ≃L[ℂ] ComplexModel (freeDimension+essentialDimension)
  priorityCoordinates : ∀z i,priorityLinear z (priorityPermutation i)=z i
  essentialImage : priorityPermutation '' B={i : Fin (freeDimension+essentialDimension) | freeDimension ≤ i.val}
  freeChart : LocalHolomorphicEquivAt (n:=freeDimension) (0 : ComplexModel freeDimension)
  freeChart_zero : freeChart.toFun 0=0
  chart : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)
  chart_zero : chart.toFun 0=0
  forwardProduct : chart.toFun=priorityLinear.symm ∘
    (actual_zeroSection_localEquiv freeDimension essentialDimension 0 freeChart).toFun ∘ priorityLinear
  inverseProduct : chart.invFun=priorityLinear.symm ∘
    (actual_zeroSection_localEquiv freeDimension essentialDimension 0 freeChart).invFun ∘ priorityLinear
  centreDimensionBound : k≤freeDimension
  normalContains : B⊆{i : Fin n | k≤(priorityPermutation i).val}
  centre : ∀z∈chart.source,z∈C ↔ chart.toFun z∈coordinateSubsetPlane
    {i : Fin n | k≤(priorityPermutation i).val}
  essentialCoordinates : ∀z,∀i∈B,chart.toFun z i=z i ∧ chart.invFun z i=z i
  fixedSection : ∀F,actualBlockProjectionGermHom B ((localGermAlgEquiv chart chart_zero).symm F)=
    actualBlockProjectionGermHom B F
  derivative : ∀β : Fin n →₀ ℕ,(∀i,i∉B → β i=0) → ∀F,
    actualAnalyticMultiDerivative β ((localGermAlgEquiv chart chart_zero).symm F)=
      (localGermAlgEquiv chart chart_zero).symm (actualAnalyticMultiDerivative β F)

private theorem compatible_chart_of_dimension {m e k : ℕ} (hdim : m+e=n)
    (B : Set (Fin n)) (p : Fin n ≃ Fin n) (hImage : p '' B={i : Fin n | m ≤ i.val})
    (C : Set (ComplexModel n)) (hreg : RegularAtDim (n:=n) C 0 k)
    (hPlane : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈C → z∈coordinateSubsetPlane B) :
    Nonempty (ActualCompatibleMovingCentreChart B C k) := by
  subst n
  obtain ⟨χ,hχ0,Ψ,hΨ0,hTo,hInv,Φ,hΦ0,hChart,hkm,hContains,hCentre,hCoordinates,_hSectionInv,hSection⟩:=
    exists_actual_original_index_free_centre_chart m e k B p hImage C hreg hPlane
  subst Φ
  let R:=actualPermutationLinearEquiv p
  refine ⟨{
    freeDimension:=m
    essentialDimension:=e
    dimension:=rfl
    priorityPermutation:=p
    priorityLinear:=R.symm
    priorityCoordinates:=?_
    essentialImage:=hImage
    freeChart:=χ
    freeChart_zero:=hχ0
    chart:=linearChart R.symm R.symm Ψ
    chart_zero:=hΦ0
    forwardProduct:=?_
    inverseProduct:=?_
    centreDimensionBound:=hkm
    normalContains:=hContains
    centre:=hCentre
    essentialCoordinates:=hCoordinates
    fixedSection:=hSection
    derivative:=?_ }⟩
  · intro z i
    rw [actualPermutationLinearEquiv_symm_apply,p.symm_apply_apply]
  · funext z
    change R (Ψ.toFun (R.symm z))=R ((actual_zeroSection_localEquiv m e 0 χ).toFun (R.symm z))
    rw [hTo]
  · funext z
    change R (Ψ.invFun (R.symm z))=R ((actual_zeroSection_localEquiv m e 0 χ).invFun (R.symm z))
    rw [hInv]
  · intro β hβ F
    have hConj:=actual_conjugate_free_chart_germ m e p χ hχ0 Ψ hΨ0 hInv
    change (localGermAlgEquiv (linearChart R.symm R.symm Ψ) hΦ0).symm=
      ((actualPermutationGermEquiv p).trans (actualFreeProductGermEquiv m e χ hχ0)).trans
        (actualPermutationGermEquiv p).symm at hConj
    rw [hConj]
    exact actual_conjugate_free_product_multiDerivative m e p B hImage χ hχ0 β hβ F

/-- A genuine regular centre locally in the historical essential-zero plane
internally produces its compatible free chart in ORIGINAL indices. The
actual dimension split and priority permutation are chosen here. No centre
dimension bound, compatible chart, derivative/section or history certificate
is a premise. -/
theorem exists_actual_compatible_moving_centre_chart
    (B : Set (Fin n)) (C : Set (ComplexModel n)) (k : ℕ)
    (hreg : RegularAtDim (n:=n) C 0 k)
    (hPlane : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈C → z∈coordinateSubsetPlane B) :
    Nonempty (ActualCompatibleMovingCentreChart B C k) := by
  let m:=Fintype.card (↥(Bᶜ))
  let e:=Fintype.card B
  have hdim : m+e=n := by
    simpa only [m,e,Fintype.card_sum,Fintype.card_fin] using
      Fintype.card_congr ((Equiv.sumComm (↥(Bᶜ)) B).trans (Equiv.Set.sumCompl B))
  exact compatible_chart_of_dimension hdim B (essentialFreeFirstEquiv B)
    (essentialFreeFirstEquiv_block_image B) C hreg hPlane

/-- The ACTUAL full native weighted record forces each individual member's
ordinary mark at EVERY nearby point of its given centre. The entire given
boundary is retained; no member-order or centre-power law is supplied. -/
theorem actual_native_weighted_centre_orders
    {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀a,0<w a)
    (F : ι → ComplexModel n → ℂ) (U : TopologicalSpace.Opens (ComplexModel n))
    (hF : ∀a,DifferentiableOn ℂ (F a) U) (E : List (Set U))
    (C : Set (ComplexModel n))
    (hC : ∀z : U,(z : ComplexModel n)∈C →
      z∈(⟨univ,E,weightedFunctionIdeal w (fun a (q : U)=>F a q),weightedCommonMark w⟩ : MarkedIdeal n U).cosupp) :
    ∀p (hp : p∈U),p∈C → ∀a,
      translatedGerm p (F a) (holAt_of_differentiableOn U.isOpen (hF a) hp)∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w a := by
  have hNative (a : ι) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun z : U=>F a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen
      (mdifferentiableOn_iff_differentiableOn.mpr (hF a)) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  intro p hp hpC a
  let z : U:=⟨p,hp⟩
  have hz:=hC z hpC
  change z∈cosupport n univ (weightedFunctionIdeal w (fun i (q : U)=>F i q)) (weightedCommonMark w) at hz
  have hAll : z∈⋂i,cosupport n univ (finiteFunctionIdeal (fun _ : Unit=>(fun q : U=>F i q))) (w i):=
    (congrArg (fun D : Set U=>z∈D) (cosupport_weightedFunctionIdeal w hw (fun i (q : U)=>F i q) hNative)).mp hz
  have hv:=(mem_cosupport_finiteFunctionIdeal_iff
    (fun _ : Unit=>(fun q : U=>F a q)) z (w a)
    (fun _=>Eventually.of_forall fun q=>hNative a q)).mp (mem_iInter.mp hAll a) ()
  have hExt:=mem_idealPow_pointIdeal_extendOpens U (w a) (mem_idealPow_of_vanishesToOrderOn_univ hv)
  have hAmbient : (idealPow (pointIdeal n p) (w a)).mem p (F a) := by
    apply mem_idealPow_congr hExt
    filter_upwards [U.isOpen.mem_nhds hp] with q hq
    change extendOpens U (fun q : U=>F a q) (⟨q,hq⟩ : U).val=F a q
    rw [extendOpens_val]
  exact (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal p (F a)
    (holAt_of_differentiableOn U.isOpen (hF a) hp) (w a)).mpr hAmbient

/-- Individual orders derived from the SAME full native cosupport give
the actual WHOLE original smooth-centre powers of the SAME members. -/
theorem actual_native_weighted_smooth_centre_powers
    {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀a,0<w a)
    (Γ : ι → HolGerm (ComplexModel n)) (F : ι → ComplexModel n → ℂ)
    (U : TopologicalSpace.Opens (ComplexModel n)) (h0U : (0 : ComplexModel n)∈U)
    (hF : ∀a,DifferentiableOn ℂ (F a) U)
    (hRep : ∀a,HolGerm.mk (F a) (holAt_of_differentiableOn U.isOpen (hF a) h0U)=Γ a)
    (E : List (Set U)) (C : Set (ComplexModel n)) (k : ℕ)
    (hreg : RegularAtDim (n:=n) C 0 k)
    (hC : ∀z : U,(z : ComplexModel n)∈C →
      z∈(⟨univ,E,weightedFunctionIdeal w (fun a (q : U)=>F a q),weightedCommonMark w⟩ : MarkedIdeal n U).cosupp) :
    ∀a,Γ a∈originalCoherentOriginIdeal (vanishingIdeal (n:=n) C)^w a := by
  obtain ⟨hkn,_h0C,Φ,hΦ0,hFlat⟩:=(model_regular_iff n k C).mp hreg
  obtain ⟨t,ht⟩:=Nat.exists_eq_add_of_le hkn
  subst n
  have hsrc : Φ.source⊆(chartAt (ComplexModel (k+t)) (0 : ComplexModel (k+t))).target:=by
    simp [chartAt_self_eq]
  have hflat : ∀{y : ComplexModel (k+t)},y∈(chartAt (ComplexModel (k+t)) 0).source →
      chartAt (ComplexModel (k+t)) 0 y∈Φ.source →
      (y∈C ↔ Φ.toFun (chartAt (ComplexModel (k+t)) 0 y)∈complexCoordinatePlane (k+t) k) := by
    intro y _hy hys
    simpa [chartAt_self_eq] using hFlat (by simpa [chartAt_self_eq] using hys)
  intro a
  rw [←hRep a]
  exact (actual_member_mem_smooth_centre_power_in_flattening k t (w a) C (F a) U
    U.isOpen h0U (fun p hp=>holAt_of_differentiableOn U.isOpen (hF a) hp)
    (fun p hp hpC=>actual_native_weighted_centre_orders w hw F U hF E C hC p hp hpC a)
    Φ hsrc (by simpa [chartAt_self_eq] using hΦ0) hflat).2

private theorem nearby_zero_eq_local
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0)
    (h0T : (0 : ComplexModel n)∈Φ.target) :
    actualNearbyGermEquiv Φ 0 h0T=localGermAlgEquiv Φ hΦ0 := by
  apply AlgEquiv.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualNearbyGermEquiv
    rw [localGermAlgEquiv_mk,localGermAlgEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>by
      change f (Φ.toFun (z+Φ.invFun 0)-0)=f (Φ.toFun z)
      rw [local_invFun_zero Φ hΦ0,add_zero,sub_zero]

private theorem standard_chart_inverse_germ
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0)
    (p : Fin n ≃ Fin n) :
    let R:=actualPermutationLinearEquiv p
    let Ω:=linearChart (ContinuousLinearEquiv.refl ℂ (ComplexModel n)) R Φ
    let hΩ0:=linearChart_zero (ContinuousLinearEquiv.refl ℂ (ComplexModel n)) R Φ hΦ0
    (localGermAlgEquiv Ω hΩ0).symm=
      (localGermAlgEquiv Φ hΦ0).symm.trans (actualPermutationGermEquiv p) := by
  dsimp only
  apply AlgEquiv.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
    have hComp : HolAt (fun z=>f (Φ.invFun (actualPermutationLinearEquiv p z))) 0:=
      holomorphic_comp (actualPermutationLinearEquiv p)
        (Eventually.of_forall fun _=>(actualPermutationLinearEquiv p).differentiableAt)
        (map_zero _) (holomorphic_comp Φ.invFun (local_invFun_holomorphic Φ hΦ0)
          (local_invFun_zero Φ hΦ0) hf)
    change HolGerm.mk (fun z=>f (Φ.invFun (actualPermutationLinearEquiv p z))) hComp=
      HolGerm.mk (fun z=>f (Φ.invFun (actualPermutationLinearEquiv p z))) hComp
    rfl

/-- The ACTUAL given compatible chart, in ORIGINAL variable indices,
retains the genuine coordinate-centre power derived from nearby orders.
No separate coordinate-power or arbitrary-chart compatibility is assumed. -/
theorem actual_member_mem_coordinate_power_in_same_chart (k t μ : ℕ)
    (p : Fin (k+t) ≃ Fin (k+t)) (C : Set (ComplexModel (k+t)))
    (f : ComplexModel (k+t) → ℂ) (U : Set (ComplexModel (k+t)))
    (hU : IsOpen U) (h0U : (0 : ComplexModel (k+t))∈U)
    (hhol : ∀z∈U,HolAt f z)
    (hOrders : ∀z (hz : z∈U),z∈C → translatedGerm z f (hhol z hz)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (k+t)))^μ)
    (Φ : LocalHolomorphicEquivAt (n:=k+t) (0 : ComplexModel (k+t))) (hΦ0 : Φ.toFun 0=0)
    (hFlat : ∀z∈Φ.source,z∈C ↔ Φ.toFun z∈coordinateSubsetPlane
      {i : Fin (k+t) | k≤(p i).val}) :
    (localGermAlgEquiv Φ hΦ0).symm (HolGerm.mk f (hhol 0 h0U))∈
      actualAnalyticCoordinateIdeal {i : Fin (k+t) | k≤(p i).val}^μ := by
  let R:=actualPermutationLinearEquiv p
  let Ω:=linearChart (ContinuousLinearEquiv.refl ℂ (ComplexModel (k+t))) R Φ
  have hΩ0 : Ω.toFun 0=0:=linearChart_zero _ R Φ hΦ0
  have hsrc : Ω.source⊆(chartAt (ComplexModel (k+t)) (0 : ComplexModel (k+t))).target:=by
    simp [chartAt_self_eq]
  have hFlatΩ : ∀{y : ComplexModel (k+t)},y∈(chartAt (ComplexModel (k+t)) 0).source →
      chartAt (ComplexModel (k+t)) 0 y∈Ω.source →
      (y∈C ↔ Ω.toFun (chartAt (ComplexModel (k+t)) 0 y)∈complexCoordinatePlane (k+t) k) := by
    intro y _hy hys
    have hyΦ : y∈Φ.source:=by simpa [Ω,linearChart,chartAt_self_eq] using hys
    have hGeom : y∈C ↔ Ω.toFun y∈complexCoordinatePlane (k+t) k:=
      (hFlat y hyΦ).trans (coordinateSubsetPlane_permutation p k (Φ.toFun y)).symm
    simpa [chartAt_self_eq] using hGeom
  have hPower:=(actual_member_mem_smooth_centre_power_in_flattening k t μ C f U hU h0U hhol
    hOrders Ω hsrc (by simpa [chartAt_self_eq] using hΩ0) hFlatΩ).1
  have h0T : (0 : ComplexModel (k+t))∈Ω.target:=by
    simpa only [hΩ0] using Ω.mapsTo_toFun Ω.center_mem_source
  have hPower' : (actualNearbyGermEquiv Ω 0 h0T).symm (HolGerm.mk f (hhol 0 h0U))∈normalIdeal k t^μ:=hPower
  rw [nearby_zero_eq_local Ω hΩ0 h0T] at hPower'
  rw [standard_chart_inverse_germ Φ hΦ0 p] at hPower'
  let A : Set (Fin (k+t)):={i | k≤(p i).val}
  have hImage : p '' A=actualTangentCentreVariables k t := by
    ext i
    constructor
    · rintro ⟨j,hj,rfl⟩
      change k≤(p j).val at hj
      have hlt:=(p j).isLt
      refine ⟨⟨(p j).val-k,by omega⟩,Fin.ext (by dsimp;omega)⟩
    · rintro ⟨j,rfl⟩
      refine ⟨p.symm (j.natAdd k),?_,p.apply_symm_apply _⟩
      change k≤(p (p.symm (j.natAdd k))).val
      rw [p.apply_symm_apply,Fin.val_natAdd]
      omega
  let P:=actualPermutationGermEquiv p
  have hMap : Ideal.map P.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal A^μ)=normalIdeal k t^μ := by
    rw [Ideal.map_pow]
    have hBase : Ideal.map P.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal A)=
        actualAnalyticCoordinateIdeal (p '' A):=map_coordinateIdeal_actualPermutation p A
    rw [hBase,hImage,actualAnalyticCoordinateIdeal_normal]
  have hMem : P ((localGermAlgEquiv Φ hΦ0).symm (HolGerm.mk f (hhol 0 h0U)))∈
      Ideal.map P.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal A^μ):=by
    rw [hMap]
    exact hPower'
  obtain ⟨g,hg,hgEq⟩:=(Ideal.mem_map_iff_of_surjective P.toRingEquiv.toRingHom P.surjective).mp hMem
  exact P.injective hgEq ▸ hg

/-- A selected derivative below its original member mark genuinely vanishes
as a VALUE at every point carrying that mark. This uses the entire Taylor
kernel and actual derivative naturality, without moving monicity. -/
theorem selected_derivative_value_zero_of_mark
    (β : Fin n →₀ ℕ) (μ : ℕ) (hβ : normalExponentDegree β<μ)
    (f : ComplexModel n → ℂ) (p : ComplexModel n) (hf : HolAt f p)
    (hdf : HolAt (iterDeriv ((actualCoordinateDerivativeWord β).map
      (fun i=>EuclideanSpace.single i (1 : ℂ))) f) p)
    (hMark : translatedGerm p f hf∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^μ) :
    iterDeriv ((actualCoordinateDerivativeWord β).map (fun i=>EuclideanSpace.single i (1 : ℂ))) f p=0 := by
  have hCoeff:=(actual_maximal_power_iff_formal_coefficients_zero n μ (translatedGerm p f hf)).mp hMark β hβ
  have hZero : HolGerm.eval (actualAnalyticMultiDerivative β (translatedGerm p f hf))=0 := by
    rw [←HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,actualTaylor_actualAnalyticMultiDerivative,
      coeff_actualFormalMultiDerivative,zero_add,hCoeff,zero_mul]
  rw [HironakaActualHistoricalMovingPrefixSupport.actualAnalyticMultiDerivative_translatedGerm β p f hf hdf,
    HironakaHolomorphicJetRankLoci.translatedGerm,HolGerm.eval_mk,zero_add] at hZero
  exact hZero

/-- ONE real open is selected before EVERY future prescribed centre in the
SAME full native Q cosupport. Its points lie in the historical essential
zero plane, derived from source actual contact and nonzero Jacobians.
No HS-on-C, plane containment, member orders or normal powers are inputs. -/
theorem exists_actual_native_weighted_centres_essential_plane
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (F : V → ComplexModel n → ℂ)
    (U : TopologicalSpace.Opens (ComplexModel n)) (h0U : (0 : ComplexModel n)∈U)
    (hF : ∀a,DifferentiableOn ℂ (F a) U)
    (hRep : ∀a,HolGerm.mk (F a) (holAt_of_differentiableOn U.isOpen (hF a) h0U)=Γ a)
    (hw : ∀a : V,0<normalExponentDegree a.val)
    (hContact : ∀r,actualFixedSelectorContactAt S Γ r)
    (hdet : ∀r,(actualFixedSelectorJacobian S Γ r).det≠0) (E : List (Set U)) :
    ∃O : Set (ComplexModel n),IsOpen O ∧ (0 : ComplexModel n)∈O ∧ O⊆U ∧
      ∀C : Set (ComplexModel n),
        (∀z : U,(z : ComplexModel n)∈C →
          z∈(⟨univ,E,weightedFunctionIdeal (fun a : V=>normalExponentDegree a.val)
            (fun a (q : U)=>F a q),weightedCommonMark (fun a : V=>normalExponentDegree a.val)⟩ : MarkedIdeal n U).cosupp) →
        ∀p∈O,p∈C → p∈coordinateSubsetPlane (fixedSelectorEssential V) := by
  let f : fixedSelectorEssential V → ComplexModel n → ℂ:=fun j=>
    iterDeriv ((actualCoordinateDerivativeWord (fixedSelectorBeta S j)).map
      (fun i=>EuclideanSpace.single i (1 : ℂ))) (F (S.selected j))
  have hf (j : fixedSelectorEssential V) : HolAt (f j) 0:=
    eventually_holomorphic_iterDeriv (holAt_of_differentiableOn U.isOpen (hF (S.selected j)) h0U) _
  have hRepD (j : fixedSelectorEssential V) : HolGerm.mk (f j) (hf j)=actualFixedSelectorDerivative S Γ j := by
    rw [actualFixedSelectorDerivative,←hRep (S.selected j),actualAnalyticMultiDerivative,
      actualAnalyticWordDerivative,iteratedDerivativeGerm_mk]
  obtain ⟨O,hO,h0O,hOU,_hHol,hFlags⟩:=
    HironakaActualSelectedContactCarriers.exists_actual_selected_contact_flags_neighborhood_of_det
      S Γ hdet hContact f hf hRepD U U.isOpen h0U
  refine ⟨O,hO,h0O,hOU,?_⟩
  intro C hC p hp hpC i hi
  have hOrders:=actual_native_weighted_centre_orders (fun a : V=>normalExponentDegree a.val)
    hw F U hF E C hC p (hOU hp) hpC
  have hZero (j : fixedSelectorEssential V) : f j p=0 := by
    have hDegree:=fixedSelector_beta_degree S j
    have hβ : normalExponentDegree (fixedSelectorBeta S j)<normalExponentDegree (S.selected j).val:=by omega
    have hdf : HolAt (f j) p:=by
      filter_upwards [U.isOpen.mem_nhds (hOU hp)] with z hz
      exact (differentiableOn_iterDeriv (hF (S.selected j)) U.isOpen _ z hz).differentiableAt
        (U.isOpen.mem_nhds hz)
    exact selected_derivative_value_zero_of_mark _ _ hβ (F (S.selected j)) p
      (holAt_of_differentiableOn U.isOpen (hF (S.selected j)) (hOU hp)) hdf (hOrders (S.selected j))
  let K:=V.sup normalExponentDegree
  have hPlane:=(hFlags K p hp).mp (fun j _=>hZero j)
  obtain ⟨a,ha⟩:=hi
  exact hPlane i ⟨a,Finset.le_sup a.property,ha⟩

private theorem same_chart_coordinate_power_of_le
    (k μ : ℕ) (hkn : k≤n) (p : Fin n ≃ Fin n)
    (C : Set (ComplexModel n)) (f : ComplexModel n → ℂ) (U : Set (ComplexModel n))
    (hU : IsOpen U) (h0U : (0 : ComplexModel n)∈U) (hhol : ∀z∈U,HolAt f z)
    (hOrders : ∀z (hz : z∈U),z∈C → translatedGerm z f (hhol z hz)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^μ)
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0)
    (hFlat : ∀z∈Φ.source,z∈C ↔ Φ.toFun z∈coordinateSubsetPlane {i : Fin n | k≤(p i).val}) :
    (localGermAlgEquiv Φ hΦ0).symm (HolGerm.mk f (hhol 0 h0U))∈
      actualAnalyticCoordinateIdeal {i : Fin n | k≤(p i).val}^μ := by
  obtain ⟨t,ht⟩:=Nat.exists_eq_add_of_le hkn
  subst n
  exact actual_member_mem_coordinate_power_in_same_chart k t μ p C f U hU h0U hhol hOrders Φ hΦ0 hFlat

/-- ORIGINAL representatives/contact/Jacobians/full Q cosupport produce
ONE actual window before ANY prescribed centre, and internally construct
its compatible chart together with SAME-chart whole member powers. -/
theorem exists_actual_native_weighted_compatible_centre_chart
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (F : V → ComplexModel n → ℂ)
    (U : TopologicalSpace.Opens (ComplexModel n)) (h0U : (0 : ComplexModel n)∈U)
    (hF : ∀a,DifferentiableOn ℂ (F a) U)
    (hRep : ∀a,HolGerm.mk (F a) (holAt_of_differentiableOn U.isOpen (hF a) h0U)=Γ a)
    (hw : ∀a : V,0<normalExponentDegree a.val)
    (hContact : ∀r,actualFixedSelectorContactAt S Γ r)
    (hdet : ∀r,(actualFixedSelectorJacobian S Γ r).det≠0) (E : List (Set U)) :
    ∃O : Set (ComplexModel n),IsOpen O ∧ (0 : ComplexModel n)∈O ∧ O⊆U ∧
      ∀(C : Set (ComplexModel n))(k : ℕ),RegularAtDim (n:=n) C 0 k →
        (∀z : U,(z : ComplexModel n)∈C →
          z∈(⟨univ,E,weightedFunctionIdeal (fun a : V=>normalExponentDegree a.val)
            (fun a (q : U)=>F a q),weightedCommonMark (fun a : V=>normalExponentDegree a.val)⟩ : MarkedIdeal n U).cosupp) →
        ∃D : ActualCompatibleMovingCentreChart (fixedSelectorEssential V) C k,
          ∀a : V,(localGermAlgEquiv D.chart D.chart_zero).symm (Γ a)∈
            actualAnalyticCoordinateIdeal {i : Fin n | k≤(D.priorityPermutation i).val}^normalExponentDegree a.val := by
  obtain ⟨O,hO,h0O,hOU,hPlane⟩:=
    exists_actual_native_weighted_centres_essential_plane S Γ F U h0U hF hRep hw hContact hdet E
  refine ⟨O,hO,h0O,hOU,?_⟩
  intro C k hreg hC
  have hPlaneC : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈C → z∈coordinateSubsetPlane (fixedSelectorEssential V):=by
    filter_upwards [hO.mem_nhds h0O] with z hz hzC
    exact hPlane C hC z hz hzC
  obtain ⟨D⟩:=exists_actual_compatible_moving_centre_chart (fixedSelectorEssential V) C k hreg hPlaneC
  refine ⟨D,?_⟩
  intro a
  let p : Fin n ≃ Fin n:=D.priorityPermutation.trans (finCongr D.dimension)
  have hkn : k≤n:=by
    rw [←D.dimension]
    exact D.centreDimensionBound.trans (Nat.le_add_right _ _)
  have hFlat : ∀z∈D.chart.source,z∈C ↔ D.chart.toFun z∈coordinateSubsetPlane {i : Fin n | k≤(p i).val}:=by
    simpa only [p,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using D.centre
  have hPow:=same_chart_coordinate_power_of_le k (normalExponentDegree a.val) hkn p C (F a) U
    U.isOpen h0U (fun z hz=>holAt_of_differentiableOn U.isOpen (hF a) hz)
    (fun z hz hzC=>actual_native_weighted_centre_orders (fun b : V=>normalExponentDegree b.val)
      hw F U hF E C hC z hz hzC a) D.chart D.chart_zero hFlat
  rw [hRep a] at hPow
  simpa only [p,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using hPow

end
end Hironaka.HironakaActualHistoricalMovingCentreChart

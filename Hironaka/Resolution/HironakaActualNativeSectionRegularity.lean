import Hironaka.Resolution.HironakaActualSubspaceManifoldRegularity
import Hironaka.Resolution.HironakaActualNativeSectionOrderHistory

/-! The literal induced native section has true projection-stable windows.
Actual quotient-subspace isomorphisms compare original subset regularity;
the zero-special codimension-one dictionary uses those same original sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionRegularity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense SubmanifoldChartedSpace IsManifold
variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

theorem exists_actual_native_retraction_window (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀p : W,∃(U : Opens X),p.val∈U ∧ ∃R : U→W,
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ R ∧
      (∀q : W,∀hq : q.val∈U,R ⟨q.val,hq⟩=q) ∧
      ∀y : U,(R y).val∈U := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p
  let F:=FlatData.ofRegularAtDim (hW p.val p.property)
  let e:=F.chart hk
  let G : X→ComplexModel k:=fun y=>coordinateProjection n k (F.flat (F.amb.val y))
  have hG (y : X) (hy : y∈F.ambSource) :
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G y := by
    have h₁ : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ F.amb.val y:=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property) hy.1
    have h₂ : ContDiffAt ℂ ∞ (fun z=>coordinateProjection n k (F.flat z)) (F.amb.val y):=
      (coordinateProjection n k).contDiff.contDiffAt.comp _
        ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
          F.flat.open_source).contDiffAt (F.flat.open_source.mem_nhds hy.2))
    exact h₂.contMDiffAt.comp y h₁
  have hGc : ContinuousOn G F.ambSource:=fun y hy=>(hG y hy).continuousAt.continuousWithinAt
  let U : Opens X:=⟨F.ambSource∩G ⁻¹' e.target,
    hGc.isOpen_inter_preimage F.isOpen_ambSource e.open_target⟩
  have hpSrc : p∈e.source:=FlatData.mem_ambSource_ofRegularAtDim (hW p.val p.property)
  have hpU : p.val∈U:=⟨hpSrc,e.map_source hpSrc⟩
  let R : U→W:=fun y=>e.symm (G y.val)
  have heMax : e∈maximalAtlas 𝓘(ℂ,ComplexModel k) ∞ W:=
    IsManifold.subset_maximalAtlas (chart_mem_atlas hk hW F)
  have hR : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ R:=by
    intro y
    exact (contMDiffAt_symm_of_mem_maximalAtlas heMax y.property.2).comp y
      ((hG y.val y.property.1).comp y (contMDiff_subtype_val y))
  refine ⟨U,hpU,R,hR,?_,?_⟩
  · intro q hq
    exact e.left_inv hq.1
  · intro y
    have hsrc : R y∈e.source:=e.map_target y.property.2
    refine ⟨hsrc,?_⟩
    change e (e.symm (G y.val))∈e.target
    rw [e.right_inv y.property.2]
    exact y.property.2

open CategoryTheory AlgebraicGeometry
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence
  HironakaActualSubspaceManifoldRegularity HironakaReducedComplexAnalyticSpaces

theorem regularAtDim_native_image_iff (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(A : Set W)(p : W)(j : ℕ),
      RegularAtDim (n:=n) ((Subtype.val : W→X) '' A) p.val j ↔
        RegularAtDim (n:=k) A p j := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A p j
  by_cases hpA : p∈A
  · obtain ⟨U,hpU,R,hR,hFix,hRU⟩:=exists_actual_native_retraction_window hk hW p
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
    have hyD : y∈D:=hpA
    have hxy : (e.hom.base ⟨x,hxC⟩).val=y:=by
      apply Subtype.ext
      exact hFix p hpU
    have hyx : (e.inv.base ⟨y,hyD⟩).val=x:=rfl
    constructor
    · intro hr
      have hrC : RegularAtDim (n:=n) C x j:=AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hr
      have hrD:=regularAtDim_of_actual_subspace_iso e (actualSubspaceMap_point hf hCD) ⟨x,hxC⟩ hrC
      rw [hxy] at hrD
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hrD
    · intro hr
      have hrD : RegularAtDim (n:=k) D y j:=AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hr
      have hrC:=regularAtDim_of_actual_subspace_iso e.symm (actualSubspaceMap_point hg hDC) ⟨y,hyD⟩ hrD
      change RegularAtDim (n:=n) C (e.inv.base ⟨y,hyD⟩).val j at hrC
      rw [hyx] at hrC
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hrC
  · constructor
    · intro hr
      obtain ⟨q,hqA,hq⟩:=hr.2.1
      exact (hpA ((Subtype.val_injective hq) ▸ hqA)).elim
    · intro hr
      exact (hpA hr.2.1).elim

open CodimOneSupportAlong GermIdealOrder
  HironakaActualNativeSectionOrder HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionOrderHistory
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings

theorem codimOnePartAlong_native_preimage (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    ∀(A : Set W)(J : GermIdeal n X)
      (_hJ : ∀x g,J.mem x g → HolomorphicAt n g x) (d : ℕ),
      (Subtype.val : W→X) ⁻¹' codimOnePartAlong ((Subtype.val : W→X) '' A) J d=
        codimOnePartAlong A (GermIdeal.pullback (m:=k) (Subtype.val : W→X) J) d := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ d
  have hS:=cosupport_native_image hk hW A J hJ d
  ext p
  constructor
  · rintro ⟨j,hN,hC⟩
    rw [←hS] at hC
    exact ⟨j,(regularAtDim_native_image_iff hk hW A p (j+1)).mp hN,
      (regularAtDim_native_image_iff hk hW _ p j).mp hC⟩
  · rintro ⟨j,hN,hC⟩
    refine ⟨j,(regularAtDim_native_image_iff hk hW A p (j+1)).mpr hN,?_⟩
    rw [←hS]
    exact (regularAtDim_native_image_iff hk hW _ p j).mpr hC

theorem Lift.current_codimOnePart
    {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
    {hW : ∀x∈W,RegularAtDim (n:=n) W x k} {E : List (Set X)}
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    (Subtype.val : V→Y) ⁻¹' codimOnePartAlong (geoTransformAlong M T).N
      (geoTransformAlong M T).ideal (geoTransformAlong M T).d=
      codimOnePartAlong (geoTransformAlong (nativePullback hk W hW M) Q).N
        (geoTransformAlong (nativePullback hk W hW M) Q).ideal
        (geoTransformAlong (nativePullback hk W hW M) Q).d := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let A:=(Subtype.val : V→Y) ⁻¹' (geoTransformAlong M T).N
  have hImage : (Subtype.val : V→Y) '' A=(geoTransformAlong M T).N:=by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hy
      exact ⟨⟨y,(Lift.current_carrier_subset h M hMN) hy⟩,hy,rfl⟩
  have hc:=codimOnePartAlong_native_preimage hk hV A (geoTransformAlong M T).ideal
    (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong M hhol T) (geoTransformAlong M T).d
  rw [hImage] at hc
  have hrec:=h.whole_records hn hE hTrans M hME hMN hhol
  rw [hrec]
  exact hc

end
end Hironaka.HironakaActualNativeSectionRegularity

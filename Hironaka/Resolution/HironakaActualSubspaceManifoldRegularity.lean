import Hironaka.Resolution.HironakaActualSectionInitialValues

/-! Original regularity is recovered from a genuine native manifold chart
of the actual reduced subspace in an arbitrary ambient manifold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSubspaceManifoldRegularity
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceRegularityConverse
  HironakaActualFlatCoordinateIntrinsicHS HironakaReducedComplexAnalyticSpaces
  HironakaActualNestedSectionCoordinates BlowupFlatCoordinates
variable {n d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def chartIdentity (p : M) : LocalHolomorphicEquivAt (chartAt (ComplexModel n) p p) where
  source := (chartAt (ComplexModel n) p).target
  target := (chartAt (ComplexModel n) p).target
  isOpen_source := (chartAt (ComplexModel n) p).open_target
  isOpen_target := (chartAt (ComplexModel n) p).open_target
  center_mem_source := (chartAt (ComplexModel n) p).map_source (mem_chart_source _ p)
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ h=>h
  mapsTo_invFun := fun _ h=>h
  left_inv := fun _ _=>rfl
  right_inv := fun _ _=>rfl

theorem regularAtDim_of_actual_manifold_chart {O : Opens (ComplexModel d)} {C : Set M}
    (j : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) O ⟶
      actualSubspaceLocallyRingedSpace (n:=n) C)
    [hj : LocallyRingedSpace.IsOpenImmersion j]
    (hjp : j ≫ subspacePointMap (n:=n) C=ambientPointMap d O) (x : O) :
    RegularAtDim (n:=n) C (j.base x).val d := by
  let p:=(j.base x).val
  let Φ:=chartIdentity (n:=n) p
  let U : Opens M:=⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let V : Opens (ComplexModel n):=⟨Φ.target,Φ.isOpen_target⟩
  let e:=actualFlatCoordinateDiffeomorph Φ (Subset.refl _)
  have hpU : p∈U:=⟨mem_chart_source _ p,Φ.center_mem_source⟩
  let C₀ : Set U:=(Subtype.val : U→M) ⁻¹' C
  let K:=actualOpenSubspaceMap (n:=n) C U
  let W : Opens O:=⟨(fun z : O=>(j.base z).val) ⁻¹' U,
    U.isOpen.preimage (continuous_subtype_val.comp j.base.hom.continuous)⟩
  have hxW : x∈W:=hpU
  let F:=actualOpenSubspaceMap (n:=d) (univ : Set O) W ≫
    (actualSubspaceUnivIso (n:=d) (M:=O)).hom ≫ j
  have hRange : range F.base⊆range K.base:=by
    rintro _ ⟨z,rfl⟩
    refine ⟨⟨⟨(j.base z.val.val).val,z.val.property⟩,(j.base z.val.val).property⟩,?_⟩
    apply Subtype.ext
    rfl
  let L:=LocallyRingedSpace.IsOpenImmersion.lift K F hRange
  have hLK : L≫K=F:=LocallyRingedSpace.IsOpenImmersion.lift_fac K F hRange
  have hL : LocallyRingedSpace.IsOpenImmersion L:=by
    let : IsIso (pullback.snd K F):=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset K F hRange
    dsimp only [L,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion L:=hL
  let C₁ : Set V:=e.symm ⁻¹' C₀
  let H:=actualSubspaceBiholomorphicIso e C₀ C₁ (fun z=>by
    change z∈C₀ ↔ e.symm (e z)∈C₀
    rw [e.symm_apply_apply])
  let E:=baseEquiv O W
  let B:=actualSubspaceBiholomorphicIso E.symm (univ : Set (globalImage O W))
    (univ : Set W) (fun _=>iff_of_true (mem_univ _) (mem_univ _))
  let J:=(actualSubspaceUnivIso (n:=d) (M:=globalImage O W)).inv ≫ B.hom ≫ L ≫ H.hom
  have hJ : LocallyRingedSpace.IsOpenImmersion J:=by dsimp only [J];infer_instance
  let : LocallyRingedSpace.IsOpenImmersion J:=hJ
  have hLp : L≫subspacePointMap (n:=n) C₀=subspacePointMap (n:=d) (univ : Set W) := by
    have hKp : K≫subspacePointMap (n:=n) C=subspacePointMap (n:=n) C₀:=
      actualSubspaceMap_point contMDiff_subtype_val (fun _ h=>h)
    rw [←hKp,←Category.assoc,hLK]
    dsimp only [F]
    rw [Category.assoc,Category.assoc,hjp]
    rw [actualSubspaceUnivIso_hom]
    change actualOpenSubspaceMap (n:=d) (univ : Set O) W ≫
      subspacePointMap (n:=d) (univ : Set O)=_
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ _=>mem_univ _)
  have hJp : J≫subspacePointMap (n:=n) C₁=ambientPointMap d (globalImage O W):=by
    have hHp : H.hom≫subspacePointMap (n:=n) C₁=subspacePointMap (n:=n) C₀:=
      actualSubspaceMap_point e.contMDiff (fun z hz=>by change e.symm (e z)∈C₀;simpa using hz)
    have hBp : B.hom≫subspacePointMap (n:=d) (univ : Set W)=
        subspacePointMap (n:=d) (univ : Set (globalImage O W)):=
      actualSubspaceMap_point E.symm.contMDiff (fun _ _=>mem_univ _)
    simp only [J,Category.assoc,hHp,hLp,hBp]
    exact actualSubspaceUnivIso_inv_point
  have hr:=regularAtDim_of_native_manifold_chart J hJp (E ⟨x,hxW⟩)
  have hBase : (J.base (E ⟨x,hxW⟩)).val=e ⟨p,hpU⟩ := by
    let u : (univ : Set W):=⟨⟨x,hxW⟩,mem_univ _⟩
    have hLpoint : (L.base u).val.val=p := by
      have h:=congrArg (fun f=>(f.base u).val) hLK
      exact h
    let E₀:=actualSubspaceUnivIso (n:=d) (M:=globalImage O W)
    have hInv (z : globalImage O W) : (E₀.inv.base z).val=z := by
      have h:=congrArg (fun f=>f.base z) E₀.inv_hom_id
      exact h
    have hBpoint : B.hom.base (E₀.inv.base (E ⟨x,hxW⟩))=u := by
      apply Subtype.ext
      change E.symm ((E₀.inv.base (E ⟨x,hxW⟩)).val)=_
      rw [hInv,E.symm_apply_apply]
    change e (L.base (B.hom.base (E₀.inv.base (E ⟨x,hxW⟩)))).val=e ⟨p,hpU⟩
    rw [hBpoint]
    exact congrArg e (Subtype.ext hLpoint)
  rw [hBase] at hr
  have hr₀ : RegularAtDim (n:=n) C₀ ⟨p,hpU⟩ d:=
    by simpa only [e.symm_apply_apply] using (CodimOnePartCanonical.regularAtDim_preimage_iff e.symm).mp hr
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hr₀

theorem regularAtDim_of_actual_subspace_iso
    {m ℓ : ℕ} {N : Type} [TopologicalSpace N]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {A : Set M} {B : Set N}
    (e : actualSubspaceLocallyRingedSpace (n:=n) A ≅ actualSubspaceLocallyRingedSpace (n:=m) B)
    (he : e.hom≫subspacePointMap (n:=m) B=subspacePointMap (n:=n) A)
    (x : A) (hreg : RegularAtDim (n:=n) A x.val ℓ) :
    RegularAtDim (n:=m) B (e.hom.base x).val ℓ := by
  obtain ⟨t,hn⟩:=Nat.exists_eq_add_of_le hreg.1
  subst n
  obtain ⟨O,i,hi,hip,hxi⟩:=exists_actual_regular_subspace_manifold_chart A x.val hreg
  let : LocallyRingedSpace.IsOpenImmersion i:=hi
  let j:=i≫e.hom
  have hj : LocallyRingedSpace.IsOpenImmersion j:=by dsimp only [j];infer_instance
  let : LocallyRingedSpace.IsOpenImmersion j:=hj
  have hjp : j≫subspacePointMap (n:=m) B=ambientPointMap ℓ O:=by
    dsimp only [j]
    rw [Category.assoc,he,hip]
  obtain ⟨z,hz⟩:=hxi
  have hr:=regularAtDim_of_actual_manifold_chart j hjp z
  have hp : (j.base z).val=(e.hom.base x).val:=by
    change (e.hom.base (i.base z)).val=_
    have hx : i.base z=x:=by simpa only [Subtype.ext_iff] using hz
    rw [hx]
  simpa only [hp] using hr

end
end Hironaka.HironakaActualSubspaceManifoldRegularity

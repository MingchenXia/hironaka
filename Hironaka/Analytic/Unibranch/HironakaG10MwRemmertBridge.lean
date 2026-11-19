import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular
import Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse
import Hironaka.Resolution.HironakaActualHolomorphicStalkSurjection
import Hironaka.Analytic.AnalyticIrreducibleComponents

/-!
# Native Remmert, item 5.1: the chart bridge for the native rank (lane G10MW)

* `rankIn_eq_finrank_range_of_param` — on a complex manifold, the rank of `F` on `A` at a regular point of
  dimension `d` is the rank of the differential of `F ∘ p` for ANY holomorphic `p` from `ℂ^d` into `A`
  through the point with injective differential (read in charts);
* `nativeRankAt_eq_rankAt_lift` — **the bridge**: the native rank of `φ` at a regular point equals the library
  rank (`RankDegeneracy.rankAt`) of any holomorphic lift of `pointMap φ`, on the trace of the carrier, in any local
  embedding.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry Module
open IsManifold ChartedSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertBridge

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaActualHolomorphicStalkSurjection
  HolomorphicIdealSheaves RankDegeneracy SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular

noncomputable section

/-! ### Ranks through a parametrization -/

section Param

variable {N k d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel N) X]
  [IsComplexManifold N X] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- **The rank through a parametrization.**  If `A` is regular of dimension `d` at `x` and `P` (a chart reading
of a holomorphic map from `ℂ^d` into `A` through `x`) has injective differential at `u₀`, then the rank of `F`
on `A` at `x` is the rank of the differential of `F ∘ P`. -/
theorem rankIn_eq_finrank_range_of_param {A : Set X} {x : X} (hx : RegularAtDim (n := N) A x d)
    (e : ComplexChart N X) (hxe : x ∈ e.val.source) (e' : ComplexChart k M) {F : X → M}
    (hFx : F x ∈ e'.val.source)
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel k) F x)
    {P : ComplexModel d → ComplexModel N} {u₀ : ComplexModel d} (hP0 : P u₀ = e.val x)
    (hPd : DifferentiableAt ℂ P u₀) (hPinj : Function.Injective (fderiv ℂ P u₀))
    (hPA : ∀ᶠ u in 𝓝 u₀, P u ∈ e.val.target ∧ e.val.symm (P u) ∈ A) :
    rankIn e e' F A x =
      finrank ℂ (LinearMap.range ((fderiv ℂ (fun u => e'.val (F (e.val.symm (P u)))) u₀ :
        ComplexModel d →L[ℂ] ComplexModel k) : ComplexModel d →ₗ[ℂ] ComplexModel k)) := by
  have hqt : e.val x ∈ e.val.target := e.val.map_source hxe
  have hsq : e.val.symm (e.val x) = x := e.val.left_inv hxe
  have hFd : DifferentiableAt ℂ (fun w => e'.val (F (e.val.symm w))) (e.val x) :=
    differentiableAt_chartReading e e' hxe hFx hF
  have hlim : Tendsto (fun u => e.val.symm (P u)) (𝓝 u₀) (𝓝 x) := by
    have h2 : ContinuousAt e.val.symm (P u₀) := by
      rw [hP0]
      exact e.val.continuousAt_symm hqt
    have h3 := ContinuousAt.comp (g := e.val.symm) (f := P) h2 hPd.continuousAt
    have h4 : Tendsto (fun u => e.val.symm (P u)) (𝓝 u₀) (𝓝 (e.val.symm (P u₀))) := h3.tendsto
    rwa [hP0, hsq] at h4
  have hT : tangentSpaceIn e A x =
      LinearMap.range ((fderiv ℂ P u₀ : ComplexModel d →L[ℂ] ComplexModel N) :
        ComplexModel d →ₗ[ℂ] ComplexModel N) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, rfl⟩
      rw [mem_tangentSpaceIn]
      intro g hg
      have hgd : DifferentiableAt ℂ (fun w => g (e.val.symm w)) (e.val x) :=
        StokesSingularLocusAnalytic.differentiableAt_chart e hqt
          (by rw [hsq]; exact hg.1.self_of_nhds)
      have hzero : (fun u => g (e.val.symm (P u))) =ᶠ[𝓝 u₀] fun _ => (0 : ℂ) := by
        filter_upwards [hPA, hlim.eventually hg.2] with u hu hvan
        exact hvan hu.2
      have hcomp : fderiv ℂ (fun u => g (e.val.symm (P u))) u₀ =
          (fderiv ℂ (fun w => g (e.val.symm w)) (e.val x)).comp (fderiv ℂ P u₀) :=
        fderiv_comp_of_eq (g := fun w => g (e.val.symm w)) (f := P) hP0 hgd hPd
      have h0 : fderiv ℂ (fun u => g (e.val.symm (P u))) u₀ = 0 := by
        rw [hzero.fderiv_eq]
        simp
      have h := congrArg (fun L : ComplexModel d →L[ℂ] ℂ => L v) (hcomp.symm.trans h0)
      simpa using h
    · rw [finrank_tangentSpaceIn_of_regularAtDim e hxe hx, LinearMap.finrank_range_of_inj hPinj,
        finrank_euclideanSpace_fin]
  have hcomp : fderiv ℂ (fun u => e'.val (F (e.val.symm (P u)))) u₀ =
      (fderiv ℂ (fun w => e'.val (F (e.val.symm w))) (e.val x)).comp (fderiv ℂ P u₀) :=
    fderiv_comp_of_eq (g := fun w => e'.val (F (e.val.symm w))) (f := P) hP0 hFd hPd
  unfold rankIn chartDeriv
  rw [hT, hcomp]
  exact congrArg (fun S : Submodule ℂ (ComplexModel k) => finrank ℂ S)
    (LinearMap.range_comp ((fderiv ℂ P u₀ : _ →L[ℂ] _) : ComplexModel d →ₗ[ℂ] ComplexModel N)
      ((fderiv ℂ (fun w => e'.val (F (e.val.symm w))) (e.val x) : _ →L[ℂ] _) :
        ComplexModel N →ₗ[ℂ] ComplexModel k)).symm

end Param

/-! ### A native parametrization of a local embedding near a regular point -/

section Native

variable {Y : SourceReducedComplexSpace} {d : ℕ}

private theorem openImmersion_lift' {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (Limits.pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem native_inclusion_point' (O : Opens (ComplexModel d)) :
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d))) ≫
      ambientPointMap d (ComplexModel d) = ambientPointMap d O :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (IP := 𝓘(ℂ, ComplexModel 0))
    contMDiff_subtype_val
    (show ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : ComplexModel d => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- Stalk surjectivity of a holomorphic map whose native model map is an open immersion. -/
private theorem stalk_surjective_of_openImmersion {n : ℕ} {O : Opens (ComplexModel d)}
    {V : Opens (ComplexModel n)} {f : O → V}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f)
    {C : Set V} (hC : ∀ y ∈ (univ : Set O), f y ∈ C)
    [hopen : LocallyRingedSpace.IsOpenImmersion (actualSubspaceMap hf hC)] (x : O) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x) := by
  let u : (univ : Set O) := ⟨x, mem_univ _⟩
  let J := actualSubspaceMap hf hC
  let E := actualSubspaceUnivIso (n := d) (M := O)
  have hEinj : Function.Injective ((actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u) := by
    change Function.Injective (E.hom.stalkMap u)
    exact ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).1
  have hJsurj : Function.Surjective (J.stalkMap u) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).2
  intro q
  obtain ⟨b, hb⟩ := hJsurj ((actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u q)
  obtain ⟨r, hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective C (J.base u) b
  refine ⟨r, hEinj ?_⟩
  have he := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hC u) r
  change J.stalkMap u ((actualSubspaceInclusion (n := n) C).stalkMap (J.base u) r) =
    (actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x r) at he
  have hr' : (actualSubspaceInclusion (n := n) C).stalkMap (J.base u) r = b := hr
  exact he.symm.trans ((congrArg (J.stalkMap u) hr').trans hb)

/-- **A native parametrization.**  Near a point of a regular chart `D` lying in a local embedding `a`, the
chart lifts to a holomorphic map `f` into the ambient space of `a`, with values in the carrier, inducing the
chart on points, and with injective differential. -/
theorem exists_native_param (D : RegChart Y d) (a : LocalEmbedding Y) (c : a.carrier)
    (v₀ : D.domain) (hv : D.map.base v₀ = a.toPoint c) :
    ∃ (V : Opens (ComplexModel d)) (hVD : (V : Set (ComplexModel d)) ⊆ D.domain) (z₀ : V)
      (f : V → a.ambient), z₀.val = v₀.val ∧
      ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ∞ f ∧
      (∀ z : V, f z ∈ a.carrier) ∧
      (∀ (z : V) (h : f z ∈ a.carrier), a.toPoint ⟨f z, h⟩ = D.map.base ⟨z.val, hVD z.property⟩) ∧
      f z₀ = c.val ∧
      Function.Injective
        (fderiv ℂ (actualOpenVectorExtension V (fun z : V => (f z).val)) z₀.val) := by
  let i := D.map
  let : LocallyRingedSpace.IsOpenImmersion i := D.openImmersion
  let : LocallyRingedSpace.IsOpenImmersion a.map := a.isOpenImmersion
  let j : actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier ⟶ Y.obj.left := a.map
  let : LocallyRingedSpace.IsOpenImmersion j := a.isOpenImmersion
  have hjp : j ≫ Y.obj.hom = subspacePointMap (n := a.dim) a.carrier := a.overPoint
  let P : Opens D.domain := ⟨i.base ⁻¹' range a.map.base,
    a.isOpenImmersion.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  have hvP : v₀ ∈ P := by
    change i.base v₀ ∈ range a.map.base
    exact ⟨c, hv.symm⟩
  let V : Opens (ComplexModel d) :=
    ⟨(Subtype.val : D.domain → ComplexModel d) '' (P : Set D.domain),
      D.domain.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  have hVD : (V : Set (ComplexModel d)) ⊆ D.domain := by
    rintro _ ⟨u, -, rfl⟩
    exact u.property
  let a' := ChartedSpace.locallyRingedSpaceMap (Subtype.val : D.domain → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  let b := ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel d)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
  have hab : range b.base ⊆ range a'.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨u, _hu, huz⟩ := z.property
    exact ⟨u, huz⟩
  let k := LocallyRingedSpace.IsOpenImmersion.lift a' b hab
  let : LocallyRingedSpace.IsOpenImmersion k := openImmersion_lift' a' b hab
  have hka : k ≫ a' = b := LocallyRingedSpace.IsOpenImmersion.lift_fac a' b hab
  have hkz (z : V) : (k.base z).val = z.val := congrArg (fun f => f.base z) hka
  have hkP (z : V) : k.base z ∈ P := by
    obtain ⟨u, hu, huz⟩ := z.property
    have hku : k.base z = u := Subtype.ext ((hkz z).trans huz.symm)
    exact hku.symm ▸ hu
  have hkp : k ≫ ambientPointMap d D.domain = ambientPointMap d V := by
    rw [← native_inclusion_point' D.domain, ← Category.assoc, hka]
    exact native_inclusion_point' V
  let g := k ≫ i
  have hgp : g ≫ Y.obj.hom = ambientPointMap d V := by
    dsimp only [g]
    rw [Category.assoc, D.overPoint, hkp]
  have hge : range g.base ⊆ range a.map.base := by
    rintro _ ⟨z, rfl⟩
    exact hkP z
  let H := LocallyRingedSpace.IsOpenImmersion.lift j g hge
  let : LocallyRingedSpace.IsOpenImmersion H := openImmersion_lift' j g hge
  have hHe : H ≫ j = g := LocallyRingedSpace.IsOpenImmersion.lift_fac j g hge
  have hHp : H ≫ subspacePointMap (n := a.dim) a.carrier = ambientPointMap d V := by
    rw [← hjp, ← Category.assoc, hHe, hgp]
  let z₀ : V := ⟨v₀.val, ⟨v₀, hvP, rfl⟩⟩
  have hkv : k.base z₀ = v₀ := Subtype.ext (hkz z₀)
  have hpt (z : V) : a.toPoint (H.base z) = D.map.base ⟨z.val, hVD z.property⟩ := by
    have hh := congrArg (fun f => f.base z) hHe
    change j.base (H.base z) = i.base (k.base z) at hh
    change j.base (H.base z) = _
    rw [hh]
    congr 1
    exact Subtype.ext (hkz z)
  have hHc : H.base z₀ = c := by
    apply a.toPoint_injective
    rw [hpt z₀, ← hv]
  let f : V → a.ambient := fun z => (H.base z).val
  have hf : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ∞ f :=
    contMDiff_native_source_pointMap H hHp
  have hC : ∀ y ∈ (univ : Set V), f y ∈ a.carrier := fun y _ => (H.base y).property
  let E := actualSubspaceUnivIso (n := d) (M := V)
  have hpoint : (E.hom ≫ H) ≫ subspacePointMap (n := a.dim) a.carrier =
      subspacePointMap (n := d) (univ : Set V) := by
    rw [Category.assoc, hHp]
    rfl
  have hJ : actualSubspaceMap hf hC = E.hom ≫ H := original_morphism_eq_actualSubspaceMap _ hpoint
  let : LocallyRingedSpace.IsOpenImmersion (actualSubspaceMap hf hC) := by
    rw [hJ]
    infer_instance
  have hsurj := stalk_surjective_of_openImmersion hf hC z₀
  refine ⟨V, hVD, z₀, f, rfl, hf, fun z => (H.base z).property, fun z h => hpt z, ?_,
    injective_fderiv_of_native_stalk_surjective hf z₀ hsurj⟩
  change (H.base z₀).val = c.val
  rw [hHc]

end Native

/-! ### The bridge -/

section Bridge

variable {Y : SourceReducedComplexSpace} {d : ℕ} [SecondCountableTopology Y.obj.left]
  {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M] {C : Set M} {hC : IsComplexAnalyticSubset (n := k) C}

/-- **The chart bridge for the native rank.**  In any local embedding `a`, on any open `W` of its ambient
space, for any holomorphic `G : W → M` lifting `pointMap φ` on the carrier, the native rank of `φ` at a regular
point of the carrier is the library rank of `G` on the trace of the carrier. -/
theorem nativeRankAt_eq_rankAt_lift (φ : Y ⟶ ofClosedAnalytic C hC) (a : LocalEmbedding Y)
    (W : Opens a.ambient) {G : W → M}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) ∞ G)
    (hGφ : ∀ (w : W) (hw : w.val ∈ a.carrier), G w = pointMap φ (a.toPoint ⟨w.val, hw⟩))
    (w : W) (hw : w.val ∈ a.carrier) (hreg : a.toPoint ⟨w.val, hw⟩ ∈ regLocus Y d) :
    nativeRankAt d φ ⟨_, hreg⟩ =
      rankAt (n := a.dim) (n' := k) G ((Subtype.val : W → a.ambient) ⁻¹' a.carrier) w := by
  let yr : regLocus Y d := ⟨_, hreg⟩
  let c : a.carrier := ⟨w.val, hw⟩
  let D := regChartAt yr
  obtain ⟨v₀, hv₀⟩ := mem_range_regChartAt yr
  have hv : D.map.base v₀ = a.toPoint c := congrArg Subtype.val hv₀
  obtain ⟨V, hVD, z₀, f, hz₀, hf, hfC, hfpt, hfc, hinj⟩ := exists_native_param D a c v₀ hv
  have hGw : G w = regPointMap d φ yr := hGφ w hw
  -- the manifold side
  let eY := complexChartAt (n := d) yr
  have heY : eY.val = D.chart := rfl
  let e' := complexChartAt (n := k) (regPointMap d φ yr)
  have hgd : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) (regPointMap d φ) yr :=
    ((contMDiff_regPointMap φ) yr).mdifferentiableAt (by simp)
  have hL := rankIn_eq_finrank_range_of_param (AnalyticIrreducibleComponents.regularAtDim_univ yr)
    eY (mem_complexChartAt_source yr) e' (mem_complexChartAt_source _) hgd
    (P := fun u => u) (u₀ := eY.val yr) rfl differentiableAt_id
    (by rw [fderiv_fun_id]; exact Function.injective_id)
    (by filter_upwards [eY.val.open_target.mem_nhds (eY.val.map_source (mem_complexChartAt_source yr))]
          with u hu
        exact ⟨hu, mem_univ _⟩)
  -- the carrier side
  let eW := complexChartAt (n := a.dim) w
  have heW : ∀ w' : W, eW.val w' = w'.val.val := fun _ => rfl
  have hsrcW : ∀ w' : W, w' ∈ eW.val.source := by
    intro w'
    change w' ∈ (chartAt (ComplexModel a.dim) w).source
    rw [AnalyticSubsetOpens.mem_chartAt_opens_source, AnalyticSubsetOpens.mem_chartAt_opens_source]
    exact mem_univ _
  let P₀ := actualOpenVectorExtension V (fun z : V => (f z).val)
  have hfVec : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ∞ (fun z : V => (f z).val) :=
    (contMDiff_subtype_val (U := a.ambient)).comp hf
  have hPd : DifferentiableAt ℂ P₀ z₀.val :=
    mdifferentiableAt_iff_differentiableAt.mp
      ((actualOpenVectorExtension_contMDiffAt V (fun z : V => (f z).val) z₀
        hfVec.contMDiffAt).mdifferentiableAt (by simp))
  have hP0 : P₀ z₀.val = eW.val w := by
    change actualOpenVectorExtension V (fun z : V => (f z).val) z₀.val = eW.val w
    rw [actualOpenVectorExtension_apply V _ z₀, hfc, heW]
  -- the open set of parameters landing in `W`
  let U' : Set V := f ⁻¹' (W : Set a.ambient)
  have hU' : IsOpen U' := W.isOpen.preimage hf.continuous
  have hz₀U' : z₀ ∈ U' := by
    change f z₀ ∈ W
    rw [hfc]
    exact w.property
  have hnhds : (Subtype.val '' U' : Set (ComplexModel d)) ∈ 𝓝 z₀.val :=
    (V.isOpen.isOpenMap_subtype_val _ hU').mem_nhds ⟨z₀, hz₀U', rfl⟩
  have hPA : ∀ᶠ u in 𝓝 z₀.val, P₀ u ∈ eW.val.target ∧
      eW.val.symm (P₀ u) ∈ (Subtype.val : W → a.ambient) ⁻¹' a.carrier := by
    filter_upwards [hnhds] with u hu
    obtain ⟨z, hzU, rfl⟩ := hu
    let wz : W := ⟨f z, hzU⟩
    have hPz : P₀ z.val = eW.val wz := by
      change actualOpenVectorExtension V (fun z : V => (f z).val) z.val = eW.val wz
      rw [actualOpenVectorExtension_apply V _ z, heW]
    rw [hPz, eW.val.left_inv (hsrcW wz)]
    exact ⟨eW.val.map_source (hsrcW wz), hfC z⟩
  have hGd : MDifferentiableAt 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) G w :=
    (hG w).mdifferentiableAt (by simp)
  have hR := rankIn_eq_finrank_range_of_param
    (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
      ((OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y a c d).mp hreg))
    eW (hsrcW w) e' (by rw [hGw]; exact mem_complexChartAt_source _) hGd hP0 hPd hinj hPA
  -- comparison
  have hpt0 : eY.val yr = z₀.val := by
    rw [hz₀, heY]
    change D.chart yr = v₀.val
    exact (congrArg D.chart hv₀).symm.trans (D.chart_pointMap v₀)
  have heq : (fun u => e'.val (regPointMap d φ (eY.val.symm u))) =ᶠ[𝓝 z₀.val]
      (fun u => e'.val (G (eW.val.symm (P₀ u)))) := by
    filter_upwards [hnhds] with u hu
    obtain ⟨z, hzU, rfl⟩ := hu
    let wz : W := ⟨f z, hzU⟩
    have hPz : P₀ z.val = eW.val wz := by
      change actualOpenVectorExtension V (fun z : V => (f z).val) z.val = eW.val wz
      rw [actualOpenVectorExtension_apply V _ z, heW]
    rw [hPz, eW.val.left_inv (hsrcW wz), hGφ wz (hfC z), heY,
      D.chart_symm z.val (hVD z.property)]
    change e'.val (pointMap φ (D.map.base ⟨z.val, _⟩)) = e'.val (pointMap φ (a.toPoint ⟨f z, _⟩))
    rw [hfpt z (hfC z)]
  change rankIn eY e' (regPointMap d φ) univ yr =
    rankIn eW (complexChartAt (n := k) (G w)) G ((Subtype.val : W → a.ambient) ⁻¹' a.carrier) w
  have hce : complexChartAt (n := k) (G w) = e' := by rw [hGw]
  rw [hce, hL, hR, hpt0, heq.fderiv_eq]

end Bridge

end

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertBridge

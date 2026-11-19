import Hironaka.Analytic.Unibranch.OriginalSmoothSourceAnalytic
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-!
# Native smooth structure on the SAME original compact point space

Actual full scalar-compatible smooth local OIs internally produce the native
atlas and full original sheaf comparison. Uniform dimension is ordinary local
source data; compactness supplies second countability, not an input atlas.
Blueprint: `original-smooth-native-model.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open IsManifold ChartedSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalSmoothNativeModel

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaEmbeddedNativeMorphism HironakaIntrinsicMorphismGluingAnalytic

noncomputable section

variable {X : SourceReducedComplexSpace} {n : ℕ}

/-- Exactly the original smooth-local-model property with ONE dimension. -/
abbrev UniformSmoothModels (X : SourceReducedComplexSpace) (n : ℕ) : Prop :=
  ∀ x : X.obj.left, ∃ (V : Opens (ComplexModel n))
    (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V ⟶ X.obj.left),
    LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ X.obj.hom = ambientPointMap n V ∧
      x ∈ range i.base

private structure LocalModel (X : SourceReducedComplexSpace) (n : ℕ) where
  domain : Opens (ComplexModel n)
  map : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) domain ⟶ X.obj.left
  openImmersion : LocallyRingedSpace.IsOpenImmersion map
  overPoint : map ≫ X.obj.hom = ambientPointMap n domain
  nonempty : Nonempty domain

private theorem exists_localModel (h : UniformSmoothModels X n) (x : X.obj.left) :
    ∃ D : LocalModel X n, x ∈ range D.map.base := by
  obtain ⟨V, i, hi, hp, v, hv⟩ := h x
  exact ⟨⟨V, i, hi, hp, ⟨v⟩⟩, v, hv⟩

private def localModel (h : UniformSmoothModels X n) (x : X.obj.left) : LocalModel X n :=
  Classical.choose (exists_localModel h x)

private theorem localModel_covers (h : UniformSmoothModels X n) (x : X.obj.left) :
    x ∈ range (localModel h x).map.base := Classical.choose_spec (exists_localModel h x)

private abbrev LocalModel.pointMap (D : LocalModel X n) : D.domain → X.obj.left := D.map.base

private theorem LocalModel.pointOpen (D : LocalModel X n) : IsOpenEmbedding D.pointMap :=
  D.openImmersion.base_open

private def LocalModel.chart (D : LocalModel X n) :
    OpenPartialHomeomorph X.obj.left (ComplexModel n) := by
  letI := D.nonempty
  exact (D.pointOpen.toOpenPartialHomeomorph D.pointMap).symm.trans
    (D.domain.openPartialHomeomorphSubtypeCoe D.nonempty)

private theorem LocalModel.chart_source (D : LocalModel X n) :
    D.chart.source = range D.map.base := by
  simp [LocalModel.chart, LocalModel.pointMap]

private theorem LocalModel.chart_target (D : LocalModel X n) :
    D.chart.target = D.domain := by
  simp [LocalModel.chart]

private theorem LocalModel.chart_map (D : LocalModel X n) (v : D.domain) :
    D.chart (D.map.base v) = v.val := by
  have := D.nonempty
  change ((D.pointOpen.toOpenPartialHomeomorph D.pointMap).symm
    (D.pointMap v)).val = v.val
  rw [D.pointOpen.toOpenPartialHomeomorph_left_inv]

private theorem LocalModel.chart_symm (D : LocalModel X n) (v : ComplexModel n)
    (hv : v ∈ D.domain) : D.chart.symm v = D.map.base ⟨v, hv⟩ := by
  apply D.chart.injOn (D.chart.map_target (D.chart_target ▸ hv))
    (D.chart_source ▸ (show D.map.base (⟨v, hv⟩ : D.domain) ∈ range D.map.base from ⟨_, rfl⟩))
  rw [D.chart.right_inv (D.chart_target ▸ hv), D.chart_map]

/-- The SAME original point set and topology, with charts chosen from actual original OIs. -/
@[instance_reducible] def nativeChartedSpace (h : UniformSmoothModels X n) :
    ChartedSpace (ComplexModel n) X.obj.left where
  atlas := range (fun x => (localModel h x).chart)
  chartAt x := (localModel h x).chart
  mem_chart_source x := (localModel h x).chart_source ▸ localModel_covers h x
  chart_mem_atlas x := mem_range_self x

private theorem local_transition_contDiff (D E : LocalModel X n) :
    ContDiffOn ℂ ∞ (D.chart.symm.trans E.chart) (D.chart.symm.trans E.chart).source := by
  let O : Opens (ComplexModel n) :=
    ⟨(D.chart.symm.trans E.chart).source, (D.chart.symm.trans E.chart).open_source⟩
  have hOD : (O : Set (ComplexModel n)) ⊆ D.domain := by
    intro z hz
    exact D.chart_target ▸ hz.1
  let a : O → D.domain := Opens.inclusion hOD
  let A := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel n)) a (contMDiff_inclusion hOD)
  let F := A ≫ D.map
  have := E.openImmersion
  have hRange : range F.base ⊆ range E.map.base := by
    rintro _ ⟨z, rfl⟩
    have hz : D.chart.symm z.val ∈ E.chart.source := z.property.2
    rw [LocalModel.chart_source] at hz
    rwa [D.chart_symm z.val (hOD z.property)] at hz
  let L := LocallyRingedSpace.IsOpenImmersion.lift E.map F hRange
  have hfac : L ≫ E.map = F := LocallyRingedSpace.IsOpenImmersion.lift_fac E.map F hRange
  have hLp : L ≫ ambientPointMap n E.domain = ambientPointMap n O := by
    rw [← E.overPoint, ← Category.assoc, hfac]
    change (A ≫ D.map) ≫ X.obj.hom = ambientPointMap n O
    rw [Category.assoc, D.overPoint]
    exact (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
      (IN := 𝓘(ℂ, ComplexModel n)) (IP := 𝓘(ℂ, ComplexModel 0))
      (contMDiff_inclusion hOD) contMDiff_const).symm
  have hSmooth := contMDiff_native_morphism L hLp
  have hPoint (z : O) : (L.base z).val = (D.chart.symm.trans E.chart) z.val := by
    have hi : E.map.base (L.base z) = D.map.base (a z) :=
      congrArg (fun f => f.base z) hfac
    change (L.base z).val = E.chart (D.chart.symm z.val)
    rw [D.chart_symm z.val (hOD z.property), ← hi, E.chart_map]
  intro z hz
  have hS : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : O => (D.chart.symm.trans E.chart) z.val) ⟨z, hz⟩ := by
    rw [show (fun z : O => (D.chart.symm.trans E.chart) z.val) =
      (fun z : O => (L.base z).val) from funext (fun z => (hPoint z).symm)]
    exact (contMDiff_subtype_val.comp hSmooth).contMDiffAt
  exact (contMDiffAt_subtype_iff.mp hS).contDiffAt.contDiffWithinAt

/-- Actual original local OIs DERIVE all genuine native chart transitions. -/
theorem isManifold_nativeChartedSpace (h : UniformSmoothModels X n) :
    letI := nativeChartedSpace h
    IsManifold 𝓘(ℂ, ComplexModel n) ∞ X.obj.left := by
  let := nativeChartedSpace h
  apply isManifold_of_contDiffOn 𝓘(ℂ, ComplexModel n) ∞ X.obj.left
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa only [mfld_simps] using local_transition_contDiff (localModel h x) (localModel h y)

/-- An actual finite subcover consists of the SAME original smooth-model charts. -/
theorem exists_finite_native_chart_cover [CompactSpace X.obj.left]
    (h : UniformSmoothModels X n) :
    letI := nativeChartedSpace h
    ∃ s : Finset X.obj.left, ⋃ x ∈ s, (chartAt (ComplexModel n) x).source = univ := by
  let := nativeChartedSpace h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.obj.left => (chartAt (ComplexModel n) x).source)
    (fun x => (chartAt (ComplexModel n) x).open_source)
    (by rw [iUnion_source_chartAt])
  exact ⟨s, eq_univ_of_univ_subset hs⟩

/-- Compactness DERIVES the required native countability on the ORIGINAL topology. -/
theorem isComplexManifold_nativeChartedSpace [CompactSpace X.obj.left]
    (h : UniformSmoothModels X n) :
    letI := nativeChartedSpace h
    IsComplexManifold n X.obj.left := by
  let := nativeChartedSpace h
  have := isManifold_nativeChartedSpace h
  obtain ⟨s, hs⟩ := exists_finite_native_chart_cover h
  have : SecondCountableTopology X.obj.left :=
    ChartedSpace.secondCountable_of_countable_cover (ComplexModel n) hs s.finite_toSet.countable
  have : T2Space X.obj.left := X.property.1
  exact IsComplexManifold.mk

private def LocalModel.rangeOpen (D : LocalModel X n) : Opens X.obj.left :=
  ⟨range D.map.base, D.openImmersion.base_open.isOpen_range⟩

private def modelDiffeomorph [CompactSpace X.obj.left] (h : UniformSmoothModels X n)
    (x : X.obj.left) :
    letI := nativeChartedSpace h
    (localModel h x).domain ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (localModel h x).rangeOpen := by
  letI := nativeChartedSpace h
  have := isComplexManifold_nativeChartedSpace h
  let D := localModel h x
  have hAtlas : D.chart ∈ maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ X.obj.left :=
    chart_mem_maximalAtlas x
  refine {
    toFun := fun v => ⟨D.pointMap v, v, rfl⟩
    invFun := fun y => ⟨D.chart y.val,
      (by
        change D.chart y.val ∈ (D.domain : Set (ComplexModel n))
        rw [← D.chart_target]
        apply D.chart.map_source
        rw [D.chart_source]
        exact y.property)⟩
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro v
    apply Subtype.ext
    exact D.chart_map v
  · intro y
    apply Subtype.ext
    change D.map.base ⟨D.chart y.val, _⟩ = y.val
    rw [← D.chart_symm]
    exact D.chart.left_inv (D.chart_source ▸ y.property)
  · apply (ContMDiff.subtypeVal_comp_iff D.rangeOpen _).mp
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun v : D.domain => D.pointMap v)
    have hEq : (fun v : D.domain => D.pointMap v) =
        (fun v : D.domain => D.chart.symm v.val) :=
      funext (fun v => (D.chart_symm v.val v.property).symm)
    rw [hEq]
    intro v
    exact (contMDiffAt_symm_of_mem_maximalAtlas hAtlas (D.chart_target ▸ v.property)).comp v
      contMDiff_subtype_val.contMDiffAt
  · apply (ContMDiff.subtypeVal_comp_iff D.domain _).mp
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : D.rangeOpen => D.chart y.val)
    intro y
    exact (contMDiffAt_of_mem_maximalAtlas hAtlas (D.chart_source ▸ y.property)).comp y
      contMDiff_subtype_val.contMDiffAt

section NativeMaps

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [ChartedSpace (ComplexModel n) N]
  [IsComplexManifold n M] [IsComplexManifold n N]

-- Existing native map/scalar and inverse engines, with zero separate credit.
private theorem nativeMap_point (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap n N = ambientPointMap n M :=
  (ChartedSpace.locallyRingedSpace_comp (IP := 𝓘(ℂ, ComplexModel 0)) hf contMDiff_const).symm

private def nativeLRSIso
    (e : M ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ N) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) N where
  hom := ChartedSpace.locallyRingedSpaceMap e e.contMDiff
  inv := ChartedSpace.locallyRingedSpaceMap e.symm e.symm.contMDiff
  hom_inv_id := by
    rw [← ChartedSpace.locallyRingedSpace_comp]
    have h : (e.symm ∘ e : M → M) = id := funext e.symm_apply_apply
    simpa only [h] using ChartedSpace.locallyRingedSpace_id 𝓘(ℂ, ComplexModel n) M
  inv_hom_id := by
    rw [← ChartedSpace.locallyRingedSpace_comp]
    have h : (e ∘ e.symm : N → N) = id := funext e.apply_symm_apply
    simpa only [h] using ChartedSpace.locallyRingedSpace_id 𝓘(ℂ, ComplexModel n) N

end NativeMaps

/-- Actual ORIGINAL smooth local models derive a FULL original-category native
model isomorphism, on the SAME original point space with literal point identity. -/
theorem exists_original_native_model_iso [CompactSpace X.obj.left]
    (h : UniformSmoothModels X n) :
    letI := nativeChartedSpace h
    letI := isComplexManifold_nativeChartedSpace h
    ∃ E : SourceReducedComplexSpace.ofClosedAnalytic (n := n) (univ : Set X.obj.left)
        (isComplexAnalyticSubset_univ (n := n)) ≅ X,
      ∀ y, E.hom.hom.left.base y = y.val := by
  let := nativeChartedSpace h
  have := isComplexManifold_nativeChartedSpace h
  let Q := actualSubspaceUnivIso (n := n) (M := X.obj.left)
  let T := actualSubspaceLocallyRingedSpace (n := n) (univ : Set X.obj.left)
  let σ := subspacePointMap (n := n) (univ : Set X.obj.left)
  let U (x : X.obj.left) :=
    ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) (localModel h x).domain
  let j (x : X.obj.left) : U x ⟶ X.obj.left := (localModel h x).map
  have hJ : ∀ x, ∃ J : U x ⟶ T,
      LocallyRingedSpace.IsOpenImmersion J ∧
      J ≫ σ = ambientPointMap n (localModel h x).domain ∧
      ∀ v, (J.base v).val = (j x).base v := by
    intro x
    let D := localModel h x
    let e := modelDiffeomorph h x
    let I := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel n))
      (IN := 𝓘(ℂ, ComplexModel n)) (Subtype.val : D.rangeOpen → X.obj.left)
      contMDiff_subtype_val
    let L := (nativeLRSIso e).hom ≫ I
    let J := L ≫ Q.inv
    have hOI : LocallyRingedSpace.IsOpenImmersion J := by
      dsimp only [J, L, I]
      infer_instance
    have hp : J ≫ σ = ambientPointMap n D.domain := by
      change ((nativeLRSIso e).hom ≫ I) ≫ Q.inv ≫ σ = _
      rw [actualSubspaceUnivIso_inv_point, Category.assoc, nativeMap_point]
      exact nativeMap_point e e.contMDiff
    have hQ (z : X.obj.left) : (Q.inv.base z).val = z :=
      congrArg (fun f => f.base z) Q.inv_hom_id
    refine ⟨J, hOI, hp, ?_⟩
    intro v
    exact hQ (D.pointMap v)
  choose J hJOI hJp hJbase using hJ
  have : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := fun x => (localModel h x).openImmersion
  have : ∀ x, LocallyRingedSpace.IsOpenImmersion (J x) := hJOI
  have hcover : ∀ x : X.obj.left, ∃ (i : X.obj.left) (v : U i), (j i).base v = x := by
    intro x
    obtain ⟨v, hv⟩ := localModel_covers h x
    exact ⟨x, v, hv⟩
  have hNativeCharts (x : X.obj.left) :
      hasAnalyticCharts (Over.mk (ambientPointMap n (localModel h x).domain)) := by
    let D := localModel h x
    exact hasAnalyticCharts_of_openImmersion _ _
      (hasAnalyticCharts_model D.domain univ (isComplexAnalyticSubset_univ (n := n)))
      (actualSubspaceUnivIso (n := n) (M := D.domain)).inv
      actualSubspaceUnivIso_inv_point
  have hCompat (a b : X.obj.left) :
      pullback.fst (j a) (j b) ≫ J a = pullback.snd (j a) (j b) ≫ J b := by
    let P := pullback (j a) (j b)
    let σP := pullback.fst (j a) (j b) ≫ ambientPointMap n (localModel h a).domain
    have hP : hasAnalyticCharts (Over.mk σP) :=
      hasAnalyticCharts_of_openImmersion σP _ (hNativeCharts a) (pullback.fst (j a) (j b)) rfl
    apply HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq σP hP
    · rw [Category.assoc, hJp a]
    · rw [Category.assoc, hJp b, ← (localModel h b).overPoint,
        ← Category.assoc, ← pullback.condition, Category.assoc, (localModel h a).overPoint]
    · ext v
      apply Subtype.ext
      exact (hJbase a _).trans
        ((congrArg (fun f => f.base v) (pullback.condition (f := j a) (g := j b))).trans
          (hJbase b _).symm)
  obtain ⟨G, hG, _⟩ := HironakaIntrinsicMorphismGluing.exists_unique_over U j hcover
    X.obj.hom σ J hCompat (fun x => (hJp x).trans (localModel h x).overPoint.symm)
  let g := G.left
  have hgbase (x : X.obj.left) : (g.base x).val = x := by
    obtain ⟨i, v, rfl⟩ := hcover x
    exact (congrArg (fun f => (f.base v).val) (hG i)).trans (hJbase i v)
  have hgOpen : IsOpenEmbedding g.base := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap g.base.hom.continuous
    · intro x y hxy
      exact (hgbase x).symm.trans ((congrArg Subtype.val hxy).trans (hgbase y))
    · intro A hA
      have hImage : g.base '' A = (Subtype.val : ↥(univ : Set X.obj.left) → X.obj.left) ⁻¹' A := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          change (g.base x).val ∈ A
          rwa [hgbase]
        · intro hy
          exact ⟨y.val, hy, Subtype.ext (hgbase y.val)⟩
      rw [hImage]
      exact hA.preimage continuous_subtype_val
  have hsurj : Function.Surjective g.base :=
    fun y => ⟨y.val, Subtype.ext (hgbase y.val)⟩
  have : ∀ x, IsIso (g.stalkMap x) := by
    intro x
    obtain ⟨i, v, rfl⟩ := hcover x
    have hc : IsIso ((j i ≫ g).stalkMap v) := by
      rw [hG i]
      infer_instance
    rw [LocallyRingedSpace.stalkMap_comp] at hc
    have : IsIso (g.stalkMap ((j i).base v) ≫ (j i).stalkMap v) := hc
    exact IsIso.of_isIso_comp_right _ ((j i).stalkMap v)
  have : Epi g.base := (TopCat.epi_iff_surjective _).mpr hsurj
  have : LocallyRingedSpace.IsOpenImmersion g := LocallyRingedSpace.IsOpenImmersion.of_stalk_iso g hgOpen
  have : IsIso g := LocallyRingedSpace.IsOpenImmersion.to_iso g
  let E := (asIso g).symm
  have hp : E.hom ≫ X.obj.hom = σ := by
    have hgσ : g ≫ σ = X.obj.hom := Over.w G
    calc
      E.hom ≫ X.obj.hom = E.hom ≫ (g ≫ σ) :=
        congrArg (fun f => E.hom ≫ f) hgσ.symm
      _ = σ := (asIso g).inv_hom_id_assoc σ
  let F : SourceReducedComplexSpace.ofClosedAnalytic (n := n) (univ : Set X.obj.left)
      (isComplexAnalyticSubset_univ (n := n)) ≅ X := ObjectProperty.isoMk _ (Over.isoMk E hp)
  refine ⟨F, ?_⟩
  intro y
  exact (hgbase (E.hom.base y)).symm.trans
    (congrArg (fun f => (f.base y).val) (asIso g).inv_hom_id)

end

end Hironaka.Analytic.Unibranch.OriginalSmoothNativeModel

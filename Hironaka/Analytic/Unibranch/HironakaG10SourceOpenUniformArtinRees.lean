import Hironaka.Analytic.Unibranch.HironakaG10SourceUniformArtinRees
import Hironaka.Resolution.HironakaG10HirIdealGerms
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic

/-! # Uniform Artin--Rees for ideal families defined on an open domain -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Hironaka
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaG10ChowUniformArtinRees HironakaG10PNIdealNoetherModel
  HironakaG10AnalyticChartsUniformArtinRees HironakaG10OpenImmersionUniformArtinRees
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaResolutionSpaceComplex HironakaIntrinsicMorphismGluingAnalytic

/-- The local analytic-model clause passes through an open immersion over the complex point
(the chart part of `hasAnalyticCharts_of_openImmersion`, without any countability). -/
private theorem charts_of_openImmersion {H T : LocallyRingedSpace}
    (σH : H ⟶ complexPoint) (σT : T ⟶ complexPoint)
    (hT : ∀ x : T, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ T,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σT = (modelOver U C).hom ∧ x ∈ range i.base)
    (j : H ⟶ T) [hj : LocallyRingedSpace.IsOpenImmersion j] (hjp : j ≫ σT = σH) :
    ∀ x : H, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ H,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σH = (modelOver U C).hom ∧
          x ∈ range i.base := by
  intro x
  obtain ⟨n, V, C, hC, i, hi, hip, c, hcx⟩ := hT (j.base x)
  change C at c
  change actualSubspaceLocallyRingedSpace (n := n) C ⟶ T at i
  change i.base c = j.base x at hcx
  change i ≫ σT = subspacePointMap (n := n) C at hip
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let Q : Opens (TopCat.of C) :=
    ⟨i.base ⁻¹' range j.base, hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  obtain ⟨O, hO, hOQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let A : Opens V := ⟨O, hO⟩
  have hcA : c.val ∈ A := by
    change c ∈ Subtype.val ⁻¹' O
    rw [hOQ]
    change i.base c ∈ range j.base
    rw [hcx]
    exact ⟨x, rfl⟩
  let C' : Set A := (Subtype.val : A → V) ⁻¹' C
  let R := actualOpenSubspaceMap (n := n) C A ≫ i
  have : LocallyRingedSpace.IsOpenImmersion R := by
    dsimp [R]
    infer_instance
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (⟨y.val.val, y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val, y.property⟩ : C) ∈ (Q : Set C)
      rw [← hOQ]
      exact y.val.property
    exact hy
  let L := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : L ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  have : LocallyRingedSpace.IsOpenImmersion L := by
    let : IsIso (pullback.snd j R) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j R hR
    dsimp [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hLp : L ≫ σH = subspacePointMap (n := n) C' := by
    rw [← hjp, ← Category.assoc, hfac]
    dsimp [R]
    rw [Category.assoc, hip]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let c' : C' := ⟨⟨c.val, hcA⟩, c.property⟩
  have hLc : L.base c' = x := by
    apply hj.base_open.injective
    calc
      j.base (L.base c') = R.base c' := congrArg (fun f => f.base c') hfac
      _ = j.base x := hcx
  have hC' : IsComplexAnalyticSubset (n := n) C' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC A
  obtain ⟨V', D, hD, k, hk, hkp, z, hzc⟩ := exists_model_chart hC' c'
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, V', D, hD, k ≫ L, inferInstance, ?_, z, ?_⟩
  · rw [Category.assoc, hLp]
    exact hkp
  · change L.base (k.base z) = x
    rw [hzc, hLc]

/-- Pulling a family generated on an open domain to a space mapping entirely
into that domain makes it a locally finitely generated family there. -/
theorem isLocallyFinitelyGenerated_pull_of_range_subset
    {X Y : LocallyRingedSpace.{0}} (f : Y ⟶ X) (V : Set X)
    (J : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hJ : IsLocallyFinitelyGeneratedOn X V J) (hf : ∀ y : Y, f.base y ∈ V) :
    IsLocallyFinitelyGenerated Y (pullFamily f J) := by
  intro y
  obtain ⟨W,hyW,r,s,hs⟩ := hJ (f.base y) (hf y)
  refine ⟨(Opens.map f.base).obj W,hyW,r,fun i => f.c.app (op W) (s i),?_⟩
  intro y' hy'
  rw [pullFamily, hs (f.base y') hy' (hf y'), Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i => LocallyRingedSpace.stalkMap_germ_apply f W y' hy' (s i)))

/-- On an open domain, local finite generation of two native ideal families
is enough to obtain one uniform exponent near each point of that domain. -/
theorem exists_local_uniform_artinRees_on (X : SourceReducedComplexSpace)
    (V : Set X.obj.left) (hV : IsOpen V)
    (I K : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X.obj.left V I)
    (hK : IsLocallyFinitelyGeneratedOn X.obj.left V K) (x : X.obj.left) (hx : x ∈ V) :
    ∃ α : ℕ, ∃ O : Set X.obj.left, IsOpen O ∧ x ∈ O ∧ O ⊆ V ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α := by
  let W : Opens X.obj.left := ⟨V,hV⟩
  let Y : LocallyRingedSpace := X.obj.left.restrict W.isOpenEmbedding
  let j : Y ⟶ X.obj.left := X.obj.left.ofRestrict W.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion j := LocallyRingedSpace.IsOpenImmersion.ofRestrict _ _
  have hj : ∀ y : Y, j.base y ∈ V := fun y => y.property
  have hc := charts_of_openImmersion (j ≫ X.obj.hom) X.obj.hom X.property.2.2 j rfl
  have hcharts : HasAnalyticModelCharts Y := fun z => by
    obtain ⟨n,U,C,hC,i,hi,_,hz⟩ := hc z
    exact ⟨n,U,C,hC,i,hi,hz⟩
  have hI' := isLocallyFinitelyGenerated_pull_of_range_subset j V I hI hj
  have hK' := isLocallyFinitelyGenerated_pull_of_range_subset j V K hK hj
  let x' : Y := ⟨x,hx⟩
  have hlocal := exists_charts_uniform_artinRees hcharts (pullFamily j I) (pullFamily j K) hI' hK' x'
  obtain ⟨α,O,hO,hxO,hAR⟩ := exists_uniform_artinRees_of_openImmersion j I K x' hlocal
  refine ⟨α,O ∩ V,hO.inter hV,⟨hxO,hx⟩,inter_subset_right,?_⟩
  exact fun y hy => hAR y hy.1

/-- A single exponent works on an open neighbourhood of a compact subset
of the domain on which both ideal families are locally finitely generated. -/
theorem exists_compact_uniform_artinRees_on (X : SourceReducedComplexSpace)
    (V : Set X.obj.left) (hV : IsOpen V)
    (I K : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X.obj.left V I)
    (hK : IsLocallyFinitelyGeneratedOn X.obj.left V K)
    (Q : Set X.obj.left) (hQ : IsCompact Q) (hQV : Q ⊆ V) :
    ∃ α : ℕ, ∃ O : Set X.obj.left, IsOpen O ∧ Q ⊆ O ∧ O ⊆ V ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α := by
  obtain ⟨O,α,hO,hQO,hAR⟩ := exists_artinReesOn_of_local I K Q hQ
    (fun y hy => by
      obtain ⟨a,U,hU,hyU,_,hlocal⟩ := exists_local_uniform_artinRees_on X V hV I K hI hK y (hQV hy)
      exact ⟨U,hU.mem_nhds hyU,a,hlocal⟩)
  exact ⟨α,O ∩ V,hO.inter hV,fun y hy => ⟨hQO hy,hQV hy⟩,inter_subset_right,
    fun y hy => hAR y hy.1⟩

end Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees

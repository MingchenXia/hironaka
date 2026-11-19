import Hironaka.Analytic.Unibranch.Resolution
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Topology.Category.TopCat.Limits.Products

/-! # Actual arbitrary disjoint native analytic sources

The existing native coproduct and full scalar descent are used unchanged.
Paracompactness is derived componentwise, with no finite/compact/countable
restriction. Proper maps over a genuine disjoint open target cover assemble
into the same actual descended native map. Blueprint first:
`hironaka-g1-native-disjoint-coproduct.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeDisjointCoproduct

open Hironaka
  Hironaka.HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace

noncomputable section

/-- Arbitrary topological sums preserve genuine paracompactness. -/
theorem paracompactSpace_sigma {ι : Type} {T : ι → Type}
    [∀ i, TopologicalSpace (T i)] [∀ i, ParacompactSpace (T i)] :
    ParacompactSpace (Σ i, T i) where
  locallyFinite_refinement α s ho hc := by
    have hcover (i : ι) : (⋃ a, Sigma.mk i ⁻¹' s a) = univ := by
      rw [← preimage_iUnion, hc, preimage_univ]
    choose v hvopen hvcover hvfinite hvsub using fun i =>
      precise_refinement (fun a => Sigma.mk i ⁻¹' s a)
        (fun a => (ho a).preimage continuous_sigmaMk) (hcover i)
    refine ⟨Σ _ : ι, α, fun ia => Sigma.mk ia.1 '' v ia.1 ia.2,
      fun ia => isOpenMap_sigmaMk _ (hvopen ia.1 ia.2), ?_, ?_, ?_⟩
    · apply iUnion_eq_univ_iff.mpr
      rintro ⟨i, x⟩
      obtain ⟨a, ha⟩ := iUnion_eq_univ_iff.mp (hvcover i) x
      exact ⟨⟨i, a⟩, x, ha, rfl⟩
    · rintro ⟨i, x⟩
      obtain ⟨N, hN, hfin⟩ := hvfinite i x
      obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.mp hN
      refine ⟨Sigma.mk i '' O, (isOpenMap_sigmaMk O hO).mem_nhds ⟨x, hxO, rfl⟩,
        (hfin.image (fun a => (⟨i, a⟩ : Σ _ : ι, α))).subset ?_⟩
      rintro ⟨j, a⟩ ⟨_, ⟨z, hz, rfl⟩, w, hw, he⟩
      have hij : i = j := congrArg Sigma.fst he
      subst j
      have hwz : w = z := sigma_mk_injective he
      subst w
      exact ⟨a, ⟨z, hz, hON hw⟩, rfl⟩
    · rintro ⟨i, a⟩
      refine ⟨a, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hvsub i a hx

variable {ι : Type} (Z : ι → SourceReducedComplexSpace)

private def diagram : Discrete ι ⥤ LocallyRingedSpace.{0} :=
  Discrete.functor (fun i => (Z i).obj.left)

private def raw : LocallyRingedSpace.{0} := LocallyRingedSpace.coproduct (diagram Z)

private def rawCofan : Cocone (diagram Z) := LocallyRingedSpace.coproductCofan (diagram Z)

private def rawColimit : IsColimit (rawCofan Z) :=
  LocallyRingedSpace.coproductCofanIsColimit (diagram Z)

private def rawInclusion (i : ι) : (Z i).obj.left ⟶ raw Z :=
  (rawCofan Z).ι.app (Discrete.mk i)

private def scalarMap : raw Z ⟶ complexPoint :=
  (rawColimit Z).desc (Cofan.mk complexPoint (fun i => (Z i).obj.hom))

private theorem rawInclusion_scalar (i : ι) :
    rawInclusion Z i ≫ scalarMap Z = (Z i).obj.hom :=
  (rawColimit Z).fac (Cofan.mk complexPoint (fun i => (Z i).obj.hom)) (Discrete.mk i)

private def sheafDiagram := diagram Z ⋙ LocallyRingedSpace.forgetToSheafedSpace

private def topDiagram := sheafDiagram Z ⋙ SheafedSpace.forget CommRingCat.{0}

private def rawTopIso : (raw Z).toTopCat ≅ TopCat.of (Σ i, (Z i).obj.left) :=
  preservesColimitIso (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := topDiagram Z)) ≪≫
      TopCat.sigmaIsoSigma (fun i => (Z i).obj.left.toTopCat)

private theorem rawInclusion_topIso (i : ι) :
    (rawInclusion Z i).base ≫ (rawTopIso Z).hom =
      TopCat.sigmaι (fun j => (Z j).obj.left.toTopCat) i := by
  let P := preservesColimitIso (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z)
  let Q := HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := topDiagram Z))
  let R := TopCat.sigmaIsoSigma (fun j => (Z j).obj.left.toTopCat)
  exact (show (rawInclusion Z i).base ≫ (rawTopIso Z).hom =
      (((rawInclusion Z i).base ≫ P.hom) ≫ Q.hom) ≫ R.hom from rfl).trans
    ((congrArg (fun K => (K ≫ Q.hom) ≫ R.hom)
      (ι_preservesColimitIso_hom (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z) (Discrete.mk i))).trans
      ((congrArg (fun K => K ≫ R.hom)
        (HasColimit.isoOfNatIso_ι_hom (Discrete.natIsoFunctor (F := topDiagram Z)) (Discrete.mk i))).trans
          (TopCat.sigmaIsoSigma_hom_ι (fun j => (Z j).obj.left.toTopCat) i)))

private def rawPointHomeomorph : raw Z ≃ₜ (Σ i, (Z i).obj.left) :=
  TopCat.homeoOfIso (rawTopIso Z)

private theorem rawPointHomeomorph_inclusion (i : ι) (z : (Z i).obj.left) :
    rawPointHomeomorph Z ((rawInclusion Z i).base z) = Sigma.mk i z :=
  ConcreteCategory.congr_hom (rawInclusion_topIso Z i) z

private theorem rawInclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (rawInclusion Z i) :=
  SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion (sheafDiagram Z) (Discrete.mk i)

private theorem rawJointlySurjective (x : raw Z) :
    ∃ (i : ι) (z : (Z i).obj.left), (rawInclusion Z i).base z = x := by
  cases hpoint : rawPointHomeomorph Z x with
  | mk i z =>
    exact ⟨i, z, (rawPointHomeomorph Z).injective
      ((rawPointHomeomorph_inclusion Z i z).trans hpoint.symm)⟩

private theorem rawDisjoint : Pairwise (fun i j =>
    Disjoint (range (rawInclusion Z i).base) (range (rawInclusion Z j).base)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  have hs : (Sigma.mk i a : Σ k, (Z k).obj.left) = Sigma.mk j b :=
    (rawPointHomeomorph_inclusion Z i a).symm.trans
      ((congrArg (rawPointHomeomorph Z) (ha.trans hb.symm)).trans
        (rawPointHomeomorph_inclusion Z j b))
  exact hij (congrArg Sigma.fst hs)

private theorem rawT2 : T2Space (raw Z) := by
  have : ∀ i, T2Space (Z i).obj.left := fun i => (Z i).property.1
  exact (rawPointHomeomorph Z).isEmbedding.t2Space

private theorem rawAnalyticAtlas :
    ∀ x : raw Z, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ f : (modelOver U C).left ⟶ raw Z,
        LocallyRingedSpace.IsOpenImmersion f ∧
        f ≫ scalarMap Z = (modelOver U C).hom ∧ x ∈ range f.base := by
  intro x
  obtain ⟨i, z, rfl⟩ := rawJointlySurjective Z x
  obtain ⟨n, U, C, hC, f, hf, hp, c, hc⟩ := (Z i).property.2.2 z
  refine ⟨n, U, C, hC, f ≫ rawInclusion Z i,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ f hf _ (rawInclusion_isOpenImmersion Z i), ?_,
    c, congrArg (rawInclusion Z i).base hc⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun K => f ≫ K) (rawInclusion_scalar Z i)).trans hp)

private theorem rawParacompact : ParacompactSpace (raw Z) := by
  let : ∀ i, ParacompactSpace (Z i).obj.left := fun i => (Z i).property.2.1
  let : ParacompactSpace (Σ i, (Z i).obj.left) := paracompactSpace_sigma
  exact (rawPointHomeomorph Z).paracompactSpace_iff.mpr inferInstance

/-- The SAME actual native coproduct, with ORIGINAL properties derived. -/
def coproduct : SourceReducedComplexSpace := by
  refine ⟨Over.mk (scalarMap Z), rawT2 Z, ?_, rawAnalyticAtlas Z⟩
  exact rawParacompact Z

/-- The genuine entire native cofan inclusion as an ORIGINAL morphism. -/
def inclusion (i : ι) : Z i ⟶ coproduct Z :=
  ObjectProperty.homMk (Over.homMk (rawInclusion Z i) (rawInclusion_scalar Z i))

/-- The genuine coproduct point space, with no index-countability premise. -/
def pointHomeomorph : (coproduct Z).obj.left ≃ₜ (Σ i, (Z i).obj.left) :=
  rawPointHomeomorph Z

theorem pointHomeomorph_inclusion (i : ι) (z : (Z i).obj.left) :
    pointHomeomorph Z ((inclusion Z i).hom.left.base z) = Sigma.mk i z :=
  rawPointHomeomorph_inclusion Z i z

theorem inclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (inclusion Z i).hom.left :=
  rawInclusion_isOpenImmersion Z i

theorem inclusion_jointly_surjective (x : (coproduct Z).obj.left) :
    ∃ (i : ι) (z : (Z i).obj.left), (inclusion Z i).hom.left.base z = x :=
  rawJointlySurjective Z x

theorem inclusion_pairwise_disjoint : Pairwise (fun i j =>
    Disjoint (range (inclusion Z i).hom.left.base) (range (inclusion Z j).hom.left.base)) :=
  rawDisjoint Z

/-- Local actual smooth models may have unrelated dimensions. -/
theorem isSmooth_coproduct (h : ∀ i, (Z i).IsSmooth) : (coproduct Z).IsSmooth := by
  intro x
  obtain ⟨i, z, rfl⟩ := inclusion_jointly_surjective Z x
  obtain ⟨n, V, f, hf, hp, v, hv⟩ := h i z
  refine ⟨n, V, f ≫ (inclusion Z i).hom.left,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ f hf _ (inclusion_isOpenImmersion Z i), ?_,
    v, congrArg (inclusion Z i).hom.left.base hv⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun K => f ≫ K) (Over.w (inclusion Z i).hom)).trans hp)

variable {X : SourceReducedComplexSpace}

private def rawDesc (F : ∀ i, Z i ⟶ X) : (coproduct Z).obj.left ⟶ X.obj.left :=
  (rawColimit Z).desc (Cofan.mk X.obj.left (fun i => (F i).hom.left))

private theorem rawDesc_fac (F : ∀ i, Z i ⟶ X) (i : ι) :
    (inclusion Z i).hom.left ≫ rawDesc Z F = (F i).hom.left :=
  (rawColimit Z).fac (Cofan.mk X.obj.left (fun i => (F i).hom.left)) (Discrete.mk i)

private theorem rawDesc_scalar (F : ∀ i, Z i ⟶ X) :
    rawDesc Z F ≫ X.obj.hom = (coproduct Z).obj.hom := by
  apply (rawColimit Z).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun K => K ≫ X.obj.hom) (rawDesc_fac Z F i.as)).trans
      ((Over.w (F i.as).hom).trans (rawInclusion_scalar Z i.as).symm))

/-- The EXISTING native entire coproduct descent retains the scalar square. -/
def desc (F : ∀ i, Z i ⟶ X) : coproduct Z ⟶ X :=
  ObjectProperty.homMk (Over.homMk (rawDesc Z F) (rawDesc_scalar Z F))

theorem inclusion_desc (F : ∀ i, Z i ⟶ X) (i : ι) :
    inclusion Z i ≫ desc Z F = F i := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawDesc_fac Z F i

theorem hom_ext (F G : coproduct Z ⟶ X)
    (h : ∀ i, inclusion Z i ≫ F = inclusion Z i ≫ G) : F = G := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (rawColimit Z).hom_ext
  intro i
  exact congrArg (fun K : Z i.as ⟶ X => K.hom.left) (h i.as)

/-- Genuine proper piece maps over a disjoint native open target cover give a
proper SAME descended native morphism, for an arbitrary index type. -/
theorem desc_isProperMap_of_disjoint_cover {Y : SourceReducedComplexSpace}
    {T : ι → SourceReducedComplexSpace} (j : ∀ i, T i ⟶ Y)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ y : Y.obj.left, ∃ (i : ι) (t : (T i).obj.left), (j i).hom.left.base t = y)
    (hdisj : Pairwise fun i k =>
      Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base))
    (q : ∀ i, Z i ⟶ T i) (hq : ∀ i, IsProperMap (q i).hom.left.base) :
    IsProperMap (desc Z (fun i => q i ≫ j i)).hom.left.base := by
  let f := desc Z (fun i => q i ≫ j i)
  have hpoint (i : ι) (z : (Z i).obj.left) :
      f.hom.left.base ((inclusion Z i).hom.left.base z) =
        (j i).hom.left.base ((q i).hom.left.base z) :=
    congrArg (fun k : Z i ⟶ Y => k.hom.left.base z)
      (inclusion_desc Z (fun i => q i ≫ j i) i)
  have hlabel (i k : ι) (t : (T i).obj.left) (u : (T k).obj.left)
      (he : (j i).hom.left.base t = (j k).hom.left.base u) : i = k := by
    by_contra hne
    exact disjoint_left.mp (hdisj hne) ⟨t, rfl⟩ ⟨u, he.symm⟩
  have himage (i : ι) (S : Set (coproduct Z).obj.left) :
      (j i).hom.left.base ⁻¹' (f.hom.left.base '' S) =
        (q i).hom.left.base '' ((inclusion Z i).hom.left.base ⁻¹' S) := by
    ext t
    constructor
    · rintro ⟨z, hz, he⟩
      obtain ⟨k, u, rfl⟩ := inclusion_jointly_surjective Z z
      rw [hpoint] at he
      have hki := hlabel k i ((q k).hom.left.base u) t he
      subst k
      exact ⟨u, hz, (hj i).base_open.injective he⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(inclusion Z i).hom.left.base z, hz, hpoint i z⟩
  have hclosed : IsClosedMap f.hom.left.base := by
    intro S hS
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨i, t, rfl⟩ := hcover y
    have htrace : IsClosed ((j i).hom.left.base ⁻¹' (f.hom.left.base '' S)) := by
      rw [himage]
      exact (hq i).isClosedMap _ (hS.preimage (inclusion Z i).hom.left.base.hom.continuous)
    let V := ((j i).hom.left.base ⁻¹' (f.hom.left.base '' S))ᶜ
    have hV : IsOpen V := htrace.isOpen_compl
    have hVO : IsOpen ((j i).hom.left.base '' V) := (hj i).base_open.isOpenMap V hV
    apply Filter.mem_of_superset (hVO.mem_nhds ⟨t, hy, rfl⟩)
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hfibre (y : Y.obj.left) : IsCompact (f.hom.left.base ⁻¹' {y}) := by
    obtain ⟨i, t, rfl⟩ := hcover y
    have he : f.hom.left.base ⁻¹' {(j i).hom.left.base t} =
        (inclusion Z i).hom.left.base '' ((q i).hom.left.base ⁻¹' {t}) := by
      ext z
      constructor
      · intro hz
        obtain ⟨k, u, rfl⟩ := inclusion_jointly_surjective Z z
        change f.hom.left.base ((inclusion Z k).hom.left.base u) = (j i).hom.left.base t at hz
        rw [hpoint] at hz
        have hki := hlabel k i ((q k).hom.left.base u) t hz
        subst k
        exact ⟨u, (hj i).base_open.injective hz, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        change (q i).hom.left.base u = t at hu
        change f.hom.left.base ((inclusion Z i).hom.left.base u) = (j i).hom.left.base t
        rw [hpoint, hu]
    rw [he]
    exact ((hq i).isCompact_preimage isCompact_singleton).image
      (inclusion Z i).hom.left.base.hom.continuous
  exact isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨f.hom.left.base.hom.continuous, hclosed, hfibre⟩


end

end Hironaka.Analytic.Unibranch.HironakaG1NativeDisjointCoproduct

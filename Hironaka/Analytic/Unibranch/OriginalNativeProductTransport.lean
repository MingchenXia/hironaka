import Hironaka.Analytic.Unibranch.OriginalNativeProductUniversal

/-! Actual full native cylinder transport, with genuine open-image geometry.
Blueprint first: `original-native-product-transport.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductTransport
noncomputable section
open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace
  OriginalNativeProductWindow OriginalNativeProductUniversal
open scoped ProductComplexManifold

variable {X Y Z A : SourceReducedComplexSpace}

/-- The true full native pair constructed from the two actual projection maps. -/
def productMap (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) : productSpace e r ⟶ productSpace d r :=
  (exists_unique_pair d r (firstToChart e r ≫ F) (second e r)).choose

theorem productMap_first (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) :
    productMap e d r F ≫ firstToChart d r = firstToChart e r ≫ F :=
  (exists_unique_pair d r (firstToChart e r ≫ F) (second e r)).choose_spec.1.1

theorem productMap_second (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) :
    productMap e d r F ≫ second d r = second e r :=
  (exists_unique_pair d r (firstToChart e r ≫ F) (second e r)).choose_spec.1.2

theorem productMap_point (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) (p : (productSpace e r).obj.left) :
    ((productMap e d r F).hom.left.base p).val =
      ((F.hom.left.base ⟨p.val.1,p.property⟩).val,p.val.2) := by
  apply Prod.ext
  · exact congrArg Subtype.val
      (congrArg (fun a => a.hom.left.base p) (productMap_first e d r F))
  · exact congrArg Subtype.val
      (congrArg (fun a => a.hom.left.base p) (productMap_second e d r F))

theorem hom_ext (e : LocalEmbedding X) (r : ℕ) (H K : A ⟶ productSpace e r)
    (hfirst : H ≫ firstToChart e r = K ≫ firstToChart e r)
    (hsecond : H ≫ second e r = K ≫ second e r) : H = K :=
  (exists_unique_pair e r (H ≫ firstToChart e r) (H ≫ second e r)).unique
    ⟨rfl,rfl⟩ ⟨hfirst.symm,hsecond.symm⟩

theorem productMap_id (e : LocalEmbedding X) (r : ℕ) :
    productMap e e r (𝟙 (chartSpace e)) = 𝟙 (productSpace e r) := by
  apply hom_ext e r
  · simpa only [Category.comp_id,Category.id_comp] using productMap_first e e r (𝟙 _)
  · simpa only [Category.id_comp] using productMap_second e e r (𝟙 _)

theorem productMap_comp (e : LocalEmbedding X) (d : LocalEmbedding Y) (c : LocalEmbedding Z) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) (G : chartSpace d ⟶ chartSpace c) :
    productMap e d r F ≫ productMap d c r G = productMap e c r (F ≫ G) := by
  apply hom_ext c r
  · rw [Category.assoc,productMap_first,← Category.assoc,productMap_first,Category.assoc,productMap_first]
  · rw [Category.assoc,productMap_second,productMap_second,productMap_second]

def productIso (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (I : chartSpace e ≅ chartSpace d) : productSpace e r ≅ productSpace d r where
  hom := productMap e d r I.hom
  inv := productMap d e r I.inv
  hom_inv_id := (productMap_comp e d e r I.hom I.inv).trans
    ((congrArg (productMap e e r) I.hom_inv_id).trans (productMap_id e r))
  inv_hom_id := (productMap_comp d e d r I.inv I.hom).trans
    ((congrArg (productMap d d r) I.inv_hom_id).trans (productMap_id d r))

private def openLift {B C D : SourceReducedComplexSpace} (i : B ⟶ D) (a : C ⟶ D)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hr : range a.hom.left.base ⊆ range i.hom.left.base) : C ⟶ B := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left a.hom.left hr
  have hfac : l ≫ i.hom.left = a.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hp : l ≫ B.obj.hom = C.obj.hom := by
    calc
      _ = l ≫ (i.hom.left ≫ D.obj.hom) := congrArg (fun t => l ≫ t) (Over.w i.hom).symm
      _ = (l ≫ i.hom.left) ≫ D.obj.hom := (Category.assoc _ _ _).symm
      _ = a.hom.left ≫ D.obj.hom := congrArg (fun t => t ≫ D.obj.hom) hfac
      _ = _ := Over.w a.hom
  exact ObjectProperty.homMk (Over.homMk l hp)

private theorem openLift_fac {B C D : SourceReducedComplexSpace} (i : B ⟶ D) (a : C ⟶ D)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hr : range a.hom.left.base ⊆ range i.hom.left.base) : openLift i a hi hr ≫ i = a := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr

/-- An actual native open immersion internally gives an actual product open immersion. -/
theorem productMap_isOpenImmersion (e : LocalEmbedding X) (d : LocalEmbedding Y) (r : ℕ)
    (F : chartSpace e ⟶ chartSpace d) (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left) :
    LocallyRingedSpace.IsOpenImmersion (productMap e d r F).hom.left := by
  have hopen : IsOpen (range F.hom.left.base : Set d.carrier) := hF.base_open.isOpen_range
  obtain ⟨U,hU,htrace⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hopen
  let W : Opens (productAmbient d r) := ⟨Prod.fst ⁻¹' U,hU.preimage continuous_fst⟩
  let q := windowFirstToChart d r W
  have hrq : range q.hom.left.base ⊆ range F.hom.left.base := by
    rintro _ ⟨p,rfl⟩
    change windowCarrier d r W at p
    exact (Set.ext_iff.mp htrace _).mp p.val.property
  let k₁ := openLift F q hF hrq
  have hk₁ : k₁ ≫ F = q := openLift_fac F q hF hrq
  obtain ⟨K,hK,_⟩ := exists_unique_pair e r k₁ (windowSecond d r W)
  let jW := windowInclusion d r W
  have hjW : LocallyRingedSpace.IsOpenImmersion jW.hom.left := windowInclusion_isOpenImmersion d r W
  have hjfirst : jW ≫ firstToChart d r = q := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    rfl
  have hKM : K ≫ productMap e d r F = jW := by
    apply hom_ext d r
    · calc
        _ = (K ≫ firstToChart e r) ≫ F :=
          (Category.assoc _ _ _).trans ((congrArg (fun a => K ≫ a) (productMap_first e d r F)).trans
            (Category.assoc _ _ _).symm)
        _ = k₁ ≫ F := congrArg (fun a => a ≫ F) hK.1
        _ = q := hk₁
        _ = _ := hjfirst.symm
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun a => K ≫ a) (productMap_second e d r F)).trans
          (hK.2.trans (window_second_square d r W).symm))
  let M := productMap e d r F
  have hrM : range M.hom.left.base ⊆ range jW.hom.left.base := by
    rintro _ ⟨p,rfl⟩
    let v := M.hom.left.base p
    have hv : (⟨v.val.1,v.property⟩ : d.carrier) ∈ range F.hom.left.base :=
      ⟨⟨p.val.1,p.property⟩,Subtype.ext (congrArg Prod.fst (productMap_point e d r F p)).symm⟩
    have hvW : v.val ∈ W := (Set.ext_iff.mp htrace _).mpr hv
    exact ⟨⟨⟨v.val,hvW⟩,v.property⟩,rfl⟩
  let L := openLift jW M hjW hrM
  have hLM : L ≫ jW = M := openLift_fac jW M hjW hrM
  have hMinj : Function.Injective M.hom.left.base := by
    intro p z hpz
    have hfirst : (F.hom.left.base ⟨p.val.1,p.property⟩).val =
        (F.hom.left.base ⟨z.val.1,z.property⟩).val :=
      (congrArg Prod.fst (productMap_point e d r F p)).symm.trans
        ((congrArg (fun t => t.val.1) hpz).trans (congrArg Prod.fst (productMap_point e d r F z)))
    have hsecond : p.val.2 = z.val.2 :=
      (congrArg Prod.snd (productMap_point e d r F p)).symm.trans
        ((congrArg (fun t => t.val.2) hpz).trans (congrArg Prod.snd (productMap_point e d r F z)))
    exact Subtype.ext (Prod.ext (congrArg Subtype.val (hF.base_open.injective (Subtype.ext hfirst))) hsecond)
  have hLK : L ≫ K = 𝟙 (productSpace e r) := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply hMinj
    have htriangle : (L ≫ K) ≫ M = M :=
      (Category.assoc _ _ _).trans ((congrArg (fun a => L ≫ a) hKM).trans hLM)
    exact congrArg (fun a => a.hom.left.base z) htriangle
  have hKL : K ≫ L = 𝟙 (windowSpace d r W) := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply hjW.base_open.injective
    have htriangle : (K ≫ L) ≫ jW = jW :=
      (Category.assoc _ _ _).trans ((congrArg (fun a => K ≫ a) hLM).trans hKM)
    exact congrArg (fun a => a.hom.left.base z) htriangle
  let I : productSpace e r ≅ windowSpace d r W := ⟨L,K,hLK,hKL⟩
  have hL : LocallyRingedSpace.IsOpenImmersion L.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft I).hom
    infer_instance
  have hcomp : LocallyRingedSpace.IsOpenImmersion (L.hom.left ≫ jW.hom.left) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ L.hom.left hL jW.hom.left hjW
  exact Eq.mp (congrArg (fun a => LocallyRingedSpace.IsOpenImmersion a)
    (congrArg (fun a => a.hom.left) hLM)) hcomp

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductTransport

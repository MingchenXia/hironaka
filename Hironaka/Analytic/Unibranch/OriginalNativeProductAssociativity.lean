import Hironaka.Analytic.Unibranch.OriginalNativeProductTransport

/-! Actual whole coordinate-open cylinder models and full native associators.
Blueprint first: `original-native-product-associativity.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductAssociativity
noncomputable section
open Hironaka Hironaka
  ProductComplexManifold HironakaSubmersionActualProductWindow
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace OriginalNativeProductWindow
open scoped ProductComplexManifold

variable {X : SourceReducedComplexSpace}

def flatAmbient (e : LocalEmbedding X) (s : ℕ) : Opens (ComplexModel (e.dim+s)) :=
  ⟨(fun z => ((prodModelEquiv e.dim s).symm z).1) ⁻¹' (e.ambient : Set (ComplexModel e.dim)),
    e.ambient.isOpen.preimage (continuous_fst.comp (prodModelEquiv e.dim s).symm.continuous)⟩

def flatDiffeomorph (e : LocalEmbedding X) (s : ℕ) :
    productAmbient e s ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+s)),𝓘(ℂ,ComplexModel (e.dim+s))⟯ flatAmbient e s where
  toFun p := ⟨prodModelEquiv e.dim s (p.1.val,p.2),by
    change ((prodModelEquiv e.dim s).symm (prodModelEquiv e.dim s (p.1.val,p.2))).1 ∈ e.ambient
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using p.1.property⟩
  invFun z := (⟨((prodModelEquiv e.dim s).symm z.val).1,z.property⟩,
    ((prodModelEquiv e.dim s).symm z.val).2)
  left_inv p := by
    dsimp only
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  right_inv z := Subtype.ext ((prodModelEquiv e.dim s).apply_symm_apply z.val)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (flatAmbient e s) _).mp
    exact (join_holomorphic e.dim s).comp
      (ProductComplexManifold.contMDiff_prodMk
        (contMDiff_subtype_val.comp ProductComplexManifold.contMDiff_fst)
        ProductComplexManifold.contMDiff_snd)
  contMDiff_invFun := by
    apply ProductComplexManifold.contMDiff_prodMk
    · apply (ContMDiff.subtypeVal_comp_iff e.ambient _).mp
      exact (((ContinuousLinearMap.fst ℂ (ComplexModel e.dim) (ComplexModel s)).contDiff.contMDiff).comp
        (prodModelEquiv e.dim s).symm.contDiff.contMDiff).comp contMDiff_subtype_val
    · exact (((ContinuousLinearMap.snd ℂ (ComplexModel e.dim) (ComplexModel s)).contDiff.contMDiff).comp
        (prodModelEquiv e.dim s).symm.contDiff.contMDiff).comp contMDiff_subtype_val

def flatCarrier (e : LocalEmbedding X) (s : ℕ) : Set (flatAmbient e s) :=
  (flatDiffeomorph e s).symm ⁻¹' productCarrier e s

theorem flatCarrier_analytic (e : LocalEmbedding X) (s : ℕ) :
    IsComplexAnalyticSubset (n := e.dim+s) (flatCarrier e s) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (flatDiffeomorph e s).symm.contMDiff (productCarrier_analytic e s)

def flatChart (e : LocalEmbedding X) (s : ℕ) : LocalEmbedding (productSpace e s) where
  dim := e.dim+s
  ambient := flatAmbient e s
  carrier := flatCarrier e s
  analytic := flatCarrier_analytic e s
  map := (actualSubspaceBiholomorphicIso (flatDiffeomorph e s).symm
    (flatCarrier e s) (productCarrier e s) (fun _ => Iff.rfl)).hom
  isOpenImmersion := by
    let I := actualSubspaceBiholomorphicIso (flatDiffeomorph e s).symm
      (flatCarrier e s) (productCarrier e s) (fun _ => Iff.rfl)
    change LocallyRingedSpace.IsOpenImmersion I.hom
    infer_instance
  overPoint := actualSubspaceMap_point (flatDiffeomorph e s).symm.contMDiff (fun _ hx => hx)

private def nativeBiholomorphicIso {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (D : M ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel m)⟯ N)
    (C : Set M) (E : Set N) (hC : IsComplexAnalyticSubset (n := n) C)
    (hE : IsComplexAnalyticSubset (n := m) E) (hCE : ∀ z, z ∈ C ↔ D z ∈ E) :
    ofClosedAnalytic C hC ≅ ofClosedAnalytic E hE := by
  let I := actualSubspaceBiholomorphicIso D C E hCE
  have hp : I.hom ≫ subspacePointMap (n := m) E = subspacePointMap (n := n) C :=
    actualSubspaceMap_point D.contMDiff (fun z hz => (hCE z).mp hz)
  have hpi : I.inv ≫ subspacePointMap (n := n) C = subspacePointMap (n := m) E := by
    calc
      _ = I.inv ≫ (I.hom ≫ subspacePointMap (n := m) E) := congrArg (fun t => I.inv ≫ t) hp.symm
      _ = (I.inv ≫ I.hom) ≫ subspacePointMap (n := m) E := (Category.assoc _ _ _).symm
      _ = _ := (congrArg (fun t => t ≫ subspacePointMap (n := m) E) I.inv_hom_id).trans (Category.id_comp _)
  refine ⟨ObjectProperty.homMk (Over.homMk I.hom hp),ObjectProperty.homMk (Over.homMk I.inv hpi),?_,?_⟩
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact I.hom_inv_id
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact I.inv_hom_id

def flatChartIso (e : LocalEmbedding X) (s : ℕ) : chartSpace (flatChart e s) ≅ productSpace e s :=
  nativeBiholomorphicIso (flatDiffeomorph e s).symm (flatCarrier e s) (productCarrier e s)
    (flatCarrier_analytic e s) (productCarrier_analytic e s) (fun _ => Iff.rfl)

def associatorAmbient (e : LocalEmbedding X) (s r : ℕ) :
    (flatAmbient e s × ComplexModel r) ≃ₘ⟮𝓘(ℂ,ComplexModel ((e.dim+s)+r)),𝓘(ℂ,ComplexModel (e.dim+(s+r)))⟯
      productAmbient e (s+r) where
  toFun p := (((flatDiffeomorph e s).symm p.1).1,
    prodModelEquiv s r (((flatDiffeomorph e s).symm p.1).2,p.2))
  invFun p := (flatDiffeomorph e s (p.1,((prodModelEquiv s r).symm p.2).1),
    ((prodModelEquiv s r).symm p.2).2)
  left_inv p := by
    dsimp only
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext ((flatDiffeomorph e s).apply_symm_apply p.1) rfl
  right_inv p := by
    dsimp only
    simp only [Diffeomorph.symm_apply_apply]
    exact Prod.ext rfl ((prodModelEquiv s r).apply_symm_apply p.2)
  contMDiff_toFun := by
    apply ProductComplexManifold.contMDiff_prodMk
    · exact ProductComplexManifold.contMDiff_fst.comp
        ((flatDiffeomorph e s).symm.contMDiff.comp ProductComplexManifold.contMDiff_fst)
    · exact (join_holomorphic s r).comp (ProductComplexManifold.contMDiff_prodMk
        (ProductComplexManifold.contMDiff_snd.comp
          ((flatDiffeomorph e s).symm.contMDiff.comp ProductComplexManifold.contMDiff_fst))
        ProductComplexManifold.contMDiff_snd)
  contMDiff_invFun := by
    apply ProductComplexManifold.contMDiff_prodMk
    · exact (flatDiffeomorph e s).contMDiff.comp (ProductComplexManifold.contMDiff_prodMk
        ProductComplexManifold.contMDiff_fst
        ((((ContinuousLinearMap.fst ℂ (ComplexModel s) (ComplexModel r)).contDiff.contMDiff).comp
          (prodModelEquiv s r).symm.contDiff.contMDiff).comp ProductComplexManifold.contMDiff_snd))
    · exact (((ContinuousLinearMap.snd ℂ (ComplexModel s) (ComplexModel r)).contDiff.contMDiff).comp
        (prodModelEquiv s r).symm.contDiff.contMDiff).comp ProductComplexManifold.contMDiff_snd

theorem associatorCarrier (e : LocalEmbedding X) (s r : ℕ) (p : productAmbient (flatChart e s) r) :
    p ∈ productCarrier (flatChart e s) r ↔ associatorAmbient e s r p ∈ productCarrier e (s+r) := Iff.rfl

def associator (e : LocalEmbedding X) (s r : ℕ) :
    productSpace (flatChart e s) r ≅ productSpace e (s+r) :=
  nativeBiholomorphicIso (associatorAmbient e s r)
    (productCarrier (flatChart e s) r) (productCarrier e (s+r))
    (productCarrier_analytic (flatChart e s) r) (productCarrier_analytic e (s+r)) (associatorCarrier e s r)

theorem associator_first (e : LocalEmbedding X) (s r : ℕ) :
    (associator e s r).hom ≫ first e (s+r) =
      firstToChart (flatChart e s) r ≫ chartInclusion (flatChart e s) ≫ first e s := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro p
  rfl

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductAssociativity

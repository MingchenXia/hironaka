import Hironaka.Resolution.HironakaFiniteSectionGraph
import Hironaka.Analytic.ProductComplexManifold

/-!
# A finite-section graph in the literal original ambient manifold

The ambient may be the original coordinate open itself. No analytic
extension of its reduced carrier to the entire coordinate space is assumed.
The WHOLE pulled coordinate-plane ideal retains nonradical multiplicities.
Blueprint: `hironaka-finite-section-product-graph.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaFiniteSectionProductGraph

open Hironaka.HolomorphicIdealSheaves
  ProductComplexManifold HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceLocalFunctions HironakaFiniteSectionGraph
  HironakaSingularSubspaceBlowupCartierCentreIdeal BlowupFlatCoordinates
  HironakaActualWholeStalkHolomorphicPullback

open scoped ProductComplexManifold

noncomputable section

variable {n k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal graph inside the actual native product ambient. -/
def productGraph (S : Set M) (G : M → ComplexModel k) : Set (M × ComplexModel k) :=
  {p | p.1 ∈ S ∧ p.2 = G p.1}

/-- The actual product graph is analytic in the SAME original ambient. -/
theorem productGraph_analytic (S : Set M) (hS : IsComplexAnalyticSubset (n := n) S)
    (G : M → ComplexModel k) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) :
    IsComplexAnalyticSubset (n := n+k) (productGraph S G) := by
  have hp := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (ProductComplexManifold.contMDiff_fst (n := n) (m := k) (X := M) (Y := ComplexModel k)) hS
  have hq := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (ProductComplexManifold.contMDiff_snd.sub (hG.comp ProductComplexManifold.contMDiff_fst))
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel k))
  convert hp.inter hq using 1
  ext p
  simp only [productGraph,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_singleton_iff,sub_eq_zero,Function.comp_apply]

/-- The FULL original graph parametrization/projection isomorphism, derived
from actual holomorphic maps and their identities on the literal sets. -/
def productGraphIso (S : Set M) (G : M → ComplexModel k)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) :
    actualSubspaceLocallyRingedSpace (n := n) S ≅
      actualSubspaceLocallyRingedSpace (n := n+k) (productGraph S G) :=
  actualSubspaceMutualRestrictionIso (contMDiff_prodMk contMDiff_id hG) ProductComplexManifold.contMDiff_fst
    (fun _ hu => ⟨hu,rfl⟩) (fun _ hp => hp.1)
    (fun _ _ => rfl) (fun _ hp => Prod.ext rfl hp.2.symm)

/-- The actual product graph isomorphism retains the original scalar triangle. -/
theorem productGraphIso_hom_point (S : Set M) (G : M → ComplexModel k)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) :
    (productGraphIso S G hG).hom ≫ subspacePointMap (n := n+k) (productGraph S G) =
      subspacePointMap (n := n) S :=
  actualSubspaceMap_point (C := S) (D := productGraph S G) (contMDiff_prodMk contMDiff_id hG) (fun _ hu => ⟨hu,rfl⟩)

/-- The entire original graph inclusion square, including the sheaf map. -/
theorem productGraphIso_inclusion (S : Set M) (G : M → ComplexModel k)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) :
    (productGraphIso S G hG).hom ≫ actualSubspaceInclusion (n := n+k) (productGraph S G) =
      actualSubspaceInclusion (n := n) S ≫
        ChartedSpace.locallyRingedSpaceMap (fun u : M => (u,G u))
          (contMDiff_prodMk contMDiff_id hG) :=
  (actualSubspaceMap_inclusion (C := S) (D := productGraph S G) (contMDiff_prodMk contMDiff_id hG) (fun _ hu => ⟨hu,rfl⟩)).symm

private def chartIdentity {a : ℕ} {P : Type} [TopologicalSpace P]
    [ChartedSpace (ComplexModel a) P] (p : P) :
    LocalHolomorphicEquivAt (n := a) (chartAt (ComplexModel a) p p) where
  source := (chartAt (ComplexModel a) p).target
  target := (chartAt (ComplexModel a) p).target
  isOpen_source := (chartAt (ComplexModel a) p).open_target
  isOpen_target := (chartAt (ComplexModel a) p).open_target
  center_mem_source := (chartAt (ComplexModel a) p).map_source (mem_chart_source _ p)
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ h => h
  mapsTo_invFun := fun _ h => h
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

omit [IsComplexManifold n M] in
private theorem product_chart_normal (p q : M × ComplexModel k) (i : Fin k) :
    (chartAt (ComplexModel (n+k)) p q) (i.natAdd n) = q.2 i := by
  change (prodModelEquiv n k ((chartAt (ComplexModel n) p.1) q.1,
    (chartAt (ComplexModel k) p.2) q.2)) (i.natAdd n) = q.2 i
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
    chartAt_self_eq]

private theorem normal_coordinate_holomorphic (p : M × ComplexModel k) (i : Fin k) :
    HolomorphicAt (n+k) (fun q : M × ComplexModel k => q.2 i) p :=
  Eventually.of_forall fun _ =>
    (((EuclideanSpace.proj i : ComplexModel k →L[ℂ] ℂ).contMDiff.comp
      ProductComplexManifold.contMDiff_snd).contMDiffAt).mdifferentiableAt (by simp)

private theorem original_function_congr {a : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel a) P] [IsComplexManifold a P]
    (p : P) (f g : P → ℂ) (hf : HolomorphicAt a f p) (hg : HolomorphicAt a g p)
    (he : f =ᶠ[𝓝 p] g) :
    actualOriginalFunctionGerm p f hf = actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := a) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p f g hf hg he

/-- The WHOLE ambient product-zero-plane ideal at EVERY actual point is
the span of the original second-coordinate germs, including off-plane points. -/
theorem whole_product_zero_plane_ideal (p : M × ComplexModel k) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
      {q : M × ComplexModel k | q.2 = 0}) p =
      Ideal.span (Set.range fun i : Fin k => actualOriginalFunctionGerm p
        (fun q : M × ComplexModel k => q.2 i) (normal_coordinate_holomorphic p i)) := by
  let Φ := chartIdentity (a := n+k) p
  have hsrc : Φ.source ⊆ (chartAt (ComplexModel (n+k)) p).target := Subset.rfl
  have hflat : ∀ {q : M × ComplexModel k}, q ∈ (chartAt (ComplexModel (n+k)) p).source →
      chartAt (ComplexModel (n+k)) p q ∈ Φ.source →
      (q ∈ {q : M × ComplexModel k | q.2 = 0} ↔
        Φ.toFun (chartAt (ComplexModel (n+k)) p q) ∈ complexCoordinatePlane (n+k) n) := by
    intro q _ _
    change q.2 = 0 ↔ ∀ i : Fin (n+k), n ≤ i.val → (chartAt (ComplexModel (n+k)) p q) i = 0
    constructor
    · intro hq i hi
      let j : Fin k := ⟨i.val-n,by omega⟩
      have he : j.natAdd n = i := Fin.ext (by dsimp [j]; omega)
      rw [← he,product_chart_normal,hq]
      rfl
    · intro hq
      ext i
      rw [← product_chart_normal (n := n) p q i]
      exact hq (i.natAdd n) (by simp)
  rw [actualWholeSheafCentreIdeal_eq_span_normal_coordinates hsrc hflat p (mem_flatDomain_self Φ)]
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨i,rfl⟩
    let j : Fin k := ⟨i.val.val-n,by omega⟩
    refine ⟨j,?_⟩
    have he : j.natAdd n = i.val := Fin.ext (by dsimp [j]; omega)
    apply original_function_congr
    exact Eventually.of_forall fun q => by
      change q.2 j = (chartAt (ComplexModel (n+k)) p q) i.val
      rw [← he,product_chart_normal]
  · rintro ⟨i,rfl⟩
    refine ⟨⟨i.natAdd n,by simp⟩,?_⟩
    apply original_function_congr
    exact Eventually.of_forall fun q => by
      change (chartAt (ComplexModel (n+k)) p q) (i.natAdd n) = q.2 i
      exact product_chart_normal (n := n) p q i

private theorem native_function {a b : ℕ} {P Q : Type}
    [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace (ComplexModel a) P] [IsComplexManifold a P]
    [ChartedSpace (ComplexModel b) Q] [IsComplexManifold b Q]
    {F : P → Q} (hF : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ F)
    (p : P) (f : Q → ℂ) (hf : HolomorphicAt b f (F p)) :
    (ChartedSpace.locallyRingedSpaceMap F hF).stalkMap p
      (actualOriginalFunctionGerm (F p) f hf) =
      actualOriginalFunctionGerm p (f ∘ F)
        (hf.comp_contMDiff (Eventually.of_forall fun _ => hF.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := a) p).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

omit [IsComplexManifold n M] in
private theorem component_holomorphic (G : M → ComplexModel k)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) (p : M) (i : Fin k) :
    HolomorphicAt n (fun q : M => G q i) p :=
  Eventually.of_forall fun _ =>
    (((EuclideanSpace.proj i : ComplexModel k →L[ℂ] ℂ).contMDiff.comp hG).contMDiffAt).mdifferentiableAt (by simp)

private theorem product_graph_coordinate_ideal (S : Set M) (G : M → ComplexModel k)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G) (y : S) :
    Ideal.map (((productGraphIso S G hG).hom ≫
      actualSubspaceInclusion (n := n+k) (productGraph S G)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
        {q : M × ComplexModel k | q.2 = 0})
          (((productGraphIso S G hG).hom ≫ actualSubspaceInclusion (n := n+k) (productGraph S G)).base y)) =
      Ideal.span (Set.range fun i : Fin k => (actualSubspaceInclusion (n := n) S).stalkMap y
        (actualOriginalFunctionGerm y.val (fun u : M => G u i) (component_holomorphic G hG y.val i))) := by
  rw [productGraphIso_inclusion,whole_product_zero_plane_ideal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply]
  rw [LocallyRingedSpace.stalkMap_comp]
  change (actualSubspaceInclusion (n := n) S).stalkMap y
      ((ChartedSpace.locallyRingedSpaceMap (fun u : M => (u,G u))
        (contMDiff_prodMk contMDiff_id hG)).stalkMap y.val
          (actualOriginalFunctionGerm (y.val,G y.val) (fun q : M × ComplexModel k => q.2 i) _)) = _
  exact congrArg ((actualSubspaceInclusion (n := n) S).stalkMap y)
    (native_function (contMDiff_prodMk contMDiff_id hG) y.val (fun q : M × ComplexModel k => q.2 i) _)

/-- Actual quotient sections on the literal original ambient manifold
produce an actual product graph and the ENTIRE same generated ideal.
No global-coordinate analytic extension or reduced pulled ideal occurs. -/
theorem exists_product_graph_of_finite_sections
    (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W) (V : Opens (TopCat.of W))
    (s : Fin k → ((actualSubspaceSheaf (n := n) W).presheaf.obj (op V)).carrier)
    (x : W) (hx : x ∈ V) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O)
      (G : O → ComplexModel k) (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G)
      (hOV : ∀ y : W, y.val ∈ O → y ∈ V),
      IsComplexAnalyticSubset (n := n+k)
        (productGraph ((Subtype.val : O → M) ⁻¹' W) G) ∧
      ∀ y : ((Subtype.val : O → M) ⁻¹' W),
        Ideal.map (((productGraphIso ((Subtype.val : O → M) ⁻¹' W) G hG).hom ≫
          actualSubspaceInclusion (n := n+k) (productGraph ((Subtype.val : O → M) ⁻¹' W) G)).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
            {q : O × ComplexModel k | q.2 = 0})
              (((productGraphIso ((Subtype.val : O → M) ⁻¹' W) G hG).hom ≫
                actualSubspaceInclusion (n := n+k) (productGraph ((Subtype.val : O → M) ⁻¹' W) G)).base y)) =
          Ideal.map ((actualOpenSubspaceMap (n := n) W O).stalkMap y).hom
            (Ideal.span (Set.range fun i : Fin k =>
              (actualSubspaceSheaf (n := n) W).presheaf.germ V
                ((actualOpenSubspaceMap (n := n) W O).base y) (hOV _ y.val.property) (s i))) := by
  obtain ⟨O,hxO,t,hOV,ht⟩ := exists_finite_ambient_sections W V s x hx
  let G : O → ComplexModel k := fun u =>
    (EuclideanSpace.equiv (Fin k) ℂ).symm (fun i => t i u)
  have hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ G :=
    (EuclideanSpace.equiv (Fin k) ℂ).symm.toContinuousLinearMap.contMDiff.comp
      (contMDiff_pi_space.mpr (fun i => smoothSheaf.contMDiff_section (t i)))
  refine ⟨O,hxO,G,hG,hOV,productGraph_analytic _
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O) G hG,?_⟩
  intro y
  rw [product_graph_coordinate_ideal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply]
  rw [ht i ((actualOpenSubspaceMap (n := n) W O).base y) y.val.property]
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let r := F.germ O y.val.val y.val.property (t i)
  have hsq := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (f := (Subtype.val : O → M))
      contMDiff_subtype_val (fun _ hu => hu) y) r
  change (actualOpenSubspaceMap (n := n) W O).stalkMap y
      ((actualSubspaceInclusion (n := n) W).stalkMap
        ((actualOpenSubspaceMap (n := n) W O).base y) r) =
      (actualSubspaceInclusion (n := n) ((Subtype.val : O → M) ⁻¹' W)).stalkMap y
        ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → M)
          contMDiff_subtype_val).stalkMap y.val r) at hsq
  change _ = (actualOpenSubspaceMap (n := n) W O).stalkMap y
    ((actualSubspaceInclusion (n := n) W).stalkMap
      ((actualOpenSubspaceMap (n := n) W O).base y) r)
  rw [hsq]
  apply congrArg ((actualSubspaceInclusion (n := n) ((Subtype.val : O → M) ⁻¹' W)).stalkMap y)
  have hr : r = actualOriginalFunctionGerm y.val.val (sectionExtension O (t i))
      (sectionExtension_holomorphicAt O (t i) y.val.val y.val.property) :=
    (actualOriginalFunctionGerm_eq_section O y.val.val y.val.property (t i)
      (sectionExtension O (t i))
      (sectionExtension_holomorphicAt O (t i) y.val.val y.val.property) Filter.EventuallyEq.rfl).symm
  rw [hr]
  calc
    _ = actualOriginalFunctionGerm y.val ((sectionExtension O (t i)) ∘ (Subtype.val : O → M)) _ :=
      original_function_congr y.val _ _ _ _ (Eventually.of_forall fun u =>
        (sectionExtension_apply O (t i) u.val u.property).symm)
    _ = _ := (native_function contMDiff_subtype_val y.val (sectionExtension O (t i)) _).symm

end
end Hironaka.HironakaFiniteSectionProductGraph

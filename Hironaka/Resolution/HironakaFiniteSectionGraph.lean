import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions
import Hironaka.Resolution.HironakaActualLocalCommonGraphModel
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierCentreIdeal
import Hironaka.Analytic.FibreDimensionLowerBound

/-!
# Finite original quotient sections, actual graphs and the whole zero-plane ideal

The ambient zero-plane is not required to be contained in the graph. Its
entire ideal pulls back to the original generated ideal, without taking a
radical. Blueprint: `hironaka-finite-section-graph.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaFiniteSectionGraph

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceLocalFunctions HironakaActualLocalCommonGraphModel
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualHolomorphicGraphIdeal HironakaActualWholeStalkHolomorphicPullback
  HironakaSingularSubspaceBlowupCartierCentreIdeal BlowupFlatCoordinates

noncomputable section

/-- One genuine ambient open realizes a finite family of actual quotient
sections at EVERY original point of the open, including the empty family. -/
theorem exists_finite_ambient_sections {n k : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (W : Set M) (V : Opens (TopCat.of W))
    (s : Fin k → ((actualSubspaceSheaf (n := n) W).presheaf.obj (op V)).carrier)
    (x : W) (hx : x ∈ V) :
    ∃ (O : Opens M) (_hxO : x.val ∈ O)
      (t : Fin k → actualComplexSection (n := n) O)
      (hOV : ∀ y : W, y.val ∈ O → y ∈ V),
      ∀ i (y : W) (hy : y.val ∈ O),
        (actualSubspaceSheaf (n := n) W).presheaf.germ V y (hOV y hy) (s i) =
          (actualSubspaceInclusion (n := n) W).stalkMap y
            ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy (t i)) := by
  classical
  choose O hxO t hOV ht using fun i => actualSubspaceSection_local_ambient W V (s i) x hx
  obtain ⟨T,hT,hTV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp V.isOpen
  let U : Opens M := ⟨T,hT⟩ ⊓ ⨅ i, O i
  have hUO (i : Fin k) : U ≤ O i := inf_le_right.trans (iInf_le O i)
  have hxU : x.val ∈ U := by
    change x.val ∈ T ∩ ((⨅ i, O i : Opens M) : Set M)
    rw [Opens.coe_iInf]
    exact ⟨by change x ∈ Subtype.val ⁻¹' T; rw [hTV]; exact hx, Set.mem_iInter.mpr hxO⟩
  have hUV : ∀ y : W, y.val ∈ U → y ∈ V := by
    intro y hy
    change y ∈ (V : Set W)
    rw [← hTV]
    exact hy.1
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  refine ⟨U,hxU,fun i => F.map (homOfLE (hUO i)).op (t i),hUV,?_⟩
  intro i y hy
  calc
    _ = (actualSubspaceInclusion (n := n) W).stalkMap y
        (F.germ (O i) y.val (hUO i hy) (t i)) := ht i y (hUO i hy)
    _ = _ := congrArg ((actualSubspaceInclusion (n := n) W).stalkMap y)
      (F.germ_res_apply (homOfLE (hUO i)) y.val hy (t i)).symm

private def identityCoordinates {q : ℕ} (p : ComplexModel q) :
    LocalHolomorphicEquivAt (n := q) (chartAt (ComplexModel q) p p) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

/-- At EVERY actual ambient point, the WHOLE zero-plane ideal has exactly
the original last-coordinate generators. No point-in-plane premise occurs. -/
theorem whole_coordinate_plane_ideal {n k : ℕ} (z : ComplexModel (n+k)) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
      (complexCoordinatePlane (n+k) n)) z =
      Ideal.span (Set.range fun i : Fin k =>
        actualOriginalFunctionGerm z (fun w : ComplexModel (n+k) => w (i.natAdd n))
          (Eventually.of_forall fun _ =>
            (EuclideanSpace.proj (i.natAdd n) : ComplexModel (n+k) →L[ℂ] ℂ).mdifferentiableAt)) := by
  let Φ := identityCoordinates z
  have hsrc : Φ.source ⊆ (chartAt (ComplexModel (n+k)) z).target := by
    simp [Φ,identityCoordinates,chartAt_self_eq]
  have hflat : ∀ {w : ComplexModel (n+k)}, w ∈ (chartAt (ComplexModel (n+k)) z).source →
      chartAt (ComplexModel (n+k)) z w ∈ Φ.source →
      (w ∈ complexCoordinatePlane (n+k) n ↔
        Φ.toFun (chartAt (ComplexModel (n+k)) z w) ∈ complexCoordinatePlane (n+k) n) := by
    intro w _ _
    simp [Φ,identityCoordinates,chartAt_self_eq]
  have hz : z ∈ flatDomain Φ := by
    simp [flatDomain,Φ,identityCoordinates,chartAt_self_eq]
  rw [actualWholeSheafCentreIdeal_eq_span_normal_coordinates hsrc hflat z hz]
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨i,rfl⟩
    let j : Fin k := ⟨i.val.val-n,by omega⟩
    refine ⟨j,?_⟩
    have hi : j.natAdd n = i.val := Fin.ext (by dsimp [j]; omega)
    simp only [hi]
    rfl
  · rintro ⟨i,rfl⟩
    refine ⟨⟨i.natAdd n,by simp⟩,?_⟩
    rfl

private theorem vector_on_open {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ (fun u : O => G u.val) := by
  intro u
  exact contMDiffAt_subtype_iff.mpr
    ((hG.contDiffAt (O.isOpen.mem_nhds u.property)).contMDiffAt)

private theorem graph_section_contMDiff {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+k)) ∞
      (fun u : O => graphSection G u.val) := by
  exact ((tangentInclusion n k).contMDiff.comp contMDiff_subtype_val).add
    ((actualJointNormalInclusion n k).contMDiff.comp (vector_on_open O G hG))

/-- The literal graph in the genuine wide ambient open is closed analytic,
derived from the original analytic carrier and the actual holomorphic vector. -/
theorem firstGraphSubset_analytic {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
    {W : Set (ComplexModel n)} (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n+k) (firstGraphSubset O G W) := by
  let A := firstWideDomain (m := k) O
  let p : A → O := fun z => ⟨tangentProjection n k z.val,z.property⟩
  have hp : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel n) ∞ p := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    exact (tangentProjection n k).contMDiff.comp contMDiff_subtype_val
  have hbase := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    ((tangentProjection n k).contMDiff.comp (contMDiff_subtype_val (U := A))) hW
  have hdiff : ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel k) ∞
      (fun z : A => actualJointNormalProjection n k z.val - G (tangentProjection n k z.val)) :=
    ((actualJointNormalProjection n k).contMDiff.comp contMDiff_subtype_val).sub
      ((vector_on_open O G hG).comp hp)
  have hzero := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hdiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel k))
  convert hbase.inter hzero using 1
  ext z
  simp only [firstGraphSubset,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_singleton_iff,sub_eq_zero,Function.comp_apply]

/-- The full original ambient map of the SAME actual graph isomorphism. -/
def graphAmbientMap {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
    (W : Set (ComplexModel n)) :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : O → ComplexModel n) ⁻¹' W) ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+k)) (ComplexModel (n+k)) :=
  (firstGraphModelIso O G hG W).hom ≫
    actualSubspaceInclusion (n := n+k) (firstGraphSubset O G W) ≫
      ChartedSpace.locallyRingedSpaceMap
        (Subtype.val : firstWideDomain (m := k) O → ComplexModel (n+k)) contMDiff_subtype_val

/-- The entire actual graph ambient map is the genuine graph-section map
after the SAME original source quotient inclusion, including all sheaf maps. -/
theorem graphAmbientMap_eq {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
    (W : Set (ComplexModel n)) :
    graphAmbientMap O G hG W =
      actualSubspaceInclusion (n := n) ((Subtype.val : O → ComplexModel n) ⁻¹' W) ≫
        ChartedSpace.locallyRingedSpaceMap (fun u : O => graphSection G u.val)
          (graph_section_contMDiff O G hG) := by
  let f : O → firstWideDomain (m := k) O := fun u => ⟨graphSection G u.val,by
    change tangentProjection n k (graphSection G u.val) ∈ O
    rw [projection_graphSection]
    exact u.property⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+k)) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff (firstWideDomain O) f).mp (graph_section_contMDiff O G hG)
  have hm : ∀ u ∈ (Subtype.val : O → ComplexModel n) ⁻¹' W,
      f u ∈ firstGraphSubset O G W := by
    intro u hu
    exact ⟨by simpa [f] using hu,by simp [f]⟩
  change actualSubspaceMap hf hm ≫ (actualSubspaceInclusion (firstGraphSubset O G W) ≫ _) = _
  rw [← Category.assoc, ← actualSubspaceMap_inclusion hf hm, Category.assoc,
    ← ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ,ComplexModel n))
      (IN := 𝓘(ℂ,ComplexModel (n+k))) (IP := 𝓘(ℂ,ComplexModel (n+k))) hf contMDiff_subtype_val]
  rfl

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

private theorem coordinate_on_open {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
    (i : Fin k) (u : O) : HolomorphicAt n (fun v : O => G v.val i) u :=
  Eventually.of_forall fun _ =>
    (((EuclideanSpace.proj i : ComplexModel k →L[ℂ] ℂ).contMDiff.comp
      (vector_on_open O G hG)).contMDiffAt).mdifferentiableAt (by simp)

private theorem original_function_congr {a : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel a) P] [IsComplexManifold a P]
    (p : P) (f g : P → ℂ) (hf : HolomorphicAt a f p) (hg : HolomorphicAt a g p)
    (he : f =ᶠ[𝓝 p] g) :
    actualOriginalFunctionGerm p f hf = actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := a) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p f g hf hg he

private theorem graph_coordinate_ideal {n k : ℕ} (O : Opens (ComplexModel n))
    (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
    (W : Set (ComplexModel n))
    (y : ((Subtype.val : O → ComplexModel n) ⁻¹' W)) :
    Ideal.map ((graphAmbientMap O G hG W).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
        (complexCoordinatePlane (n+k) n)) ((graphAmbientMap O G hG W).base y)) =
      Ideal.span (Set.range fun i : Fin k =>
        (actualSubspaceInclusion (n := n) ((Subtype.val : O → ComplexModel n) ⁻¹' W)).stalkMap y
          (actualOriginalFunctionGerm y.val (fun u : O => G u.val i) (coordinate_on_open O G hG i y.val))) := by
  rw [graphAmbientMap_eq,whole_coordinate_plane_ideal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply]
  rw [LocallyRingedSpace.stalkMap_comp]
  change (actualSubspaceInclusion (n := n) ((Subtype.val : O → ComplexModel n) ⁻¹' W)).stalkMap y
      ((ChartedSpace.locallyRingedSpaceMap (fun u : O => graphSection G u.val)
        (graph_section_contMDiff O G hG)).stalkMap y.val
        (actualOriginalFunctionGerm (graphSection G y.val.val)
          (EuclideanSpace.proj (i.natAdd n) : ComplexModel (n+k) →L[ℂ] ℂ) _)) = _
  apply congrArg ((actualSubspaceInclusion (n := n)
    ((Subtype.val : O → ComplexModel n) ⁻¹' W)).stalkMap y)
  have he : (fun w : ComplexModel (n+k) => w (i.natAdd n)) ∘
      (fun u : O => graphSection G u.val) = (fun u : O => G u.val i) := by
    funext u
    exact congrArg (fun v : ComplexModel k => v i) (normalProjection_graphSection G u.val)
  calc
    _ = actualOriginalFunctionGerm y.val
        ((EuclideanSpace.proj (i.natAdd n) : ComplexModel (n+k) →L[ℂ] ℂ) ∘
          (fun u : O => graphSection G u.val)) _ :=
      native_function (graph_section_contMDiff O G hG) y.val _ _
    _ = _ := original_function_congr y.val _ _ _ _
      (Eventually.of_forall fun u => congrFun he u)

/-- Original finite quotient sections internally produce an actual analytic
graph whose WHOLE ambient zero-plane ideal is exactly the SAME original
generated ideal, with all nonradical multiplicities retained. -/
theorem exists_graph_of_finite_sections {n k : ℕ}
    (W : Set (ComplexModel n)) (hW : IsComplexAnalyticSubset (n := n) W)
    (V : Opens (TopCat.of W))
    (s : Fin k → ((actualSubspaceSheaf (n := n) W).presheaf.obj (op V)).carrier)
    (x : W) (hx : x ∈ V) :
    ∃ (O : Opens (ComplexModel n)) (_hxO : x.val ∈ O)
      (G : ComplexModel n → ComplexModel k) (hG : ContDiffOn ℂ ∞ G O)
      (hOV : ∀ y : W, y.val ∈ O → y ∈ V),
      IsComplexAnalyticSubset (n := n+k) (firstGraphSubset O G W) ∧
      ∀ y : ((Subtype.val : O → ComplexModel n) ⁻¹' W),
        Ideal.map ((graphAmbientMap O G hG W).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+k)
            (complexCoordinatePlane (n+k) n)) ((graphAmbientMap O G hG W).base y)) =
          Ideal.map ((actualOpenSubspaceMap (n := n) W O).stalkMap y).hom
            (Ideal.span (Set.range fun i : Fin k =>
              (actualSubspaceSheaf (n := n) W).presheaf.germ V
                ((actualOpenSubspaceMap (n := n) W O).base y)
                (hOV _ y.val.property) (s i))) := by
  obtain ⟨O,hxO,t,hOV,ht⟩ := exists_finite_ambient_sections W V s x hx
  let G : ComplexModel n → ComplexModel k :=
    fun u => WithLp.toLp 2 (fun i => sectionExtension O (t i) u)
  have hG : ContDiffOn ℂ ∞ G O := by
    apply (contDiffOn_piLp 2).mpr
    intro i u hu
    exact (sectionExtension_contMDiffAt O (t i) u hu).contDiffAt.contDiffWithinAt
  refine ⟨O,hxO,G,hG,hOV,firstGraphSubset_analytic O G hG hW,?_⟩
  intro y
  rw [graph_coordinate_ideal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply]
  rw [ht i ((actualOpenSubspaceMap (n := n) W O).base y) y.val.property]
  let F := (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let r := F.germ O y.val.val y.val.property (t i)
  have hsq := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (f := (Subtype.val : O → ComplexModel n))
      contMDiff_subtype_val (fun _ hu => hu) y) r
  simp only [ConcreteCategory.comp_apply] at hsq
  change _ = (actualOpenSubspaceMap (n := n) W O).stalkMap y
    ((actualSubspaceInclusion (n := n) W).stalkMap
      ((actualOpenSubspaceMap (n := n) W O).base y) r)
  change (actualOpenSubspaceMap (n := n) W O).stalkMap y
      ((actualSubspaceInclusion (n := n) W).stalkMap
        ((actualOpenSubspaceMap (n := n) W O).base y) r) =
      (actualSubspaceInclusion (n := n) ((Subtype.val : O → ComplexModel n) ⁻¹' W)).stalkMap y
        ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel n)
          contMDiff_subtype_val).stalkMap y.val r) at hsq
  rw [hsq]
  have hr : r = actualOriginalFunctionGerm y.val.val (sectionExtension O (t i))
      (sectionExtension_holomorphicAt O (t i) y.val.val y.val.property) :=
    (actualOriginalFunctionGerm_eq_section O y.val.val y.val.property (t i)
      (sectionExtension O (t i))
      (sectionExtension_holomorphicAt O (t i) y.val.val y.val.property) Filter.EventuallyEq.rfl).symm
  rw [hr,native_function]
  rfl

end
end Hironaka.HironakaFiniteSectionGraph

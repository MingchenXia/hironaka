import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaProductZeroPlaneBlowup

set_option maxHeartbeats 300000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaFiniteSectionProductGraph HironakaG10HirIdealGerms
  HironakaProductZeroPlaneBlowup
open scoped ProductComplexManifold
open Hironaka.Analytic.Unibranch Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphDensity Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform

namespace Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic

noncomputable section

private theorem ideal_map_stalk_comp_aux {A D T : LocallyRingedSpace} (f : A ⟶ D) (g : D ⟶ T)
    (x : A) (I : Ideal (T.presheaf.stalk ((f ≫ g).base x)).carrier) :
    Ideal.map ((f ≫ g).stalkMap x).hom I =
      Ideal.map (f.stalkMap x).hom (Ideal.map (g.stalkMap (f.base x)).hom I) := by
  calc
    _ = Ideal.map (g.stalkMap (f.base x) ≫ f.stalkMap x).hom I :=
      congrArg (fun h : T.presheaf.stalk ((f ≫ g).base x) ⟶ A.presheaf.stalk x =>
        Ideal.map h.hom I) (LocallyRingedSpace.stalkMap_comp f g x)
    _ = _ := (Ideal.map_map (g.stalkMap (f.base x)).hom (f.stalkMap x).hom).symm

/-- The support of a local flattener has a genuine analytic chart around
  every point of its domain. -/
theorem local_support_analytic {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (Z : LocalFlattener f) (x : X.obj.left) (hx : x ∈ Z.V) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Z.V ∧
      ∃ A : Set e.ambient, IsComplexAnalyticSubset (n := e.dim) A ∧
        e.toPoint ⁻¹' Z.support = Subtype.val ⁻¹' A := by
  obtain ⟨U,hxU,r,s,hs⟩ := Z.fg x hx
  obtain ⟨e,⟨w,hw⟩,heV,_⟩ := LocalEmbedding.exists_domain x Z.isOpen hx
  let F := e.map
  let V : Opens (TopCat.of e.carrier) := (Opens.map F.base).obj U
  let a : Fin r → ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.obj (op V)).carrier :=
    fun i => F.c.app (op U) (s i)
  have hwV : w ∈ V := by change e.toPoint w ∈ U; rw [hw]; exact hxU
  obtain ⟨O,hwO,G,hG,hOV,hΓ,hgraph⟩ :=
    exists_product_graph_of_finite_sections e.carrier e.analytic V a w hwV
  let S := (Subtype.val : O → e.ambient) ⁻¹' e.carrier
  let Γ := productGraph S G
  let E := productGraphIso S G hG
  let j := actualOpenSubspaceMap (n := e.dim) e.carrier O
  let J := chartGraphMorphism e O G hG hΓ
  let : LocallyRingedSpace.IsOpenImmersion J.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (chartGraphMap e O G hG)
    infer_instance
  let T : Set (O × ComplexModel r) := {q | q.2 = 0}
  have hT : IsComplexAnalyticSubset (n := e.dim+r) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_product_zero_plane (M := O) (n := e.dim) (r := r))
  have hparam (y : S) :
      Ideal.map ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r) T)
          ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y)) =
      Ideal.map ((j ≫ F).stalkMap y).hom (Z.H ((j ≫ F).base y)) := by
    rw [hgraph y]
    have hyU : F.base (j.base y) ∈ U := hOV (j.base y) y.val.property
    have hyV : F.base (j.base y) ∈ Z.V := heV ⟨j.base y,rfl⟩
    have hspan : Ideal.map (F.stalkMap (j.base y)).hom (Z.H (F.base (j.base y))) =
        Ideal.span (Set.range fun i => (actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.germ V
          (j.base y) (hOV _ y.val.property) (a i)) := by
      rw [hs _ hyU hyV, Ideal.map_span, ← Set.range_comp]
      apply congrArg Ideal.span
      apply congrArg Set.range
      funext i
      exact (LocallyRingedSpace.stalkMap_germ_apply F U (j.base y) hyU (s i))
    rw [← hspan]
    exact (ideal_map_stalk_comp_aux j F y (Z.H ((j ≫ F).base y))).symm
  have htrace (z : Γ) : z.val ∈ T ↔ (J.hom.left.base z) ∈ Z.support := by
    let y : S := E.inv.base z
    have hyz : E.hom.base y = z := by
      change E.hom.base (E.inv.base z) = z
      exact congrArg (fun k => k.base z) E.inv_hom_id
    have hq := hparam y
    have ht := local_map_ideal_eq_top_iff
      ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r) T)
        ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y))
    have hf := local_map_ideal_eq_top_iff ((j ≫ F).stalkMap y).hom (Z.H ((j ≫ F).base y))
    have hzero := actualWholeVanishing_eq_top_iff (n := e.dim+r) T hT.isClosed
      ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y)
    have hzbase : (E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y = z.val := by
      change (E.hom.base y).val = z.val
      rw [hyz]
    have hzero' : actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r) T)
        ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y) = ⊤ ↔ z.val ∉ T := by
      simpa only [hzbase] using hzero
    have hyJ : (j ≫ F).base y = J.hom.left.base z := by
      rw [← hyz]
      rfl
    have hyunit : z.val ∉ T ↔ Z.H (J.hom.left.base z) = ⊤ := by
      rw [← hyJ]
      rw [← hzero', ← ht, hq, hf]
    have hzV : J.hom.left.base z ∈ Z.V := by
      rw [← hyJ]
      exact heV ⟨j.base y,rfl⟩
    change z.val ∈ T ↔ J.hom.left.base z ∈ Z.V ∧ Z.H (J.hom.left.base z) ≠ ⊤
    exact ⟨fun h => ⟨hzV,fun heq => (hyunit.mpr heq) h⟩,
      fun h => by_contra fun hn => h.2 (hyunit.mp hn)⟩
  let z : Γ := ⟨(⟨w.val,hwO⟩,G ⟨w.val,hwO⟩),⟨w.property,rfl⟩⟩
  have hz : J.hom.left.base z = x := hw
  obtain ⟨e',he',A,hA,htrace'⟩ := (isAnalyticSubset_preimage_val hΓ hT) z
  let eX : LocalEmbedding X :=
    { dim := e'.dim
      ambient := e'.ambient
      carrier := e'.carrier
      analytic := e'.analytic
      map := e'.map ≫ J.hom.left
      isOpenImmersion := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e'.map e'.isOpenImmersion _ (by infer_instance)
      overPoint := by rw [Category.assoc, Over.w J.hom]; exact e'.overPoint }
  refine ⟨eX, ?_, ?_, A, hA, ?_⟩
  · obtain ⟨u,hu⟩ := he'
    exact ⟨u,(congrArg J.hom.left.base hu).trans hz⟩
  · rintro _ ⟨u,rfl⟩
    exact heV ⟨⟨(e'.toPoint u).val.1.val,(e'.toPoint u).property.1⟩,rfl⟩
  · have heq : eX.toPoint ⁻¹' Z.support = e'.toPoint ⁻¹' ((Subtype.val : Γ → O × ComplexModel r) ⁻¹' T) := by
      ext u
      exact (htrace (e'.toPoint u)).symm
    exact heq.trans htrace'

end

end Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic

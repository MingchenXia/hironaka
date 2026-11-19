import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal
import Hironaka.Resolution.HironakaNativeFiniteIdealSections
import Hironaka.Resolution.HironakaFiniteSectionProductGraph

/-!
# Global ORIGINAL ideal sections produce real local graph charts

Finite type is used on the ORIGINAL global space. Only the literal functions
b(s_i) are pulled through actual chart components; no finite-type assertion on
a custom pulled ideal module is assumed. Both whole-ideal dictionaries keep
the SAME original global b, including nonradical multiplicities.
Blueprint: `original-finite-ideal-graph-chart.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart

open Hironaka
  Hironaka.HolomorphicIdealSheaves Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaNativeFiniteIdealSections HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaFiniteSectionProductGraph
  SourceReducedComplexSpace EmbeddedBlowupGlobalUniversalLocal

open scoped ProductComplexManifold

noncomputable section

private theorem idealFamily_map_specializes {A : LocallyRingedSpace}
    (I : ∀ x : A, Ideal (A.presheaf.stalk x).carrier) {x y : A} (h : x = y) :
    Ideal.map (A.presheaf.stalkSpecializes (specializes_of_eq h)).hom (I y) = I x := by
  cases h
  simp only [TopCat.Presheaf.stalkSpecializes_refl,CommRingCat.hom_id,Ideal.map_id]

private theorem idealFamily_map_iso_inverse {A D : LocallyRingedSpace} (E : A ≅ D)
    (I : ∀ z : D, Ideal (D.presheaf.stalk z).carrier)
    (J : ∀ x : A, Ideal (A.presheaf.stalk x).carrier)
    (h : ∀ x, Ideal.map (E.hom.stalkMap x).hom (I (E.hom.base x)) = J x)
    (z : D) : Ideal.map (E.inv.stalkMap z).hom (J (E.inv.base z)) = I z := by
  have hz : z = E.hom.base (E.inv.base z) :=
    (congrArg (fun H => H.base z) E.inv_hom_id).symm
  have hs : (E.inv.stalkMap z).hom.comp (E.hom.stalkMap (E.inv.base z)).hom =
      (D.presheaf.stalkSpecializes (specializes_of_eq hz)).hom := by
    simpa only [CommRingCat.hom_comp] using
      congrArg (fun H => H.hom) (LocallyRingedSpace.stalkMap_hom_inv E z)
  calc
    _ = Ideal.map (E.inv.stalkMap z).hom
        (Ideal.map (E.hom.stalkMap (E.inv.base z)).hom (I (E.hom.base (E.inv.base z)))) :=
      congrArg (Ideal.map (E.inv.stalkMap z).hom) (h (E.inv.base z)).symm
    _ = _ := by rw [Ideal.map_map,hs]; exact idealFamily_map_specializes I hz

private theorem ideal_map_stalk_comp {A D T : LocallyRingedSpace} (f : A ⟶ D) (g : D ⟶ T)
    (x : A) (I : Ideal (T.presheaf.stalk ((f ≫ g).base x)).carrier) :
    Ideal.map ((f ≫ g).stalkMap x).hom I =
      Ideal.map (f.stalkMap x).hom (Ideal.map (g.stalkMap (f.base x)).hom I) := by
  calc
    _ = Ideal.map (g.stalkMap (f.base x) ≫ f.stalkMap x).hom I :=
      congrArg (fun h : T.presheaf.stalk ((f ≫ g).base x) ⟶ A.presheaf.stalk x =>
        Ideal.map h.hom I) (LocallyRingedSpace.stalkMap_comp f g x)
    _ = _ := (Ideal.map_map (g.stalkMap (f.base x)).hom (f.stalkMap x).hom).symm

private theorem pulled_ideal_span {A T : LocallyRingedSpace} (f : A ⟶ T)
    (B : SheafOfModules.{0} (forgetRing T.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing T.toSheafedSpace.sheaf))
    (U : Opens T.toTopCat) {r : ℕ} (s : Fin r → B.val.obj (op U))
    (hspan : ∀ (y : T) (hy : y ∈ U),
      LinearMap.range (stalkInclusionLinearMap T.toSheafedSpace.sheaf B b y) =
        Ideal.span (Set.range fun i => T.presheaf.germ U y hy (b.val.app (op U) (s i))))
    (x : A) (hx : f.base x ∈ U) :
    nativePulledIdealStalkIdeal f B b x =
      Ideal.span (Set.range fun i => A.presheaf.germ ((Opens.map f.base).obj U) x hx
        (f.c.app (op U) (b.val.app (op U) (s i)))) := by
  unfold nativePulledIdealStalkIdeal
  rw [hspan (f.base x) hx]
  erw [Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact LocallyRingedSpace.stalkMap_germ_apply f U x hx (b.val.app (op U) (s i))

variable {X : SourceReducedComplexSpace}

private abbrev embeddingMap (e : LocalEmbedding X) :
    actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map

private instance embeddingMap_isOpenImmersion (e : LocalEmbedding X) :
    LocallyRingedSpace.IsOpenImmersion (embeddingMap e) := e.isOpenImmersion

private theorem embeddingMap_overPoint (e : LocalEmbedding X) :
    embeddingMap e ≫ X.obj.hom = subspacePointMap (n := e.dim) e.carrier := e.overPoint

/-- The SAME full original graph chart map, through the actual inverse graph
isomorphism, actual source open inclusion and GIVEN original embedding. -/
def chartGraphMap (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G) :
    actualSubspaceLocallyRingedSpace (n := e.dim+r)
      (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G) ⟶ X.obj.left :=
  (productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).inv ≫
    actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ embeddingMap e

instance chartGraphMap_isOpenImmersion (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G) :
    LocallyRingedSpace.IsOpenImmersion (chartGraphMap e O G hG) := by
  unfold chartGraphMap
  infer_instance

/-- The full original complex-point triangle of the genuine graph chart. -/
theorem chartGraphMap_overPoint (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G) :
    chartGraphMap e O G hG ≫ X.obj.hom =
      subspacePointMap (n := e.dim+r) (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G) := by
  let E := productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG
  have hp : (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ embeddingMap e) ≫ X.obj.hom =
      subspacePointMap (n := e.dim) ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) := by
    rw [Category.assoc,embeddingMap_overPoint]
    exact HironakaReducedComplexAnalyticSpaces.actualSubspaceMap_point
      contMDiff_subtype_val (fun _ hu => hu)
  change (E.inv ≫ (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ embeddingMap e)) ≫ _ = _
  rw [Category.assoc,hp]
  calc
    _ = E.inv ≫ (E.hom ≫ subspacePointMap (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)) :=
      congrArg (fun f => E.inv ≫ f) (productGraphIso_hom_point _ G hG).symm
    _ = _ := by rw [← Category.assoc,E.inv_hom_id,Category.id_comp]

/-- The original point map is the literal first-projection chart point. -/
theorem chartGraphMap_base (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
    (z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G) :
    (chartGraphMap e O G hG).base z = e.toPoint ⟨z.val.1.val,z.property.1⟩ := rfl

/-- The SAME full graph map packaged in the EXISTING original category. -/
def chartGraphMorphism (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
    (hΓ : IsComplexAnalyticSubset (n := e.dim+r)
      (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)) :
    ofClosedAnalytic (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G) hΓ ⟶ X :=
  ObjectProperty.homMk (Over.homMk (chartGraphMap e O G hG) (chartGraphMap_overPoint e O G hG))

section Ideal

variable (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]

/-- Standard finite type is used on GLOBAL ORIGINAL X first. Actual chart
components pull only the literal original functions. BOTH entire graph ideal
dictionaries are then DERIVED, on S and on the literal Γ respectively. -/
theorem exists_graph_chart_on_embedding (e : LocalEmbedding X) (w : e.carrier) :
    ∃ (O : Opens e.ambient) (_hwO : w.val ∈ O) (r : ℕ)
      (G : O → ComplexModel r)
      (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
      (_hΓ : IsComplexAnalyticSubset (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)),
      (∀ y : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier),
        Ideal.map (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
          actualSubspaceInclusion (n := e.dim+r)
            (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
            {q : O × ComplexModel r | q.2 = 0})
              (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
                actualSubspaceInclusion (n := e.dim+r)
                  (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).base y)) =
          nativePulledIdealStalkIdeal (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ e.map) B b y) ∧
      (∀ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        Ideal.map ((actualSubspaceInclusion (n := e.dim+r)
          (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap z).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
              {q : O × ComplexModel r | q.2 = 0}) z.val) =
          nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z) ∧
      ∃ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        (chartGraphMap e O G hG).base z = e.toPoint w := by
  obtain ⟨U,hwU,r,s,_hep,hspan⟩ := exists_finite_ideal_sections B b (e.toPoint w)
  let f := embeddingMap e
  let V : Opens (TopCat.of e.carrier) := (Opens.map f.base).obj U
  let a : Fin r → ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.obj (op V)).carrier :=
    fun i => f.c.app (op U) (b.val.app (op U) (s i))
  have hwV : w ∈ V := hwU
  obtain ⟨O,hwO,G,hG,hOV,hΓ,hgraph⟩ :=
    exists_product_graph_of_finite_sections e.carrier e.analytic V a w hwV
  let S := (Subtype.val : O → e.ambient) ⁻¹' e.carrier
  let Γ := productGraph S G
  let E := productGraphIso S G hG
  let j := actualOpenSubspaceMap (n := e.dim) e.carrier O
  let F := j ≫ f
  have hparam (y : S) :
      Ideal.map ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap y).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
          {q : O × ComplexModel r | q.2 = 0})
            ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y)) =
        nativePulledIdealStalkIdeal F B b y := by
    rw [hgraph y,nativePulledIdealStalkIdeal_comp j f B b y]
    apply congrArg (Ideal.map (j.stalkMap y).hom)
    have hyU : f.base (j.base y) ∈ U := hOV (j.base y) y.val.property
    exact (pulled_ideal_span f B b U s hspan (j.base y) hyU).symm
  let I : ∀ z : Γ, Ideal ((actualSubspaceLocallyRingedSpace (n := e.dim+r) Γ).presheaf.stalk z).carrier :=
    fun z => Ideal.map ((actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap z).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
        {q : O × ComplexModel r | q.2 = 0}) z.val)
  have hforward (y : S) : Ideal.map (E.hom.stalkMap y).hom (I (E.hom.base y)) =
      nativePulledIdealStalkIdeal F B b y := by
    exact (ideal_map_stalk_comp E.hom (actualSubspaceInclusion (n := e.dim+r) Γ) y
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
        {q : O × ComplexModel r | q.2 = 0})
          ((E.hom ≫ actualSubspaceInclusion (n := e.dim+r) Γ).base y))).symm.trans (hparam y)
  have hΓideal (z : Γ) : I z = nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z := by
    change I z = nativePulledIdealStalkIdeal (E.inv ≫ F) B b z
    rw [nativePulledIdealStalkIdeal_comp]
    exact (idealFamily_map_iso_inverse E I (fun y => nativePulledIdealStalkIdeal F B b y) hforward z).symm
  refine ⟨O,hwO,r,G,hG,hΓ,hparam,hΓideal,?_⟩
  refine ⟨⟨(⟨w.val,hwO⟩,G ⟨w.val,hwO⟩),⟨w.property,rfl⟩⟩,?_⟩
  rfl

/-- Every ORIGINAL point has an ACTUAL graph chart, with BOTH entire
original global-ideal dictionaries and a genuine original graph point over it. -/
theorem exists_graph_chart (x : X.obj.left) :
    ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (r : ℕ)
      (G : O → ComplexModel r)
      (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
      (_hΓ : IsComplexAnalyticSubset (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)),
      (∀ y : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier),
        Ideal.map (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
          actualSubspaceInclusion (n := e.dim+r)
            (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap y).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
            {q : O × ComplexModel r | q.2 = 0})
              (((productGraphIso ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G hG).hom ≫
                actualSubspaceInclusion (n := e.dim+r)
                  (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).base y)) =
          nativePulledIdealStalkIdeal (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ e.map) B b y) ∧
      (∀ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        Ideal.map ((actualSubspaceInclusion (n := e.dim+r)
          (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap z).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
              {q : O × ComplexModel r | q.2 = 0}) z.val) =
          nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z) ∧
      ∃ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        (chartGraphMap e O G hG).base z = x := by
  obtain ⟨d,U,W,hW,i,hi,hip,w,hw⟩ := X.property.2.2 x
  let e : LocalEmbedding X :=
    { dim := d, ambient := U, carrier := W, analytic := hW,
      map := i, isOpenImmersion := hi, overPoint := hip }
  obtain ⟨O,_hwO,r,G,hG,hΓ,hparam,hΓideal,z,hz⟩ := exists_graph_chart_on_embedding B b e w
  exact ⟨e,O,r,G,hG,hΓ,hparam,hΓideal,z,hz.trans hw⟩

end Ideal

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart

import Hironaka.Analytic.Unibranch.EmbeddedBlowupObjectGluing
import Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversalSheaf
import Hironaka.Resolution.HironakaNativePulledIdealStalk
import Hironaka.Resolution.HironakaIntrinsicReducedCentreIdealModel
import Hironaka.Resolution.HironakaIntrinsicReducedCentreChartIdeal

/-!
# Genuine local source lifts for the global intrinsic TARGET-centre ideal

The source A is ORIGINAL and arbitrary: no global source countability,
chosen local lift or ideal dictionary is supplied. The actual source images
of the reduced target ideal stay WHOLE and can be nonradical.
Blueprint: `embedded-blowup-global-universal-local.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularModuleSheafStalk
  HironakaSingularLocallyFreeStalk HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreChartIdeal
  HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaSingularIdealRegularPrincipal SourceReducedComplexSpace EmbeddedBlowupOverlap
  EmbeddedBlowupUniversal

noncomputable section

/-- Standard native rank-one data identify the invertible WHOLE actual
pulled ideal using the PROVED exact native stalk equivalence. -/
theorem moduleInvertible_nativePulledIdeal_of_locallyFreeData
    {A B : LocallyRingedSpace.{0}} (F : A ⟶ B)
    (M : SheafOfModules.{0} (forgetRing B.toSheafedSpace.sheaf))
    (b : M ⟶ SheafOfModules.unit (forgetRing B.toSheafedSpace.sheaf))
    (q : (nativePulledIdealModule F M b).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] (x : A) :
    Module.Invertible (A.presheaf.stalk x).carrier (nativePulledIdealStalkIdeal F M b x) := by
  let : Module.Invertible (A.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (nativePulledIdealModule F M b).val.presheaf x) :=
    stalkInvertible_of_locallyFreeData A.toSheafedSpace.sheaf q x
  exact Module.Invertible.congr (nativePulledIdealStalkIdealEquiv F M b x)

/-- Whole native pulled ideal images compose through the ORIGINAL stalk maps.
This is a generic API connection, with no separate milestone credit. -/
theorem nativePulledIdealStalkIdeal_comp {A B D : LocallyRingedSpace.{0}}
    (F : A ⟶ B) (j : B ⟶ D)
    (M : SheafOfModules.{0} (forgetRing D.toSheafedSpace.sheaf))
    (b : M ⟶ SheafOfModules.unit (forgetRing D.toSheafedSpace.sheaf)) (x : A) :
    nativePulledIdealStalkIdeal (F ≫ j) M b x =
      Ideal.map (F.stalkMap x).hom (nativePulledIdealStalkIdeal j M b (F.base x)) := by
  unfold nativePulledIdealStalkIdeal
  rw [Ideal.map_map, LocallyRingedSpace.stalkMap_comp]
  rfl

variable {X : SourceReducedComplexSpace} {ι : Type} (E : ι → LocalEmbedding X)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : (E i).carrier), (E i).toPoint w = x)

include hcover in
/-- An actual source LocalEmbedding is internally chosen inside the inverse
image of one GIVEN original target chart; full factorization is derived. -/
theorem exists_source_chart_factor (A : SourceReducedComplexSpace) (F : A ⟶ X) (x : A.obj.left) :
    ∃ (i : ι) (a : LocalEmbedding A) (z : a.carrier)
      (G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic (E i).carrier (E i).analytic),
      a.toPoint z = x ∧ G ≫ chartMorphism (E i) = chartMorphism a ≫ F := by
  obtain ⟨i, w, hw⟩ := hcover (F.hom.left.base x)
  let N : Set A.obj.left := F.hom.left.base ⁻¹' range (E i).toPoint
  have hN : IsOpen N := (E i).isOpen_range_toPoint.preimage F.hom.left.base.hom.continuous
  have hxN : x ∈ N := ⟨w, hw⟩
  obtain ⟨a, hxA, haN, _⟩ := LocalEmbedding.exists_domain x hN hxN
  obtain ⟨z, hzx⟩ := hxA
  let : LocallyRingedSpace.IsOpenImmersion (E i).map := (E i).isOpenImmersion
  have hr : range (a.map ≫ F.hom.left).base ⊆ range (E i).map.base := by
    rintro _ ⟨y, rfl⟩
    exact haN ⟨y, rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift (E i).map (a.map ≫ F.hom.left) hr
  have hL : L ≫ (E i).map = a.map ≫ F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac (E i).map (a.map ≫ F.hom.left) hr
  have hp : L ≫ subspacePointMap (n := (E i).dim) (E i).carrier =
      subspacePointMap (n := a.dim) a.carrier := by
    calc
      _ = L ≫ ((E i).map ≫ X.obj.hom) := congrArg (fun t => L ≫ t) (E i).overPoint.symm
      _ = (L ≫ (E i).map) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = (a.map ≫ F.hom.left) ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) hL
      _ = a.map ≫ (F.hom.left ≫ X.obj.hom) := Category.assoc _ _ _
      _ = a.map ≫ A.obj.hom := congrArg (fun t => a.map ≫ t) (Over.w F.hom)
      _ = _ := a.overPoint
  let G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic (E i).carrier (E i).analytic :=
    ObjectProperty.homMk (Over.homMk L hp)
  refine ⟨i, a, z, G, hzx, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hL

private theorem source_chart_ideal_eq (e : LocalEmbedding X) {C₀ : Set e.ambient}
    (hCW : C₀ ⊆ e.carrier) (Z : Set X.obj.left)
    (htrace : ∀ w : e.carrier, w.val ∈ C₀ ↔ e.toPoint w ∈ Z)
    (A : SourceReducedComplexSpace) (F : A ⟶ X) (a : LocalEmbedding A)
    (G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic e.carrier e.analytic)
    (hG : G ≫ chartMorphism e = chartMorphism a ≫ F) (z : a.carrier) :
    nativePulledIdealStalkIdeal (a.map ≫ F.hom.left)
        (intrinsicReducedCentreIdealModule X.obj.left Z)
        (intrinsicReducedCentreIdealInclusion X.obj.left Z) z =
      Ideal.map (G.hom.left.stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap (G.hom.left.base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim) C₀) (G.hom.left.base z).val)) := by
  let B := intrinsicReducedCentreIdealModule X.obj.left Z
  let b := intrinsicReducedCentreIdealInclusion X.obj.left Z
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  have hraw : G.hom.left ≫ e.map = a.map ≫ F.hom.left :=
    congrArg (fun H => H.hom.left) hG
  calc
    _ = nativePulledIdealStalkIdeal (G.hom.left ≫ e.map) B b z :=
      (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier ⟶ X.obj.left =>
        nativePulledIdealStalkIdeal H B b z) hraw).symm
    _ = Ideal.map (G.hom.left.stalkMap z).hom
        (nativePulledIdealStalkIdeal e.map B b (G.hom.left.base z)) :=
      nativePulledIdealStalkIdeal_comp G.hom.left e.map B b z
    _ = _ := congrArg (Ideal.map (G.hom.left.stalkMap z).hom)
      (chart_pulled_stalkIdeal_eq e.map Z hCW (fun w => (htrace w).symm) (G.hom.left.base z))

variable {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (E i).dim) (Y i)]
  [∀ i, IsComplexManifold (E i).dim (Y i)]
  {C : ∀ i, Set (E i).ambient} {π : ∀ i, Y i → (E i).ambient}
  (hπ : ∀ i, IsBlowupAlong (E i).dim (C i) (π i))
  (hCW : ∀ i, C i ⊆ (E i).carrier) (Z : Set X.obj.left)
  (htrace : ∀ i (w : (E i).carrier), w.val ∈ C i ↔ (E i).toPoint w ∈ Z)

include hcover hCW htrace in
/-- Standard native rank-one data on the SAME global pulled ideal internally
produce actual source-open lifts, native charts and DENSE global good loci.
The original arbitrary A has NO global second-countability assumption. -/
theorem exists_local_source_lift (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (q : (nativePulledIdealModule F.hom.left
      (intrinsicReducedCentreIdealModule X.obj.left Z)
      (intrinsicReducedCentreIdealInclusion X.obj.left Z)).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ t, Unique (q.generators t).I] (x : A.obj.left) :
    ∃ (i : ι) (P : LocallyRingedSpace) (j : P ⟶ A.obj.left)
      (K : P ⟶ EmbeddedBlowupObjectGluing.localObject E hπ i),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      hasAnalyticCharts (Over.mk (j ≫ A.obj.hom)) ∧
      K ≫ EmbeddedBlowupObjectGluing.localProjection E hπ i = j ≫ F.hom.left ∧
      Dense {u : P | F.hom.left.base (j.base u) ∉ Z} := by
  obtain ⟨i, a, z, G, haz, hG⟩ := exists_source_chart_factor E hcover A F x
  let B := intrinsicReducedCentreIdealModule X.obj.left Z
  let b := intrinsicReducedCentreIdealInclusion X.obj.left Z
  let : LocallyRingedSpace.IsOpenImmersion a.map := a.isOpenImmersion
  have hInvG : ∀ w : a.carrier,
      Module.Invertible ((ofClosedAnalytic a.carrier a.analytic).obj.left.presheaf.stalk w).carrier
        (Ideal.map (G.hom.left.stalkMap w).hom
          (Ideal.map ((actualSubspaceInclusion (n := (E i).dim) (E i).carrier).stalkMap
              (G.hom.left.base w)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := (E i).dim) (C i))
              (G.hom.left.base w).val))) := by
    intro w
    let I := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      (F.hom.left.base (a.map.base w)))
    have hInv := moduleInvertible_nativePulledIdeal_of_locallyFreeData F.hom.left B b q (a.toPoint w)
    obtain ⟨alpha, hreg, hspan⟩ := exists_regular_generator_on_open_chart a.map F.hom.left w I hInv
    have hspan' : nativePulledIdealStalkIdeal (a.map ≫ F.hom.left) B b w = Ideal.span {alpha} := hspan
    exact moduleInvertible_of_span_eq _
      ((source_chart_ideal_eq (E i) (hCW i) Z (htrace i) A F a G hG w).symm.trans hspan') hreg
  obtain ⟨P, j₀, K, hj₀, hzj, hP, _, hK, hd⟩ :=
    exists_local_source_factorization_of_module_invertible (hπ i) (E i).analytic
      (ofClosedAnalytic a.carrier a.analytic) G hInvG z
  let : LocallyRingedSpace.IsOpenImmersion j₀ := hj₀
  let j := j₀ ≫ a.map
  have hraw : G.hom.left ≫ (E i).map = a.map ≫ F.hom.left :=
    congrArg (fun H => H.hom.left) hG
  refine ⟨i, P, j, K, inferInstance, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hzj
    refine ⟨u, ?_⟩
    change a.map.base (j₀.base u) = x
    rw [hu]
    exact haz
  · change hasAnalyticCharts (Over.mk ((j₀ ≫ a.map) ≫ A.obj.hom))
    rw [Category.assoc, a.overPoint]
    exact hP
  · calc
      _ = (K ≫ strictTransformProjection (hπ i) (E i).analytic.isClosed) ≫ (E i).map := by
        simp only [EmbeddedBlowupObjectGluing.localProjection, id_eq, Category.assoc]
      _ = (j₀ ≫ G.hom.left) ≫ (E i).map := congrArg (fun t => t ≫ (E i).map) hK
      _ = j₀ ≫ (G.hom.left ≫ (E i).map) := Category.assoc _ _ _
      _ = j₀ ≫ (a.map ≫ F.hom.left) := congrArg (fun t => j₀ ≫ t) hraw
      _ = _ := (Category.assoc _ _ _).symm
  · have hset : {u : P | F.hom.left.base (j.base u) ∉ Z} =
        {u : P | (G.hom.left.base (j₀.base u)).val ∉ C i} := by
      ext u
      have hp : (E i).toPoint (G.hom.left.base (j₀.base u)) =
          F.hom.left.base (j.base u) := congrArg (fun H => H.base (j₀.base u)) hraw
      exact (not_congr ((htrace i (G.hom.left.base (j₀.base u))).trans
        (iff_of_eq (congrArg (fun y => y ∈ Z) hp)))).symm
    rw [hset]
    exact hd

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal

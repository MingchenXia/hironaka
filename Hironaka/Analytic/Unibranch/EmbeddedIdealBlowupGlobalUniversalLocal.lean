import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOverlap
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal

/-!
# Actual local source lifts for the same native whole target ideal

Original source charts and the complete local ideal dictionaries retain all
pulled-source multiplicities. Standard native locally-free singleton data
derive actual invertibility, genuine local lifts, and dense good source opens.
Neither global source countability nor a reduced-centre ideal is introduced.
Blueprint: `embedded-ideal-blowup-global-universal-local.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversalLocal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaSingularIdealRegularPrincipal SourceReducedComplexSpace EmbeddedBlowupOverlap
  EmbeddedBlowupUniversal EmbeddedBlowupGlobalUniversalLocal EmbeddedIdealBlowupNonunitLocus

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ} {M : ι → Type}
  [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (ComplexModel (n i)) (M i)]
  [∀ i, IsComplexManifold (n i) (M i)] {W : ∀ i, Set (M i)}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

include hcover in
/-- Actual source local embeddings are chosen inside a GIVEN actual target chart. -/
theorem exists_source_chart_factor (A : SourceReducedComplexSpace) (F : A ⟶ X) (x : A.obj.left) :
    ∃ (i : ι) (a : LocalEmbedding A) (z : a.carrier)
      (G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic (W i) (hW i)),
      a.toPoint z = x ∧ G ≫ J i = chartMorphism a ≫ F := by
  obtain ⟨i, w, hw⟩ := hcover (F.hom.left.base x)
  let N : Set A.obj.left := F.hom.left.base ⁻¹' range (J i).hom.left.base
  have hN : IsOpen N := (hJopen i).base_open.isOpen_range.preimage F.hom.left.base.hom.continuous
  have hxN : x ∈ N := ⟨w, hw⟩
  obtain ⟨a, hxA, haN, _⟩ := LocalEmbedding.exists_domain x hN hxN
  obtain ⟨z, hzx⟩ := hxA
  have hr : range (a.map ≫ F.hom.left).base ⊆ range (J i).hom.left.base := by
    rintro _ ⟨y, rfl⟩
    exact haN ⟨y, rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift (J i).hom.left (a.map ≫ F.hom.left) hr
  have hL : L ≫ (J i).hom.left = a.map ≫ F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac (J i).hom.left (a.map ≫ F.hom.left) hr
  have hp : L ≫ subspacePointMap (n := n i) (W i) =
      subspacePointMap (n := a.dim) a.carrier := by
    calc
      _ = L ≫ ((J i).hom.left ≫ X.obj.hom) :=
        congrArg (fun t => L ≫ t) (Over.w (J i).hom).symm
      _ = (L ≫ (J i).hom.left) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = (a.map ≫ F.hom.left) ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) hL
      _ = a.map ≫ (F.hom.left ≫ X.obj.hom) := Category.assoc _ _ _
      _ = a.map ≫ A.obj.hom := congrArg (fun t => a.map ≫ t) (Over.w F.hom)
      _ = _ := a.overPoint
  let G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic (W i) (hW i) :=
    ObjectProperty.homMk (Over.homMk L hp)
  refine ⟨i, a, z, G, hzx, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hL

variable {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (J i).hom.left B b y)

include hJ in
omit hJopen in
private theorem source_chart_ideal_eq (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (a : LocalEmbedding A) (i : ι)
    (G : ofClosedAnalytic a.carrier a.analytic ⟶ ofClosedAnalytic (W i) (hW i))
    (hG : G ≫ J i = chartMorphism a ≫ F) (z : a.carrier) :
    nativePulledIdealStalkIdeal (a.map ≫ F.hom.left) B b z =
      Ideal.map (G.hom.left.stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap (G.hom.left.base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) (G.hom.left.base z).val)) := by
  have hraw : G.hom.left ≫ (J i).hom.left = a.map ≫ F.hom.left :=
    congrArg (fun H => H.hom.left) hG
  calc
    _ = nativePulledIdealStalkIdeal (G.hom.left ≫ (J i).hom.left) B b z :=
      (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier ⟶ X.obj.left =>
        nativePulledIdealStalkIdeal H B b z) hraw).symm
    _ = Ideal.map (G.hom.left.stalkMap z).hom
        (nativePulledIdealStalkIdeal (J i).hom.left B b (G.hom.left.base z)) :=
      nativePulledIdealStalkIdeal_comp G.hom.left (J i).hom.left B b z
    _ = _ := congrArg (Ideal.map (G.hom.left.stalkMap z).hom) (hJ i (G.hom.left.base z)).symm

include hJ hcover in
/-- SAME global whole-ideal q produces genuine local lifts and dense original good loci. -/
theorem exists_local_source_lift (A : SourceReducedComplexSpace) (F : A ⟶ X)
    (q : (nativePulledIdealModule F.hom.left B b).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ t, Unique (q.generators t).I] (x : A.obj.left) :
    ∃ (i : ι) (P : LocallyRingedSpace) (j : P ⟶ A.obj.left)
      (K : P ⟶ (EmbeddedIdealBlowupOverlap.localSpace hW hπ i).obj.left),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      hasAnalyticCharts (Over.mk (j ≫ A.obj.hom)) ∧
      K ≫ (EmbeddedIdealBlowupOverlap.localProjection hW hπ J i).hom.left = j ≫ F.hom.left ∧
      Dense {u : P | F.hom.left.base (j.base u) ∉ nonunitLocus B b} := by
  obtain ⟨i, a, z, G, haz, hG⟩ := exists_source_chart_factor hW J hcover A F x
  let : LocallyRingedSpace.IsOpenImmersion a.map := a.isOpenImmersion
  have hInvG : ∀ w : a.carrier,
      Module.Invertible ((ofClosedAnalytic a.carrier a.analytic).obj.left.presheaf.stalk w).carrier
        (Ideal.map (G.hom.left.stalkMap w).hom
          (Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap (G.hom.left.base w)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) (G.hom.left.base w).val))) := by
    intro w
    let I := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      (F.hom.left.base (a.map.base w)))
    have hInv := moduleInvertible_nativePulledIdeal_of_locallyFreeData F.hom.left B b q (a.toPoint w)
    obtain ⟨alpha, hreg, hspan⟩ := exists_regular_generator_on_open_chart a.map F.hom.left w I hInv
    have hspan' : nativePulledIdealStalkIdeal (a.map ≫ F.hom.left) B b w = Ideal.span {alpha} := hspan
    exact moduleInvertible_of_span_eq _
      ((source_chart_ideal_eq hW J B b hJ A F a i G hG w).symm.trans hspan') hreg
  obtain ⟨P, j₀, K, hj₀, hzj, hP, _, hK, hd⟩ :=
    exists_local_source_factorization_of_module_invertible (hπ i) (hW i)
      (ofClosedAnalytic a.carrier a.analytic) G hInvG z
  let : LocallyRingedSpace.IsOpenImmersion j₀ := hj₀
  let j := j₀ ≫ a.map
  have hraw : G.hom.left ≫ (J i).hom.left = a.map ≫ F.hom.left :=
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
  · change K ≫ (strictTransformProjection (hπ i) (hW i).isClosed ≫ (J i).hom.left) = j ≫ F.hom.left
    rw [← Category.assoc, hK, Category.assoc, hraw]
    rfl
  · have hset : {u : P | F.hom.left.base (j.base u) ∉ nonunitLocus B b} =
        {u : P | (G.hom.left.base (j₀.base u)).val ∉ C i} := by
      ext u
      have hp : (J i).hom.left.base (G.hom.left.base (j₀.base u)) =
          F.hom.left.base (j.base u) := congrArg (fun H => H.base (j₀.base u)) hraw
      exact (not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ i (G.hom.left.base (j₀.base u))).trans
        (iff_of_eq (congrArg (fun y => y ∈ nonunitLocus B b) hp)))).symm
    rw [hset]
    exact hd

end

end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupGlobalUniversalLocal

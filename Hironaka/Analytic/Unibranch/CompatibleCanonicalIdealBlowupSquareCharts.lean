import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotChart
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupSquare
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace
import Hironaka.Resolution.HironakaRealOpenGeometricStrictSaturation
import Hironaka.Resolution.HironakaVanishingQuotientOriginalSubspaceBridge

/-! SAME pulled-list ORIGINAL canonical GEOMETRIC square and whole generator loci.
BP FIRST: three ordinary-input public producers; all scalar/sheaf squares are native.
The compatible SATURATED quotient charts/whole P0,Q0/graph-kernel/raw-fibre and
full G10/S0 comparison remain OPEN in the explicit work FRONTIER/leaf plan.
No future chart, Cartier, UP, cover, lift, saturation or kernel packet is input.
Native Hadamard/whole ideal/Cartier/UP/graph factories receive zero duplicate credit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupFlatCoordinates GiraudAlong RelativePrincipalizationSpan DerivativeIdealAlong
  ProductComplexManifold HironakaSmoothSubmersionOrderedChoiceImageTrace
  BlowupStrictSubmanifold
open scoped ProductComplexManifold

section ZeroPlane
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

-- Reused native product chart/normal-coordinate plumbing, zero engine credit.
private def productChartIdentity (p : P × ComplexModel r) :
    LocalHolomorphicEquivAt (n := n+r) (chartAt (ComplexModel (n+r)) p p) where
  source := (chartAt (ComplexModel (n+r)) p).target
  target := (chartAt (ComplexModel (n+r)) p).target
  isOpen_source := (chartAt (ComplexModel (n+r)) p).open_target
  isOpen_target := (chartAt (ComplexModel (n+r)) p).open_target
  center_mem_source := (chartAt (ComplexModel (n+r)) p).map_source (mem_chart_source _ p)
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := fun _ h => h
  mapsTo_invFun := fun _ h => h
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

omit [IsComplexManifold n P] in
private theorem product_chart_normal (p q : P × ComplexModel r) (i : Fin r) :
    (chartAt (ComplexModel (n+r)) p q) (i.natAdd n)=q.2 i := by
  change (prodModelEquiv n r ((chartAt (ComplexModel n) p.1) q.1,
    (chartAt (ComplexModel r) p.2) q.2)) (i.natAdd n)=q.2 i
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
    chartAt_self_eq]

private theorem normal_holomorphic (p : P × ComplexModel r) (i : Fin r) :
    HolomorphicAt (n+r) (fun q : P × ComplexModel r => q.2 i) p :=
  Eventually.of_forall fun _ =>
    (((EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ).contMDiff.comp
      ProductComplexManifold.contMDiff_snd).contMDiffAt).mdifferentiableAt (by simp)

private theorem normal_mem_zero_plane (p : P × ComplexModel r) (i : Fin r) :
    (vanishingIdeal (n := n+r) {q : P × ComplexModel r | q.2=0}).mem p
      (fun q => q.2 i) := by
  refine ⟨normal_holomorphic p i,Eventually.of_forall fun q hq => ?_⟩
  change q.2=0 at hq
  change q.2 i=0
  rw [hq]
  rfl

/-- The actual whole normal-coordinate ideal dictionary at EVERY point.
This is a function-germ consumer of held Hadamard, including off-plane/unit
points and r=0; no separate generic ideal engine credit. -/
private theorem zero_plane_mem_iff_span (p : P × ComplexModel r) (g : P × ComplexModel r → ℂ) :
    (vanishingIdeal (n := n+r) {q : P × ComplexModel r | q.2=0}).mem p g ↔
      IsInSpanAt (n := n+r) (· ∈ range (fun i : Fin r => fun q : P × ComplexModel r => q.2 i)) p g := by
  let Φ := productChartIdentity (n := n) p
  have hsrc : Φ.source ⊆ (chartAt (ComplexModel (n+r)) p).target := Subset.rfl
  have hflat : ∀ {q : P × ComplexModel r}, q ∈ (chartAt (ComplexModel (n+r)) p).source →
      chartAt (ComplexModel (n+r)) p q ∈ Φ.source →
      (q ∈ {q : P × ComplexModel r | q.2=0} ↔
        Φ.toFun (chartAt (ComplexModel (n+r)) p q) ∈ complexCoordinatePlane (n+r) n) := by
    intro q _ _
    change q.2=0 ↔ ∀ i : Fin (n+r),n ≤ i.val → (chartAt (ComplexModel (n+r)) p q) i=0
    constructor
    · intro hq i hi
      let j : Fin r := ⟨i.val-n,by omega⟩
      have he : j.natAdd n=i := Fin.ext (by dsimp [j];omega)
      rw [←he,product_chart_normal,hq]
      rfl
    · intro hq
      ext i
      rw [←product_chart_normal (n := n) p q i]
      exact hq (i.natAdd n) (by simp)
  constructor
  · intro hg
    obtain ⟨b,hb0,hb,he⟩ := exists_eq_sum_flatCoord Φ hsrc hflat (mem_flatDomain_self Φ) hg
    refine ⟨hg.1,r,(fun i q => q.2 i),(fun i => b (i.natAdd n)),fun i => ⟨i,rfl⟩,
      fun i => hb (i.natAdd n),?_⟩
    filter_upwards [he] with q hq
    rw [hq,Fin.sum_univ_add]
    have hzero : (∑ i : Fin n,b (i.castAdd r) q * flatCoord Φ (i.castAdd r) q)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hb0 (i.castAdd r) i.isLt]
      simp
    rw [hzero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    change b (i.natAdd n) q * (chartAt (ComplexModel (n+r)) p q) (i.natAdd n)=_
    rw [product_chart_normal]
  · intro hg
    apply vanishingIdeal_mem_of_isInSpanAt
    exact hg.mono fun h ⟨i,hi⟩ => hi ▸ normal_mem_zero_plane p i

end ZeroPlane

section NormalProduct
variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)

private def normalProduct : P × ComplexModel r → Q × ComplexModel r :=
  Prod.map f id

include hf in
private theorem normalProduct_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ (normalProduct (r := r) f) :=
  contMDiff_prodMap hf contMDiff_id

include hf in
/-- SAME literal normals give WHOLE ideal equality, for arbitrary genuine f.
No submersion, future ideal dictionary or raw-ring cancellation is assumed. -/
private theorem normalProduct_zero_ideal :
    GermIdeal.pullback (m := n+r) (normalProduct (r := r) f)
      (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}) =
      vanishingIdeal (n := n+r) {p : P × ComplexModel r | p.2=0} := by
  apply GermIdeal.ext
  funext p g
  apply propext
  constructor
  · intro hg
    apply vanishingIdeal_mem_of_isInSpanAt
    refine (GermIdeal.mem_pullback_iff.mp hg).mono ?_
    rintro a ⟨b,hb,rfl⟩
    refine ⟨hb.1.comp_contMDiff (Eventually.of_forall fun z =>
      (normalProduct_holomorphic f hf).contMDiffAt),?_⟩
    have ht := ((normalProduct_holomorphic f hf).continuous.continuousAt (x := p)).tendsto
    filter_upwards [ht.eventually hb.2] with q hq hq0
    exact hq hq0
  · intro hg
    apply GermIdeal.mem_pullback_iff.mpr
    refine ((zero_plane_mem_iff_span (n := n) p g).mp hg).mono ?_
    rintro a ⟨i,rfl⟩
    exact ⟨(fun q : Q × ComplexModel r => q.2 i),
      normal_mem_zero_plane (n := m) (normalProduct f p) i,rfl⟩

end NormalProduct

section NormalBlowups
variable {n m r : ℕ} {P Q YS YT : Type}
  [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  [TopologicalSpace YS] [ChartedSpace (ComplexModel (n+r)) YS] [IsComplexManifold (n+r) YS]
  [TopologicalSpace YT] [ChartedSpace (ComplexModel (m+r)) YT] [IsComplexManifold (m+r) YT]
  (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
  (πS : YS → P × ComplexModel r)
  (hS : IsBlowupAlong (n+r) {p : P × ComplexModel r | p.2=0} πS)
  (πT : YT → Q × ComplexModel r)
  (hT : IsBlowupAlong (m+r) {q : Q × ComplexModel r | q.2=0} πT)

include hf hS in
private theorem normalProduct_base_ideal :
    GermIdeal.pullback (m := n+r) (normalProduct f ∘ πS)
      (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}) =
      GermIdeal.pullback (m := n+r) πS
        (vanishingIdeal (n := n+r) {p : P × ComplexModel r | p.2=0}) := by
  have hMembers : ∀ q a,
      (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}).mem q a →
        HolomorphicAt (m+r) a q := fun _ _ h => h.1
  exact (whole_pullback_comp (normalProduct_holomorphic f hf) hS.contMDiff
    (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}) hMembers).trans
      (congrArg (GermIdeal.pullback (m := n+r) πS) (normalProduct_zero_ideal f hf))

omit [IsComplexManifold (m+r) YT] in
include hf hS hT in
/-- The actual target native UP accepts this derived pullback of SOURCE OWN
invertibility in EVERY source dimension. No f-submersion or input lift.
This is a required consumer, with zero recredit for the held native UP. -/
private theorem existsUnique_normalProduct_lift :
    ∃! L : YS → YT,
      ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L ∧
        πT ∘ L=normalProduct f ∘ πS := by
  have hInv : (GermIdeal.pullback (m := n+r) (normalProduct f ∘ πS)
      (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0})).IsInvertible := by
    rw [normalProduct_base_ideal f hf πS hS]
    exact hS.2.2.2.1
  exact hT.2.2.2.2 (n+r) YS (normalProduct f ∘ πS)
    ((normalProduct_holomorphic f hf).comp hS.contMDiff) hInv

end NormalBlowups

-- Literal off-centre closure landing; generic topology has zero new engine credit.
private theorem normalProduct_strict_landing {r : ℕ} {P Q YS YT : Type}
    [TopologicalSpace YS] [TopologicalSpace YT]
    (f : P → Q) (πS : YS → P × ComplexModel r) (πT : YT → Q × ComplexModel r)
    (L : YS → YT) (hL : Continuous L) (hComm : πT ∘ L=normalProduct f ∘ πS)
    (WS : Set (P × ComplexModel r)) (WT : Set (Q × ComplexModel r))
    (hGraph : MapsTo (normalProduct f) WS WT) :
    MapsTo L (geoStrictTransform πS {p : P × ComplexModel r | p.2=0} WS)
      (geoStrictTransform πT {q : Q × ComplexModel r | q.2=0} WT) := by
  have hsub : πS ⁻¹' (WS \ {p : P × ComplexModel r | p.2=0}) ⊆
      L ⁻¹' closure (πT ⁻¹' (WT \ {q : Q × ComplexModel r | q.2=0})) := by
    intro z hz
    apply subset_closure
    change πT (L z)∈WT ∧ πT (L z)∉{q : Q × ComplexModel r | q.2=0}
    have hProj : πT (L z)=normalProduct f (πS z) := congrFun hComm z
    rw [hProj]
    exact ⟨hGraph hz.1,hz.2⟩
  exact closure_minimal hsub (isClosed_closure.preimage hL)

open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces
  HironakaFiniteSectionProductGraph

/-- The source list is LITERALLY G composed with f on its WHOLE actual open.
Only ordinary original-carrier landing is used; no strict landing input. -/
private theorem normalProduct_graph_maps {r : ℕ} {P Q : Type}
    (f : P → Q) (G : Q → ComplexModel r) (S : Set P) (T : Set Q)
    (hST : MapsTo f S T) :
    MapsTo (normalProduct f) (productGraph S (G ∘ f)) (productGraph T G) := by
  intro z hz
  exact ⟨hST hz.1,hz.2⟩

/-- Resetting an internally derived ambient representative to SAME target
functions leaves its FULL original reduced-carrier map unchanged. This uses
OLD vanishing-ideal subspaces only, never raw nonreduced point faithfulness. -/
private theorem reset_graph_map {n m r : ℕ} {P Q : Type}
    [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
    (S : Set P) (T : Set Q) (G : Q → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel r) ∞ G)
    (H : P → Q × ComplexModel r)
    (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (m+r)) ∞ H)
    (hLanding : ∀ z∈S,H z∈productGraph T G) :
    let f : P → Q := fun z => (H z).1
    let hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f := contMDiff_fst.comp hH
    ∃ hReset : ∀ z∈S,(f z,G (f z))∈productGraph T G,
      actualSubspaceMap (contMDiff_prodMk hf (hG.comp hf)) hReset =
        actualSubspaceMap hH hLanding := by
  dsimp only
  have hReset : ∀ z∈S,((H z).1,G (H z).1)∈productGraph T G :=
    fun z hz => ⟨(hLanding z hz).1,rfl⟩
  refine ⟨hReset,?_⟩
  apply actualSubspaceMap_eq_of_base_eq
  · exact actualSubspaceMap_point _ _
  · exact actualSubspaceMap_point _ _
  · ext z
    apply Subtype.ext
    exact Prod.ext rfl (hLanding z.val z.property).2.symm

open SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces

/-- An ordinary ORIGINAL open chart containing F(x) internally derives a
source chart, scalar-compatible native lift and FULL original square.
This held local-model/OI adapter has zero separate engine credit. -/
private theorem exists_source_chart_to_original_open
    {X S Y : SourceReducedComplexSpace} (F : X ⟶ S) (J : Y ⟶ S)
    [LocallyRingedSpace.IsOpenImmersion J.hom.left]
    (x : X.obj.left) (hx : F.hom.left.base x∈range J.hom.left.base) :
    ∃ (a : LocalEmbedding X) (z : a.carrier)
      (K : ofClosedAnalytic a.carrier a.analytic ⟶ Y),
      a.toPoint z=x ∧ K ≫ J=EmbeddedBlowupOverlap.chartMorphism a ≫ F := by
  let N : Set X.obj.left := F.hom.left.base ⁻¹' range J.hom.left.base
  have hN : IsOpen N :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion J.hom.left).base_open.isOpen_range.preimage
      F.hom.left.base.hom.continuous
  obtain ⟨a,hxa,haN,_⟩ := LocalEmbedding.exists_domain x hN hx
  obtain ⟨z,hzx⟩ := hxa
  have hRange : range (a.map ≫ F.hom.left).base ⊆ range J.hom.left.base := by
    rintro _ ⟨w,rfl⟩
    exact haN ⟨w,rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift J.hom.left (a.map ≫ F.hom.left) hRange
  have hL : L ≫ J.hom.left=a.map ≫ F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hRange
  have hPoint : L ≫ Y.obj.hom=(ofClosedAnalytic a.carrier a.analytic).obj.hom := by
    calc
      _ = L ≫ (J.hom.left ≫ S.obj.hom) :=
        congrArg (fun v => L ≫ v) (Over.w J.hom).symm
      _ = (L ≫ J.hom.left) ≫ S.obj.hom := (Category.assoc _ _ _).symm
      _ = (a.map ≫ F.hom.left) ≫ S.obj.hom := congrArg (fun v => v ≫ S.obj.hom) hL
      _ = a.map ≫ X.obj.hom := by rw [Category.assoc,Over.w F.hom]
      _ = _ := a.overPoint
  let K : ofClosedAnalytic a.carrier a.analytic ⟶ Y :=
    ObjectProperty.homMk (Over.homMk L hPoint)
  refine ⟨a,z,K,hzx,?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hL

open HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSingularSubspaceBlowupCartier HironakaProductZeroPlaneBlowup
  HironakaNativePulledIdealSheaf HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealComposition

private abbrev graphCentreStalkIdeal {n r : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    (S : Set P) (G : P → ComplexModel r) (z : productGraph S G) :=
  Ideal.map ((actualSubspaceInclusion (n := n+r) (productGraph S G)).stalkMap z).hom
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r)
      {q : P × ComplexModel r | q.2=0}) z.val)

/-- Actual normal identity transports the ENTIRE native centre ideal, including
all nonradical source ideal images, not just the underlying support. -/
private theorem normalProduct_graph_whole_centre {n m r : ℕ} {P Q : Type}
    [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
    (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (G : Q → ComplexModel r) (S : Set P) (T : Set Q) (hST : MapsTo f S T)
    (z : productGraph S (G ∘ f)) :
    let hMap := normalProduct_graph_maps f G S T hST
    let hNorm := normalProduct_holomorphic (r := r) f hf
    Ideal.map ((actualSubspaceMap hNorm hMap).stalkMap z).hom
      (graphCentreStalkIdeal (n := m) T G ((actualSubspaceMap hNorm hMap).base z)) =
      graphCentreStalkIdeal (n := n) S (G ∘ f) z := by
  dsimp only
  have hA : (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal
      (isClosedSubmanifold_product_zero_plane (n := m) (r := r) (M := Q))
  have hTransport := map_actualSubspace_stalk_ideal_pullback
    (normalProduct_holomorphic (r := r) f hf) (normalProduct_graph_maps f G S T hST)
    (vanishingIdeal (n := m+r) {q : Q × ComplexModel r | q.2=0}) hA z
  have hSame := congrArg
    (fun I : GermIdeal (n+r) (P × ComplexModel r) =>
      Ideal.map ((actualSubspaceInclusion (n := n+r) (productGraph S (G ∘ f))).stalkMap z).hom
        (actualWholeSheafStalkIdeal I z.val)) (normalProduct_zero_ideal (r := r) f hf)
  exact hTransport.trans hSame

/-- Private whole-dictionary composition: final ordinary caller DERIVES the
target dictionary and full square; neither is a public hypothesis. Every
native multiplicity in JF is retained. Generic image composition is 0credit. -/
private theorem source_graph_whole_dictionary
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (F : X ⟶ Y) {n m r : ℕ} {P Q : Type}
    [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
    (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (G : Q → ComplexModel r) (S : Set P) (T : Set Q) (hST : MapsTo f S T)
    (hΓS : IsComplexAnalyticSubset (n := n+r) (productGraph S (G ∘ f)))
    (hΓT : IsComplexAnalyticSubset (n := m+r) (productGraph T G))
    (JX : ofClosedAnalytic (productGraph S (G ∘ f)) hΓS ⟶ X)
    (JY : ofClosedAnalytic (productGraph T G) hΓT ⟶ Y)
    (hSquare : actualSubspaceMap (normalProduct_holomorphic (r := r) f hf)
        (normalProduct_graph_maps f G S T hST) ≫ JY.hom.left=JX.hom.left ≫ F.hom.left)
    (hTarget : ∀ y : productGraph T G,
      graphCentreStalkIdeal (n := m) T G y=nativePulledIdealStalkIdeal JY.hom.left B b y)
    (z : productGraph S (G ∘ f)) :
    graphCentreStalkIdeal (n := n) S (G ∘ f) z=
      nativePulledIdealStalkIdeal JX.hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z := by
  let H : actualSubspaceLocallyRingedSpace (n := n+r) (productGraph S (G ∘ f)) ⟶
      actualSubspaceLocallyRingedSpace (n := m+r) (productGraph T G) :=
    actualSubspaceMap (normalProduct_holomorphic (r := r) f hf)
      (normalProduct_graph_maps f G S T hST)
  let JXraw : actualSubspaceLocallyRingedSpace (n := n+r) (productGraph S (G ∘ f)) ⟶ X.obj.left :=
    JX.hom.left
  let JYraw : actualSubspaceLocallyRingedSpace (n := m+r) (productGraph T G) ⟶ Y.obj.left :=
    JY.hom.left
  have hSquareRaw : H ≫ JYraw=JXraw ≫ F.hom.left := hSquare
  have hCentre : graphCentreStalkIdeal (n := n) S (G ∘ f) z=
      Ideal.map (H.stalkMap z).hom (graphCentreStalkIdeal (n := m) T G (H.base z)) :=
    (normalProduct_graph_whole_centre f hf G S T hST z).symm
  have hTargetImage :
      Ideal.map (H.stalkMap z).hom (graphCentreStalkIdeal (n := m) T G (H.base z)) =
      Ideal.map (H.stalkMap z).hom (nativePulledIdealStalkIdeal JYraw B b (H.base z)) :=
    congrArg (Ideal.map (H.stalkMap z).hom) (hTarget (H.base z))
  have hComp : Ideal.map (H.stalkMap z).hom (nativePulledIdealStalkIdeal JYraw B b (H.base z)) =
      nativePulledIdealStalkIdeal (H ≫ JYraw) B b z :=
    (EmbeddedBlowupGlobalUniversalLocal.nativePulledIdealStalkIdeal_comp H JYraw B b z).symm
  have hImageSquare : nativePulledIdealStalkIdeal (H ≫ JYraw) B b z =
      nativePulledIdealStalkIdeal (JXraw ≫ F.hom.left) B b z :=
    congrArg
      (fun K : actualSubspaceLocallyRingedSpace (n := n+r) (productGraph S (G ∘ f)) ⟶ Y.obj.left =>
        nativePulledIdealStalkIdeal K B b z) hSquareRaw
  have hFinal : nativePulledIdealStalkIdeal (JXraw ≫ F.hom.left) B b z =
      nativePulledIdealStalkIdeal JXraw
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z :=
    (stalkIdeal_comp F.hom.left JXraw B b z).symm
  exact hCentre.trans (hTargetImage.trans (hComp.trans (hImageSquare.trans hFinal)))

open HironakaActualAnalyticSubspaceOpenRestriction
  HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting

-- Native inverse scalar law, inherited from the existing full graph isomorphism.
private theorem graphIso_inv_point {n r : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    (S : Set P) (G : P → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ G) :
    (productGraphIso S G hG).inv ≫ subspacePointMap (n := n) S =
      subspacePointMap (n := n+r) (productGraph S G) := by
  let E := productGraphIso S G hG
  calc
    _ = E.inv ≫ (E.hom ≫ subspacePointMap (n := n+r) (productGraph S G)) :=
      congrArg (fun v => E.inv ≫ v) (productGraphIso_hom_point S G hG).symm
    _ = _ := by rw [←Category.assoc,E.inv_hom_id,Category.id_comp]

/-- The actual ordinary source-chart/ambient-lift/reset assembly. Target
geometry is ordinary here and will be produced internally by676 in the
PUBLIC BFT caller; no supplied square or source dictionary is needed here. -/
private theorem exists_actual_compatible_source_graph
    {X Y : SourceReducedComplexSpace} (F : X ⟶ Y)
    {m r : ℕ} {Q : Type} [TopologicalSpace Q]
    [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
    (T : Set Q) (G : Q → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel r) ∞ G)
    (hΓT : IsComplexAnalyticSubset (n := m+r) (productGraph T G))
    (JT : ofClosedAnalytic (productGraph T G) hΓT ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion JT.hom.left]
    (x : X.obj.left) (hx : F.hom.left.base x∈range JT.hom.left.base) :
    ∃ (a : LocalEmbedding X) (z : a.carrier),
      ∃ (V : Opens a.ambient) (hzV : z.val∈V)
        (O : Opens V) (_hzO : (⟨z.val,hzV⟩ : V)∈O)
        (f : O → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel m) ∞ f)
        (hST : MapsTo f ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) T)
        (hΓS : IsComplexAnalyticSubset (n := a.dim+r)
          (productGraph ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f)))
        (JS : ofClosedAnalytic _ hΓS ⟶ X),
      LocallyRingedSpace.IsOpenImmersion JS.hom.left ∧
      actualSubspaceMap (normalProduct_holomorphic (r := r) f hf)
        (normalProduct_graph_maps f G _ T hST) ≫ JT.hom.left=JS.hom.left ≫ F.hom.left ∧
      ∃ zs : (ofClosedAnalytic _ hΓS).obj.left,JS.hom.left.base zs=x := by
  obtain ⟨a,z,K,hzx,hK⟩ := exists_source_chart_to_original_open F JT x hx
  let Kraw : actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier ⟶
      actualSubspaceLocallyRingedSpace (n := m+r) (productGraph T G) := K.hom.left
  have hKpoint : Kraw ≫ subspacePointMap (n := m+r) (productGraph T G) =
      subspacePointMap (n := a.dim) a.carrier := Over.w K.hom
  obtain ⟨V,hzV,O,hzO,H,hH,hLanding,hHfull⟩ :=
    exists_local_ambient_representative Kraw hKpoint z
  let S0 : Set O := (Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)
  have hSV : IsComplexAnalyticSubset (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val a.analytic
  have hS0 : IsComplexAnalyticSubset (n := a.dim) S0 :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hSV
  let f : O → Q := fun u => (H u).1
  have hf : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel m) ∞ f :=
    contMDiff_fst.comp hH
  have hST : MapsTo f S0 T := fun u hu => (hLanding u hu).1
  have hσ : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel r) ∞ (G ∘ f) := hG.comp hf
  obtain ⟨hReset,hResetEq⟩ := reset_graph_map S0 T G hG H hH hLanding
  have hΓS : IsComplexAnalyticSubset (n := a.dim+r) (productGraph S0 (G ∘ f)) :=
    productGraph_analytic S0 hS0 (G ∘ f) hσ
  let E := productGraphIso S0 (G ∘ f) hσ
  let jO : actualSubspaceLocallyRingedSpace (n := a.dim) S0 ⟶
      actualSubspaceLocallyRingedSpace (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) :=
    actualOpenSubspaceMap (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) O
  let jV : actualSubspaceLocallyRingedSpace (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) ⟶
      actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier := actualOpenSubspaceMap a.carrier V
  let j0 : actualSubspaceLocallyRingedSpace (n := a.dim) S0 ⟶
      actualSubspaceLocallyRingedSpace (n := a.dim) a.carrier := jO ≫ jV
  let Jraw : actualSubspaceLocallyRingedSpace (n := a.dim+r) (productGraph S0 (G ∘ f)) ⟶
      X.obj.left := E.inv ≫ (j0 ≫ a.map)
  have hjOpoint : jO ≫ subspacePointMap (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) =
      subspacePointMap (n := a.dim) S0 := actualSubspaceMap_point contMDiff_subtype_val (fun _ hu => hu)
  have hjVpoint : jV ≫ subspacePointMap (n := a.dim) a.carrier =
      subspacePointMap (n := a.dim) ((Subtype.val : V → a.ambient) ⁻¹' a.carrier) :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hu => hu)
  have hj0point : j0 ≫ subspacePointMap (n := a.dim) a.carrier =
      subspacePointMap (n := a.dim) S0 :=
    (Category.assoc jO jV _).trans ((congrArg (fun v => jO ≫ v) hjVpoint).trans hjOpoint)
  have hParamPoint : (j0 ≫ a.map) ≫ X.obj.hom=subspacePointMap (n := a.dim) S0 :=
    (Category.assoc j0 a.map _).trans ((congrArg (fun v => j0 ≫ v) a.overPoint).trans hj0point)
  have hJpoint : Jraw ≫ X.obj.hom=subspacePointMap (n := a.dim+r) (productGraph S0 (G ∘ f)) :=
    (Category.assoc E.inv (j0 ≫ a.map) _).trans
      ((congrArg (fun v => E.inv ≫ v) hParamPoint).trans (graphIso_inv_point S0 (G ∘ f) hσ))
  let JS : ofClosedAnalytic (productGraph S0 (G ∘ f)) hΓS ⟶ X :=
    ObjectProperty.homMk (Over.homMk Jraw hJpoint)
  have hjOo : LocallyRingedSpace.IsOpenImmersion jO :=
    actualOpenSubspaceMap_isOpenImmersion _ _
  have hjVo : LocallyRingedSpace.IsOpenImmersion jV :=
    actualOpenSubspaceMap_isOpenImmersion _ _
  have hj0o : LocallyRingedSpace.IsOpenImmersion j0 :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ jO hjOo jV hjVo
  have hParamO : LocallyRingedSpace.IsOpenImmersion (j0 ≫ a.map) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ j0 hj0o a.map a.isOpenImmersion
  have hEo : LocallyRingedSpace.IsOpenImmersion E.inv := inferInstance
  have hJopen : LocallyRingedSpace.IsOpenImmersion JS.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (E.inv ≫ (j0 ≫ a.map))
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.inv hEo (j0 ≫ a.map) hParamO
  let Hgraph : actualSubspaceLocallyRingedSpace (n := a.dim+r) (productGraph S0 (G ∘ f)) ⟶
      actualSubspaceLocallyRingedSpace (n := m+r) (productGraph T G) :=
    actualSubspaceMap (normalProduct_holomorphic (r := r) f hf)
      (normalProduct_graph_maps f G S0 T hST)
  have hEH : E.hom ≫ Hgraph=actualSubspaceMap (contMDiff_prodMk hf hσ) hReset := by
    apply actualSubspaceMap_eq_of_base_eq
    · exact (Category.assoc E.hom Hgraph _).trans
        ((congrArg (fun v => E.hom ≫ v) (actualSubspaceMap_point _ _)).trans
          (productGraphIso_hom_point S0 (G ∘ f) hσ))
    · exact actualSubspaceMap_point _ _
    · ext w
      rfl
  have hMapFac : E.hom ≫ Hgraph=j0 ≫ Kraw := by
    calc
      _ = actualSubspaceMap (contMDiff_prodMk hf hσ) hReset := hEH
      _ = actualSubspaceMap hH hLanding := hResetEq
      _ = jO ≫ (jV ≫ Kraw) := hHfull
      _ = j0 ≫ Kraw := (Category.assoc jO jV Kraw).symm
  have hEJ : E.hom ≫ Jraw=j0 ≫ a.map := by
    calc
      _ = (E.hom ≫ E.inv) ≫ (j0 ≫ a.map) := (Category.assoc E.hom E.inv _).symm
      _ = j0 ≫ a.map := by rw [E.hom_inv_id,Category.id_comp]
  have hKraw : Kraw ≫ JT.hom.left=a.map ≫ F.hom.left := congrArg (fun v => v.hom.left) hK
  have hSquare : Hgraph ≫ JT.hom.left=JS.hom.left ≫ F.hom.left := by
    apply (cancel_epi E.hom).mp
    calc
      _ = (E.hom ≫ Hgraph) ≫ JT.hom.left := (Category.assoc E.hom Hgraph _).symm
      _ = (j0 ≫ Kraw) ≫ JT.hom.left := congrArg (fun v => v ≫ JT.hom.left) hMapFac
      _ = j0 ≫ (Kraw ≫ JT.hom.left) := Category.assoc j0 Kraw _
      _ = j0 ≫ (a.map ≫ F.hom.left) := congrArg (fun v => j0 ≫ v) hKraw
      _ = (j0 ≫ a.map) ≫ F.hom.left := (Category.assoc j0 a.map _).symm
      _ = (E.hom ≫ Jraw) ≫ F.hom.left := congrArg (fun v => v ≫ F.hom.left) hEJ.symm
      _ = E.hom ≫ (Jraw ≫ F.hom.left) := Category.assoc E.hom Jraw _
  let w : S0 := ⟨⟨⟨z.val,hzV⟩,hzO⟩,z.property⟩
  have hPoint : JS.hom.left.base (E.hom.base w)=x :=
    (congrArg (fun v => v.base w) hEJ).trans hzx
  exact ⟨a,z,V,hzV,O,hzO,f,hf,hST,hΓS,JS,hJopen,hSquare,E.hom.base w,hPoint⟩

open OriginalFiniteIdealGraphChart EmbeddedGeometricBlowup


/-- Internally CONSTRUCTED target output data, never a public input.
The record keeps native dependent geometry typed without repeatedly
unfolding the enormous canonical source during existential elimination. -/
structure CanonicalTargetGraph {Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) where
  embedding : LocalEmbedding Y
  domain : Opens embedding.ambient
  rank : ℕ
  functions : domain → ComplexModel rank
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel embedding.dim) 𝓘(ℂ,ComplexModel rank) ∞ functions
  analytic : IsComplexAnalyticSubset (n := embedding.dim+rank)
    (productGraph ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions)
  positive : 0<rank
  wholeIdeal : ∀ z : productGraph
      ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions,
    graphCentreStalkIdeal (n := embedding.dim)
      ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions z =
      nativePulledIdealStalkIdeal (chartGraphMap embedding domain functions holomorphic) B b z
  lift : Type
  [liftTopology : TopologicalSpace lift]
  [liftAtlas : ChartedSpace (ComplexModel (embedding.dim+rank)) lift]
  [liftComplex : IsComplexManifold (embedding.dim+rank) lift]
  projection : lift → domain × ComplexModel rank
  blowup : IsBlowupAlong (embedding.dim+rank) {q : domain × ComplexModel rank | q.2=0} projection
  comparison : geometricSource blowup analytic ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject B b
  comparison_open : LocallyRingedSpace.IsOpenImmersion comparison.hom.left
  comparison_projection : comparison ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
    geometricProjectionMorphism blowup analytic ≫ chartGraphMorphism embedding domain functions holomorphic analytic
  comparison_range : range comparison.hom.left.base =
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
      range (chartGraphMap embedding domain functions holomorphic).base
  point : (geometricSource blowup analytic).obj.left
  point_over : comparison.hom.left.base point=y

attribute [instance] CanonicalTargetGraph.liftTopology CanonicalTargetGraph.liftAtlas CanonicalTargetGraph.liftComplex

private theorem derivedTargetGraph_nonempty {Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) :
    Nonempty (CanonicalTargetGraph B b y) := by
  obtain ⟨e,U,r,G,hG,hΓT,hr,hTarget,hRest⟩ :=
    CompatibleCanonicalIdealBlowupPivotChart.exists_canonical_geometric_graph_chart (X := Y) B b y
  obtain ⟨YT,tYT,aYT,cYT,πT,hπT,LT,hLTo,hLTp,hLTr,zt,hzt⟩ := hRest
  let := tYT
  let := aYT
  let := cYT
  exact ⟨{
    embedding := e
    domain := U
    rank := r
    functions := G
    holomorphic := hG
    analytic := hΓT
    positive := hr
    wholeIdeal := hTarget
    lift := YT
    liftTopology := tYT
    liftAtlas := aYT
    liftComplex := cYT
    projection := πT
    blowup := hπT
    comparison := LT
    comparison_open := hLTo
    comparison_projection := hLTp
    comparison_range := hLTr
    point := zt
    point_over := hzt }⟩

/-- The output source geometry uses the LITERAL target list composed with
its derived ambient f. All full-square/whole-ideal assertions below are
OUTPUTS of the ordinary existence theorem, never hypotheses of it. -/
def HasSameTargetSourceGraph
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (F : X ⟶ Y) (x : X.obj.left)
    {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
    (t : CanonicalTargetGraph B b y) : Prop :=
  let e := t.embedding
  let U := t.domain
  let r := t.rank
  let G := t.functions
  let hG := t.holomorphic
  let hΓT := t.analytic
  ∃ (a : LocalEmbedding X) (z : a.carrier),
    ∃ (V : Opens a.ambient) (hzV : z.val∈V)
      (O : Opens V) (_hzO : (⟨z.val,hzV⟩ : V)∈O)
      (f : O → U) (hf : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel e.dim) ∞ f)
      (hST : MapsTo f ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier))
        ((Subtype.val : U → e.ambient) ⁻¹' e.carrier))
      (hΓS : IsComplexAnalyticSubset (n := a.dim+r)
        (productGraph ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f)))
      (JS : ofClosedAnalytic _ hΓS ⟶ X),
    LocallyRingedSpace.IsOpenImmersion JS.hom.left ∧
    actualSubspaceMap
      (C := productGraph ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f))
      (D := productGraph ((Subtype.val : U → e.ambient) ⁻¹' e.carrier) G)
      (f := Prod.map f (id : ComplexModel r → ComplexModel r))
      (ProductComplexManifold.contMDiff_prodMap hf contMDiff_id)
      (fun _q hq => ⟨hST hq.1,hq.2⟩) ≫ (chartGraphMorphism e U G hG hΓT).hom.left =
        JS.hom.left ≫ F.hom.left ∧
    (∀ zs : productGraph
        ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f),
      Ideal.map ((actualSubspaceInclusion (n := a.dim+r)
        (productGraph ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier))
          (G ∘ f))).stalkMap zs).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := a.dim+r)
          {q : O × ComplexModel r | q.2=0}) zs.val) =
        nativePulledIdealStalkIdeal JS.hom.left (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b) zs) ∧
    ∃ zs : (ofClosedAnalytic _ hΓS).obj.left,JS.hom.left.base zs=x

/-- ONLY original F/BFT/b and the genuine raw pair produce the source graph
of LITERALLY the SAME target functions, the FULL original graph square,
its actual point over x, and the ENTIRE literal JF dictionary. Target
geometry and its canonical chart are internally produced by accepted676. -/
theorem exists_same_target_pulled_source_graph_chart
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (F : X ⟶ Y) (x : X.obj.left)
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ t : CanonicalTargetGraph B b y, HasSameTargetSourceGraph B b F x t := by
  let t := Classical.choice (derivedTargetGraph_nonempty (Y := Y) B b y)
  refine ⟨t,?_⟩
  unfold HasSameTargetSourceGraph
  let e := t.embedding
  let U := t.domain
  let r := t.rank
  let G := t.functions
  let hG := t.holomorphic
  let hΓT := t.analytic
  let hTarget := t.wholeIdeal
  let JT : ofClosedAnalytic _ hΓT ⟶ Y := chartGraphMorphism e U G hG hΓT
  let : LocallyRingedSpace.IsOpenImmersion JT.hom.left := chartGraphMap_isOpenImmersion e U G hG
  have hxJT : F.hom.left.base x∈range JT.hom.left.base := by
    have hy : (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y∈
        range JT.hom.left.base := (Set.ext_iff.mp t.comparison_range y).mp ⟨t.point,t.point_over⟩
    exact hxy.symm ▸ hy
  obtain ⟨a,z,V,hzV,O,hzO,f,hf,hST,hΓS,JS,hJSo,hSquare,zs,hzs⟩ :=
    exists_actual_compatible_source_graph (X := X) (Y := Y) (m := e.dim) (r := r) (Q := U)
      F ((Subtype.val : U → e.ambient) ⁻¹' e.carrier) G hG hΓT JT x hxJT
  have hWhole (w : productGraph
      ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f)) :
      graphCentreStalkIdeal (n := a.dim)
        ((Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)) (G ∘ f) w =
      nativePulledIdealStalkIdeal JS.hom.left (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b) w :=
    source_graph_whole_dictionary (X := X) (Y := Y) (n := a.dim) (m := e.dim) (r := r)
      (P := O) (Q := U) B b F f hf G _ _ hST hΓS hΓT JS JT hSquare hTarget w
  exact ⟨a,z,V,hzV,O,hzO,f,hf,hST,hΓS,JS,hJSo,hSquare,hWhole,zs,hzs⟩



-- The following family comparison reuses BOTH existing OWN Cartier/UP
-- engines verbatim. No private choice of canonical generators is compared.
section FamilyComparison

open SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace} {ι : Type} {dims : ι → ℕ}
  {Ambient Lift : ι → Type} [∀ i, TopologicalSpace (Ambient i)]
  [∀ i, TopologicalSpace (Lift i)]
  [∀ i, ChartedSpace (ComplexModel (dims i)) (Ambient i)]
  [∀ i, IsComplexManifold (dims i) (Ambient i)]
  [∀ i, ChartedSpace (ComplexModel (dims i)) (Lift i)]
  [∀ i, IsComplexManifold (dims i) (Lift i)]
  {Centre Carrier : ∀ i, Set (Ambient i)} {π : ∀ i, Lift i → Ambient i}
  (hCarrier : ∀ i, IsComplexAnalyticSubset (n := dims i) (Carrier i))
  (hπ : ∀ i, IsBlowupAlong (dims i) (Centre i) (π i))
  (chart : ∀ i, ofClosedAnalytic (Carrier i) (hCarrier i) ⟶ X)
  [∀ i, LocallyRingedSpace.IsOpenImmersion (chart i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hIdeal : ∀ i (y : Carrier i),
    Ideal.map ((actualSubspaceInclusion (n := dims i) (Carrier i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := dims i) (Centre i)) y.val) =
        nativePulledIdealStalkIdeal (chart i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : Carrier i), (chart i).hom.left.base w=x)

/-- A private adapter only: the actual graph dictionaries and cover will be
DERIVED from original sections in the ordinary consumer. Both OWN Cartier
structures and BOTH full UPs are derived from the real native mothers here.
No UP/Cartier/iso input is added. This reuse earns no new UP engine credit. -/
private theorem exists_geometric_family_canonical_iso :
    ∃ E : EmbeddedGeometricIdealOriginalObject.sourceObject
        hCarrier hπ chart B b hIdeal hcover ≅
        OriginalFiniteIdealGeometricBlowup.sourceObject B b,
      E.hom ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        EmbeddedGeometricIdealOriginalObject.projectionMorphism
          hCarrier hπ chart B b hIdeal hcover := by
  classical
  let A := EmbeddedGeometricIdealOriginalObject.sourceObject hCarrier hπ chart B b hIdeal hcover
  let P := OriginalFiniteIdealGeometricBlowup.sourceObject B b
  let a : A ⟶ X := EmbeddedGeometricIdealOriginalObject.projectionMorphism
    hCarrier hπ chart B b hIdeal hcover
  let p : P ⟶ X := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  obtain ⟨qaRaw,hqaRaw,huaRaw⟩ := EmbeddedGeometricIdealGlobalCartier.projection_ideal_exists_locallyFreeData
    hCarrier hπ chart B b hIdeal
  obtain ⟨qpRaw,hqpRaw,hupRaw⟩ := OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_exists_locallyFreeData B b
  let qa : (nativePulledIdealModule a.hom.left B b).LocalGeneratorsData := qaRaw
  let qp : (nativePulledIdealModule p.hom.left B b).LocalGeneratorsData := qpRaw
  let hqaInstance : qa.IsLocallyFreeData := hqaRaw
  let huaInstance : ∀ i, Unique (qa.generators i).I := fun i => Classical.choice (huaRaw i)
  let hqpInstance : qp.IsLocallyFreeData := hqpRaw
  let hupInstance : ∀ i, Unique (qp.generators i).I := fun i => Classical.choice (hupRaw i)
  obtain ⟨f,hf,_⟩ := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b A a qa
  obtain ⟨g,hg,_⟩ := EmbeddedGeometricIdealGlobalUniversal.exists_unique_lift_of_locallyFreeData
    hCarrier hπ chart B b hIdeal hcover P p qp
  obtain ⟨fa,hfa,huaUnique⟩ := EmbeddedGeometricIdealGlobalUniversal.exists_unique_lift_of_locallyFreeData
    hCarrier hπ chart B b hIdeal hcover A a qa
  obtain ⟨fp,hfp,hupUnique⟩ := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b P p qp
  have hfg : f ≫ g=𝟙 A := by
    apply (huaUnique (f ≫ g) ?_).trans
    exact (huaUnique (𝟙 A) (Category.id_comp a)).symm
    change (f ≫ g) ≫ a=a
    rw [Category.assoc,hg,hf]
  have hgf : g ≫ f=𝟙 P := by
    apply (hupUnique (g ≫ f) ?_).trans
    exact (hupUnique (𝟙 P) (Category.id_comp p)).symm
    change (g ≫ f) ≫ p=p
    rw [Category.assoc,hf,hg]
  exact ⟨{hom:=f,inv:=g,hom_inv_id:=hfg,inv_hom_id:=hgf},hf⟩

end FamilyComparison

section MarkedWholeCover
open SourceReducedComplexSpace OriginalPositiveFiniteIdealGraphChart
  HironakaProductZeroPlaneBlowup

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

-- Pure PRIVATE bookkeeping for the real geometries constructed below.
-- The ordinary public caller does not take any such record as an input.
private structure WholeModel where
  dim : ℕ
  ambient : Type
  [ambientTopology : TopologicalSpace ambient]
  [ambientAtlas : ChartedSpace (ComplexModel dim) ambient]
  [ambientComplex : IsComplexManifold dim ambient]
  centre : Set ambient
  carrier : Set ambient
  analytic : IsComplexAnalyticSubset (n := dim) carrier
  chart : ofClosedAnalytic carrier analytic ⟶ X
  chart_open : LocallyRingedSpace.IsOpenImmersion chart.hom.left
  lift : Type
  [liftTopology : TopologicalSpace lift]
  [liftAtlas : ChartedSpace (ComplexModel dim) lift]
  [liftComplex : IsComplexManifold dim lift]
  projection : lift → ambient
  blowup : IsBlowupAlong dim centre projection
  wholeIdeal : ∀ z : carrier,
    Ideal.map ((actualSubspaceInclusion (n := dim) carrier).stalkMap z).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := dim) centre) z.val) =
        nativePulledIdealStalkIdeal chart.hom.left B b z

attribute [instance] WholeModel.ambientTopology WholeModel.ambientAtlas
  WholeModel.ambientComplex WholeModel.liftTopology WholeModel.liftAtlas
  WholeModel.liftComplex WholeModel.chart_open

private structure CoverModel (x : X.obj.left) extends WholeModel B b where
  point : carrier
  point_over : chart.hom.left.base point=x

private theorem coverModel_nonempty [B.IsFiniteType] (x : X.obj.left) :
    Nonempty (CoverModel B b x) := by
  obtain ⟨e,O,r,G,hG,hΓ,hJ,hr,z,hz⟩ := exists_positive_graph_chart B b x
  obtain ⟨Y,tY,aY,cY,π,hπ⟩ := exists_product_zero_plane_blowup (n := e.dim) (M := O) hr
  let := tY
  let := aY
  let := cY
  exact ⟨{
    dim := e.dim+r
    ambient := O × ComplexModel r
    centre := {q : O × ComplexModel r | q.2=0}
    carrier := productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G
    analytic := hΓ
    chart := chartGraphMorphism e O G hG hΓ
    chart_open := chartGraphMap_isOpenImmersion e O G hG
    lift := Y
    liftTopology := tY
    liftAtlas := aY
    liftComplex := cY
    projection := π
    blowup := hπ
    wholeIdeal := hJ
    point := z
    point_over := hz }⟩

variable [B.IsFiniteType]

private def fallbackModel (x : X.obj.left) : CoverModel B b x :=
  Classical.choice (coverModel_nonempty B b x)

private def markedFamily (marked : WholeModel B b) : Option X.obj.left → WholeModel B b
  | none => marked
  | some x => (fallbackModel B b x).toWholeModel

private def markedFamily_chart (marked : WholeModel B b) (i : Option X.obj.left) :
    ofClosedAnalytic (markedFamily B b marked i).carrier
      (markedFamily B b marked i).analytic ⟶ X :=
  (markedFamily B b marked i).chart

private instance markedFamily_chart_open (marked : WholeModel B b) (i : Option X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (markedFamily_chart B b marked i).hom.left :=
  (markedFamily B b marked i).chart_open

private theorem markedFamily_cover (marked : WholeModel B b) (x : X.obj.left) :
    ∃ (i : Option X.obj.left) (w : (markedFamily B b marked i).carrier),
      (markedFamily_chart B b marked i).hom.left.base w=x :=
  ⟨some x,(fallbackModel B b x).point,(fallbackModel B b x).point_over⟩

/-- The marked real model is inserted into a derived whole source cover.
Its actual strict source is an open chart of SAME canonical source, with
FULL projection and exact range. All fallback models are constructed from
ordinary BFT/b, so no cover, Cartier or UP packet is supplied publicly. -/
private theorem exists_marked_canonical_chart (marked : WholeModel B b) :
    ∃ L : geometricSource marked.blowup marked.analytic ⟶
        OriginalFiniteIdealGeometricBlowup.sourceObject B b,
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      L ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        geometricProjectionMorphism marked.blowup marked.analytic ≫ marked.chart ∧
      range L.hom.left.base =
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
          range marked.chart.hom.left.base := by
  let hA := fun i : Option X.obj.left => (markedFamily B b marked i).analytic
  let hP := fun i : Option X.obj.left => (markedFamily B b marked i).blowup
  let c := markedFamily_chart B b marked
  let hI := fun i : Option X.obj.left => (markedFamily B b marked i).wholeIdeal
  let hc := markedFamily_cover B b marked
  obtain ⟨E,hE⟩ := exists_geometric_family_canonical_iso hA hP c B b hI hc
  let A := EmbeddedGeometricIdealOriginalObject.sourceObject hA hP c B b hI hc
  let a : A ⟶ X := EmbeddedGeometricIdealOriginalObject.projectionMorphism hA hP c B b hI hc
  let p := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  let k := EmbeddedGeometricIdealOriginalObject.localMorphism hA hP c B b hI hc none
  let L : geometricSource marked.blowup marked.analytic ⟶
      OriginalFiniteIdealGeometricBlowup.sourceObject B b := k ≫ E.hom
  have hLopen : LocallyRingedSpace.IsOpenImmersion L.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      (k.hom.left ≫ (SourceReducedComplexSpace.isoLeft E).hom)
    have hk : LocallyRingedSpace.IsOpenImmersion k.hom.left :=
      EmbeddedGeometricIdealOriginalObject.localMorphism_isOpenImmersion hA hP c B b hI hc none
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k.hom.left hk
      (SourceReducedComplexSpace.isoLeft E).hom inferInstance
  have hkp : k ≫ a=geometricProjectionMorphism marked.blowup marked.analytic ≫ marked.chart :=
    EmbeddedGeometricIdealOriginalObject.localMorphism_projection hA hP c B b hI hc none
  have hLp : L ≫ p=geometricProjectionMorphism marked.blowup marked.analytic ≫ marked.chart :=
    (Category.assoc k E.hom p).trans ((congrArg (fun v => k ≫ v) hE).trans hkp)
  have hInv : E.inv ≫ a=p := by
    calc
      _ = E.inv ≫ (E.hom ≫ p) := congrArg (fun v => E.inv ≫ v) hE.symm
      _ = p := by rw [←Category.assoc,E.inv_hom_id,Category.id_comp]
  refine ⟨L,hLopen,hLp,?_⟩
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨(geometricProjection marked.blowup marked.analytic.isClosed).base z,
      (congrArg (fun H => H.hom.left.base z) hLp).symm⟩
  · intro hy
    let zA := E.inv.hom.left.base y
    have hyA : a.hom.left.base zA∈range marked.chart.hom.left.base :=
      (congrArg (fun H => H.hom.left.base y) hInv).symm ▸ hy
    obtain ⟨w,hw⟩ := (Set.ext_iff.mp
      (EmbeddedGeometricIdealObjectGluing.preimage_chart_range hA hP c B b hI none) zA).mp hyA
    refine ⟨w,?_⟩
    change E.hom.hom.left.base
      ((EmbeddedGeometricIdealObjectGluing.inclusion hA hP c B b hI none).base w)=y
    rw [hw]
    exact congrArg (fun H => H.hom.left.base y) E.inv_hom_id

end MarkedWholeCover



section DerivedNativeCartier
open HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
  HironakaSingularRankOneLocalGenerators HironakaNativePulledIdealStalk

-- Reused actual over-site instance, no new module/sheaf/scalar object.
private instance overHasWeakSheafify (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) :
    HasWeakSheafify ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0}

/-- PRIVATE native consumer of OWN actual regular SECTIONS. The ordinary
public caller derives this WHOLE original dictionary, then obtains q on
EXACTLY the composite B-pull. No local-free/Cartier output is hypothesized. -/
private theorem geometric_native_rank_one
    {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {C W : Set M} {π : Y → M}
    (hπ : IsBlowupAlong n C π) (hW : IsComplexAnalyticSubset (n := n) W)
    {Z : SourceReducedComplexSpace} (J : ofClosedAnalytic W hW ⟶ Z)
    (B : SheafOfModules.{0} (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Z.obj.left.toSheafedSpace.sheaf))
    (hIdeal : ∀ z : W,
      Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) z.val) =
          nativePulledIdealStalkIdeal J.hom.left B b z) :
    ∃ q : (nativePulledIdealModule
        (geometricProjectionMorphism hπ hW ≫ J).hom.left B b).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  classical
  let A := (geometricSource hπ hW).obj.left
  let p := geometricProjection hπ hW.isClosed
  let H := p ≫ actualSubspaceInclusion (n := n) W
  let K : A ⟶ Z.obj.left := p ≫ J.hom.left
  have hWhole (z : geoStrictTransform π C W) :
      Ideal.map (H.stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base z)) =
          nativePulledIdealStalkIdeal K B b z := by
    have hOne : Ideal.map (H.stalkMap z).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (H.base z)) =
        Ideal.map (p.stalkMap z).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (p.base z)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π z.val))) :=
      geometricProjection_wholeCentreIdeal hπ hW.isClosed z
    have hTwo : Ideal.map (p.stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (p.base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (π z.val))) =
        Ideal.map (p.stalkMap z).hom (nativePulledIdealStalkIdeal J.hom.left B b (p.base z)) :=
      congrArg (Ideal.map (p.stalkMap z).hom) (hIdeal (p.base z))
    exact hOne.trans (hTwo.trans
      (EmbeddedBlowupGlobalUniversalLocal.nativePulledIdealStalkIdeal_comp p J.hom.left B b z).symm)
  choose U hxU s hs using EmbeddedGeometricBlowupCartier.exists_local_geometric_ideal_sheaf_generator hπ hW.isClosed
  let t (x : A) : nativePulledIdealSectionIdeal K B b (U x) :=
    ⟨(s x).val,fun y hy => (hWhole y) ▸ (s x).property y hy⟩
  exact exists_locallyFreeData_of_regular_sections A.toSheafedSpace.sheaf
    (nativePulledIdealInclusion K B b) (fun _ => Subtype.val_injective)
    U (fun x => ⟨x,hxU x⟩) t
    (fun i x hx => (hs i x hx).2)
    (fun i x hx => (nativePulledIdealStalkInclusion_range K B b x).trans
      ((hWhole x).symm.trans (hs i x hx).1))

end DerivedNativeCartier

-- Actual geometric normal-map assembly: native WHOLE ideal/UP/closure consumers.
section GeometricNormalMaps
variable {n m r : ℕ} {P Q YS YT : Type}
  [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  [TopologicalSpace YS] [ChartedSpace (ComplexModel (n+r)) YS] [IsComplexManifold (n+r) YS]
  [TopologicalSpace YT] [ChartedSpace (ComplexModel (m+r)) YT] [IsComplexManifold (m+r) YT]
  (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
  (G : Q → ComplexModel r) (S : Set P) (T : Set Q) (hST : MapsTo f S T)
  (hΓS : IsComplexAnalyticSubset (n := n+r) (productGraph S (G ∘ f)))
  (hΓT : IsComplexAnalyticSubset (n := m+r) (productGraph T G))
  (πS : YS → P × ComplexModel r)
  (hS : IsBlowupAlong (n+r) {p : P × ComplexModel r | p.2=0} πS)
  (πT : YT → Q × ComplexModel r)
  (hT : IsBlowupAlong (m+r) {q : Q × ComplexModel r | q.2=0} πT)

def graphNormalMorphism : ofClosedAnalytic _ hΓS ⟶ ofClosedAnalytic _ hΓT :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (normalProduct_holomorphic (r := r) f hf)
      (normalProduct_graph_maps f G S T hST)) (actualSubspaceMap_point _ _))

def geometricNormalMorphism
    (L : YS → YT) (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hComm : πT ∘ L=normalProduct f ∘ πS) :
    geometricSource hS hΓS ⟶ geometricSource hT hΓT :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hL (normalProduct_strict_landing f πS πT L hL.continuous hComm
      (productGraph S (G ∘ f)) (productGraph T G) (normalProduct_graph_maps f G S T hST)))
    (actualSubspaceMap_point _ _))

theorem geometricNormalMorphism_projection
    (L : YS → YT) (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hComm : πT ∘ L=normalProduct f ∘ πS) :
    geometricNormalMorphism f G S T hST hΓS hΓT πS hS πT hT L hL hComm ≫
        geometricProjectionMorphism hT hΓT =
      geometricProjectionMorphism hS hΓS ≫ graphNormalMorphism f hf G S T hST hΓS hΓT := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply actualSubspaceMap_eq_of_base_eq
  · exact (geometricNormalMorphism f G S T hST hΓS hΓT πS hS πT hT L hL hComm ≫
      geometricProjectionMorphism hT hΓT).hom.w
  · exact (geometricProjectionMorphism hS hΓS ≫
      graphNormalMorphism f hf G S T hST hΓS hΓT).hom.w
  · ext z
    apply Subtype.ext
    exact congrFun hComm z.val

include hS hT in
private theorem exists_actual_geometric_normal_map :
    ∃ (L : YS → YT)
      (hL : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
      (hComm : πT ∘ L=normalProduct f ∘ πS),
      ∃ H : geometricSource hS hΓS ⟶ geometricSource hT hΓT,
        H=(geometricNormalMorphism f G S T hST hΓS hΓT πS hS πT hT L hL hComm) ∧
        H ≫ geometricProjectionMorphism hT hΓT =
          geometricProjectionMorphism hS hΓS ≫ graphNormalMorphism f hf G S T hST hΓS hΓT := by
  obtain ⟨L,⟨hL,hComm⟩,_⟩ := existsUnique_normalProduct_lift f hf πS hS πT hT
  exact ⟨L,hL,hComm,geometricNormalMorphism f G S T hST hΓS hΓT πS hS πT hT L hL hComm,rfl,
    geometricNormalMorphism_projection f hf G S T hST hΓS hΓT πS hS πT hT L hL hComm⟩
end GeometricNormalMaps

-- FULL canonical comparison from the derived OWN native ideal sections.
section FullCanonicalComparison
variable {n m r : ℕ} {P Q YS YT : Type}
  [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  [TopologicalSpace YS] [ChartedSpace (ComplexModel (n+r)) YS] [IsComplexManifold (n+r) YS]
  [TopologicalSpace YT] [ChartedSpace (ComplexModel (m+r)) YT] [IsComplexManifold (m+r) YT]
  (f : P → Q) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
  (G : Q → ComplexModel r) (S : Set P) (T : Set Q) (hST : MapsTo f S T)
  (hΓS : IsComplexAnalyticSubset (n := n+r) (productGraph S (G ∘ f)))
  (hΓT : IsComplexAnalyticSubset (n := m+r) (productGraph T G))
  (πS : YS → P × ComplexModel r)
  (hS : IsBlowupAlong (n+r) {p : P × ComplexModel r | p.2=0} πS)
  (πT : YT → Q × ComplexModel r)
  (hT : IsBlowupAlong (m+r) {q : Q × ComplexModel r | q.2=0} πT)
  {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- Only a PRIVATE assembly interface: all inputs displayed here are actual
constructions made by the ordinary caller. The SAME composite B-pull q is
DERIVED from the whole source dictionary/OWN sections, then canonical UP
uniqueness identifies ENTIRE native maps, including all scalar actions. -/
private theorem full_canonical_square_of_derived_geometry
    (JS : ofClosedAnalytic _ hΓS ⟶ X) (JT : ofClosedAnalytic _ hΓT ⟶ Y)
    (hOriginal : graphNormalMorphism f hf G S T hST hΓS hΓT ≫ JT=JS ≫ F)
    (hWhole : ∀ z : productGraph S (G ∘ f),
      graphCentreStalkIdeal (n := n) S (G ∘ f) z =
        nativePulledIdealStalkIdeal JS.hom.left (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b) z)
    (LS : geometricSource hS hΓS ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b))
    (hLS : LS ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) =
      geometricProjectionMorphism hS hΓS ≫ JS)
    (LT : geometricSource hT hΓT ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject B b)
    (hLT : LT ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      geometricProjectionMorphism hT hΓT ≫ JT)
    (H : geometricSource hS hΓS ⟶ geometricSource hT hΓT)
    (hH : H ≫ geometricProjectionMorphism hT hΓT =
      geometricProjectionMorphism hS hΓS ≫ graphNormalMorphism f hf G S T hST hΓS hΓT) :
    LS ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F=H ≫ LT := by
  have hIdealB (z : productGraph S (G ∘ f)) :
      graphCentreStalkIdeal (n := n) S (G ∘ f) z =
        nativePulledIdealStalkIdeal (JS ≫ F).hom.left B b z :=
    (hWhole z).trans (stalkIdeal_comp F.hom.left JS.hom.left B b z)
  obtain ⟨q,hq,huniq⟩ := geometric_native_rank_one hS hΓS (JS ≫ F) B b hIdealB
  let := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  let pY := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  let pX := OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
  let pS := geometricProjectionMorphism hS hΓS
  let pT := geometricProjectionMorphism hT hΓT
  let Fprime := OriginalFiniteIdealBlowupSquare.inducedMorphism B b F
  let K := pS ≫ (JS ≫ F)
  have hLeft : (LS ≫ Fprime) ≫ pY=K := by
    calc
      _ = LS ≫ (Fprime ≫ pY) := Category.assoc LS Fprime pY
      _ = LS ≫ (pX ≫ F) := congrArg (fun v => LS ≫ v)
        (OriginalFiniteIdealBlowupSquare.inducedMorphism_square B b F)
      _ = (LS ≫ pX) ≫ F := (Category.assoc LS pX F).symm
      _ = (pS ≫ JS) ≫ F := congrArg (fun v => v ≫ F) hLS
      _ = K := Category.assoc pS JS F
  have hRight : (H ≫ LT) ≫ pY=K := by
    calc
      _ = H ≫ (LT ≫ pY) := Category.assoc H LT pY
      _ = H ≫ (pT ≫ JT) := congrArg (fun v => H ≫ v) hLT
      _ = (H ≫ pT) ≫ JT := (Category.assoc H pT JT).symm
      _ = (pS ≫ graphNormalMorphism f hf G S T hST hΓS hΓT) ≫ JT :=
        congrArg (fun v => v ≫ JT) hH
      _ = pS ≫ (graphNormalMorphism f hf G S T hST hΓS hΓT ≫ JT) := Category.assoc _ _ _
      _ = K := congrArg (fun v => pS ≫ v) hOriginal
  obtain ⟨u,_hu,hUnique⟩ := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b (geometricSource hS hΓS) K q
  exact (hUnique _ hLeft).trans (hUnique _ hRight).symm
end FullCanonicalComparison



section RetainedSourceGeometry

private abbrev sourceTrace {X : SourceReducedComplexSpace} (a : LocalEmbedding X)
    (V : Opens a.ambient) (O : Opens V) : Set O :=
  (Subtype.val : O → V) ⁻¹' ((Subtype.val : V → a.ambient) ⁻¹' a.carrier)

/-- OUTPUT geometry retaining the actual real opens and literal target list.
The ordinary existence theorem constructs it internally; no such data are
an input to that public theorem. -/
structure CanonicalCompatibleSourceGraph
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (F : X ⟶ Y) (x : X.obj.left)
    {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
    (t : CanonicalTargetGraph B b y) where
  embedding : LocalEmbedding X
  domain : Opens embedding.ambient
  subdomain : Opens domain
  baseMap : subdomain → t.domain
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel embedding.dim) 𝓘(ℂ,ComplexModel t.embedding.dim) ∞ baseMap
  landing : MapsTo baseMap (sourceTrace embedding domain subdomain)
    ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
  analytic : IsComplexAnalyticSubset (n := embedding.dim+t.rank)
    (productGraph (sourceTrace embedding domain subdomain) (t.functions ∘ baseMap))
  chart : ofClosedAnalytic _ analytic ⟶ X
  chart_open : LocallyRingedSpace.IsOpenImmersion chart.hom.left
  graph_square : graphNormalMorphism baseMap holomorphic t.functions
      (sourceTrace embedding domain subdomain)
      ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
      landing analytic t.analytic ≫
        chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic = chart ≫ F
  wholeIdeal : ∀ z : productGraph (sourceTrace embedding domain subdomain) (t.functions ∘ baseMap),
    graphCentreStalkIdeal (n := embedding.dim) (sourceTrace embedding domain subdomain)
      (t.functions ∘ baseMap) z =
      nativePulledIdealStalkIdeal chart.hom.left (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b) z
  point : (ofClosedAnalytic _ analytic).obj.left
  point_over : chart.hom.left.base point=x

private theorem compatibleSourceGraph_nonempty
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (F : X ⟶ Y) (x : X.obj.left)
    {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
    (t : CanonicalTargetGraph B b y) (h : HasSameTargetSourceGraph B b F x t) :
    Nonempty (CanonicalCompatibleSourceGraph B b F x t) := by
  unfold HasSameTargetSourceGraph at h
  obtain ⟨a,_z,V,_hzV,O,_hzO,f,hf,hST,hΓS,JS,hJSo,hSquare,hWhole,zs,hzs⟩ := h
  have hFull : graphNormalMorphism f hf t.functions (sourceTrace a V O)
      ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
      hST hΓS t.analytic ≫
        chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic = JS ≫ F := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hSquare
  exact ⟨{
    embedding := a
    domain := V
    subdomain := O
    baseMap := f
    holomorphic := hf
    landing := hST
    analytic := hΓS
    chart := JS
    chart_open := hJSo
    graph_square := hFull
    wholeIdeal := hWhole
    point := zs
    point_over := hzs }⟩

end RetainedSourceGeometry

-- Actual ordinary source-graph-to-canonical-square assembly.
section OrdinaryCanonicalGeometry
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

structure CanonicalSquareGeometry (c : CanonicalCompatibleSourceGraph B b F x t) where
  lift : Type
  [liftTopology : TopologicalSpace lift]
  [liftAtlas : ChartedSpace (ComplexModel (c.embedding.dim+t.rank)) lift]
  [liftComplex : IsComplexManifold (c.embedding.dim+t.rank) lift]
  projection : lift → c.subdomain × ComplexModel t.rank
  blowup : IsBlowupAlong (c.embedding.dim+t.rank)
    {q : c.subdomain × ComplexModel t.rank | q.2=0} projection
  comparison : geometricSource blowup c.analytic ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
  comparison_open : LocallyRingedSpace.IsOpenImmersion comparison.hom.left
  comparison_projection : comparison ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) =
    geometricProjectionMorphism blowup c.analytic ≫ c.chart
  comparison_range : range comparison.hom.left.base =
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base ⁻¹'
        range c.chart.hom.left.base
  ambientLift : lift → t.lift
  lift_holomorphic : ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
    𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) ∞ ambientLift
  lift_projection : t.projection ∘ ambientLift=normalProduct c.baseMap ∘ projection
  full_canonical_square : comparison ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F =
    geometricNormalMorphism c.baseMap t.functions
      (sourceTrace c.embedding c.domain c.subdomain)
      ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
      c.landing c.analytic t.analytic projection blowup t.projection t.blowup
      ambientLift lift_holomorphic lift_projection ≫ t.comparison

attribute [instance] CanonicalSquareGeometry.liftTopology
  CanonicalSquareGeometry.liftAtlas CanonicalSquareGeometry.liftComplex

private theorem canonicalSquareGeometry_nonempty (c : CanonicalCompatibleSourceGraph B b F x t) :
    Nonempty (CanonicalSquareGeometry B b F x t c) := by
  obtain ⟨YS,tYS,aYS,cYS,πS,hS⟩ :=
    HironakaProductZeroPlaneBlowup.exists_product_zero_plane_blowup
      (n := c.embedding.dim) (M := c.subdomain) t.positive
  let := tYS
  let := aYS
  let := cYS
  let JF := nativePulledIdealModule F.hom.left B b
  let jF := nativePulledIdealInclusion F.hom.left B b
  let marked : WholeModel (X := X) JF jF := {
    dim := c.embedding.dim+t.rank
    ambient := c.subdomain × ComplexModel t.rank
    ambientTopology := inferInstance
    ambientAtlas := inferInstance
    ambientComplex := inferInstance
    centre := {q : c.subdomain × ComplexModel t.rank | q.2=0}
    carrier := productGraph (sourceTrace c.embedding c.domain c.subdomain) (t.functions ∘ c.baseMap)
    analytic := c.analytic
    chart := c.chart
    chart_open := c.chart_open
    lift := YS
    liftTopology := tYS
    liftAtlas := aYS
    liftComplex := cYS
    projection := πS
    blowup := hS
    wholeIdeal := c.wholeIdeal }
  obtain ⟨LS,hLSo,hLSp,hLSr⟩ := exists_marked_canonical_chart JF jF marked
  obtain ⟨L,⟨hL,hComm⟩,_⟩ := existsUnique_normalProduct_lift
    c.baseMap c.holomorphic πS hS t.projection t.blowup
  have hFull : LS ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F =
      geometricNormalMorphism c.baseMap t.functions
        (sourceTrace c.embedding c.domain c.subdomain)
        ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        c.landing c.analytic t.analytic πS hS t.projection t.blowup L hL hComm ≫ t.comparison :=
    full_canonical_square_of_derived_geometry c.baseMap c.holomorphic t.functions
      (sourceTrace c.embedding c.domain c.subdomain)
      ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
      c.landing c.analytic t.analytic πS hS t.projection t.blowup B b F
      c.chart (chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic)
      c.graph_square c.wholeIdeal LS hLSp t.comparison t.comparison_projection
      (geometricNormalMorphism c.baseMap t.functions
        (sourceTrace c.embedding c.domain c.subdomain)
        ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        c.landing c.analytic t.analytic πS hS t.projection t.blowup L hL hComm)
      (geometricNormalMorphism_projection c.baseMap c.holomorphic t.functions
        (sourceTrace c.embedding c.domain c.subdomain)
        ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        c.landing c.analytic t.analytic πS hS t.projection t.blowup L hL hComm)
  exact ⟨{
    lift := YS
    liftTopology := tYS
    liftAtlas := aYS
    liftComplex := cYS
    projection := πS
    blowup := hS
    comparison := LS
    comparison_open := hLSo
    comparison_projection := hLSp
    comparison_range := hLSr
    ambientLift := L
    lift_holomorphic := hL
    lift_projection := hComm
    full_canonical_square := hFull }⟩

end OrdinaryCanonicalGeometry

/-- ONLY ordinary original data and an actual raw pair internally construct
SAME pulled-list graph geometry and the FULL SAME canonical geometric square.
The original source point is retained; a strict-source point above it is NOT
asserted. The compatible saturated quotient chart remains downstream. -/
theorem exists_same_canonical_geometric_square
    {X Y : SourceReducedComplexSpace}
    (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (F : X ⟶ Y) (x : X.obj.left)
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t),
      Nonempty (CanonicalSquareGeometry B b F x t c) := by
  obtain ⟨t,ht⟩ := exists_same_target_pulled_source_graph_chart B b F x y hxy
  let c := Classical.choice (compatibleSourceGraph_nonempty B b F x t ht)
  exact ⟨t,c,canonicalSquareGeometry_nonempty B b F x t c⟩



section AmbientComparison

/-- PRIVATE consumer of the EXISTING native ambient uniqueness engine.
The internally chosen and explicit geometric models have genuine inverse
FULL original maps, BOTH ambient numerator squares and the SAME projection.
No ambient or geometric comparison certificate is assumed. -/
private structure NativeGeometricComparison
    {n : ℕ} {M Y₁ Y₂ : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
    {C W : Set M} {π₁ : Y₁ → M} {π₂ : Y₂ → M}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂)
    (hW : IsComplexAnalyticSubset (n := n) W) where
  ambient : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂
  projection : π₂ ∘ ambient=π₁
  original : geometricSource h₁ hW ≅ geometricSource h₂ hW
  forward : original.hom.hom.left ≫ actualSubspaceInclusion (n := n) (geoStrictTransform π₂ C W) =
    actualSubspaceInclusion (n := n) (geoStrictTransform π₁ C W) ≫
      ChartedSpace.locallyRingedSpaceMap ambient ambient.contMDiff
  backward : original.inv.hom.left ≫ actualSubspaceInclusion (n := n) (geoStrictTransform π₁ C W) =
    actualSubspaceInclusion (n := n) (geoStrictTransform π₂ C W) ≫
      ChartedSpace.locallyRingedSpaceMap ambient.symm ambient.symm.contMDiff
  original_projection : original.hom ≫ geometricProjectionMorphism h₂ hW=geometricProjectionMorphism h₁ hW

-- Native ambient inclusion laws are used with their actual orientation.
private theorem exists_full_geometric_blowup_comparison
    {n : ℕ} {M Y₁ Y₂ : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
    {C W : Set M} {π₁ : Y₁ → M} {π₂ : Y₂ → M}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    Nonempty (NativeGeometricComparison h₁ h₂ hW) := by
  obtain ⟨e,f,he,hf,hπe,_hπf,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over h₁ h₂
  let χ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂ :=
    ⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩
  have hStrict : geoStrictTransform π₁ C W=χ ⁻¹' geoStrictTransform π₂ C W := by
    rw [←hπe]
    exact BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ π₂ C W
  let Er : (geometricSource h₁ hW).obj.left ≅ (geometricSource h₂ hW).obj.left :=
    actualSubspaceBiholomorphicIso χ (geoStrictTransform π₁ C W) (geoStrictTransform π₂ C W)
      (fun z => Set.ext_iff.mp hStrict z)
  have hForward : Er.hom ≫ (geometricSource h₂ hW).obj.hom=(geometricSource h₁ hW).obj.hom :=
    actualSubspaceMap_point _ _
  let E : geometricSource h₁ hW ≅ geometricSource h₂ hW :=
    ObjectProperty.isoMk sourceReducedComplexSpaceProperty
      (Over.isoMk Er hForward)
  have hRaw : Er.hom ≫ geometricProjection h₂ hW.isClosed=geometricProjection h₁ hW.isClosed := by
    change actualSubspaceMap χ.contMDiff _ ≫ actualSubspaceMap h₂.contMDiff _ =
      actualSubspaceMap h₁.contMDiff _
    rw [←actualSubspaceMap_comp]
    have heq : π₂ ∘ (χ : Y₁ → Y₂)=π₁ := hπe
    cases heq
    rfl
  have hOriginal : E.hom ≫ geometricProjectionMorphism h₂ hW=geometricProjectionMorphism h₁ hW := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hRaw
  exact ⟨{
    ambient := χ
    projection := hπe
    original := E
    forward := (actualSubspaceMap_inclusion (n := n) (m := n) (M := Y₁) (N := Y₂)
      (f := (χ : Y₁ → Y₂)) χ.contMDiff
      (C := geoStrictTransform π₁ C W) (D := geoStrictTransform π₂ C W)
      (fun z hz => (Set.ext_iff.mp hStrict z).mp hz)).symm
    backward := (actualSubspaceMap_inclusion (n := n) (m := n) (M := Y₂) (N := Y₁)
      (f := (χ.symm : Y₂ → Y₁)) χ.symm.contMDiff
      (C := geoStrictTransform π₂ C W) (D := geoStrictTransform π₁ C W)
      (fun z hz => (Set.ext_iff.mp hStrict (χ.symm z)).mpr
        (by
          change χ (χ.symm z)∈geoStrictTransform π₂ C W
          simpa only [χ.apply_symm_apply] using hz))).symm
    original_projection := hOriginal }⟩

end AmbientComparison

-- Native normal flattenings and exact exceptional ratio offsets.
section ProductNormalFlattening
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

-- The actual preferred product flattening retains LITERAL normal functions.
private def productNormalFlatChart (p : P) (j : Fin r) :
    BlowupConstruction.FlatChart (n+r) {q : P × ComplexModel r | q.2=0} where
  y₀ := (p,0)
  k := n
  Φ := productChartIdentity (n := n) (p,0)
  hsrc := Subset.rfl
  hflat := by
    intro q _hq _hq'
    change q.2=0 ↔ ∀i : Fin (n+r),n ≤ i.val →
      (chartAt (ComplexModel (n+r)) ((p,0) : P × ComplexModel r) q) i=0
    constructor
    · intro hq i hi
      let l : Fin r := ⟨i.val-n,by omega⟩
      have he : l.natAdd n=i := Fin.ext (by dsimp [l];omega)
      rw [←he,product_chart_normal,hq]
      rfl
    · intro hq
      ext i
      rw [←product_chart_normal (n := n) ((p,0) : P × ComplexModel r) q i]
      exact hq (i.natAdd n) (by simp)
  j := j.natAdd n
  hj := by simp

omit [IsComplexManifold n P] in
private theorem productNormalFlatChart_normal (p : P) (j i : Fin r)
    (q : P × ComplexModel r) :
    (productNormalFlatChart (n := n) p j).τ (i.natAdd n) q=q.2 i :=
  product_chart_normal ((p,0) : P × ComplexModel r) q i

omit [IsComplexManifold n P] in
private theorem productNormalFlatChart_base_mem (p : P) (j : Fin r) (v : ComplexModel r) :
    (p,v)∈(productNormalFlatChart (n := n) p j).dom := by
  have hs : (p,v)∈(chartAt (ComplexModel (n+r)) ((p,0) : P × ComplexModel r)).source := by
    rw [ProductComplexManifold.chartAt_prod,ProductComplexManifold.prodChart_source]
    exact ⟨mem_chart_source _ p,by trivial⟩
  exact ⟨hs,(chartAt (ComplexModel (n+r)) ((p,0) : P × ComplexModel r)).map_source hs⟩
end ProductNormalFlattening

section ActualRatioOffsets
open BlowupMonomialCharts HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower

private theorem normal_index_mem_iff {d t : ℕ} (i : Fin (d+t)) :
    i∈actualTangentCentreVariables d t ↔ d ≤ i.val := by
  constructor
  · rintro ⟨j,rfl⟩
    simp
  · intro hi
    let j : Fin t := ⟨i.val-d,by omega⟩
    exact ⟨j,Fin.ext (by dsimp [j];omega)⟩

/-- The ACTUAL raw monomial translation retains exactly the same ratio
values as the offsets b, with no entire extension or ideal assumption. -/
private theorem monomial_translate_exceptional
    (d t : ℕ) (j : Fin t) (w₀ z : ComplexModel (d+t))
    (hε : w₀ (j.natAdd d)=0) :
    monomial d (j.natAdd d) (w₀+z)=
      monomial d (j.natAdd d) w₀+
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) (fun i => w₀ i) z := by
  classical
  ext i
  change (if d ≤ i.val ∧ i≠j.natAdd d then
      (w₀ i+z i)*(w₀ (j.natAdd d)+z (j.natAdd d)) else w₀ i+z i) =
    (if d ≤ i.val ∧ i≠j.natAdd d then w₀ i*w₀ (j.natAdd d) else w₀ i)+
      (if i∈actualTangentCentreVariables d t then
        if i=j.natAdd d then z (j.natAdd d) else z (j.natAdd d)*(w₀ i+z i) else z i)
  rw [normal_index_mem_iff]
  by_cases hi : d ≤ i.val
  · by_cases hij : i=j.natAdd d
    · subst i
      simp [hε]
    · simp [hi,hij,hε,mul_comm]
  · simp [hi]
end ActualRatioOffsets

-- Actual intrinsic WHOLE-generator compatibility for SAME canonical square.
section NativePivotPullback
open HironakaSingularIdealInvertibleModule

-- Reused regular-generator elementary algebra, zero new engine credit.
private theorem span_regular_multiple_iff_unit {R : Type*} [CommRing R]
    (ε r : R) (hε : IsRegular ε) :
    Ideal.span ({ε*r} : Set R)=Ideal.span {ε} ↔ IsUnit r := by
  constructor
  · intro h
    have hm : ε∈Ideal.span ({ε*r} : Set R) := h.symm ▸ Ideal.mem_span_singleton_self ε
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hm
    have hc : ε*(a*r)=ε*1 := by
      calc
        _ = a*(ε*r) := by ring
        _ = ε := ha
        _ = _ := (mul_one ε).symm
    have hunit : a*r=1 := hε.left hc
    exact ⟨⟨r,a,by rw [mul_comm];exact hunit,hunit⟩,rfl⟩
  · rintro ⟨u,rfl⟩
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro x (rfl : x=ε*↑u)
      exact Ideal.mem_span_singleton.mpr ⟨↑u,rfl⟩
    · apply Ideal.span_le.mpr
      rintro x (rfl : x=ε)
      exact Ideal.mem_span_singleton.mpr ⟨↑u⁻¹,by simp [mul_assoc]⟩

-- This applies ONLY after deriving invertibility on both ACTUAL strict
-- stalk ideals. No regularity is imposed on any RAW ambient quotient ring.
private theorem generator_iff_under_native_local_map
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    (φ : R →+* S) [IsLocalHom φ] (I : Ideal R)
    (hI : Module.Invertible R I) (hImage : Module.Invertible S (Ideal.map φ I))
    (a : R) (ha : a∈I) :
    I=Ideal.span {a} ↔ Ideal.map φ I=Ideal.span {φ a} := by
  constructor
  · intro h
    rw [h,Ideal.map_span,Set.image_singleton]
  · intro h
    obtain ⟨ε,_hε,hSpan,hReg⟩ := exists_regular_generator I hI
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton'.mp (hSpan ▸ ha)
    have haeq : a=ε*r := hr.symm.trans (mul_comm r ε)
    have hMapSpan : Ideal.map φ I=Ideal.span {φ ε} := by
      rw [hSpan,Ideal.map_span,Set.image_singleton]
    have hRegMap : IsRegular (φ ε) := isRegular_of_span_eq _ hImage hMapSpan
    have hSpans : Ideal.span {φ ε*φ r}=Ideal.span {φ ε} := by
      have hs := h.symm.trans hMapSpan
      rwa [haeq,map_mul] at hs
    have hu : IsUnit r := isUnit_of_map_unit φ r
      ((span_regular_multiple_iff_unit (φ ε) (φ r) hRegMap).mp hSpans)
    rw [hSpan,haeq]
    exact ((span_regular_multiple_iff_unit ε r hReg).mpr hu).symm

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

private theorem canonical_square_whole_ideal
    (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z =
      Ideal.map (((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left).stalkMap z).hom
        (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
          ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z)) := by
  let pX := (OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
  let pY := (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  have hSquare : Fp ≫ pY=pX ≫ F.hom.left :=
    congrArg (fun v => v.hom.left) (OriginalFiniteIdealBlowupSquare.inducedMorphism_square B b F)
  have hWhole : nativePulledIdealStalkIdeal (pX ≫ F.hom.left) B b z=
      nativePulledIdealStalkIdeal (Fp ≫ pY) B b z :=
    congrArg (fun v => nativePulledIdealStalkIdeal v B b z) hSquare.symm
  exact (stalkIdeal_comp F.hom.left pX B b z).trans
    (hWhole.trans (EmbeddedBlowupGlobalUniversalLocal.nativePulledIdealStalkIdeal_comp Fp pY B b z))

/-- The actual SAME canonical square reflects and preserves WHOLE pivot
membership for EVERY original target-ideal germ, not merely residue values.
Both OWN invertibilities, FULL induced square and native local stalk action
are derived from ordinary BFT/b/F. This will be applied to literal c_j. -/
theorem canonical_pulled_generator_iff
    (z : (OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (a : ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk
      ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z)).carrier)
    (ha : a∈nativePulledIdealStalkIdeal
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
      ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z)) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z =
      Ideal.span {((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.stalkMap z) a} ↔
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
      ((OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base z)=Ideal.span {a} := by
  let pX := OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
  let pY := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  let Fp := OriginalFiniteIdealBlowupSquare.inducedMorphism B b F
  let φ := (Fp.hom.left.stalkMap z).hom
  let I := nativePulledIdealStalkIdeal pY.hom.left B b (Fp.hom.left.base z)
  have hImage : Module.Invertible _ (Ideal.map φ I) :=
    (canonical_square_whole_ideal B b F z) ▸
      OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_moduleInvertible
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) z
  rw [canonical_square_whole_ideal B b F z]
  exact (generator_iff_under_native_local_map φ I
    (OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_moduleInvertible B b (Fp.hom.left.base z))
    hImage a ha).symm

end NativePivotPullback

-- Actual section/locus compatibility under the SAME native Fprime.
section CanonicalSectionGeneratorLoci

def nativeWholeGeneratorLocus {A T : LocallyRingedSpace.{0}} (p : A ⟶ T)
    (B : SheafOfModules.{0} (forgetRing T.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing T.toSheafedSpace.sheaf))
    (U : Opens A.toTopCat) (s : nativePulledIdealSectionIdeal p B b U) : Set A :=
  {z | ∃ hz : z∈U,nativePulledIdealStalkIdeal p B b z=Ideal.span {A.presheaf.germ U z hz s.val}}

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

def canonicalPulledIdealSection
    (U : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)
    (s : nativePulledIdealSectionIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U) :
    nativePulledIdealSectionIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
      ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj U) := by
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  refine ⟨Fp.c.app (op U) s.val,?_⟩
  intro z hz
  rw [canonical_square_whole_ideal B b F z]
  have hm := Ideal.mem_map_of_mem (Fp.stalkMap z).hom (s.property (Fp.base z) hz)
  exact (LocallyRingedSpace.stalkMap_germ_apply Fp U z hz s.val) ▸ hm

/-- The locus is defined by the ENTIRE original ideal and actual section
BEFORE identifying it with any geometric chart image. Native local stalk
maps and BOTH OWN canonical Cartier structures derive the exact preimage. -/
theorem canonicalWholeGeneratorLocus_preimage
    (U : Opens (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)
    (s : nativePulledIdealSectionIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U) :
    nativeWholeGeneratorLocus (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
      ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj U)
      (canonicalPulledIdealSection B b F U s) =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base ⁻¹'
        nativeWholeGeneratorLocus (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b U s := by
  let Fp := (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left
  ext z
  constructor
  · rintro ⟨hz,hgen⟩
    refine ⟨hz,?_⟩
    apply (canonical_pulled_generator_iff B b F z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U (Fp.base z) hz s.val)
      (s.property (Fp.base z) hz)).mp
    change _=Ideal.span {((OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map Fp.base).obj U) z hz (Fp.c.app (op U) s.val))} at hgen
    have he := LocallyRingedSpace.stalkMap_germ_apply Fp U z hz s.val
    exact hgen.trans (congrArg (fun r => Ideal.span {r}) he.symm)
  · rintro ⟨hz,hgen⟩
    refine ⟨hz,?_⟩
    have hg := (canonical_pulled_generator_iff B b F z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ U (Fp.base z) hz s.val)
      (s.property (Fp.base z) hz)).mpr hgen
    have he := LocallyRingedSpace.stalkMap_germ_apply Fp U z hz s.val
    exact hg.trans (congrArg (fun r => Ideal.span {r}) he)

end CanonicalSectionGeneratorLoci

end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts

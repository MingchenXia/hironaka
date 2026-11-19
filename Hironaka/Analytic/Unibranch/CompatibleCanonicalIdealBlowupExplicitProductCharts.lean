import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
import Hironaka.Blowup.BlowupSpaceUniversal
import Hironaka.Blowup.BlowupUniqueness

/-! SAME actual product zero-plane explicit models from ordinary original data.
BP FIRST. No graph shear, changed centre, raw quotient regularity or supplied
comparison/Cartier/UP/generator certificate. Existing native engines0recredit.
Actual pivot-image/restriction/ALLambient-monomial/rawpair/Qsat leaves stay open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces
  HironakaActualWholeStalkHolomorphicPullback HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaSingularSubspaceBlowupCartierCentreIdeal
  HironakaFiniteSectionProductGraph ProductComplexManifold BlowupFlatCoordinates
  BlowupStrictSubmanifold BlowupConstruction SourceReducedComplexSpace EmbeddedGeometricBlowup
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupPivotChart
open scoped ProductComplexManifold

section ActualProductCharts
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

private theorem opens_chart_source {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (h : ∀ p : M,(chartAt H p).source=univ)
    (U : Opens M) (p : U) : (chartAt H p).source=univ := by
  rw [TopologicalSpace.Opens.chartAt_eq,OpenPartialHomeomorph.subtypeRestr_source,h p.val]
  exact preimage_univ

private theorem coordinate_chart_source (p : ComplexModel n) :
    (chartAt (ComplexModel n) p).source=univ := by
  rw [chartAt_self_eq]
  rfl

private theorem double_open_chart_source (A : Opens (ComplexModel n)) (U : Opens A) (p : U) :
    (chartAt (ComplexModel n) p).source=univ :=
  opens_chart_source (fun q : A => opens_chart_source coordinate_chart_source A q) U p

private theorem triple_open_chart_source (A : Opens (ComplexModel n)) (U : Opens A)
    (O : Opens U) (p : O) : (chartAt (ComplexModel n) p).source=univ :=
  opens_chart_source (double_open_chart_source A U) O p

private def identityProductCoordinates (p : P × ComplexModel r) :
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
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,chartAt_self_eq]

/-- Actual identity product-normal chart of the ORIGINAL zero-plane.
Every pivot keeps the SAME flattening; its normal indices are i.natAdd n. -/
def productNormalChart (p : P) (j : Fin r) : FlatChart (n+r) {q : P × ComplexModel r | q.2=0} where
  y₀ := (p,0)
  k := n
  Φ := identityProductCoordinates (n := n) (p,0)
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
/-- The original functions, at EVERY point, retain the prescribed normal labels. -/
theorem productNormalChart_normal (p : P) (j i : Fin r) (q : P × ComplexModel r) :
    (productNormalChart (n := n) p j).τ (i.natAdd n) q=q.2 i :=
  product_chart_normal ((p,0) : P × ComplexModel r) q i

omit [IsComplexManifold n P] in
private theorem productNormalChart_domain (h : ∀ q : P,(chartAt (ComplexModel n) q).source=univ)
    (p : P) (j : Fin r) : (productNormalChart (n := n) p j).dom=univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hs : q∈(chartAt (ComplexModel (n+r)) ((p,0) : P × ComplexModel r)).source := by
    rw [ProductComplexManifold.chartAt_prod,ProductComplexManifold.prodChart_source,h p,chartAt_self_eq]
    exact ⟨by trivial,by trivial⟩
  exact ⟨hs,(chartAt (ComplexModel (n+r)) ((p,0) : P × ComplexModel r)).map_source hs⟩

/-- Actual fixed flattening OUTPUT; its prescribed normal identities are the
preceding theorem, and its domain is the WHOLE genuine product ambient. -/
structure ProductNormalCharts (n r : ℕ) (P : Type) [TopologicalSpace P]
    [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P] where
  base : P
  domain : ∀ j : Fin r,(productNormalChart (n := n) base j).dom=univ

/-- Fact wrapper for the held true zero-plane smoothness; no new structure
or smoothness engine is copied. This enables the EXISTING explicit atlas. -/
instance productZeroPlane_fact : Fact (IsClosedSubmanifold (n+r) {q : P × ComplexModel r | q.2=0}) :=
  ⟨HironakaProductZeroPlaneBlowup.isClosedSubmanifold_product_zero_plane⟩

/-- The actual existing explicit projection, with its OWN existing predicate. -/
theorem explicitProductPredicate (hr : 0<r) : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0}
    (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) :=
  isBlowupAlong_blowupProj (HironakaProductZeroPlaneBlowup.interior_product_zero_plane_eq_empty hr)

end ActualProductCharts

structure SameAmbientComparison
    {n : ℕ} {M Y₁ Y₂ : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
    {C W : Set M} {π₁ : Y₁ → M} {π₂ : Y₂ → M}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂)
    (hW : IsComplexAnalyticSubset (n := n) W) where
  ambient : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂
  projection : π₂ ∘ ambient=π₁
  inverse_projection : π₁ ∘ ambient.symm=π₂
  original : geometricSource h₁ hW ≅ geometricSource h₂ hW
  forward : original.hom.hom.left ≫ actualSubspaceInclusion (n := n) (geoStrictTransform π₂ C W) =
    actualSubspaceInclusion (n := n) (geoStrictTransform π₁ C W) ≫
      ChartedSpace.locallyRingedSpaceMap ambient ambient.contMDiff
  backward : original.inv.hom.left ≫ actualSubspaceInclusion (n := n) (geoStrictTransform π₁ C W) =
    actualSubspaceInclusion (n := n) (geoStrictTransform π₂ C W) ≫
      ChartedSpace.locallyRingedSpaceMap ambient.symm ambient.symm.contMDiff
  original_projection : original.hom ≫ geometricProjectionMorphism h₂ hW=geometricProjectionMorphism h₁ hW

-- Native ambient inclusion laws are used with their actual orientation.
private theorem sameAmbientComparison_exists
    {n : ℕ} {M Y₁ Y₂ : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
    {C W : Set M} {π₁ : Y₁ → M} {π₂ : Y₂ → M}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    Nonempty (SameAmbientComparison h₁ h₂ hW) := by
  obtain ⟨e,f,he,hf,hπe,hπf,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over h₁ h₂
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
    inverse_projection := hπf
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


section WholeOriginalNormals
variable {n r : ℕ} {P Y₁ Y₂ : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (n+r)) Y₁] [IsComplexManifold (n+r) Y₁]
  [TopologicalSpace Y₂] [ChartedSpace (ComplexModel (n+r)) Y₂] [IsComplexManifold (n+r) Y₂]

private theorem native_original_function {a b : ℕ} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    {f : M → N} (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ f)
    (x : M) (g : N → ℂ) (hg : HolomorphicAt b g (f x)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x (actualOriginalFunctionGerm (f x) g hg)=
      actualOriginalFunctionGerm x (g ∘ f)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := a) x).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem original_germ_congr {a : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt a f x) (hg : HolomorphicAt a g x)
    (he : f=ᶠ[𝓝 x]g) : actualOriginalFunctionGerm x f hf=actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := a) x).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg he

private theorem normal_holomorphic (q : P × ComplexModel r) (i : Fin r) :
    HolomorphicAt (n+r) (fun w : P × ComplexModel r => w.2 i) q :=
  Eventually.of_forall fun _ =>
    (((EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ).contMDiff.comp
      ProductComplexManifold.contMDiff_snd).contMDiffAt).mdifferentiableAt (by simp)

private def ambientProjection {W : Set (P × ComplexModel r)} {π : Y₁ → P × ComplexModel r}
    (hπ : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0} π)
    (hW : IsComplexAnalyticSubset (n := n+r) W) :
    (geometricSource hπ hW).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) :=
  geometricProjection hπ hW.isClosed ≫ actualSubspaceInclusion (n := n+r) W

private theorem ambientProjection_normal {W : Set (P × ComplexModel r)} {π : Y₁ → P × ComplexModel r}
    (hπ : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0} π)
    (hW : IsComplexAnalyticSubset (n := n+r) W)
    (z : (geometricSource hπ hW).obj.left) (i : Fin r) :
    (ambientProjection hπ hW).stalkMap z (prescribedNormalGerm (π z.val) i)=
      (actualSubspaceInclusion (n := n+r) (geoStrictTransform π {q | q.2=0} W)).stalkMap z
        (projectionNormalGerm hπ z.val i) := by
  let inc := actualSubspaceInclusion (n := n+r) (geoStrictTransform π {q | q.2=0} W)
  let L := ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff
  have hs : inc ≫ L=ambientProjection hπ hW := geometricProjection_inclusion hπ hW.isClosed
  have he := congrArg (fun H : (geometricSource hπ hW).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) =>
    H.stalkMap z (prescribedNormalGerm (H.base z) i)) hs
  have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp inc L z)
    (prescribedNormalGerm (π z.val) i)
  have hn := native_original_function hπ.contMDiff z.val
    (fun q : P × ComplexModel r => q.2 i) (normal_holomorphic (π z.val) i)
  exact he.symm.trans (hc.trans (congrArg (fun a => inc.stalkMap z a) hn))

private theorem inverse_original_projection {C W : Set (P × ComplexModel r)}
    {π₁ : Y₁ → P × ComplexModel r} {π₂ : Y₂ → P × ComplexModel r}
    {h₁ : IsBlowupAlong (n+r) C π₁} {h₂ : IsBlowupAlong (n+r) C π₂}
    {hW : IsComplexAnalyticSubset (n := n+r) W} (E : SameAmbientComparison h₁ h₂ hW) :
    E.original.inv ≫ geometricProjectionMorphism h₁ hW=geometricProjectionMorphism h₂ hW := by
  rw [←E.original_projection,←Category.assoc,E.original.inv_hom_id,Category.id_comp]

private theorem inverse_normal_germ {W : Set (P × ComplexModel r)}
    {π₁ : Y₁ → P × ComplexModel r} {π₂ : Y₂ → P × ComplexModel r}
    {h₁ : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0} π₁}
    {h₂ : IsBlowupAlong (n+r) {q : P × ComplexModel r | q.2=0} π₂}
    {hW : IsComplexAnalyticSubset (n := n+r) W} (E : SameAmbientComparison h₁ h₂ hW)
    (z : (geometricSource h₂ hW).obj.left) (i : Fin r) :
    E.original.inv.hom.left.stalkMap z
      ((actualSubspaceInclusion (n := n+r) (geoStrictTransform π₁ {q | q.2=0} W)).stalkMap
        (E.original.inv.hom.left.base z)
        (projectionNormalGerm h₁ (E.original.inv.hom.left.base z).val i)) =
      (actualSubspaceInclusion (n := n+r) (geoStrictTransform π₂ {q | q.2=0} W)).stalkMap z
        (projectionNormalGerm h₂ z.val i) := by
  let ei := E.original.inv.hom.left
  let a₁ := ambientProjection h₁ hW
  let a₂ := ambientProjection h₂ hW
  have hp := congrArg (fun H => H.hom.left) (inverse_original_projection E)
  have hs : ei ≫ a₁=a₂ := (Category.assoc ei _ _).symm.trans
    (congrArg (fun H => H ≫ actualSubspaceInclusion (n := n+r) W) hp)
  have hg := ambientProjection_normal h₁ hW (ei.base z) i
  have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp ei a₁ z)
    (prescribedNormalGerm (a₁.base (ei.base z)) i)
  have he := congrArg (fun H : (geometricSource h₂ hW).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r) =>
    H.stalkMap z (prescribedNormalGerm (H.base z) i)) hs
  exact (congrArg (fun a => ei.stalkMap z a) hg.symm).trans
    (hc.symm.trans (he.trans (ambientProjection_normal h₂ hW z i)))

end WholeOriginalNormals

section ExplicitCentreSpan
variable {n r : ℕ} {P : Type} [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

private theorem explicit_coordinate_original (hr : 0<r) (W : Set (P × ComplexModel r))
    (p : P) (j i : Fin r)
    (z : geoStrictTransform (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) {q | q.2=0} W)
    (hz : z.val.base∈(productNormalChart (n := n) p j).dom) :
    geometricCoordinateClass W (productNormalChart (n := n) p j) z hz (i.natAdd n)=
      (actualSubspaceInclusion (n := n+r)
        (geoStrictTransform (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) {q | q.2=0} W)).stalkMap z
        (projectionNormalGerm (explicitProductPredicate (n := n) (P := P) hr) z.val i) := by
  apply congrArg ((actualSubspaceInclusion (n := n+r) _).stalkMap z)
  apply original_germ_congr
  exact Eventually.of_forall fun q => productNormalChart_normal p j i (blowupProj (n+r) _ q)

private theorem explicit_strict_centre_span (hr : 0<r) (W : Set (P × ComplexModel r))
    (charts : ProductNormalCharts n r P) (j : Fin r)
    (z : geoStrictTransform (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) {q | q.2=0} W) :
    strictCentreStalkIdeal W z=Ideal.span (range fun i : Fin r =>
      (actualSubspaceInclusion (n := n+r)
        (geoStrictTransform (blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) {q | q.2=0} W)).stalkMap z
        (projectionNormalGerm (explicitProductPredicate (n := n) (P := P) hr) z.val i)) := by
  let c := productNormalChart (n := n) charts.base j
  have hz : z.val.base∈c.dom := by rw [charts.domain j];trivial
  have hs := actualRestrictedPulledCentreIdeal_eq_span_normal_coordinates
    (HironakaProductZeroPlaneBlowup.isClosedSubmanifold_product_zero_plane (n := n) (r := r) (M := P))
    contMDiff_blowupProj c.hsrc c.hflat _ z hz
  apply hs.trans
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨i,rfl⟩
    have hi : n ≤ i.val.val := i.property
    let l : Fin r := ⟨i.val.val-n,by omega⟩
    have he : l.natAdd n=i.val := Fin.ext (by dsimp [l];omega)
    refine ⟨l,?_⟩
    exact (explicit_coordinate_original hr W charts.base j l z hz).symm.trans
      (by rw [he])
  · rintro ⟨i,rfl⟩
    refine ⟨⟨i.natAdd n,by change n ≤ n+i.val;omega⟩,?_⟩
    exact explicit_coordinate_original hr W charts.base j i z hz

end ExplicitCentreSpan

section SameCanonicalModels
open OriginalFiniteIdealGraphChart HironakaResolutionSpaceComplex
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- The EXISTING explicit target geometric source, with the original graph
and original zero-plane centre. This is an abbreviation, not a new space. -/
abbrev explicitTarget (t : CanonicalTargetGraph B b y) : SourceReducedComplexSpace :=
  geometricSource (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic

/-- The EXISTING explicit source geometric model, also when it is EMPTY. -/
abbrev explicitSource (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) :
    SourceReducedComplexSpace :=
  geometricSource (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic

structure TargetExplicitGeometry (t : CanonicalTargetGraph B b y) where
  comparison : SameAmbientComparison t.blowup
    (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic
  charts : ProductNormalCharts t.embedding.dim t.rank t.domain

structure SourceExplicitGeometry (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) where
  comparison : SameAmbientComparison g.blowup
    (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic
  charts : ProductNormalCharts c.embedding.dim t.rank c.subdomain

private def constructedTargetGeometry (t : CanonicalTargetGraph B b y) : TargetExplicitGeometry B b t where
  comparison := Classical.choice (sameAmbientComparison_exists t.blowup
    (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic)
  charts := {
    base := (t.projection t.point.val).1
    domain := fun j => productNormalChart_domain
      (double_open_chart_source t.embedding.ambient t.domain) (t.projection t.point.val).1 j }

private def constructedSourceGeometry (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) :
    SourceExplicitGeometry B b F x t c g where
  comparison := Classical.choice (sameAmbientComparison_exists g.blowup
    (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic)
  charts := {
    base := c.point.val.1
    domain := fun j => productNormalChart_domain
      (triple_open_chart_source c.embedding.ambient c.domain c.subdomain) c.point.val.1 j }

def targetCanonicalMap (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t) :
    explicitTarget B b t ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject B b :=
  e.comparison.original.inv ≫ t.comparison

def sourceCanonicalMap (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (e : SourceExplicitGeometry B b F x t c g) :
    explicitSource B b F x t c ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) :=
  e.comparison.original.inv ≫ g.comparison

private theorem target_map_open (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t) :
    LocallyRingedSpace.IsOpenImmersion (targetCanonicalMap B b t e).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((SourceReducedComplexSpace.isoLeft e.comparison.original).inv ≫ t.comparison.hom.left)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (SourceReducedComplexSpace.isoLeft e.comparison.original).inv inferInstance
    t.comparison.hom.left t.comparison_open

private theorem source_map_open (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (e : SourceExplicitGeometry B b F x t c g) :
    LocallyRingedSpace.IsOpenImmersion (sourceCanonicalMap B b F x t c g e).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((SourceReducedComplexSpace.isoLeft e.comparison.original).inv ≫ g.comparison.hom.left)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (SourceReducedComplexSpace.isoLeft e.comparison.original).inv inferInstance
    g.comparison.hom.left g.comparison_open

private theorem target_map_range (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t) :
    range (targetCanonicalMap B b t e).hom.left.base=range t.comparison.hom.left.base :=
  range_iso_hom_comp_base (SourceReducedComplexSpace.isoLeft e.comparison.original).symm t.comparison.hom.left

private theorem source_map_range (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (e : SourceExplicitGeometry B b F x t c g) :
    range (sourceCanonicalMap B b F x t c g e).hom.left.base=range g.comparison.hom.left.base :=
  range_iso_hom_comp_base (SourceReducedComplexSpace.isoLeft e.comparison.original).symm g.comparison.hom.left

private theorem target_map_projection (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t) :
    targetCanonicalMap B b t e ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      geometricProjectionMorphism (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
        t.analytic ≫ chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic := by
  change (e.comparison.original.inv ≫ t.comparison) ≫ _ = _
  rw [Category.assoc,t.comparison_projection,←Category.assoc,inverse_original_projection]

private theorem source_map_projection (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (e : SourceExplicitGeometry B b F x t c g) :
    sourceCanonicalMap B b F x t c g e ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) =
      geometricProjectionMorphism (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
        c.analytic ≫ c.chart := by
  let ei := e.comparison.original.inv
  let pX := OriginalFiniteIdealGeometricBlowup.projectionMorphism
    (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
  let p₀ := geometricProjectionMorphism g.blowup c.analytic
  have hp : g.comparison ≫ pX=p₀ ≫ c.chart := g.comparison_projection
  have hi := inverse_original_projection e.comparison
  exact (Category.assoc ei g.comparison pX).trans
    ((congrArg (fun H => ei ≫ H) hp).trans
      ((Category.assoc ei p₀ c.chart).symm.trans (congrArg (fun H => H ≫ c.chart) hi)))

private def chosenStrictMap (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) :
    geometricSource g.blowup c.analytic ⟶ geometricSource t.blowup t.analytic :=
  geometricNormalMorphism c.baseMap t.functions _ _ c.landing c.analytic t.analytic
    g.projection g.blowup t.projection t.blowup g.ambientLift g.lift_holomorphic g.lift_projection

def explicitStrictMap (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    explicitSource B b F x t c ⟶ explicitTarget B b t :=
  eS.comparison.original.inv ≫ chosenStrictMap B b F x t c g ≫ eT.comparison.original.hom

def explicitAmbientLift (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0} →
      BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0} :=
  eT.comparison.ambient ∘ g.ambientLift ∘ eS.comparison.ambient.symm

private theorem explicit_lift_holomorphic (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) ∞ (explicitAmbientLift B b F x t c g eT eS) :=
  eT.comparison.ambient.contMDiff.comp (g.lift_holomorphic.comp eS.comparison.ambient.symm.contMDiff)

private theorem explicit_lift_projection (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0} ∘
        explicitAmbientLift B b F x t c g eT eS =
      Prod.map c.baseMap id ∘ blowupProj (c.embedding.dim+t.rank)
        {q : c.subdomain × ComplexModel t.rank | q.2=0} := by
  funext z
  exact (congrFun eT.comparison.projection _).trans
    ((congrFun g.lift_projection _).trans (congrArg (Prod.map c.baseMap id)
      (congrFun eS.comparison.inverse_projection z)))

private theorem explicit_canonical_square (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    sourceCanonicalMap B b F x t c g eS ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F =
      explicitStrictMap B b F x t c g eT eS ≫ targetCanonicalMap B b t eT := by
  have hs : g.comparison ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F =
      chosenStrictMap B b F x t c g ≫ t.comparison := g.full_canonical_square
  change (eS.comparison.original.inv ≫ g.comparison) ≫ _ =
    (eS.comparison.original.inv ≫ chosenStrictMap B b F x t c g ≫ eT.comparison.original.hom) ≫
      (eT.comparison.original.inv ≫ t.comparison)
  simp only [Category.assoc,eT.comparison.original.hom_inv_id_assoc]
  exact congrArg (fun H => eS.comparison.original.inv ≫ H) hs

private theorem target_explicit_mem (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t)
    (z : (explicitTarget B b t).obj.left) :
    (targetCanonicalMap B b t e).hom.left.base z∈d.targetOpen :=
  d.target_geometric_mem (e.comparison.original.inv.hom.left.base z)

private theorem source_explicit_mem (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g)
    (z : (explicitSource B b F x t c).obj.left) :
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
      ((sourceCanonicalMap B b F x t c g e).hom.left.base z)∈d.target.targetOpen :=
  d.geometric.source_geometric_mem (e.comparison.original.inv.hom.left.base z)

private theorem target_explicit_normal_original (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t)
    (z : (explicitTarget B b t).obj.left) (i : Fin t.rank) :
    (targetCanonicalMap B b t e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.targetOpen
        ((targetCanonicalMap B b t e).hom.left.base z) (target_explicit_mem B b t d e z) (d.sections i).val) =
      (actualSubspaceInclusion (n := t.embedding.dim+t.rank)
        (geoStrictTransform (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
          {q | q.2=0} _)).stalkMap z
        (projectionNormalGerm (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) z.val i) := by
  let ei := e.comparison.original.inv.hom.left
  let LT := t.comparison.hom.left
  let w := ei.base z
  let γ := (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ
    d.targetOpen (LT.base w) (d.target_geometric_mem w) (d.sections i).val
  have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp ei LT z) γ
  exact hc.trans ((congrArg (fun a => ei.stalkMap z a) (d.target_normal w i)).trans
    (inverse_normal_germ e.comparison z i))

private theorem source_explicit_normal_original (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g)
    (z : (explicitSource B b F x t c).obj.left) (i : Fin t.rank) :
    (sourceCanonicalMap B b F x t c g e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
        ((sourceCanonicalMap B b F x t c g e).hom.left.base z) (source_explicit_mem B b F x t c g d e z)
        (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val) =
      (actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform (blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
          {q | q.2=0} _)).stalkMap z
        (projectionNormalGerm (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) z.val i) := by
  let ei := e.comparison.original.inv.hom.left
  let LS := g.comparison.hom.left
  let w := ei.base z
  let γ := (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
    (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
    ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
    (LS.base w) (d.geometric.source_geometric_mem w)
    (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val
  have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp ei LS z) γ
  exact hc.trans ((congrArg (fun a => ei.stalkMap z a) (d.geometric.source_normal w i)).trans
    (inverse_normal_germ e.comparison z i))

private theorem target_explicit_whole_ideal (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t)
    (z : (explicitTarget B b t).obj.left) :
    Ideal.map ((targetCanonicalMap B b t e).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
        ((targetCanonicalMap B b t e).hom.left.base z)) =
      strictCentreStalkIdeal (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        t.functions) z := by
  let K := (targetCanonicalMap B b t e).hom.left
  have hs := congrArg (Ideal.map (K.stalkMap z).hom)
    (d.target_span (K.base z) (target_explicit_mem B b t d e z))
  have hm := Ideal.map_span (K.stalkMap z).hom (range fun i : Fin t.rank =>
    (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.targetOpen
      (K.base z) (target_explicit_mem B b t d e z) (d.sections i).val)
  rw [←Set.range_comp] at hm
  have hn := congrArg Ideal.span (congrArg Set.range (funext fun i =>
    target_explicit_normal_original B b t d e z i))
  exact hs.trans (hm.trans (hn.trans
    (explicit_strict_centre_span t.positive _ e.charts ⟨0,t.positive⟩ z).symm))

private theorem source_explicit_whole_ideal (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g)
    (z : (explicitSource B b F x t c).obj.left) :
    Ideal.map ((sourceCanonicalMap B b F x t c g e).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
        ((sourceCanonicalMap B b F x t c g e).hom.left.base z)) =
      strictCentreStalkIdeal (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)) z := by
  let K := (sourceCanonicalMap B b F x t c g e).hom.left
  have hs := congrArg (Ideal.map (K.stalkMap z).hom)
    (d.pulled.source_span (K.base z) (source_explicit_mem B b F x t c g d e z))
  have hm := Ideal.map_span (K.stalkMap z).hom (range fun i : Fin t.rank =>
    (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
      ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
      (K.base z) (source_explicit_mem B b F x t c g d e z)
      (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val)
  rw [←Set.range_comp] at hm
  have hn := congrArg Ideal.span (congrArg Set.range (funext fun i =>
    source_explicit_normal_original B b F x t c g d e z i))
  exact hs.trans (hm.trans (hn.trans
    (explicit_strict_centre_span t.positive _ e.charts ⟨0,t.positive⟩ z).symm))

private theorem target_explicit_normal_flat (t : CanonicalTargetGraph B b y)
    (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t)
    (z : (explicitTarget B b t).obj.left) (j i : Fin t.rank) :
    (targetCanonicalMap B b t e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.targetOpen
        ((targetCanonicalMap B b t e).hom.left.base z) (target_explicit_mem B b t d e z) (d.sections i).val) =
      geometricCoordinateClass (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        t.functions) (productNormalChart (n := t.embedding.dim) e.charts.base j) z
          (by rw [e.charts.domain j];trivial) (i.natAdd t.embedding.dim) :=
  (target_explicit_normal_original B b t d e z i).trans
    (explicit_coordinate_original t.positive _ e.charts.base j i z (by rw [e.charts.domain j];trivial)).symm

private theorem source_explicit_normal_flat (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g)
    (z : (explicitSource B b F x t c).obj.left) (j i : Fin t.rank) :
    (sourceCanonicalMap B b F x t c g e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
        ((sourceCanonicalMap B b F x t c g e).hom.left.base z) (source_explicit_mem B b F x t c g d e z)
        (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val) =
      geometricCoordinateClass (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap))
        (productNormalChart (n := c.embedding.dim) e.charts.base j) z
          (by rw [e.charts.domain j];trivial) (i.natAdd c.embedding.dim) :=
  (source_explicit_normal_original B b F x t c g d e z i).trans
    (explicit_coordinate_original t.positive _ e.charts.base j i z (by rw [e.charts.domain j];trivial)).symm

private theorem chosen_strict_ambient_square (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) :
    (chosenStrictMap B b F x t c g).hom.left ≫
        actualSubspaceInclusion (n := t.embedding.dim+t.rank)
          (geoStrictTransform t.projection {q | q.2=0} _) =
      actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform g.projection {q | q.2=0} _) ≫
        ChartedSpace.locallyRingedSpaceMap g.ambientLift g.lift_holomorphic := by
  have hLanding : ∀ z∈geoStrictTransform g.projection {q | q.2=0}
      (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)),
      g.ambientLift z∈geoStrictTransform t.projection {q | q.2=0}
        (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions) :=
    fun z hz => ((chosenStrictMap B b F x t c g).hom.left.base ⟨z,hz⟩).property
  change actualSubspaceMap g.lift_holomorphic hLanding ≫ _ = _
  exact (actualSubspaceMap_inclusion g.lift_holomorphic hLanding).symm

private theorem explicit_native_lift_comp (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    ChartedSpace.locallyRingedSpaceMap (explicitAmbientLift B b F x t c g eT eS)
        (explicit_lift_holomorphic B b F x t c g eT eS) =
      ChartedSpace.locallyRingedSpaceMap eS.comparison.ambient.symm eS.comparison.ambient.symm.contMDiff ≫
        ChartedSpace.locallyRingedSpaceMap g.ambientLift g.lift_holomorphic ≫
          ChartedSpace.locallyRingedSpaceMap eT.comparison.ambient eT.comparison.ambient.contMDiff := by
  have h₁ := ChartedSpace.locallyRingedSpace_comp
    (IM := 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)))
    (IN := 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)))
    (IP := 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)))
    eS.comparison.ambient.symm.contMDiff (eT.comparison.ambient.contMDiff.comp g.lift_holomorphic)
  have h₂ := ChartedSpace.locallyRingedSpace_comp
    (IM := 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)))
    (IN := 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)))
    (IP := 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)))
    g.lift_holomorphic eT.comparison.ambient.contMDiff
  exact h₁.trans (congrArg (fun H =>
    ChartedSpace.locallyRingedSpaceMap eS.comparison.ambient.symm eS.comparison.ambient.symm.contMDiff ≫ H) h₂)

private theorem explicit_strict_ambient_square (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    (explicitStrictMap B b F x t c g eT eS).hom.left ≫
        actualSubspaceInclusion (n := t.embedding.dim+t.rank)
          (geoStrictTransform (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
            {q | q.2=0} _) =
      actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform (blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
          {q | q.2=0} _) ≫
        ChartedSpace.locallyRingedSpaceMap (explicitAmbientLift B b F x t c g eT eS)
          (explicit_lift_holomorphic B b F x t c g eT eS) := by
  let s := eS.comparison.original.inv.hom.left
  let h := (chosenStrictMap B b F x t c g).hom.left
  let u := eT.comparison.original.hom.hom.left
  let iT : (geometricSource t.blowup t.analytic).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) t.lift :=
    actualSubspaceInclusion (n := t.embedding.dim+t.rank)
    (geoStrictTransform t.projection {q | q.2=0}
      (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier) t.functions))
  let iS : (geometricSource g.blowup c.analytic).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) g.lift :=
    actualSubspaceInclusion (n := c.embedding.dim+t.rank)
    (geoStrictTransform g.projection {q | q.2=0}
      (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)))
  let nT := ChartedSpace.locallyRingedSpaceMap eT.comparison.ambient eT.comparison.ambient.contMDiff
  let nS := ChartedSpace.locallyRingedSpaceMap eS.comparison.ambient.symm eS.comparison.ambient.symm.contMDiff
  let nL := ChartedSpace.locallyRingedSpaceMap g.ambientLift g.lift_holomorphic
  let iET : (explicitTarget B b t).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
        (BlowupSpace (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0}) :=
    actualSubspaceInclusion (n := t.embedding.dim+t.rank) _
  let iES : (explicitSource B b F x t c).obj.left ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
        (BlowupSpace (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0}) :=
    actualSubspaceInclusion (n := c.embedding.dim+t.rank) _
  have hu : u ≫ iET=iT ≫ nT := eT.comparison.forward
  have hs : s ≫ iS=iES ≫ nS := eS.comparison.backward
  have hh : h ≫ iT=iS ≫ nL := chosen_strict_ambient_square B b F x t c g
  have hcomp : (s ≫ h ≫ u) ≫ iET=iES ≫ (nS ≫ nL ≫ nT) :=
    calc
      _ = s ≫ ((h ≫ u) ≫ iET) := Category.assoc s (h ≫ u) iET
      _ = s ≫ (h ≫ (u ≫ iET)) := congrArg (fun K => s ≫ K) (Category.assoc h u iET)
      _ = s ≫ (h ≫ (iT ≫ nT)) := congrArg (fun K => s ≫ h ≫ K) hu
      _ = s ≫ ((h ≫ iT) ≫ nT) := congrArg (fun K => s ≫ K) (Category.assoc h iT nT).symm
      _ = s ≫ ((iS ≫ nL) ≫ nT) := congrArg (fun K => s ≫ (K ≫ nT)) hh
      _ = s ≫ (iS ≫ (nL ≫ nT)) := congrArg (fun K => s ≫ K) (Category.assoc iS nL nT)
      _ = (s ≫ iS) ≫ (nL ≫ nT) := (Category.assoc s iS (nL ≫ nT)).symm
      _ = (iES ≫ nS) ≫ (nL ≫ nT) := congrArg (fun K => K ≫ (nL ≫ nT)) hs
      _ = iES ≫ (nS ≫ nL ≫ nT) := Category.assoc iES nS (nL ≫ nT)
  change (s ≫ h ≫ u) ≫ iET=iES ≫ _
  exact hcomp.trans (congrArg (fun K => iES ≫ K)
    (explicit_native_lift_comp B b F x t c g eT eS).symm)

private theorem explicit_strict_projection (t : CanonicalTargetGraph B b y)
    (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c)
    (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    explicitStrictMap B b F x t c g eT eS ≫
        geometricProjectionMorphism (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic =
      geometricProjectionMorphism (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫
        graphNormalMorphism c.baseMap c.holomorphic t.functions _ _ c.landing c.analytic t.analytic := by
  let s := eS.comparison.original.inv
  let H := chosenStrictMap B b F x t c g
  let u := eT.comparison.original.hom
  let pT := geometricProjectionMorphism t.blowup t.analytic
  let pS := geometricProjectionMorphism g.blowup c.analytic
  let f := graphNormalMorphism c.baseMap c.holomorphic t.functions _ _ c.landing c.analytic t.analytic
  have hh : H ≫ pT=pS ≫ f :=
    geometricNormalMorphism_projection c.baseMap c.holomorphic t.functions _ _ c.landing c.analytic t.analytic
      g.projection g.blowup t.projection t.blowup g.ambientLift g.lift_holomorphic g.lift_projection
  have hu := eT.comparison.original_projection
  have hs := inverse_original_projection eS.comparison
  change (s ≫ H ≫ u) ≫ _ = _ ≫ f
  calc
    _ = s ≫ H ≫ pT := by rw [Category.assoc,Category.assoc,hu]
    _ = s ≫ (pS ≫ f) := congrArg (fun K => s ≫ K) hh
    _ = (s ≫ pS) ≫ f := (Category.assoc s pS f).symm
    _ = _ := congrArg (fun K => K ≫ f) hs

-- Public assertion groups retain the exact complete private statements.

structure TargetExplicitMapLaws (t : CanonicalTargetGraph B b y) (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t) : Prop where
  open_immersion : LocallyRingedSpace.IsOpenImmersion (targetCanonicalMap B b t e).hom.left
  range_eq : (d.targetOpen : Set (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.toTopCat)=
    range (targetCanonicalMap B b t e).hom.left.base
  projection : targetCanonicalMap B b t e ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      geometricProjectionMorphism (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
        t.analytic ≫ chartGraphMorphism t.embedding t.domain t.functions t.holomorphic t.analytic
  scalar : (targetCanonicalMap B b t e).hom.left ≫ (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.hom=(explicitTarget B b t).obj.hom

structure SourceExplicitMapLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (e : SourceExplicitGeometry B b F x t c g) : Prop where
  open_immersion : LocallyRingedSpace.IsOpenImmersion (sourceCanonicalMap B b F x t c g e).hom.left
  range_eq : range (sourceCanonicalMap B b F x t c g e).hom.left.base=range g.comparison.hom.left.base
  projection : sourceCanonicalMap B b F x t c g e ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism
      (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) =
      geometricProjectionMorphism (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
        c.analytic ≫ c.chart
  scalar : (sourceCanonicalMap B b F x t c g e).hom.left ≫ (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).obj.hom=(explicitSource B b F x t c).obj.hom

structure TargetExplicitNormalLaws (t : CanonicalTargetGraph B b y) (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t) : Prop where
  geometric_mem : ∀ (z : (explicitTarget B b t).obj.left),
    (targetCanonicalMap B b t e).hom.left.base z∈d.targetOpen
  whole_ideal : ∀ (z : (explicitTarget B b t).obj.left),
    Ideal.map ((targetCanonicalMap B b t e).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
        ((targetCanonicalMap B b t e).hom.left.base z)) =
      strictCentreStalkIdeal (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        t.functions) z
  normal : ∀ (z : (explicitTarget B b t).obj.left) (j i : Fin t.rank),
    (targetCanonicalMap B b t e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.germ d.targetOpen
        ((targetCanonicalMap B b t e).hom.left.base z) (geometric_mem z) (d.sections i).val) =
      geometricCoordinateClass (productGraph ((Subtype.val : t.domain → t.embedding.ambient) ⁻¹' t.embedding.carrier)
        t.functions) (productNormalChart (n := t.embedding.dim) e.charts.base j) z
          (by rw [e.charts.domain j];trivial) (i.natAdd t.embedding.dim)

structure SourceExplicitNormalLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g) : Prop where
  geometric_mem : ∀ (z : (explicitSource B b F x t c).obj.left),
    (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base
      ((sourceCanonicalMap B b F x t c g e).hom.left.base z)∈d.target.targetOpen
  whole_ideal : ∀ (z : (explicitSource B b F x t c).obj.left),
    Ideal.map ((sourceCanonicalMap B b F x t c g e).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)
        ((sourceCanonicalMap B b F x t c g e).hom.left.base z)) =
      strictCentreStalkIdeal (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap)) z
  normal : ∀ (z : (explicitSource B b F x t c).obj.left) (j i : Fin t.rank),
    (sourceCanonicalMap B b F x t c g e).hom.left.stalkMap z
      ((OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left.presheaf.germ
        ((Opens.map (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base).obj d.target.targetOpen)
        ((sourceCanonicalMap B b F x t c g e).hom.left.base z) (geometric_mem z)
        (canonicalPulledIdealSection B b F d.target.targetOpen (d.target.sections i)).val) =
      geometricCoordinateClass (productGraph ((Subtype.val : c.subdomain → c.domain) ⁻¹'
        ((Subtype.val : c.domain → c.embedding.ambient) ⁻¹' c.embedding.carrier)) (t.functions ∘ c.baseMap))
        (productNormalChart (n := c.embedding.dim) e.charts.base j) z
          (by rw [e.charts.domain j];trivial) (i.natAdd c.embedding.dim)

structure ExplicitProductSquareLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
      𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank)) ∞ (explicitAmbientLift B b F x t c g eT eS)
  ambient_projection : blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0} ∘
        explicitAmbientLift B b F x t c g eT eS =
      Prod.map c.baseMap id ∘ blowupProj (c.embedding.dim+t.rank)
        {q : c.subdomain × ComplexModel t.rank | q.2=0}
  canonical_square : sourceCanonicalMap B b F x t c g eS ≫ OriginalFiniteIdealBlowupSquare.inducedMorphism B b F =
      explicitStrictMap B b F x t c g eT eS ≫ targetCanonicalMap B b t eT
  ambient_inclusion : (explicitStrictMap B b F x t c g eT eS).hom.left ≫
        actualSubspaceInclusion (n := t.embedding.dim+t.rank)
          (geoStrictTransform (blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2=0})
            {q | q.2=0} _) =
      actualSubspaceInclusion (n := c.embedding.dim+t.rank)
        (geoStrictTransform (blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0})
          {q | q.2=0} _) ≫
        ChartedSpace.locallyRingedSpaceMap (explicitAmbientLift B b F x t c g eT eS)
          (explicit_lift_holomorphic B b F x t c g eT eS)
  strict_projection : explicitStrictMap B b F x t c g eT eS ≫
        geometricProjectionMorphism (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive) t.analytic =
      geometricProjectionMorphism (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive) c.analytic ≫
        graphNormalMorphism c.baseMap c.holomorphic t.functions _ _ c.landing c.analytic t.analytic
  scalar : (explicitStrictMap B b F x t c g eT eS).hom.left ≫ (explicitTarget B b t).obj.hom=(explicitSource B b F x t c).obj.hom

private theorem constructedTargetMapLaws (t : CanonicalTargetGraph B b y) (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t) :
    TargetExplicitMapLaws B b t d e where
  open_immersion := target_map_open B b t e
  range_eq := d.targetOpen_range.trans (target_map_range B b t e).symm
  projection := target_map_projection B b t e
  scalar := Over.w (targetCanonicalMap B b t e).hom

private theorem constructedSourceMapLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (e : SourceExplicitGeometry B b F x t c g) :
    SourceExplicitMapLaws B b F x t c g e where
  open_immersion := source_map_open B b F x t c g e
  range_eq := source_map_range B b F x t c g e
  projection := source_map_projection B b F x t c g e
  scalar := Over.w (sourceCanonicalMap B b F x t c g e).hom

private theorem constructedTargetNormalLaws (t : CanonicalTargetGraph B b y) (d : CanonicalTargetNormalSectionData B b t) (e : TargetExplicitGeometry B b t) :
    TargetExplicitNormalLaws B b t d e where
  geometric_mem := target_explicit_mem B b t d e
  whole_ideal := target_explicit_whole_ideal B b t d e
  normal := target_explicit_normal_flat B b t d e

private theorem constructedSourceNormalLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g) (e : SourceExplicitGeometry B b F x t c g) :
    SourceExplicitNormalLaws B b F x t c g d e where
  geometric_mem := source_explicit_mem B b F x t c g d e
  whole_ideal := source_explicit_whole_ideal B b F x t c g d e
  normal := source_explicit_normal_flat B b F x t c g d e

private theorem constructedSquareLaws (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (eT : TargetExplicitGeometry B b t) (eS : SourceExplicitGeometry B b F x t c g) :
    ExplicitProductSquareLaws B b F x t c g eT eS where
  holomorphic := explicit_lift_holomorphic B b F x t c g eT eS
  ambient_projection := explicit_lift_projection B b F x t c g eT eS
  canonical_square := explicit_canonical_square B b F x t c g eT eS
  ambient_inclusion := explicit_strict_ambient_square B b F x t c g eT eS
  strict_projection := explicit_strict_projection B b F x t c g eT eS
  scalar := Over.w (explicitStrictMap B b F x t c g eT eS).hom

/-- OUTPUT data: the ordinary existence theorem derives both comparisons and
all laws internally. No comparison, Cartesian square or Cartier packet is input. -/
structure SameCanonicalExplicitProductModels (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g) where
  target : TargetExplicitGeometry B b t
  source : SourceExplicitGeometry B b F x t c g
  target_maps : TargetExplicitMapLaws B b t d.target target
  source_maps : SourceExplicitMapLaws B b F x t c g source
  target_normals : TargetExplicitNormalLaws B b t d.target target
  source_normals : SourceExplicitNormalLaws B b F x t c g d source
  square : ExplicitProductSquareLaws B b F x t c g target source

private def constructedModels (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t) (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g) :
    SameCanonicalExplicitProductModels B b F x t c g d where
  target := constructedTargetGeometry B b t
  source := constructedSourceGeometry B b F x t c g
  target_maps := constructedTargetMapLaws B b t d.target (constructedTargetGeometry B b t)
  source_maps := constructedSourceMapLaws B b F x t c g (constructedSourceGeometry B b F x t c g)
  target_normals := constructedTargetNormalLaws B b t d.target (constructedTargetGeometry B b t)
  source_normals := constructedSourceNormalLaws B b F x t c g d (constructedSourceGeometry B b F x t c g)
  square := constructedSquareLaws B b F x t c g
    (constructedTargetGeometry B b t) (constructedSourceGeometry B b F x t c g)

/-- Ordinary original inputs ONLY, including the GIVEN target point. The SAME
normal sections and full canonical square are constructed internally. Identity
product charts preserve C0; source strict transforms may be EMPTY. This does
not construct a source strict point from a raw pair or assert a Qsat dictionary. -/
theorem exists_same_canonical_explicit_product_models
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x=(OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c) (d : CanonicalNormalSectionData B b F x t c g),
      Nonempty (SameCanonicalExplicitProductModels B b F x t c g d) := by
  obtain ⟨t,c,g,⟨d⟩⟩ := exists_same_pulled_canonical_normal_sections B b F x y hxy
  exact ⟨t,c,g,d,⟨constructedModels B b F x t c g d⟩⟩

end SameCanonicalModels

end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts

import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Analytic.Unibranch.OriginalNativeModification
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback
import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace
import Hironaka.Resolution.HironakaSmoothSubmersionComposition

/-! Actual reduced analytic cylinders and prescribed native product windows.
All maps retain the whole quotient sheaf and complex scalar triangle.
No smooth-morphism, centre, canonical-history or resolution packet is input.
Blueprint first: `original-native-product-window.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductWindow
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualSingularSubmersionPullback HironakaAuxiliaryGraphGeometry
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionComposition
  AnalyticSubsetPreimage SourceReducedComplexSpace OriginalNativeModification
open scoped ProductComplexManifold

variable {X : SourceReducedComplexSpace}

abbrev productAmbient (e : LocalEmbedding X) (r : ℕ) := e.ambient × ComplexModel r

/-- The literal cylinder, with every original defining equation retained. -/
def productCarrier (e : LocalEmbedding X) (r : ℕ) : Set (productAmbient e r) :=
  (Prod.fst : productAmbient e r → e.ambient) ⁻¹' e.carrier

theorem productCarrier_analytic (e : LocalEmbedding X) (r : ℕ) :
    IsComplexAnalyticSubset (n := e.dim+r) (productCarrier e r) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage ProductComplexManifold.contMDiff_fst e.analytic

def chartSpace (e : LocalEmbedding X) : SourceReducedComplexSpace :=
  ofClosedAnalytic e.carrier e.analytic

/-- The same original local embedding, in the original full native category. -/
def chartInclusion (e : LocalEmbedding X) : chartSpace e ⟶ X :=
  ObjectProperty.homMk (Over.homMk e.map e.overPoint)

/-- The actual whole-vanishing-ideal quotient on the product manifold. -/
def productSpace (e : LocalEmbedding X) (r : ℕ) : SourceReducedComplexSpace :=
  ofClosedAnalytic (n := e.dim+r) (productCarrier e r) (productCarrier_analytic e r)

def firstToChart (e : LocalEmbedding X) (r : ℕ) : productSpace e r ⟶ chartSpace e :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := Prod.fst) ProductComplexManifold.contMDiff_fst (fun _ hx => hx))
    (actualSubspaceMap_point ProductComplexManifold.contMDiff_fst (fun _ hx => hx)))

def first (e : LocalEmbedding X) (r : ℕ) : productSpace e r ⟶ X :=
  firstToChart e r ≫ chartInclusion e

def second (e : LocalEmbedding X) (r : ℕ) :
    productSpace e r ⟶ wholeModel (n := r) (ComplexModel r) :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := Prod.snd) ProductComplexManifold.contMDiff_snd (fun _ _ => mem_univ _))
    (actualSubspaceMap_point ProductComplexManifold.contMDiff_snd (fun _ _ => mem_univ _)))

/-- Actual native product points, with their original carrier proofs. -/
def pointEquiv (e : LocalEmbedding X) (r : ℕ) :
    (productSpace e r).obj.left ≃ e.carrier × ComplexModel r where
  toFun p := (⟨p.val.1,p.property⟩,p.val.2)
  invFun p := ⟨(p.1.val,p.2),p.1.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem first_point (e : LocalEmbedding X) (r : ℕ) (p : (productSpace e r).obj.left) :
    (first e r).hom.left.base p = e.toPoint (pointEquiv e r p).1 := rfl

theorem second_point (e : LocalEmbedding X) (r : ℕ) (p : (productSpace e r).obj.left) :
    ((second e r).hom.left.base p).val = (pointEquiv e r p).2 := rfl

/-- Equality of WHOLE original ideals, not only equality of their supports. -/
theorem product_whole_ideal (e : LocalEmbedding X) (r : ℕ) :
    GermIdeal.pullback (m := e.dim+r) (Prod.fst : productAmbient e r → e.ambient)
        (vanishingIdeal (n := e.dim) e.carrier) =
      vanishingIdeal (n := e.dim+r) (productCarrier e r) :=
  HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
    (isSubmersion_fst (n := e.dim) (m := r) (X := e.ambient) (Y := ComplexModel r)) e.carrier

theorem productCarrier_eq_empty_iff (e : LocalEmbedding X) (r : ℕ) :
    productCarrier e r = ∅ ↔ e.carrier = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hp : (c,(0 : ComplexModel r)) ∈ productCarrier e r := hc
    rw [h] at hp
    exact hp
  · intro h
    simp only [productCarrier,h,preimage_empty]

def windowCarrier (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) : Set W :=
  (Subtype.val : W → productAmbient e r) ⁻¹' productCarrier e r

theorem windowCarrier_analytic (e : LocalEmbedding X) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    IsComplexAnalyticSubset (n := e.dim+r) (windowCarrier e r W) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val
    (productCarrier_analytic e r)

def windowSpace (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    SourceReducedComplexSpace := ofClosedAnalytic (windowCarrier e r W) (windowCarrier_analytic e r W)

/-- The actual reduced-subspace restriction, with its entire quotient map. -/
def windowInclusion (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowSpace e r W ⟶ productSpace e r :=
  ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap (productCarrier e r) W)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

theorem windowInclusion_isOpenImmersion (e : LocalEmbedding X) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    LocallyRingedSpace.IsOpenImmersion (windowInclusion e r W).hom.left :=
  actualOpenSubspaceMap_isOpenImmersion (productCarrier e r) W

def windowProjection (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    W → e.ambient := Prod.fst ∘ Subtype.val

theorem windowProjection_holomorphic (e : LocalEmbedding X) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    ContMDiff 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞ (windowProjection e r W) :=
  ProductComplexManifold.contMDiff_fst.comp contMDiff_subtype_val

theorem window_projection_isSubmersion (e : LocalEmbedding X) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞
      (windowProjection e r W) := by
  change Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞
    ((Prod.fst : productAmbient e r → e.ambient) ∘ (Subtype.val : W → productAmbient e r))
  exact isSubmersion_composition
    (X := BlowupTowers.CMfd.of (n := e.dim) e.ambient)
    (Y := BlowupTowers.CMfd.of (n := e.dim+r) (productAmbient e r))
    (Z := BlowupTowers.CMfd.of (n := e.dim+r) W)
    (isSubmersion_fst (n := e.dim) (m := r) (X := e.ambient) (Y := ComplexModel r))
    (isSubmersion_val (A := BlowupTowers.CMfd.of (n := e.dim+r) (productAmbient e r)) W)

def windowFirstToChart (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowSpace e r W ⟶ chartSpace e :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (windowProjection_holomorphic e r W) (fun _ hx => hx))
    (actualSubspaceMap_point (windowProjection_holomorphic e r W) (fun _ hx => hx)))

def windowFirst (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowSpace e r W ⟶ X := windowFirstToChart e r W ≫ chartInclusion e

def windowSecond (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowSpace e r W ⟶ wholeModel (n := r) (ComplexModel r) :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := Prod.snd ∘ (Subtype.val : W → productAmbient e r))
      (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val) (fun _ _ => mem_univ _))
    (actualSubspaceMap_point (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val)
      (fun _ _ => mem_univ _)))

theorem window_first_square (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowInclusion e r W ≫ first e r = windowFirst e r W := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualOpenSubspaceMap (productCarrier e r) W ≫
      (actualSubspaceMap ProductComplexManifold.contMDiff_fst (fun _ hx => hx) ≫ e.map) =
    actualSubspaceMap (windowProjection_holomorphic e r W) (fun _ hx => hx) ≫ e.map
  have hcomp := actualSubspaceMap_comp (n := e.dim+r) (m := e.dim+r) (p := e.dim)
    (C := windowCarrier e r W) (D := productCarrier e r) (E := e.carrier)
    (f := (Subtype.val : W → productAmbient e r)) (g := Prod.fst)
    contMDiff_subtype_val (ProductComplexManifold.contMDiff_fst (n := e.dim) (m := r))
    (fun _ hx => hx) (fun _ hx => hx)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ e.map) hcomp.symm)

theorem window_second_square (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    windowInclusion e r W ≫ second e r = windowSecond e r W := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (actualSubspaceMap_comp contMDiff_subtype_val ProductComplexManifold.contMDiff_snd
    (fun _ hx => hx) (fun _ _ => mem_univ _)).symm

theorem window_whole_ideal (e : LocalEmbedding X) (r : ℕ) (W : Opens (productAmbient e r)) :
    GermIdeal.pullback (m := e.dim+r) (windowProjection e r W) (vanishingIdeal (n := e.dim) e.carrier) =
      vanishingIdeal (n := e.dim+r) (windowCarrier e r W) :=
  HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
    (window_projection_isSubmersion e r W) e.carrier

/-- A prescribed native open is the exact image of one internally constructed
actual ambient-open product window, retaining every point of that open. -/
theorem exists_window_of_native_open (e : LocalEmbedding X) (r : ℕ)
    (O : Opens (productSpace e r).obj.left) :
    ∃ W : Opens (productAmbient e r),
      range (windowInclusion e r W).hom.left.base = (O : Set (productSpace e r).obj.left) ∧
      ∀ p ∈ O, p.val ∈ W := by
  change Opens (productCarrier e r) at O
  have hO : IsOpen (O : Set (productCarrier e r)) := O.isOpen
  obtain ⟨V,hV,hVO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hO
  let W : Opens (productAmbient e r) := ⟨V,hV⟩
  have hpoint : ∀ p ∈ O, p.val ∈ W := by
    intro p hp
    change p ∈ (Subtype.val : productCarrier e r → productAmbient e r) ⁻¹' V
    rw [hVO]
    exact hp
  refine ⟨W,?_,hpoint⟩
  ext p
  constructor
  · rintro ⟨w,rfl⟩
    change windowCarrier e r W at w
    have hw : w.val.val ∈ productCarrier e r := w.property
    have hp : (⟨w.val.val,hw⟩ : productCarrier e r) ∈
        (Subtype.val : productCarrier e r → productAmbient e r) ⁻¹' V := w.val.property
    exact (Set.ext_iff.mp hVO _).mp hp
  · intro hp
    exact ⟨⟨⟨p.val,hpoint p hp⟩,p.property⟩,rfl⟩

/-- Literal refinement of the same reduced product trace. -/
def refinement (e : LocalEmbedding X) (r : ℕ) {V W : Opens (productAmbient e r)} (hVW : V ≤ W) :
    windowSpace e r V ⟶ windowSpace e r W :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (f := Opens.inclusion hVW) (contMDiff_inclusion hVW) (fun _ hx => hx))
    (actualSubspaceMap_point (contMDiff_inclusion hVW) (fun _ hx => hx)))

theorem refinement_square (e : LocalEmbedding X) (r : ℕ)
    {V W : Opens (productAmbient e r)} (hVW : V ≤ W) :
    refinement e r hVW ≫ windowInclusion e r W = windowInclusion e r V := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (actualSubspaceMap_comp (n := e.dim+r) (m := e.dim+r) (p := e.dim+r)
    (C := windowCarrier e r V) (D := windowCarrier e r W) (E := productCarrier e r)
    (f := Opens.inclusion hVW) (g := (Subtype.val : W → productAmbient e r))
    (contMDiff_inclusion hVW) contMDiff_subtype_val (fun _ hx => hx) (fun _ hx => hx)).symm

theorem refinement_isOpenImmersion (e : LocalEmbedding X) (r : ℕ)
    {V W : Opens (productAmbient e r)} (hVW : V ≤ W) :
    LocallyRingedSpace.IsOpenImmersion (refinement e r hVW).hom.left := by
  let jW := (windowInclusion e r W).hom.left
  let jV := (windowInclusion e r V).hom.left
  let a := (refinement e r hVW).hom.left
  let : LocallyRingedSpace.IsOpenImmersion jW := windowInclusion_isOpenImmersion e r W
  let : LocallyRingedSpace.IsOpenImmersion jV := windowInclusion_isOpenImmersion e r V
  have hfac : a ≫ jW = jV := congrArg (fun k => k.hom.left) (refinement_square e r hVW)
  have hr : range jV.base ⊆ range jW.base := by
    rintro _ ⟨p,rfl⟩
    exact ⟨a.base p,congrArg (fun k => k.base p) hfac⟩
  let b := LocallyRingedSpace.IsOpenImmersion.lift jW jV hr
  have he : a = b := by
    apply (cancel_mono jW).mp
    exact hfac.trans (LocallyRingedSpace.IsOpenImmersion.lift_fac jW jV hr).symm
  let : IsIso (CategoryTheory.Limits.pullback.snd jW jV) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset jW jV hr
  have hb : LocallyRingedSpace.IsOpenImmersion b := by
    dsimp only [b,LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  change LocallyRingedSpace.IsOpenImmersion a
  exact he.symm ▸ hb

theorem refinement_first_square (e : LocalEmbedding X) (r : ℕ)
    {V W : Opens (productAmbient e r)} (hVW : V ≤ W) :
    refinement e r hVW ≫ windowFirst e r W = windowFirst e r V := by
  rw [← window_first_square,← Category.assoc,refinement_square,window_first_square]

theorem refinement_second_square (e : LocalEmbedding X) (r : ℕ)
    {V W : Opens (productAmbient e r)} (hVW : V ≤ W) :
    refinement e r hVW ≫ windowSecond e r W = windowSecond e r V := by
  rw [← window_second_square,← Category.assoc,refinement_square,window_second_square]

/-- Zero free dimension is the actual original ambient, without point choices. -/
def zeroProductDiffeomorph (e : LocalEmbedding X) :
    productAmbient e 0 ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+0)),𝓘(ℂ,ComplexModel e.dim)⟯ e.ambient where
  toFun := Prod.fst
  invFun p := (p,0)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  right_inv _ := rfl
  contMDiff_toFun := ProductComplexManifold.contMDiff_fst
  contMDiff_invFun := ProductComplexManifold.contMDiff_prodMk contMDiff_id contMDiff_const

def zeroProductRawIso (e : LocalEmbedding X) :
    (productSpace e 0).obj.left ≅ (chartSpace e).obj.left :=
  actualSubspaceBiholomorphicIso (zeroProductDiffeomorph e) (productCarrier e 0) e.carrier
    (fun _ => Iff.rfl)

/-- The full native complex-space isomorphism, retaining the scalar triangle. -/
def zeroProductIso (e : LocalEmbedding X) : productSpace e 0 ≅ chartSpace e :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk (zeroProductRawIso e)
    (actualSubspaceMap_point (zeroProductDiffeomorph e).contMDiff (fun _ hx => hx)))

theorem zero_first_isOpenImmersion (e : LocalEmbedding X) :
    LocallyRingedSpace.IsOpenImmersion (first e 0).hom.left := by
  have hψ : LocallyRingedSpace.IsOpenImmersion (zeroProductRawIso e).hom := by infer_instance
  change LocallyRingedSpace.IsOpenImmersion ((zeroProductRawIso e).hom ≫ e.map)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (zeroProductRawIso e).hom hψ e.map e.isOpenImmersion

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductWindow

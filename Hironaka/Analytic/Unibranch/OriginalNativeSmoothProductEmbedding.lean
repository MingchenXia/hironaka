import Hironaka.Analytic.Unibranch.OriginalNativeSmoothGivenTargetWindow
import Hironaka.Analytic.Unibranch.OriginalNativeProductAssociativity
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-!
# The entire actual smooth product window as an original local embedding

The actual canonical block coordinates cover the SAME whole product open,
not a newly chosen smaller chart. Full native quotient maps, original points
and whole defining ideals are retained. Blueprint FIRST:
`original-native-smooth-product-embedding.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductEmbedding
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka ProductComplexManifold
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaSubmersionActualProductWindow
  HironakaActualOpenEmbeddingVanishingIdeal SourceReducedComplexSpace
  OriginalNativeProductWindow OriginalNativeProductAssociativity
  OriginalNativeSmoothGivenTargetWindow
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

def coordinateWindow (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r)) :
    Opens (ComplexModel (e.dim+r)) :=
  ⟨(fun p : productAmbient e r => prodModelEquiv e.dim r (p.1.val,p.2)) '' (W : Set _),
    ((flatAmbient e r).isOpen.isOpenMap_subtype_val.comp
      (flatDiffeomorph e r).toHomeomorph.isOpenMap) _ W.isOpen⟩

theorem coordinateWindow_first (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    ∀ z ∈ coordinateWindow e r W, ((prodModelEquiv e.dim r).symm z).1 ∈ e.ambient := by
  rintro _ ⟨p,_hp,rfl⟩
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using p.1.property

theorem productWindow_eq (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    productWindow (coordinateWindow e r W) e.ambient = W := by
  ext p
  change prodModelEquiv e.dim r (p.1.val,p.2) ∈
    (fun q : productAmbient e r => prodModelEquiv e.dim r (q.1.val,q.2)) '' (W : Set _) ↔ p ∈ W
  constructor
  · rintro ⟨q,hq,hqp⟩
    have hp := (prodModelEquiv e.dim r).injective hqp
    have heq : q = p := Prod.ext
      (Subtype.ext (congrArg (fun z : ComplexModel e.dim × ComplexModel r => z.1) hp))
      (congrArg (fun z : ComplexModel e.dim × ComplexModel r => z.2) hp)
    exact heq ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

def coordinateDiffeomorph (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    coordinateWindow e r W ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+r)),𝓘(ℂ,ComplexModel (e.dim+r))⟯ W :=
  Eq.mp (congrArg (fun O : Opens (productAmbient e r) =>
    coordinateWindow e r W ≃ₘ⟮𝓘(ℂ,ComplexModel (e.dim+r)),𝓘(ℂ,ComplexModel (e.dim+r))⟯ O)
    (productWindow_eq e r W))
    (splitWindowDiffeomorph (coordinateWindow e r W) e.ambient (coordinateWindow_first e r W))

def coordinateCarrier (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) : Set (coordinateWindow e r W) :=
  coordinateDiffeomorph e r W ⁻¹' windowCarrier e r W

theorem coordinateCarrier_analytic (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    IsComplexAnalyticSubset (n := e.dim+r) (coordinateCarrier e r W) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (coordinateDiffeomorph e r W).contMDiff (windowCarrier_analytic e r W)

def coordinateSpace (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r)) :
    SourceReducedComplexSpace :=
  ofClosedAnalytic (coordinateCarrier e r W) (coordinateCarrier_analytic e r W)

def coordinateIso (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r)) :
    coordinateSpace e r W ≅ windowSpace e r W :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk
      (actualSubspaceBiholomorphicIso (coordinateDiffeomorph e r W)
        (coordinateCarrier e r W) (windowCarrier e r W) (fun _ => Iff.rfl))
      (actualSubspaceMap_point (coordinateDiffeomorph e r W).contMDiff (fun _ hx => hx)))

theorem coordinateIso_point (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) (z : (coordinateSpace e r W).obj.left) :
    ((coordinateIso e r W).hom.hom.left.base z).val = coordinateDiffeomorph e r W z.val := rfl

theorem whole_coordinate_ideal (e : LocalEmbedding Y) (r : ℕ)
    (W : Opens (productAmbient e r)) :
    GermIdeal.pullback (m := e.dim+r) (coordinateDiffeomorph e r W)
        (vanishingIdeal (n := e.dim+r) (windowCarrier e r W)) =
      vanishingIdeal (n := e.dim+r) (coordinateCarrier e r W) :=
  pullback_vanishingIdeal_of_biholomorphism (coordinateDiffeomorph e r W) (windowCarrier e r W)

def productEmbedding (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) :
    LocalEmbedding X where
  dim := e.dim+r
  ambient := coordinateWindow e r W
  carrier := coordinateCarrier e r W
  analytic := coordinateCarrier_analytic e r W
  map := (coordinateIso e r W).hom.hom.left ≫ i.hom.left
  isOpenImmersion := by
    have hI : LocallyRingedSpace.IsOpenImmersion (coordinateIso e r W).hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft (coordinateIso e r W)).hom
      infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hI _ hi
  overPoint := (Category.assoc _ _ _).trans
    ((congrArg (fun a => (coordinateIso e r W).hom.hom.left ≫ a) (Over.w i.hom)).trans
      (Over.w (coordinateIso e r W).hom.hom))

theorem productEmbedding_dim (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) :
    (productEmbedding e r W i hi).dim = e.dim+r := rfl

theorem productEmbedding_square (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) :
    (productEmbedding e r W i hi).map = (coordinateIso e r W).hom.hom.left ≫ i.hom.left := rfl

theorem productEmbedding_point (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (z : (windowSpace e r W).obj.left) :
    (productEmbedding e r W i hi).toPoint ((coordinateIso e r W).inv.hom.left.base z) =
      i.hom.left.base z := by
  apply congrArg i.hom.left.base
  exact congrArg (fun a => a.hom.left.base z) (coordinateIso e r W).inv_hom_id

theorem productEmbedding_range (e : LocalEmbedding Y) (r : ℕ) (W : Opens (productAmbient e r))
    (i : windowSpace e r W ⟶ X) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) :
    range (productEmbedding e r W i hi).toPoint = range i.hom.left.base := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨(coordinateIso e r W).hom.hom.left.base z,rfl⟩
  · rintro ⟨z,rfl⟩
    exact ⟨(coordinateIso e r W).inv.hom.left.base z,productEmbedding_point e r W i hi z⟩

namespace GivenTargetWindow

variable {f : X ⟶ Y} {x : X.obj.left} {e : LocalEmbedding Y} {V : Opens X.obj.left}

def sourceEmbedding (w : GivenTargetWindow f x e V) : LocalEmbedding X :=
  productEmbedding w.target w.rank w.window w.sourceMap w.source_open

theorem sourceEmbedding_dim (w : GivenTargetWindow f x e V) :
    (sourceEmbedding w).dim = e.dim+w.rank := rfl

def sourceEmbeddingPoint (w : GivenTargetWindow f x e V) : (sourceEmbedding w).carrier :=
  (coordinateIso w.target w.rank w.window).inv.hom.left.base w.sourcePoint

theorem sourceEmbeddingPoint_image (w : GivenTargetWindow f x e V) :
    (sourceEmbedding w).toPoint (sourceEmbeddingPoint w) = x :=
  (productEmbedding_point w.target w.rank w.window w.sourceMap w.source_open w.sourcePoint).trans w.point

theorem sourceEmbedding_range (w : GivenTargetWindow f x e V) :
    range (sourceEmbedding w).toPoint ⊆ (V : Set X.obj.left) := by
  intro y hy
  exact w.source_range ((Set.ext_iff.mp
    (productEmbedding_range w.target w.rank w.window w.sourceMap w.source_open) y).mp hy)

theorem sourceEmbedding_square (w : GivenTargetWindow f x e V) :
    (sourceEmbedding w).map ≫ f.hom.left =
      (coordinateIso w.target w.rank w.window).hom.hom.left ≫ (windowFirst w.target w.rank w.window).hom.left :=
  (Category.assoc _ _ _).trans
    (congrArg (fun a => (coordinateIso w.target w.rank w.window).hom.hom.left ≫ a.hom.left) w.square)

end GivenTargetWindow
end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductEmbedding

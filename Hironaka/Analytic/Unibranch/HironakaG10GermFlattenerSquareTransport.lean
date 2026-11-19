import Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
import Hironaka.Resolution.HironakaG10FlatFamilyEquivTransport

/-! # Whole-fibre flattener transport through an isomorphic stalk square -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport

open Hironaka HironakaG10HirFlatQuotient
  HironakaG10FlatFamilyEquivTransport
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

noncomputable section

variable {X Y X' Y' : SourceReducedComplexSpace}

/-- A whole-fibre germ flattener transports across a commutative square
when the base stalk map and all new fibre target stalk maps are isomorphisms,
and the map of actual fibres is onto. -/
theorem isGermFlattenerAt_of_isomorphic_square
    (f : Y ⟶ X) (σ : X' ⟶ X) (p : Y' ⟶ X') (q : Y' ⟶ Y)
    (hsq : p ≫ σ = q ≫ f) (x' : X'.obj.left)
    (hσ : IsIso (σ.hom.left.stalkMap x'))
    (hq : ∀ y' : Y'.obj.left, p.hom.left.base y' = x' → IsIso (q.hom.left.stalkMap y'))
    (hcover : ∀ y : Y.obj.left, f.hom.left.base y = σ.hom.left.base x' →
      ∃ y' : Y'.obj.left, p.hom.left.base y' = x' ∧ q.hom.left.base y' = y)
    (I : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x')))
    (hI : IsGermFlattenerAt f (σ.hom.left.base x') I) :
    IsGermFlattenerAt p x' (I.map (σ.hom.left.stalkMap x').hom) := by
  let H : p.hom.left ≫ σ.hom.left = q.hom.left ≫ f.hom.left :=
    congrArg (fun k => k.hom.left) hsq
  let ι := {y : Y.obj.left // f.hom.left.base y = σ.hom.left.base x'}
  let κ := {y' : Y'.obj.left // p.hom.left.base y' = x'}
  have hpoint (y' : Y'.obj.left) (hy' : p.hom.left.base y' = x') :
      f.hom.left.base (q.hom.left.base y') = σ.hom.left.base x' := by
    have hh := congrArg (fun k => k.base y') H
    change σ.hom.left.base (p.hom.left.base y') = f.hom.left.base (q.hom.left.base y') at hh
    simpa only [hy'] using hh.symm
  let g : κ → ι := fun k => ⟨q.hom.left.base k.val,hpoint k.val k.property⟩
  have hg : Function.Surjective g := by
    rintro ⟨y,hy⟩
    obtain ⟨y',hy',hyy⟩ := hcover y hy
    refine ⟨⟨y',hy'⟩,?_⟩
    exact Subtype.ext hyy
  let : IsIso (σ.hom.left.stalkMap x') := hσ
  let e := (asIso (σ.hom.left.stalkMap x')).commRingCatIsoToRingEquiv
  let d (k : κ) := by
    let : IsIso (q.hom.left.stalkMap k.val) := hq k.val k.property
    exact (asIso (q.hom.left.stalkMap k.val)).commRingCatIsoToRingEquiv
  let φ (i : ι) := fibreStalkMap f (σ.hom.left.base x') i.val i.property
  let ψ (k : κ) := fibreStalkMap p x' k.val k.property
  have hsquare (k : κ) : (ψ k).comp e.toRingHom = (d k).toRingHom.comp (φ (g k)) := by
    rcases k with ⟨y',hy'⟩
    subst hy'
    ext r
    change (p.hom.left.stalkMap y').hom ((σ.hom.left.stalkMap (p.hom.left.base y')).hom r) =
      (q.hom.left.stalkMap y').hom (fibreStalkMap f _ _ (hpoint y' rfl) r)
    have heq : (p.hom.left.stalkMap y').hom ((σ.hom.left.stalkMap (p.hom.left.base y')).hom r) =
        ((p.hom.left ≫ σ.hom.left).stalkMap y').hom r := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    rw [heq, stalkMap_eq_of_eq _ _ H y' (hpoint y' rfl) r, LocallyRingedSpace.stalkMap_comp]
    rfl
  have horig : ∀ J : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x')),
      (∀ i : ι, (quotMap (φ i) J).Flat) ↔ I ≤ J := by
    intro J
    simpa only [φ, ι, Subtype.forall] using hI J
  have hnew := wholeFamilyFlattener_equiv φ ψ g hg e d hsquare I horig
  change ∀ J, (∀ y' hy', (quotMap (fibreStalkMap p x' y' hy') J).Flat) ↔ I.map e.toRingHom ≤ J
  simpa only [ψ, κ, Subtype.forall] using hnew

end

end Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport

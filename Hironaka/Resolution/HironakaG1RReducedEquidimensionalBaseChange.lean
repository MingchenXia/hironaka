import Hironaka.Resolution.HironakaG1RComponentBaseChange
import Hironaka.Resolution.HironakaG1RSmoothLocusPullback
import Hironaka.Resolution.HironakaG1RGeometricallyReduced

/-!
# Reduced equidimensional schemes under field extension

For a cartesian square `IsPullback p fL f (Spec.map (k → L))` (`X_L = X ×_k L`, `L / k` ANY field
extension) with `f` locally of finite type:

* `smoothOfRelativeDimension_smoothLocus_of_isPullback`: if the smooth locus of `X / k` is smooth of
  relative dimension `d`, so is the smooth locus of `X_L / L` (it is the preimage of the smooth locus
  of `X`, `HironakaG1RSmoothLocusPullback.preimage_smoothLocus_of_isPullback`, and relative dimension
  is stable under base change);
* `isReduced_of_isPullback` (`k` perfect): `X` reduced ⇒ `X_L` reduced (lane G1 r3);
* `isReducedEquidimensional_of_isPullback` (`k` perfect): `IsReducedEquidimensional f ⇒
  IsReducedEquidimensional fL`.

`IsReducedEquidimensional f` has VERBATIM the body of the dependency's
`AlgebraicGeometry.Scheme.IsReducedEquidimensional k X` (`deps/hironaka-ep33/Hironaka/Scheme/
Resolution/Defs.lean:99`, the input class of Kollár's Theorem 36) with the structure morphism
`X ↘ Spec k` written as `f`; the dependency's `BR_baseChange_of_class` ASSUMES this property for
`X_L` (lane G1 ALG14 note §3), and this module supplies it from the one for `X`.

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (node `g1r:reduced-equidimensional-base-change`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Hironaka.HironakaG1RReducedEquidimensionalBaseChange

open AlgebraicGeometry HironakaG1RComponentBaseChange HironakaG1RSmoothLocusPullback
open HironakaG1RGeometricallyReduced

universe u

/-- Reduced, with smooth locus smooth of a single relative dimension (verbatim body of the
dependency's `Scheme.IsReducedEquidimensional k X`, structure morphism `f`). -/
def IsReducedEquidimensional {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : Prop :=
  IsReduced X ∧ ∃ d : ℕ, SmoothOfRelativeDimension d (f.smoothLocus.ι ≫ f)

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X XL : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)} {p : XL ⟶ X}

/-- **The relative dimension of the smooth locus is invariant under field extension.** -/
theorem smoothOfRelativeDimension_smoothLocus_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [LocallyOfFiniteType fL] {d : ℕ}
    (hd : SmoothOfRelativeDimension d (f.smoothLocus.ι ≫ f)) :
    SmoothOfRelativeDimension d (fL.smoothLocus.ι ≫ fL) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have e : p ⁻¹ᵁ f.smoothLocus = fL.smoothLocus := preimage_smoothLocus_of_isPullback h
  have h₁ : IsPullback (p ∣_ f.smoothLocus) ((p ⁻¹ᵁ f.smoothLocus).ι ≫ fL)
      (f.smoothLocus.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (isPullback_morphismRestrict p f.smoothLocus).paste_vert h
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have key : SmoothOfRelativeDimension d ((p ⁻¹ᵁ f.smoothLocus).ι ≫ fL) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h₁ hd
  rw [← Scheme.isoOfEq_inv_ι XL e, Category.assoc]
  have h0 := smoothOfRelativeDimension_comp (n := 0) (m := d) (XL.isoOfEq e).inv
    ((p ⁻¹ᵁ f.smoothLocus).ι ≫ fL)
  rwa [zero_add] at h0

/-- **Reducedness under field extension** (`k` perfect). -/
theorem isReduced_of_isPullback [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) [IsReduced X] :
    IsReduced XL := by
  have := isReduced_pullback_of_perfectField f L
  exact isReduced_of_isOpenImmersion h.isoPullback.hom

/-- **Reduced equidimensional schemes stay reduced equidimensional under field extension**
(`k` perfect, `L / k` any field extension). -/
theorem isReducedEquidimensional_of_isPullback [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [LocallyOfFiniteType fL] (hX : IsReducedEquidimensional f) :
    IsReducedEquidimensional fL := by
  obtain ⟨hred, d, hd⟩ := hX
  exact ⟨isReduced_of_isPullback h, d, smoothOfRelativeDimension_smoothLocus_of_isPullback h hd⟩

end Hironaka.HironakaG1RReducedEquidimensionalBaseChange

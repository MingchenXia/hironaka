import DeJongAlterations.Geometry.CurveFibrationBaseChangeTopology
import DeJongAlterations.Geometry.CurveFibrationBaseChangeGenericFiber
import DeJongAlterations.Geometry.GenericSmoothness
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Whole pullback irreducibility and its actual reduction

The original smooth locus is retained on every actual field-valued fibre.
Neither whole irreducibility nor a dominating component is supplied as input.
The reduction is the native reduced induced subscheme of the whole pullback.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y : Scheme.{u}}

/-- The inverse image of the original smooth locus is genuinely smooth over the new base. -/
theorem smooth_originalLocus (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ S) :
    Smooth (((pullback.fst f g) ⁻¹ᵁ f.smoothLocus).ι ≫ pullback.snd f g) := by
  have H := (isPullback_morphismRestrict (pullback.fst f g) f.smoothLocus).paste_vert
    (IsPullback.of_hasPullback f g)
  exact MorphismProperty.of_isPullback H (GenericSmoothness.smooth_smoothLocus f)

/-- Actual Cartesian transport of density from an original field-valued fibre. -/
theorem dense_originalLocus_of_isPullback (f : X ⟶ S) [LocallyOfFinitePresentation f]
    {K : Type u} [Field K] (e : Spec (.of K) ⟶ S)
    (h : Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    {Q : Scheme.{u}} (a : Q ⟶ X) (b : Q ⟶ Spec (.of K))
    (H : IsPullback a b f e) : Dense (a ⁻¹' (f.smoothLocus : Set X)) := by
  have hd := h.preimage H.isoPullback.hom.isOpenMap
  convert hd using 1
  ext z
  change a z ∈ f.smoothLocus ↔
    (H.isoPullback.hom ≫ pullback.fst f e) z ∈ f.smoothLocus
  rw [H.isoPullback_hom_fst]

/-- The same original smooth open is dense on every native fibre of the new projection. -/
theorem dense_originalLocus_fiberwise (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (g : Y ⟶ S) (y : Y) :
    Dense (((pullback.snd f g).fiberι y) ⁻¹'
      (((pullback.fst f g) ⁻¹ᵁ f.smoothLocus) : Set (pullback f g : Scheme.{u}))) := by
  let p := pullback.snd f g
  let e := Y.fromSpecResidueField y ≫ g
  exact dense_originalLocus_of_isPullback f e (hsm _ e)
    (p.fiberι y ≫ pullback.fst f g) (p.fiberToSpecResidueField y)
    ((IsPullback.of_hasPullback p (Y.fromSpecResidueField y)).paste_horiz
      (IsPullback.of_hasPullback f g))

/-- The whole native pullback is irreducible under the original fibrewise smooth-density hypothesis. -/
theorem pullback_irreducibleSpace [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (g : Y ⟶ S) [IsDominant g] : IrreducibleSpace (pullback f g : Scheme.{u}) := by
  let : IsIntegral ((pullback.snd f g).fiber (genericPoint Y)) :=
    genericFiber_isIntegral f hη g
  let U := (pullback.fst f g) ⁻¹ᵁ f.smoothLocus
  let : Smooth (U.ι ≫ pullback.snd f g) := smooth_originalLocus f g
  exact irreducibleSpace_of_open_locus (pullback.snd f g) U
    (U.ι ≫ pullback.snd f g).isOpenMap (dense_originalLocus_fiberwise f hsm g)

/-- The actual reduction: the native reduced induced structure on the whole original pullback. -/
abbrev reducedPullback (f : X ⟶ S) (g : Y ⟶ S) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds (pullback f g : Scheme.{u}))).subscheme

/-- The actual original reduction map, with no replacement Cartesian object. -/
abbrev reductionι (f : X ⟶ S) (g : Y ⟶ S) : reducedPullback f g ⟶ pullback f g :=
  (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds (pullback f g : Scheme.{u}))).subschemeι

/-- The actual reduction of the whole pullback is integral. -/
theorem reducedPullback_isIntegral [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (g : Y ⟶ S) [IsDominant g] : IsIntegral (reducedPullback f g) := by
  let : IrreducibleSpace (pullback f g : Scheme.{u}) := pullback_irreducibleSpace f hη hsm g
  let : IrreducibleSpace (reducedPullback f g) :=
    Subtype.irreducibleSpace (by simpa using
      (IrreducibleSpace.isIrreducible_univ (pullback f g : Scheme.{u})))
  let : IsReduced (reducedPullback f g) :=
    ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme ⊤
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Both actual Cartesian projections retain their literal triangle after the actual reduction. -/
theorem reductionι_triangle (f : X ⟶ S) (g : Y ⟶ S) :
    (reductionι f g ≫ pullback.fst f g) ≫ f =
      (reductionι f g ≫ pullback.snd f g) ≫ g := by
  simp only [Category.assoc, pullback.condition]

end DeJongAlterations.Geometry.CurveFibrationBaseChange

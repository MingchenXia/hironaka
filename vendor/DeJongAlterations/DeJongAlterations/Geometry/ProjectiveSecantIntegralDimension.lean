import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension
import DeJongAlterations.Geometry.FiberDimensionGenericFinite
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Actual integral scalar projections and original dimension bounds

The whole original schemes, their nilpotents, and their actual native
pullback are retained. No reducedness or scalar dimension input is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integral incomparability on the actual affine pullback cover bounds the entire original source. -/
theorem topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegralHom f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  let 𝒰 : X.OpenCover := Y.affineCover.pullback₁ f
  have hchart (a : 𝒰.I₀) : topologicalKrullDim (𝒰.X a) ≤ topologicalKrullDim Y := by
    let g := Y.affineCover.pullbackHom f a
    have : IsIntegralHom g := by
      change IsIntegralHom (pullback.snd f (Y.affineCover.f a))
      infer_instance
    have : IsAffine (𝒰.X a) := isAffine_of_isAffineHom g
    have hint := Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral
      g.appTop.hom (g.isIntegral_app ⊤ (isAffineOpen_top _))
    have htarget := (Y.affineCover.f a).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [FiberDimensionGenericFinite.topologicalKrullDim_eq_ringKrullDim_of_isAffine] at htarget ⊢
    exact hint.trans htarget
  change Order.krullDim (IrreducibleCloseds X) ≤ topologicalKrullDim Y
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨a, y, rfl⟩ := 𝒰.exists_eq x
  rw [coheight_eq_of_isOpenImmersion (𝒰.f a)]
  have ho : Order.krullDim (𝒰.X a) ≤ topologicalKrullDim Y := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := 𝒰.X a))]
    exact hchart a
  exact (Order.coheight_le_krullDim y).trans ho

/-- The original algebraic coefficient map internally makes its actual scalar projection integral. -/
theorem algebraicScalarProjection_isIntegralHom
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    IsIntegralHom (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  infer_instance

/-- Every actual algebraic field base change preserves the original whole-source dimension bound. -/
theorem topologicalKrullDim_algebraicScalar_le
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}) ≤
      topologicalKrullDim X := by
  have := algebraicScalarProjection_isIntegralHom k L p
  exact topologicalKrullDim_le_of_isIntegralHom
    (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

end DeJongAlterations.Geometry.ProjectiveSecant

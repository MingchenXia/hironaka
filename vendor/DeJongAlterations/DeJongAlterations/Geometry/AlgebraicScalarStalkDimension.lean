/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Algebra.AffinePrimeDimensionMaximal
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Original stalk dimension under actual algebraic scalar extension

Only the local-dimension prerequisite of strict SNC descent is proved.
The actual split boundary component family is a separate construction.
Blueprint: `algebraic-scalar-stalk-dimension.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicScalarStalkDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual flat integral geometry preserves the dimension of every original
stalk; affine charts, original contracted primes and their heights are internal. -/
theorem ringKrullDim_stalk_eq_of_flat_integral {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [Flat f] [IsIntegralHom f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f x) (U := (⊤ : Y.Opens)) trivial
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(Y, U)
  let A := Γ(X, V)
  let : Algebra R A := (f.app U).hom.toAlgebra
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : Algebra.IsIntegral R A := ⟨f.isIntegral_app U hU⟩
  have hφ : f.appLE U V (show V ≤ f ⁻¹ᵁ U from le_rfl) = f.app U := by
    change f.app U ≫ X.presheaf.map (𝟙 _).op = f.app U
    simp
  let : Module.Flat R A := by
    have h := f.flat_appLE hU hV (show V ≤ f ⁻¹ᵁ U from le_rfl)
    rw [hφ] at h
    exact h
  let P := (hV.primeIdealOf ⟨x, hxU⟩).asIdeal
  let p := (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal
  have hcontract : P.under R = p := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hxU
    rw [hφ] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hheight : P.height = p.height := by
    rw [← hcontract]
    exact Algebra.AffinePrimeDimension.height_eq_under_of_isIntegral_of_hasGoingDown P
  let := X.presheaf.algebra_section_stalk ⟨x, (show x ∈ V from hxU)⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p := hU.isLocalization_stalk ⟨f x, hxU⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk x),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Y.presheaf.stalk (f x)), hheight]

/-- The SAME algebraic-field Cartesian square supplies the flat integral
projection internally, retaining the original point and coefficient maps. -/
theorem ringKrullDim_stalk_eq_of_algebraic_isPullback
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} {pX : X ⟶ Spec (.of L)} {pY : Y ⟶ Spec (.of k)}
    (H : IsPullback f pX pY (Spec.map (CommRingCat.ofHom (algebraMap k L)))) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : IsIntegralHom c := IsIntegralHom.SpecMap_iff.mpr
    (show (algebraMap k L).IsIntegral from fun z => Algebra.IsIntegral.isIntegral z)
  let : Flat c := inferInstance
  let : IsIntegralHom f := MorphismProperty.of_isPullback H.flip inferInstance
  let : Flat f := MorphismProperty.of_isPullback H.flip inferInstance
  exact ringKrullDim_stalk_eq_of_flat_integral f x

end DeJongAlterations.Geometry.AlgebraicScalarStalkDimension

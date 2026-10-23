import DeJongAlterations.Geometry.BlowupCartier
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Cartier pullback along dominant morphisms of integral schemes

The full native ideal pullback has the actual nonzero affine Cartier equation.
No flatness, finite type or Noetherianity hypothesis is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CartierDominantPullback

open SpecIdealSheaf

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- The full actual ideal pullback on an affine source chart. -/
theorem affine_comap_eq (f : X ⟶ Y) (D : Y.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    (D.comap f).comap U.2.fromSpec =
      specIdealSheaf Γ(X, U.1) ((D.ideal V).map (f.appLE V.1 U.1 hUV).hom) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 hUV,
    Scheme.IdealSheafData.comap_comp, BlowupCartier.comap_fromSpec]
  exact specIdealSheaf_comap (f.appLE V.1 U.1 hUV).hom (D.ideal V)

/-- Actual section pullback is injective on every nonempty affine source chart. -/
theorem appLE_injective (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hU : Nonempty U.1) :
    Function.Injective (f.appLE V.1 U.1 hUV).hom := by
  let : Nonempty U.1 := hU
  let : Nonempty V.1 :=
    ⟨⟨f (Classical.choice hU).val, hUV (Classical.choice hU).property⟩⟩
  let : IsDominant U.1.ι :=
    Opens.isDominant_ι (U.1.isOpen.dense ⟨_, (Classical.choice hU).property⟩)
  let : IsDominant U.2.fromSpec := by
    change IsDominant (U.2.isoSpec.inv ≫ U.1.ι)
    infer_instance
  let g := Spec.map (f.appLE V.1 U.1 hUV)
  have hcomp : IsDominant (g ≫ V.2.fromSpec) := by
    dsimp only [g]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 hUV]
    infer_instance
  let : IsDominant (g ≫ V.2.fromSpec) := hcomp
  have hg : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g V.2.fromSpec
  have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (f.appLE V.1 U.1 hUV).hom).mp hg.denseRange
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro a ha
  exact isNilpotent_iff_eq_zero.mp (hk ha)

/-- Dominant pullback between integral schemes preserves the full Cartier ideal. -/
theorem isEffectiveCartierDivisor_comap (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (D : Y.IdealSheafData) (hD : IsEffectiveCartierDivisor D) :
    IsEffectiveCartierDivisor (D.comap f) := by
  intro x
  obtain ⟨V, hxV, t, ht, hDt⟩ := hD (f x)
  obtain ⟨U, hUa, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ V.1) hxV
  let Ua : X.affineOpens := ⟨U, hUa⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty V.1 := ⟨⟨f x, hxV⟩⟩
  have ht0 : t ≠ 0 := by
    intro h
    exact zero_ne_one (ht.left (by simp [h]))
  have ht' : (f.appLE V.1 U hUV).hom t ≠ 0 := by
    intro h
    exact ht0 (appLE_injective f Ua V hUV inferInstance (by simpa using h))
  have hc : IsEffectiveCartierDivisor ((D.comap f).comap hUa.fromSpec) := by
    rw [affine_comap_eq f D Ua V hUV, hDt, Ideal.map_span, Set.image_singleton]
    exact isEffectiveCartierDivisor_specIdealSheaf_span _ (IsRegular.of_ne_zero ht')
  have H := CartierLocality.exists_affine_neighborhood_of_isOpenImmersion
    hUa.fromSpec (D.comap f) hc (hUa.primeIdealOf ⟨x, hxU⟩)
  simpa only [IsAffineOpen.fromSpec_primeIdealOf] using H

end DeJongAlterations.Geometry.CartierDominantPullback

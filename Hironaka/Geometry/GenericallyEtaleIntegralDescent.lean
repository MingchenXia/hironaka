import Hironaka.Geometry.IntegralDenseOpenDescent
import Hironaka.Geometry.GenericallyEtaleComposition
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Actual generic etaleness descends along integral flat covers
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.GenericallyEtaleIntegralDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native generic etaleness descends on the SAME original Cartesian square. -/
theorem of_isPullback {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (H : IsPullback a f' f b) [Surjective b] [Flat b] [IsIntegralHom b]
    [TopologicalSpace.NoetherianSpace X'] (hf' : IsGenericallyEtale f') :
    IsGenericallyEtale f := by
  let : IsIntegralHom a := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨U, hU, hEt⟩ := hf'
  let := hEt
  let V := IntegralDenseOpenDescent.descendedOpen a U
  have hV := IntegralDenseOpenDescent.descendedOpen_dense a U hU
  have hle : a ⁻¹ᵁ V ≤ U := IntegralDenseOpenDescent.preimage_descendedOpen_le a U
  let : Etale ((a ⁻¹ᵁ V).ι ≫ f') := by
    have he : (a ⁻¹ᵁ V).ι ≫ f' = X'.homOfLE hle ≫ (U.ι ≫ f') := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [he]
    infer_instance
  have hs := (isPullback_morphismRestrict a V).paste_vert H
  have hdown : Etale (V.ι ≫ f) := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hs.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨V, hV, hdown⟩

/-- The SAME original native pullback needs no comparison or descended-property certificate. -/
theorem of_pullback {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y' ⟶ Y)
    [Surjective b] [Flat b] [IsIntegralHom b]
    [TopologicalSpace.NoetherianSpace (pullback f b : Scheme.{u})]
    (hf' : IsGenericallyEtale (pullback.snd f b)) : IsGenericallyEtale f :=
  of_isPullback (IsPullback.of_hasPullback f b) hf'

end Hironaka.Geometry.GenericallyEtaleIntegralDescent

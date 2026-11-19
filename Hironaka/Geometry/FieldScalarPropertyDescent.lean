import Hironaka.Geometry.GenericallyEtaleIntegralDescent
import Hironaka.Geometry.BirationalIntegralDescent
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual algebraic field scalar squares descend their original generic properties
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FieldScalarPropertyDescent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (L K : Type u) [Field L] [Field K] [Algebra L K] [Algebra.IsAlgebraic L K]

/-- The SAME actual field scalar cover is surjective, flat and integral. -/
theorem scalarCover_properties {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L)) :
    let b := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap L K)))
    Surjective b ∧ Flat b ∧ IsIntegralHom b := by
  let : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap L K))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

omit [Algebra.IsAlgebraic L K] in
/-- ORIGINAL finite-type source geometry internally proves Noetherianity of the SAME actual scalar source. -/
theorem scalarSource_noetherian {X X' Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of L)) [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    {a : X' ⟶ X}
    {f' : X' ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap L K)))}
    (H : IsPullback a f' f (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap L K))))) :
    IsNoetherian X' := by
  have hs := H.paste_vert (IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (algebraMap L K))))
  let q := f' ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap L K)))
  let : LocallyOfFiniteType q := MorphismProperty.of_isPullback hs inferInstance
  let : QuasiCompact q := MorphismProperty.of_isPullback hs inferInstance
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace q
  exact ⟨⟩

/-- Native generic etaleness descends to the SAME original map, with scalar hypotheses proved internally. -/
theorem genericallyEtale_of_isPullback {X X' Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of L)) [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    {a : X' ⟶ X}
    {f' : X' ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap L K)))}
    (H : IsPullback a f' f (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap L K)))))
    (hf' : IsGenericallyEtale f') : IsGenericallyEtale f := by
  obtain ⟨hs, hfl, hint⟩ := scalarCover_properties L K p
  let := hs
  let := hfl
  let := hint
  let := scalarSource_noetherian L K f p H
  exact GenericallyEtaleIntegralDescent.of_isPullback H hf'

/-- Native birationality onto the ENTIRE actual target descends on the SAME original scalar square. -/
theorem birationalOver_of_isPullback {X X' Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of L)) [LocallyOfFiniteType (f ≫ p)] [QuasiCompact (f ≫ p)]
    {a : X' ⟶ X}
    {f' : X' ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap L K)))}
    (H : IsPullback a f' f (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap L K)))))
    (hf' : Scheme.BirationalOver f' (𝟙 _)) : Scheme.BirationalOver f (𝟙 Y) := by
  obtain ⟨hs, hfl, hint⟩ := scalarCover_properties L K p
  let := hs
  let := hfl
  let := hint
  let := scalarSource_noetherian L K f p H
  exact BirationalIntegralDescent.of_isPullback H hf'

end Hironaka.Geometry.FieldScalarPropertyDescent

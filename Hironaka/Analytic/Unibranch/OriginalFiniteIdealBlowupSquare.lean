import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal
import Hironaka.Resolution.HironakaNativePulledIdealFiniteType
import Hironaka.Resolution.HironakaNativePulledIdealComposition

/-! The canonical full ORIGINAL square for ordinary finite-type image-ideal
blowups. The SAME pulled ideal's finite type and own target rank-one data
are derived internally, then the actual full UP gives the unique induced
map. Its properness is derived when the original F is proper.
Blueprint FIRST: original-finite-ideal-blowup-square.tex. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupSquare

open Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealFiniteType
  HironakaNativePulledIdealComposition SourceReducedComplexSpace
  OriginalFiniteIdealGeometricBlowup

noncomputable section

private def transportLocalGeneratorsData {T : TopCat.{0}} (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    {M N : SheafOfModules.{0} R}
    (e : M ≅ N) (q : M.LocalGeneratorsData.{0}) : N.LocalGeneratorsData.{0} where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (e.hom.over (q.X i))

private theorem transportLocalGeneratorsData_isLocallyFreeData {T : TopCat.{0}} (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    {M N : SheafOfModules.{0} R}
    (e : M ≅ N) (q : M.LocalGeneratorsData.{0}) [q.IsLocallyFreeData] :
    (transportLocalGeneratorsData R e q).IsLocallyFreeData := by
  constructor
  intro i
  let f := e.hom.over (q.X i)
  let hq : IsIso (q.generators i).π :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
  let he : IsIso f :=
    inferInstanceAs (IsIso ((SheafOfModules.overFunctor R (q.X i)).map e.hom))
  have hf : IsIso ((q.generators i).π ≫ f) := inferInstance
  exact (SheafOfModules.GeneratingSections.ofEpi_π (q.generators i) f).symm ▸ hf

private theorem transportRankOneData {T : TopCat.{0}}
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    {M N : SheafOfModules.{0} R} (e : M ≅ N)
    (h : ∃ q : M.LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I)) :
    ∃ q : N.LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  obtain ⟨q,hq,huniq⟩ := h
  let := hq
  refine ⟨transportLocalGeneratorsData R e q,
    transportLocalGeneratorsData_isLocallyFreeData R e q,?_⟩
  intro i
  exact huniq i

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : Y ⟶ X)

local notation "JF" => nativePulledIdealModule F.hom.left B b
local notation "jF" => nativePulledIdealInclusion F.hom.left B b

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  nativePulledIdealModule_isFiniteType F.hom.left B b

/-- The SAME own projection Cartier data are transported through the proved
FULL native composition iso; no composite rank-one data is supplied. -/
theorem composite_ideal_exists_locallyFreeData :
    ∃ q : (nativePulledIdealModule ((projectionMorphism (X := Y) JF jF) ≫ F).hom.left B b).LocalGeneratorsData.{0},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I) := by
  let e := compositionIso F.hom.left (projectionMorphism (X := Y) JF jF).hom.left B b
  let T := (sourceObject (X := Y) JF jF).obj.left.toTopCat
  let R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{0} :=
    forgetRing (sourceObject (X := Y) JF jF).obj.left.toSheafedSpace.sheaf
  exact transportRankOneData (T := T) R e
    (OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_exists_locallyFreeData
      (X := Y) JF jF)

/-- The FULL original UP gives a UNIQUE induced morphism between the SAME
actual finite-ideal geometric blowup objects. -/
theorem exists_unique_induced_morphism :
    ∃! L : sourceObject (X := Y) JF jF ⟶ sourceObject (X := X) B b,
      L ≫ projectionMorphism (X := X) B b = projectionMorphism (X := Y) JF jF ≫ F := by
  obtain ⟨q,hq,huniq⟩ := composite_ideal_exists_locallyFreeData B b F
  let := hq
  let : ∀ i, Unique (q.generators i).I := fun i => Classical.choice (huniq i)
  exact OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    (X := X) B b (sourceObject (X := Y) JF jF) (projectionMorphism (X := Y) JF jF ≫ F) q

/-- The uniquely specified FULL original induced morphism, with original factories. -/
def inducedMorphism : sourceObject (X := Y) JF jF ⟶ sourceObject (X := X) B b :=
  Classical.choose (exists_unique_induced_morphism B b F)

/-- Equality of the FULL original square, including all structure-sheaf maps. -/
theorem inducedMorphism_square :
    inducedMorphism B b F ≫ projectionMorphism (X := X) B b = projectionMorphism (X := Y) JF jF ≫ F :=
  (Classical.choose_spec (exists_unique_induced_morphism B b F)).1

/-- EVERY full original morphism satisfying the SAME square is the induced map. -/
theorem inducedMorphism_unique (L : sourceObject (X := Y) JF jF ⟶ sourceObject (X := X) B b)
    (hL : L ≫ projectionMorphism (X := X) B b = projectionMorphism (X := Y) JF jF ≫ F) :
    L = inducedMorphism B b F :=
  (Classical.choose_spec (exists_unique_induced_morphism B b F)).2 L hL

/-- Properness of the ORIGINAL F derives properness of the SAME induced map. -/
theorem inducedMorphism_isProperMap (hF : IsProperMap F.hom.left.base) :
    IsProperMap (inducedMorphism B b F).hom.left.base := by
  let : T2Space (sourceObject (X := X) B b).obj.left.toPresheafedSpace := (sourceObject (X := X) B b).property.1
  have hcomp : IsProperMap ((inducedMorphism B b F ≫ projectionMorphism (X := X) B b).hom.left.base) := by
    rw [inducedMorphism_square B b F]
    exact hF.comp (projection_isProperMap JF jF)
  exact isProperMap_of_comp_of_t2
    (inducedMorphism B b F).hom.left.base.hom.continuous
    (projectionMorphism (X := X) B b).hom.left.base.hom.continuous hcomp

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupSquare

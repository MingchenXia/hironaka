import Hironaka.Geometry.QuotGrassmannPivotLocalPullbackFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Genuine native scheme pullback preserves ORIGINAL local generators

Every actual original generating family is transported on the SAME original
inverse-image cover by the native GeneratingSections.map construction. The
original indices are unchanged. No model-specific free-frame input occurs.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalNativeGeneratorOfIso_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S} (G : M.GeneratingSections) [IsIso G.π] (a : M ≅ N) :
    IsIso (G.ofEpi a.hom).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- Actual native local generating data on the original inverse-image cover, preserving ALL original indices. -/
def originalPullbackLocalGeneratorsData {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) :
    SheafOfModules.LocalGeneratorsData.{v} ((Scheme.Modules.pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := by
    have hc := q.coversTop
    rw [_root_.Opens.coversTop_iff] at hc ⊢
    calc
      (⨆ i, f ⁻¹ᵁ q.X i) = (TopologicalSpace.Opens.map f.base).obj (⨆ i, q.X i) :=
        (TopologicalSpace.Opens.map_iSup f.base q.X).symm
      _ = (TopologicalSpace.Opens.map f.base).obj ⊤ :=
        congrArg (TopologicalSpace.Opens.map f.base).obj hc
      _ = ⊤ := rfl
  generators i := ((q.generators i).map (originalLocalModulePullbackFunctor f (q.X i))
    (originalLocalModulePullbackUnitIso f (q.X i)).symm).ofEpi
      ((originalLocalModulePullbackNatIso f (q.X i)).app M).hom

/-- The actual original cover index is unchanged by native pullback. -/
theorem originalPullbackLocalGeneratorsData_coverIndex {X Y : Scheme.{u}}
    (f : Y ⟶ X) {M : X.Modules} (q : SheafOfModules.LocalGeneratorsData.{v} M) :
    (originalPullbackLocalGeneratorsData f q).I = q.I := rfl

/-- Every actual original generator index is unchanged by genuine native pullback. -/
theorem originalPullbackLocalGeneratorsData_generatorIndex {X Y : Scheme.{u}}
    (f : Y ⟶ X) {M : X.Modules} (q : SheafOfModules.LocalGeneratorsData.{v} M) (i : q.I) :
    ((originalPullbackLocalGeneratorsData f q).generators i).I = (q.generators i).I := rfl

/-- Actual native pullback preserves finite original generating families. -/
instance originalPullbackLocalGeneratorsData_isFiniteType {X Y : Scheme.{u}}
    (f : Y ⟶ X) {M : X.Modules} (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsFiniteType] :
    (originalPullbackLocalGeneratorsData f q).IsFiniteType where
  isFiniteType i := by
    have : (q.generators i).IsFiniteType :=
      SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
    change (((q.generators i).map (originalLocalModulePullbackFunctor f (q.X i))
      (originalLocalModulePullbackUnitIso f (q.X i)).symm).ofEpi
        ((originalLocalModulePullbackNatIso f (q.X i)).app M).hom).IsFiniteType
    infer_instance

/-- Actual native pullback preserves the ORIGINAL locally free generating isomorphisms. -/
instance originalPullbackLocalGeneratorsData_isLocallyFreeData {X Y : Scheme.{u}}
    (f : Y ⟶ X) {M : X.Modules} (q : SheafOfModules.LocalGeneratorsData.{v} M)
    [q.IsLocallyFreeData] : (originalPullbackLocalGeneratorsData f q).IsLocallyFreeData where
  isIso i := by
    let G := (q.generators i).map (originalLocalModulePullbackFunctor f (q.X i))
      (originalLocalModulePullbackUnitIso f (q.X i)).symm
    let a := (originalLocalModulePullbackNatIso f (q.X i)).app M
    have : IsIso G.π := inferInstance
    have hgen : (originalPullbackLocalGeneratorsData f q).generators i = G.ofEpi a.hom := rfl
    have hiso : IsIso (G.ofEpi a.hom).π := originalNativeGeneratorOfIso_isIso G a
    exact (congrArg (fun σ => IsIso σ.π) hgen).mpr hiso

/-- Genuine native Scheme.Modules.pullback preserves native local freeness for EVERY actual scheme and module sheaf. -/
theorem originalSchemePullback_isLocallyFree {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsLocallyFree] : ((Scheme.Modules.pullback f).obj M).IsLocallyFree := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  let := hq
  exact (originalPullbackLocalGeneratorsData f q).isLocallyFree

/-- Genuine native Scheme.Modules.pullback preserves native finite type for EVERY actual scheme and module sheaf. -/
theorem originalSchemePullback_isFiniteType {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFiniteType] : ((Scheme.Modules.pullback f).obj M).IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let := hq
  constructor
  exact ⟨originalPullbackLocalGeneratorsData f q, inferInstance⟩

end Hironaka.Geometry.QuotGrassmann

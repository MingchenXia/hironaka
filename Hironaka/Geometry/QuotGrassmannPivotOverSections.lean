import Hironaka.Geometry.QuotGrassmannPivotOverFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual original over-site finite-free section bases and native module rank

The actual finite-free section equivalence follows the pure finite biproduct
calculation in EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean,
source SHA256 a8dc9bd99f712c3e5e4dbbd0ed5237f8e205ec957695689df4147c3ceed00d7d. All maps here are actual native evaluation
and finite-product comparisons. No basis or rank output is supplied as input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original terminal-open sections of the actual native finite-free over-site sheaf
are the SAME original finite function module, through actual native comparisons. -/
def originalOverFreeSectionsIso (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Finite I] :
    (SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (originalOverTop X U))).obj
      (SheafOfModules.free (R := X.ringCatSheaf.over U) I) ≅
        ModuleCat.of Γ(X, U) (I → Γ(X, U)) := by
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (originalOverTop X U))
  let T := fun (_ : I) => SheafOfModules.unit (X.ringCatSheaf.over U)
  let : HasBiproduct T := HasBiproduct.of_hasCoproduct T
  let : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  let : PreservesLimit (Discrete.functor T) F := by
    dsimp [F]
    infer_instance
  let : PreservesBiproduct T F := preservesBiproduct_of_preservesProduct F
  exact F.mapIso (biproduct.isoCoproduct T).symm ≪≫
    F.mapBiproduct T ≪≫ biproduct.isoProduct (F.obj ∘ T) ≪≫ ModuleCat.piIsoPi (F.obj ∘ T)

/-- The actual original finite-free over-site section module has the exact native local rank. -/
theorem originalOverFreeSections_rankAtStalk (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) [Fintype I] :
    Module.rankAtStalk (R := Γ(X, U))
      ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (originalOverTop X U))).obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I)) =
      fun (_ : PrimeSpectrum Γ(X, U)) => Fintype.card I := by
  let e := (originalOverFreeSectionsIso X U I).toLinearEquiv
  funext p
  let := p.nontrivial
  calc
    _ = Module.rankAtStalk (R := Γ(X, U)) (I → Γ(X, U)) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv (R := Γ(X, U)) e) p
    _ = Module.finrank Γ(X, U) (I → Γ(X, U)) :=
      congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Γ(X, U)) (M := I → Γ(X, U))) p
    _ = Fintype.card I := Module.finrank_fintype_fun_eq_card Γ(X, U)

end Hironaka.Geometry.QuotGrassmann

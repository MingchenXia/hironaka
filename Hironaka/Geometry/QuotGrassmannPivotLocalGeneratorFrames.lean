import Hironaka.Geometry.QuotGrassmannPivotOverRestriction
import Hironaka.Geometry.QuotGrassmannPivotOverSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Actual original local generating isomorphisms give actual subopen section frames

The SAME native generating map is inverted, restricted by the original native
over-map, and evaluated at the SAME original terminal open. All finite free
section frames are constructed internally and retain original generator indices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual native restriction of an ORIGINAL generating isomorphism to an original subopen. -/
def originalLocalGeneratorSubopenFrame {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) :
    M.over V ≅ SheafOfModules.free (R := X.ringCatSheaf.over V) (q.generators i).I :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hV)).app M).symm ≪≫
    (SheafOfModules.overMap.{u} X.ringCatSheaf (homOfLE hV)).mapIso
      (asIso (q.generators i).π).symm ≪≫
    (originalOverMapFreeIso X (homOfLE hV) (q.generators i).I).symm

/-- SAME original finite generator indices yield actual native subopen section bases. -/
def originalLocalGeneratorSubopenSectionsIso {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) :
    ModuleCat.of Γ(X, V) Γ(M, V) ≅
      ModuleCat.of Γ(X, V) ((q.generators i).I → Γ(X, V)) := by
  let : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over V)
      (.op (originalOverTop X V))).mapIso (originalLocalGeneratorSubopenFrame q i V hV) ≪≫
    originalOverFreeSectionsIso X V (q.generators i).I

/-- The actual original subopen section module is finite over its actual native section ring. -/
theorem originalLocalGeneratorSubopenSections_finite {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) : Module.Finite Γ(X, V) Γ(M, V) := by
  let : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  exact Module.Finite.equiv (originalLocalGeneratorSubopenSectionsIso q i V hV).symm.toLinearEquiv

/-- The actual original subopen section module is free, by its produced original native section frame. -/
theorem originalLocalGeneratorSubopenSections_free {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) : Module.Free Γ(X, V) Γ(M, V) := by
  let : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  exact Module.Free.of_equiv (originalLocalGeneratorSubopenSectionsIso q i V hV).symm.toLinearEquiv

/-- Genuine native projectivity of SAME original sections follows from the internally produced native frame. -/
theorem originalLocalGeneratorSubopenSections_projective {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) : Module.Projective Γ(X, V) Γ(M, V) := by
  let := originalLocalGeneratorSubopenSections_free q i V hV
  exact Module.Projective.of_free

/-- At EVERY actual original prime, the produced section frame has its exact original finite generator rank. -/
theorem originalLocalGeneratorSubopenSections_rankAtStalk {X : Scheme.{u}} {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{v} M) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (V : X.Opens) (hV : V ≤ q.X i) (p : PrimeSpectrum Γ(X, V)) :
    Module.rankAtStalk (R := Γ(X, V)) Γ(M, V) p = Nat.card (q.generators i).I := by
  let : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  let : Fintype (q.generators i).I := Fintype.ofFinite _
  let := p.nontrivial
  calc
    _ = Module.rankAtStalk (R := Γ(X, V)) ((q.generators i).I → Γ(X, V)) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv (R := Γ(X, V))
        (originalLocalGeneratorSubopenSectionsIso q i V hV).toLinearEquiv) p
    _ = Module.finrank Γ(X, V) ((q.generators i).I → Γ(X, V)) :=
      congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := Γ(X, V)) (M := (q.generators i).I → Γ(X, V))) p
    _ = Nat.card (q.generators i).I := by
      have hn : Nat.card (q.generators i).I = Fintype.card (q.generators i).I :=
        Nat.card_eq_fintype_card
      exact (Module.finrank_fintype_fun_eq_card Γ(X, V)).trans hn.symm

end Hironaka.Geometry.QuotGrassmann

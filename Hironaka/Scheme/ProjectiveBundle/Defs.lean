/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.ProjectiveBundle.Functor.Defs
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Hironaka.Scheme.ProjectiveBundle.Equifibered

/-!
# The projective bundle of a quasi-coherent sheaf, and projective morphisms

For a quasi-coherent sheaf of modules `F` on a scheme `X` (Mathlib's `X.Modules` with
`SheafOfModules.IsQuasicoherent`), **the projective bundle** `P(F) = Proj_X (Sym F)`
[Sta, Tag 01OB] is `F.projectiveBundle`, with structure morphism `F.projectiveBundleπ : P(F) ⟶ X`.
It is glued by the relative gluing lemma [Sta, Tag 01LH] from the projective bundles
`P(Γ(F, U)) = Proj (Sym_{Γ(X, U)} Γ(F, U))` of the modules of sections over the affine opens `U` of
`X` (`projectiveBundleFunctor F`, `projectiveBundleNatTrans F`), whose naturality squares are
pullbacks by quasi-coherence (`projectiveBundleNatTrans_equifibered`), as the blow-up is glued from
the affine blow-ups.

A morphism `f : X ⟶ Y` is **projective** (`AlgebraicGeometry.IsProjective`) [Sta, Tag 01W8] when
`X` is isomorphic over `Y` to a closed subscheme of the projective bundle `P(E)` of a
quasi-coherent `𝒪_Y`-module `E` of finite type: `f` is a closed immersion `X ⟶ P(E)` followed by
`P(E) ⟶ Y`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section ProjectiveBundle

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- The relative gluing datum of the projective bundles over the directed affine cover
[Sta, Tag 01LH]. -/
noncomputable def projectiveBundleGluingData : X.directedAffineCover.RelativeGluingData where
  functor := projectiveBundleFunctor F
  natTrans := projectiveBundleNatTrans F
  equifibered := projectiveBundleNatTrans_equifibered F

/-- **The projective bundle** `P(F) = Proj_X (Sym F)` of a quasi-coherent sheaf of modules `F`
[Sta, Tag 01OB]: glued from the projective bundles `Proj (Sym_{Γ(X, U)} Γ(F, U))` of the modules
of sections over the affine opens `U` of `X`. -/
noncomputable def Scheme.Modules.projectiveBundle : Scheme.{u} :=
  (projectiveBundleGluingData F).glued

/-- The structure morphism `P(F) ⟶ X` of the projective bundle. -/
noncomputable def Scheme.Modules.projectiveBundleπ : F.projectiveBundle ⟶ X :=
  (projectiveBundleGluingData F).toBase

end ProjectiveBundle

/-- **A projective morphism** [Sta, Tag 01W8]: `f : X ⟶ Y` is projective when `X` is isomorphic
over `Y` to a closed subscheme of the projective bundle `P(E)` of a quasi-coherent `𝒪_Y`-module
`E` of finite type, that is, when `f` factors as a closed immersion `X ⟶ P(E)` followed by the
structure morphism `P(E) ⟶ Y`. A projective morphism is proper
(`AlgebraicGeometry.IsProjective.isProper`).

Relation to the source.
* **Translation.** Kollár's "projective morphism" [Kol07, (2) and (3); Theorem 27] is
  `IsProjective`, Grothendieck's definition as in [Sta, Tag 01W8]: `E` ranges over the
  quasi-coherent `𝒪_Y`-modules of finite type (Mathlib's `SheafOfModules.IsQuasicoherent` and
  `SheafOfModules.IsFiniteType`). Kollár's varieties are quasi-projective, and over a base with an
  ample invertible sheaf this is equivalent to being a closed subscheme of some `ℙⁿ_Y`
  [Sta, Tag 087S]; for a general base the condition with `ℙⁿ_Y` is stronger, and the
  condition on an open cover of `Y` only ("locally projective") is weaker [Sta, Tag 01W8], a
  distinction Kollár draws in [Kol07, Example 28.1]. -/
class IsProjective {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  exists_isClosedImmersion : ∃ (E : Y.Modules) (_ : E.IsQuasicoherent)
    (_ : SheafOfModules.IsFiniteType.{u} E) (i : X ⟶ E.projectiveBundle),
    IsClosedImmersion i ∧ i ≫ E.projectiveBundleπ = f

end AlgebraicGeometry

/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction maps of a sheaf of modules

For a sheaf of `𝒪_X`-modules `F` (Mathlib's `X.Modules`) and opens `U ≤ V`, the restriction
`Γ(F, V) → Γ(F, U)` is semilinear along the restriction of functions `Γ(X, V) → Γ(X, U)`:
`AlgebraicGeometry.Scheme.Modules.restrictionMap`. These are the transition maps of the modules
of sections over the affine opens from which the projective bundle `P(F)` of a quasi-coherent
sheaf is glued [Sta, Tag 01OB].
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- **The restriction map** `Γ(F, V) → Γ(F, U)` of a sheaf of modules, for opens `U ≤ V`, as a map
semilinear along the restriction of functions `Γ(X, V) → Γ(X, U)`. -/
noncomputable def restrictionMap {U V : X.Opens} (h : U ≤ V) :
    Γ(F, V) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(F, U) where
  toFun := F.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := fun r x => F.val.map_smul (homOfLE h).op r x

end AlgebraicGeometry.Scheme.Modules

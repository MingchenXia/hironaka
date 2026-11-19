/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.ProjectiveBundle.Functor.Defs
import Hironaka.Scheme.ProjectiveBundle.Affine.BaseChange
import Hironaka.Scheme.BlowUp.Glue.AffineBlowUpFunctor

/-!
# The projective bundles over the affine opens glue

For a quasi-coherent sheaf `F` and affine opens `U ≤ V` of `X`, the square

```
P(Γ(F, U)) ⟶ U
     |         |
P(Γ(F, V)) ⟶ V
```

is cartesian (`AlgebraicGeometry.projectiveBundleNatTrans_equifibered`), the hypothesis of the
relative gluing lemma [Sta, Tag 01LH]: `Γ(F, U)` is the base change
`Γ(X, U) ⊗_{Γ(X, V)} Γ(F, V)` (`Scheme.Modules.isBaseChange_resₗ`), so the projective bundles
commute with the base change `Spec Γ(X, U) ⟶ Spec Γ(X, V)`
(`affineProjectiveBundle.isPullback_mapHom`), and that square is pasted with the square of
isomorphisms `Spec Γ(X, U) ≅ U`, `Spec Γ(X, V) ≅ V` over `U ⊆ V`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- **The projective bundles over the affine opens glue**: every naturality square of
`projectiveBundleNatTrans F` is a pullback [Sta, Tags 01MX and 01LH]. -/
theorem projectiveBundleNatTrans_equifibered : (projectiveBundleNatTrans F).Equifibered := by
  intro U V h
  have hle : U ≤ V := h.le
  have hle' : (U : X.Opens) ≤ V := hle
  obtain rfl : h = homOfLE hle := (homOfLE_leOfHom h).symm
  change IsPullback (affineProjectiveBundle.mapHom (R := Γ(X, V)) (S := Γ(X, U))
      (X.presheaf.map (homOfLE (X := X.Opens) hle).op) (F.restrictionMap hle)
      (Scheme.Modules.span_range_restrictionMap_eq_top F (affineOpens_isAffineOpen U)
        (affineOpens_isAffineOpen V) hle))
    (affineProjectiveBundle.π Γ(X, U) Γ(F, U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv)
    (affineProjectiveBundle.π Γ(X, V) Γ(F, V) ≫ (affineOpens_isAffineOpen V).isoSpec.inv)
    (X.homOfLE hle')
  exact (affineProjectiveBundle.isPullback_mapHom _ _ _
    (Scheme.Modules.exists_extend_restrictionMap F (affineOpens_isAffineOpen U)
      (affineOpens_isAffineOpen V) hle)).flip.paste_vert
    (IsPullback.of_vert_isIso ⟨specMap_presheaf_map_isoSpec_inv hle⟩)

end AlgebraicGeometry

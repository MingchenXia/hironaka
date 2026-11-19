/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.SmoothAt

/-!
# The `k`-algebra structure on a stalk of a scheme over `Spec k`

For `f : X ⟶ Spec k` and a point `x`, the stalk `𝒪_{X,x}` is a `k`-algebra through
`k ≅ Γ(Spec k, ⊤) → Γ(X, f⁻¹ ⊤) → 𝒪_{X,x}` (`Scheme.Hom.stalkAlgebra`), and for every open
`U ∋ x` this structure is the composite of the `k`-algebra structure on `Γ(X, U)` induced by `f`
(`Scheme.Hom.sectionsAlgebra`) with the germ map `Γ(X, U) → 𝒪_{X,x}`
(`germ_comp_algebraMap_sectionsAlgebra`; the scalar tower `k → Γ(X, U) → 𝒪_{X,x}`). This is the
structure in which the residue field `κ(x)` of the stalk is a `k`-algebra, so that its
transcendence degree over `k` enters the dimension formula of `RegularSmooth/SchemeForms.lean`.
Like `sectionsAlgebra`, it is a definition bound with `letI`, not an instance: it depends on `f`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory

variable {X : Scheme.{u}} {k : Type u} [CommRing k]

/-- The `k`-algebra structure on the stalk `𝒪_{X,x}` induced by `f : X ⟶ Spec k`, through
`k ≅ Γ(Spec k, ⊤) → Γ(X, f⁻¹ ⊤) → 𝒪_{X,x}`. Not an instance: it depends on `f`. -/
@[instance_reducible]
noncomputable def Scheme.Hom.stalkAlgebra (f : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
    X.presheaf.germ (f ⁻¹ᵁ ⊤) x (show f x ∈ (⊤ : (Spec (.of k)).Opens) from trivial)).hom.toAlgebra

theorem Scheme.Hom.algebraMap_stalkAlgebra (f : X ⟶ Spec (.of k)) (x : X) :
    letI := f.stalkAlgebra x
    algebraMap k (X.presheaf.stalk x) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
      X.presheaf.germ (f ⁻¹ᵁ ⊤) x (show f x ∈ (⊤ : (Spec (.of k)).Opens) from trivial)).hom :=
  rfl

/-- Through any open `U ∋ x`, the `k`-algebra structure of `Γ(X, U)` followed by the germ map is
the `k`-algebra structure of the stalk. -/
theorem Scheme.Hom.germ_comp_algebraMap_sectionsAlgebra (f : X ⟶ Spec (.of k)) (U : X.Opens)
    {x : X} (hx : x ∈ U) :
    letI := f.sectionsAlgebra U
    letI := f.stalkAlgebra x
    (X.presheaf.germ U x hx).hom.comp (algebraMap k Γ(X, U)) =
      algebraMap k (X.presheaf.stalk x) := by
  rw [Scheme.Hom.algebraMap_sectionsAlgebra, Scheme.Hom.algebraMap_stalkAlgebra,
    ← CommRingCat.hom_comp]
  congr 1
  change (Scheme.ΓSpecIso (.of k)).inv ≫ (f.app ⊤ ≫ X.presheaf.map (homOfLE _).op) ≫
    X.presheaf.germ U x hx = _
  rw [Category.assoc, TopCat.Presheaf.germ_res]

/-- The scalar tower `k → Γ(X, U) → 𝒪_{X,x}` for the structures induced by `f`. -/
theorem Scheme.Hom.isScalarTower_sectionsAlgebra_stalk (f : X ⟶ Spec (.of k)) (U : X.Opens)
    {x : X} (hx : x ∈ U) :
    letI := f.sectionsAlgebra U
    letI := f.stalkAlgebra x
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
  letI := f.sectionsAlgebra U
  letI := f.stalkAlgebra x
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  IsScalarTower.of_algebraMap_eq' (f.germ_comp_algebraMap_sectionsAlgebra U hx).symm

end AlgebraicGeometry

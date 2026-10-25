/-
Adapted from StacksAndModuli/API/CompletedLocalRing.lean and the three
baseRingHom declarations in StacksAndModuli/API/GlobalSectionsOverBase.lean,
commit b3699d1342bfd3344b69d5299bf4b905c1e40afb.
SHA256 CompletedLocalRing.lean:
2450a0288861066592aaf67a9aaa3a91d6b6a2cd238afd2cfbc2871cce653ac1.
SHA256 GlobalSectionsOverBase.lean:
1e92be1be9cd89a0a473ec210196021aff7cad1b76708a0e1d35ba23b427cac0.
Original Lean code: StacksAndModuli contributors, Apache License 2.0.
Modified for DeJongAlterations: split algebra transport into its own module,
retain only the actual coefficient/stalk/completion bridge, and adapt to
Lean 4.33.1 and local Mathlib. No external imports or dependencies.
The original Apache License 2.0 is reproduced in
DeJongAlterations/Algebra/AdicCompletionTransport.lean.
-/
import DeJongAlterations.Algebra.AdicCompletionTransport
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Native completed local rings with their actual affine-base coefficients -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring map from the base ring to the global functions of a scheme over `Spec R`,
obtained from `f` on global sections together with `Γ(Spec R, ⊤) ≅ R`. -/
noncomputable def baseRingHom (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- The map from the base ring to global functions is compatible with changing the
affine base. -/
@[reassoc]
theorem baseRingHom_comp {S : CommRingCat.{u}} (φ : R ⟶ S)
    (f : X ⟶ Spec S) :
    φ ≫ baseRingHom f = baseRingHom (f ≫ Spec.map φ) := by
  unfold baseRingHom
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, ← Scheme.Hom.comp_appTop]

/-- The map from the base ring to global functions is compatible with
precomposition on the source scheme. -/
@[reassoc]
theorem baseRingHom_comp_appTop {Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec R) :
    baseRingHom p ≫ f.appTop = baseRingHom (f ≫ p) := by
  unfold baseRingHom
  rw [Category.assoc, Scheme.Hom.comp_appTop]


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

/-- The canonical ring map from the base ring to the stalk of a scheme over an affine base. -/
noncomputable def baseToStalk (f : X ⟶ Spec R) (x : X) :
    R ⟶ CommRingCat.of (X.presheaf.stalk x) :=
  Scheme.Modules.baseRingHom f ≫ X.presheaf.germ ⊤ x trivial

/-- The map from the base to a stalk sends an element first to a global function and then to
its germ. -/
@[simp]
theorem baseToStalk_apply (f : X ⟶ Spec R) (x : X) (r : R) :
    baseToStalk f x r = X.presheaf.germ ⊤ x trivial (Scheme.Modules.baseRingHom f r) :=
  rfl

/-- The map from the base ring to a stalk is compatible with changing the affine base. -/
@[reassoc]
theorem baseToStalk_comp {S : CommRingCat.{u}} (g : R ⟶ S)
    (f : X ⟶ Spec S) (x : X) :
    g ≫ baseToStalk f x = baseToStalk (f ≫ Spec.map g) x := by
  unfold baseToStalk
  rw [← Category.assoc, Scheme.Modules.baseRingHom_comp]

/-- The map from the base ring to a stalk is natural in the source scheme. -/
@[reassoc]
theorem baseToStalk_comp_stalkMap (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X) :
    baseToStalk p (g x) ≫ g.stalkMap x = baseToStalk (g ≫ p) x := by
  unfold baseToStalk
  rw [Category.assoc, Scheme.Hom.germ_stalkMap]
  change (Scheme.Modules.baseRingHom p ≫ g.appTop) ≫
    X.presheaf.germ ⊤ x trivial = _
  rw [Scheme.Modules.baseRingHom_comp_appTop]

/-- The stalk of a scheme over `Spec R` is canonically an `R`-algebra.

This is not an instance because it depends on the chosen morphism `f`. -/
@[instance_reducible]
noncomputable def stalkAlgebra (f : X ⟶ Spec R) (x : X) :
    Algebra R (X.presheaf.stalk x) :=
  (baseToStalk f x).hom.toAlgebra

/-- The algebra map for `stalkAlgebra` is `baseToStalk`. -/
@[simp]
theorem algebraMap_stalkAlgebra (f : X ⟶ Spec R) (x : X) (r : R) :
    @algebraMap R (X.presheaf.stalk x) _ _ (stalkAlgebra f x) r = baseToStalk f x r :=
  rfl

/-- A morphism of schemes induces an algebra homomorphism on stalks over any affine base of
its target. -/
noncomputable def Hom.stalkMapAlgHom (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X) :
    letI := stalkAlgebra p (g x)
    letI := stalkAlgebra (g ≫ p) x
    Y.presheaf.stalk (g x) →ₐ[R] X.presheaf.stalk x := by
  letI := stalkAlgebra p (g x)
  letI := stalkAlgebra (g ≫ p) x
  exact
    { (g.stalkMap x).hom with
      commutes' := fun r ↦ by
        change g.stalkMap x (baseToStalk p (g x) r) = baseToStalk (g ≫ p) x r
        exact DFunLike.congr_fun
          (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap g p x)) r }

/-- The underlying function of the algebra homomorphism on stalks is the usual stalk map. -/
@[simp]
theorem Hom.stalkMapAlgHom_apply (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X)
    (a : Y.presheaf.stalk (g x)) :
    g.stalkMapAlgHom p x a = g.stalkMap x a :=
  rfl

/-- An isomorphism of schemes induces an equivalence of the corresponding stalks. -/
noncomputable def stalkRingEquivOfIso (e : X ≅ Y) (x : X) :
    Y.presheaf.stalk (e.hom x) ≃+* X.presheaf.stalk x :=
  (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- The stalk equivalence induced by a scheme isomorphism is the usual stalk map in the
forward direction. -/
@[simp]
theorem stalkRingEquivOfIso_apply (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    stalkRingEquivOfIso e x a = e.hom.stalkMap x a :=
  rfl

/-- An isomorphism of schemes induces an equivalence of stalks as algebras over any affine
base of its target. -/
noncomputable def stalkAlgEquivOfIso (e : X ≅ Y) (p : Y ⟶ Spec R) (x : X) :
    letI := stalkAlgebra p (e.hom x)
    letI := stalkAlgebra (e.hom ≫ p) x
    Y.presheaf.stalk (e.hom x) ≃ₐ[R] X.presheaf.stalk x := by
  letI := stalkAlgebra p (e.hom x)
  letI := stalkAlgebra (e.hom ≫ p) x
  exact AlgEquiv.ofRingEquiv (f := stalkRingEquivOfIso e x) fun r ↦
    (e.hom.stalkMapAlgHom p x).commutes r

/-- The underlying function of the algebra equivalence on stalks is the usual stalk map. -/
@[simp]
theorem stalkAlgEquivOfIso_apply (e : X ≅ Y) (p : Y ⟶ Spec R) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    stalkAlgEquivOfIso e p x a = e.hom.stalkMap x a :=
  rfl

/-- The completed local ring of `X` at `x`, formed with respect to the maximal ideal of the
local ring `𝒪_{X,x}`. -/
abbrev completedLocalRing (X : Scheme.{u}) (x : X) :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The canonical ring map from a stalk to its completed local ring. -/
noncomputable def toCompletedLocalRing (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x →+* X.completedLocalRing x :=
  algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)

/-- The canonical map into a completed local ring is Mathlib's map into the adic
completion. -/
@[simp]
theorem toCompletedLocalRing_apply (X : Scheme.{u}) (x : X) (a : X.presheaf.stalk x) :
    X.toCompletedLocalRing x a =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) a := by
  simp [toCompletedLocalRing, AdicCompletion.algebraMap_apply]

/-- An isomorphism of schemes induces an equivalence of completed local rings. -/
noncomputable def completedLocalRingRingEquivOfIso (e : X ≅ Y) (x : X) :
    Y.completedLocalRing (e.hom x) ≃+* X.completedLocalRing x :=
  AdicCompletion.congrRingEquiv _ _ (stalkRingEquivOfIso e x)
    (IsLocalRing.map_ringEquiv_maximalIdeal (stalkRingEquivOfIso e x)).symm

/-- The equivalence of completed local rings induced by a scheme isomorphism commutes with
the canonical maps from the stalks. -/
@[simp]
theorem completedLocalRingRingEquivOfIso_toCompletedLocalRing (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom x)) :
    completedLocalRingRingEquivOfIso e x (Y.toCompletedLocalRing (e.hom x) a) =
      X.toCompletedLocalRing x (stalkRingEquivOfIso e x a) := by
  rw [toCompletedLocalRing_apply, toCompletedLocalRing_apply]
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ a

/-- The completed local ring of a scheme over `Spec R` is canonically an `R`-algebra.

This is not an instance because it depends on the chosen morphism `f`. -/
@[instance_reducible]
noncomputable def completedLocalRingAlgebra (f : X ⟶ Spec R) (x : X) :
    Algebra R (X.completedLocalRing x) := by
  letI := stalkAlgebra f x
  infer_instance

/-- The algebra map into a completed local ring is the composite of `baseToStalk` and the
canonical completion map. -/
@[simp]
theorem algebraMap_completedLocalRingAlgebra (f : X ⟶ Spec R) (x : X) (r : R) :
    @algebraMap R (X.completedLocalRing x) _ _ (completedLocalRingAlgebra f x) r =
      X.toCompletedLocalRing x (baseToStalk f x r) := by
  rfl

/-- An isomorphism of schemes induces an equivalence of completed local rings as algebras over
any affine base of its target. The source structure morphism is the composite with the
isomorphism. -/
noncomputable def completedLocalRingAlgEquivOfIso (e : X ≅ Y)
    (p : Y ⟶ Spec R) (x : X) :
    letI := completedLocalRingAlgebra p (e.hom x)
    letI := completedLocalRingAlgebra (e.hom ≫ p) x
    Y.completedLocalRing (e.hom x) ≃ₐ[R] X.completedLocalRing x := by
  letI := completedLocalRingAlgebra p (e.hom x)
  letI := completedLocalRingAlgebra (e.hom ≫ p) x
  exact AlgEquiv.ofRingEquiv (f := completedLocalRingRingEquivOfIso e x) fun r ↦ by
    rw [algebraMap_completedLocalRingAlgebra, algebraMap_completedLocalRingAlgebra,
      completedLocalRingRingEquivOfIso_toCompletedLocalRing]
    congr 1
    change e.hom.stalkMap x (baseToStalk p (e.hom x) r) = baseToStalk (e.hom ≫ p) x r
    exact DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap e.hom p x)) r

/-- The algebra equivalence of completed local rings induced by a scheme isomorphism commutes
with the canonical maps from the stalks. -/
@[simp]
theorem completedLocalRingAlgEquivOfIso_toCompletedLocalRing (e : X ≅ Y)
    (p : Y ⟶ Spec R) (x : X) (a : Y.presheaf.stalk (e.hom x)) :
    completedLocalRingAlgEquivOfIso e p x (Y.toCompletedLocalRing (e.hom x) a) =
      X.toCompletedLocalRing x (stalkAlgEquivOfIso e p x a) :=
  completedLocalRingRingEquivOfIso_toCompletedLocalRing e x a

/-- Variant of `completedLocalRingAlgEquivOfIso` for separately named structure morphisms
whose compatibility with the isomorphism is given by an equality. -/
noncomputable def completedLocalRingAlgEquivOfIsoOver (e : X ≅ Y)
    (f : X ⟶ Spec R) (p : Y ⟶ Spec R) (h : e.hom ≫ p = f) (x : X) :
    letI := completedLocalRingAlgebra p (e.hom x)
    letI := completedLocalRingAlgebra f x
    Y.completedLocalRing (e.hom x) ≃ₐ[R] X.completedLocalRing x := by
  subst f
  exact completedLocalRingAlgEquivOfIso e p x

end AlgebraicGeometry.Scheme

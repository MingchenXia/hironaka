import DeJongAlterations.Geometry.CompletedLocalRing

/-!
# Completed local rings under actual open chart maps

Every comparison below is induced by the native stalk map of the actual open
immersion. The coefficient algebras are the actual maps of the supplied
structure morphism; no completion or chart-model certificate is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

/-- The actual stalk isomorphism of an open immersion. -/
def stalkRingEquivOfOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    Y.presheaf.stalk (j x) ≃+* X.presheaf.stalk x :=
  (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv

@[simp]
theorem stalkRingEquivOfOpenImmersion_apply (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (a : Y.presheaf.stalk (j x)) :
    stalkRingEquivOfOpenImmersion j x a = j.stalkMap x a := rfl

/-- An actual open immersion identifies the corresponding native adic completions. -/
def completedLocalRingRingEquivOfOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    Y.completedLocalRing (j x) ≃+* X.completedLocalRing x :=
  AdicCompletion.congrRingEquiv _ _ (stalkRingEquivOfOpenImmersion j x)
    (IsLocalRing.map_ringEquiv_maximalIdeal (stalkRingEquivOfOpenImmersion j x)).symm

@[simp]
theorem completedLocalRingRingEquivOfOpenImmersion_toCompletedLocalRing
    (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (a : Y.presheaf.stalk (j x)) :
    completedLocalRingRingEquivOfOpenImmersion j x (Y.toCompletedLocalRing (j x) a) =
      X.toCompletedLocalRing x (j.stalkMap x a) := by
  rw [toCompletedLocalRing_apply, toCompletedLocalRing_apply]
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ a

/-- The actual open-chart comparison preserves any actual affine base. -/
def completedLocalRingAlgEquivOfOpenImmersion
    (j : X ⟶ Y) [IsOpenImmersion j] (p : Y ⟶ Spec R) (x : X) :
    letI := completedLocalRingAlgebra p (j x)
    letI := completedLocalRingAlgebra (j ≫ p) x
    Y.completedLocalRing (j x) ≃ₐ[R] X.completedLocalRing x := by
  letI := completedLocalRingAlgebra p (j x)
  letI := completedLocalRingAlgebra (j ≫ p) x
  refine AlgEquiv.ofRingEquiv (f := completedLocalRingRingEquivOfOpenImmersion j x) ?_
  intro r
  rw [algebraMap_completedLocalRingAlgebra, algebraMap_completedLocalRingAlgebra,
    completedLocalRingRingEquivOfOpenImmersion_toCompletedLocalRing]
  congr 1
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap j p x)) r

@[simp]
theorem completedLocalRingAlgEquivOfOpenImmersion_toCompletedLocalRing
    (j : X ⟶ Y) [IsOpenImmersion j] (p : Y ⟶ Spec R) (x : X)
    (a : Y.presheaf.stalk (j x)) :
    completedLocalRingAlgEquivOfOpenImmersion j p x
      (Y.toCompletedLocalRing (j x) a) =
        X.toCompletedLocalRing x (j.stalkMap x a) :=
  completedLocalRingRingEquivOfOpenImmersion_toCompletedLocalRing j x a

/-- The actual affine coordinate chart identifies the native completed local rings. -/
def completedLocalRingRingEquivOfAffineOpen (U : X.affineOpens) (x : U.1) :
    X.completedLocalRing x.val ≃+*
      (Spec Γ(X, U.1)).completedLocalRing (U.2.isoSpec.hom x) :=
  (completedLocalRingRingEquivOfOpenImmersion U.1.ι x).trans
    (completedLocalRingRingEquivOfIso U.2.isoSpec x).symm

/-- The affine-chart comparison on every actual uncompleted germ is the native stalk map. -/
theorem completedLocalRingRingEquivOfAffineOpen_toCompletedLocalRing
    (U : X.affineOpens) (x : U.1) (a : X.presheaf.stalk x.val) :
    completedLocalRingRingEquivOfIso U.2.isoSpec x
      (completedLocalRingRingEquivOfAffineOpen U x (X.toCompletedLocalRing x.val a)) =
        U.1.toScheme.toCompletedLocalRing x (U.1.ι.stalkMap x a) := by
  change completedLocalRingRingEquivOfIso U.2.isoSpec x
      ((completedLocalRingRingEquivOfIso U.2.isoSpec x).symm
        (completedLocalRingRingEquivOfOpenImmersion U.1.ι x
          (X.toCompletedLocalRing x.val a))) = _
  rw [RingEquiv.apply_symm_apply]
  exact completedLocalRingRingEquivOfOpenImmersion_toCompletedLocalRing U.1.ι x a

/-- The actual affine coordinate chart comparison preserves the original affine base. -/
def completedLocalRingAlgEquivOfAffineOpen (p : X ⟶ Spec R) (U : X.affineOpens) (x : U.1) :
    letI := completedLocalRingAlgebra p x.val
    letI := completedLocalRingAlgebra (U.2.isoSpec.inv ≫ U.1.ι ≫ p) (U.2.isoSpec.hom x)
    X.completedLocalRing x.val ≃ₐ[R]
      (Spec Γ(X, U.1)).completedLocalRing (U.2.isoSpec.hom x) := by
  letI := completedLocalRingAlgebra p (U.1.ι x)
  letI := completedLocalRingAlgebra (U.1.ι ≫ p) x
  letI := completedLocalRingAlgebra (U.2.isoSpec.inv ≫ U.1.ι ≫ p) (U.2.isoSpec.hom x)
  exact (completedLocalRingAlgEquivOfOpenImmersion U.1.ι p x).trans
    (completedLocalRingAlgEquivOfIsoOver U.2.isoSpec (U.1.ι ≫ p)
      (U.2.isoSpec.inv ≫ U.1.ι ≫ p) (by simp) x).symm

end AlgebraicGeometry.Scheme

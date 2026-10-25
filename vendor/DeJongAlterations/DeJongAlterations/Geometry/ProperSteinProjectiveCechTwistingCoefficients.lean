import DeJongAlterations.Geometry.ProperSteinProjectiveCechTwistingSheaf
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual ORIGINAL polynomial constant actions on native twisting sections

Native-only extraction from same-workspace `BingWangEntropy/ProjectiveTwistingSections.lean`,
SHA256 aa9e1bf9b3af283dc6568948ac9200c55aa8314599e8a04eda483500605ebeb9.
Generalized from fields to ANY ORIGINAL commutative coefficient ring.
No zero prime, fraction field or other-project module is imported.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
open scoped DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K I : Type u} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual constant polynomial ring map takes values in the true degree-zero part. -/
def homogeneousPolynomialDegreeZeroConstants :
    K →+* MvPolynomial.homogeneousSubmodule I K 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C I r⟩
  map_zero' := Subtype.ext (MvPolynomial.C.map_zero)
  map_one' := Subtype.ext (MvPolynomial.C.map_one)
  map_add' r s := Subtype.ext (MvPolynomial.C.map_add r s)
  map_mul' r s := Subtype.ext (MvPolynomial.C.map_mul r s)

/-- Actual constants are actual regular homogeneous fractions on each true Proj open. -/
def homogeneousPolynomialProjConstants
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    K →+* Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U) where
  toFun r := ⟨fun x => HomogeneousLocalization.fromZeroRingHom _
    x.val.asHomogeneousIdeal.toIdeal.primeCompl (homogeneousPolynomialDegreeZeroConstants r), by
      intro x
      refine ⟨U, x.property, 𝟙 U, 0, homogeneousPolynomialDegreeZeroConstants r,
        ⟨1, SetLike.one_mem_graded _⟩,
        fun y => y.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ => rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_zero
  map_one' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_one
  map_add' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_add r s
  map_mul' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_mul r s

/-- The actual regular Proj section rings carry their produced coefficient-ring algebra. -/
instance homogeneousPolynomialProjRegularAlgebra
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Algebra K Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U) :=
  (homogeneousPolynomialProjConstants U).toAlgebra

/-- Genuine constants commute with genuine restrictions. -/
theorem homogeneousPolynomialProjConstants_restrict
    {U V : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens} (i : V ⟶ U) (r : K) :
    (Proj (MvPolynomial.homogeneousSubmodule I K)).presheaf.map i.op
      (homogeneousPolynomialProjConstants U r) = homogeneousPolynomialProjConstants V r := rfl

/-- Actual homogeneous localizations use the same produced constant polynomial scalars. -/
instance homogeneousPolynomialHomogeneousLocalizationAlgebra
    (S : Submonoid (MvPolynomial I K)) :
    Algebra K (HomogeneousLocalization (MvPolynomial.homogeneousSubmodule I K) S) :=
  ((HomogeneousLocalization.fromZeroRingHom _ _).comp
    (homogeneousPolynomialDegreeZeroConstants (K := K) (I := I))).toAlgebra

/-- Actual shifted fraction section modules retain the produced coefficient-ring scalar action. -/
instance homogeneousPolynomialTwistingSectionsModule (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Module K (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U) :=
  Module.compHom _ (homogeneousPolynomialProjConstants U)

/-- The actual sheaf section module is over the actual coefficient ring. -/
instance homogeneousPolynomialTwistingBundleSectionsModule (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Module K (bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) U) :=
  inferInstanceAs (Module K
    (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U))

/-- The produced coefficient-ring action agrees with the actual regular-function action. -/
instance homogeneousPolynomialTwistingSectionsScalarTower (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    IsScalarTower K Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U)
      (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U) where
  smul_assoc r q s := by
    change ((homogeneousPolynomialProjConstants U r) * q) • s =
      homogeneousPolynomialProjConstants U r • (q • s)
    exact mul_smul _ _ _

/-- The produced homogeneous-localization constants have their actual ordinary localization values. -/
theorem homogeneousPolynomialLocalization_algebraMap_val
    (S : Submonoid (MvPolynomial I K)) (r : K) :
    (algebraMap K (HomogeneousLocalization (MvPolynomial.homogeneousSubmodule I K) S) r).val =
      algebraMap K (Localization S) r := by
  change Localization.mk (MvPolynomial.C r) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech

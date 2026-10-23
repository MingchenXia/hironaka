import DeJongAlterations.Geometry.SegreChart
import DeJongAlterations.Geometry.ProjectiveIdealCoordinateIdeal
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fin.Basic

/-!
# Native projectivity of affine identities and isomorphism transport

The sole coordinate chart of actual projective zero-space is the whole
scheme. Its empty-variable coordinate ring identifies the actual projective
structure morphism with an isomorphism. This gives projectivity of the
original identity over any commutative coefficient ring.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace

noncomputable section

universe u

namespace DeJongAlterations

/-- Precomposing a projective morphism by an actual isomorphism preserves the
literal map and its genuine closed projective embedding. -/
theorem IsProjectiveOver.precomp_isIso {R : Type u} [CommRing R]
    {X X' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    (hp : IsProjectiveOver p) (e : X' ⟶ X) [IsIso e] : IsProjectiveOver (e ≫ p) := by
  obtain ⟨n, i, hi, hpi⟩ := hp
  have := hi
  exact ⟨n, e ≫ i, inferInstance, by rw [Category.assoc, hpi]⟩

namespace Geometry.ProjectiveIdentity

open ProjectiveIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R]

/-- The sole actual projective coordinate chart is the whole native zero-space. -/
theorem zero_coordinateOpen_eq_top : nativeCoordinateOpen (R := R) (0 : Fin (0 + 1)) = ⊤ := by
  have H := iSup_nativeCoordinateOpen_eq_top (R := R) (n := 0)
  apply top_le_iff.mp
  rw [← H]
  apply iSup_le
  intro j
  have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  subst j
  exact le_rfl

/-- The original native projective zero-space structure morphism is an actual isomorphism. -/
instance projectiveZeroStructure_isIso : IsIso (projectiveSpaceStructure R 0) := by
  let i := Segre.coordinateChartInclusion (R := R) (0 : Fin (0 + 1))
  have hi : i.opensRange = ⊤ := by
    dsimp only [i, Segre.coordinateChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    exact zero_coordinateOpen_eq_top R
  have : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i hi
  have : IsEmpty {j : Fin (0 + 1) // j ≠ 0} :=
    ⟨fun j => j.2 (Fin.ext (Nat.lt_one_iff.mp j.1.isLt))⟩
  have hb : Function.Bijective (algebraMap R (CoordinateRing R (0 : Fin (0 + 1)))) := by
    have he : (MvPolynomial.isEmptyAlgEquiv R {j : Fin (0 + 1) // j ≠ 0}).symm.toRingHom =
        algebraMap R (CoordinateRing R (0 : Fin (0 + 1))) :=
      MvPolynomial.isEmptyAlgEquiv_symm_toRingHom R
    rw [← he]
    exact (MvPolynomial.isEmptyAlgEquiv R {j : Fin (0 + 1) // j ≠ 0}).symm.bijective
  have : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap R (CoordinateRing R (0 : Fin (0 + 1)))))) :=
    isIso_SpecMap_iff.mpr hb
  have : IsIso (i ≫ projectiveSpaceStructure R 0) := by
    rw [show i ≫ projectiveSpaceStructure R 0 = _ from Segre.coordinateChartInclusion_structure _]
    infer_instance
  exact IsIso.of_isIso_comp_left i _

/-- The actual zero-space isomorphism uses the original native structure morphism. -/
def projectiveZeroIsoSpec : projectiveSpace R 0 ≅ Spec (CommRingCat.of R) :=
  asIso (projectiveSpaceStructure R 0)

/-- Its literal forward map is the original projective structure map. -/
@[simp]
theorem projectiveZeroIsoSpec_hom : (projectiveZeroIsoSpec R).hom = projectiveSpaceStructure R 0 := rfl

/-- The identity of every affine spectrum has a genuine closed projective presentation. -/
theorem isProjectiveOver_id_spec : IsProjectiveOver (𝟙 (Spec (CommRingCat.of R))) :=
  ⟨0, (projectiveZeroIsoSpec R).inv, inferInstance, (projectiveZeroIsoSpec R).inv_hom_id⟩

end Geometry.ProjectiveIdentity

end DeJongAlterations

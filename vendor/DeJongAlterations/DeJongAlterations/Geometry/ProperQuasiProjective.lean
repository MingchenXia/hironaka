import DeJongAlterations.Geometry.QuasiProjectiveCompactification
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Proper quasi-projective morphisms are projective

The given actual projective immersion is itself closed: properness
descends through the separated projective structure map, and a proper
monomorphism is a native closed immersion.
-/

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of R)}

/-- The actual immersion presentation of a proper morphism is already a closed projective presentation. -/
theorem IsQuasiProjectiveOver.isProjective_of_isProper
    (hp : IsQuasiProjectiveOver p) [IsProper p] : IsProjectiveOver p := by
  obtain ⟨n, e, he, hbase⟩ := hp
  let := he
  have : IsProper (e ≫ projectiveSpaceStructure R n) := by rw [hbase]; infer_instance
  have : IsProper e := IsProper.of_comp e (projectiveSpaceStructure R n)
  exact ⟨n, e, (IsClosedImmersion.iff_isProper_and_mono e).mpr
    ⟨inferInstance, inferInstance⟩, hbase⟩

/-- Native projectivity is exactly properness together with an actual quasi-projective immersion. -/
theorem isProjectiveOver_iff_isQuasiProjectiveOver_and_isProper :
    IsProjectiveOver p ↔ IsQuasiProjectiveOver p ∧ IsProper p := by
  refine ⟨fun hp => ⟨hp.isQuasiProjective, hp.isProper⟩, ?_⟩
  rintro ⟨hp, hproper⟩
  let := hproper
  exact hp.isProjective_of_isProper

end DeJongAlterations

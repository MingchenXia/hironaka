import DeJongAlterations.Geometry.NodeCompletedLocalAffineBaseChangeUV

/-! Actual spectrum stalk localization over its SAME native external field action. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalSpecLocalization

open NodeCompletedLocalAffineBaseChangeUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option quotPrecheck false

universe u
variable (L B : Type u) [Field L] [CommRing B] [Algebra L B] (p : PrimeSpectrum B)

local notation "Z" => Spec (.of B)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap L B))
local notation "T" => Localization.AtPrime p.asIdeal

/-- The actual native spectrum stalk is its literal prime localization over the ENTIRE original external field. -/
def stalkEquiv :
    letI := Scheme.stalkAlgebra q p
    (Z).presheaf.stalk p ≃ₐ[L] T := by
  letI := Scheme.stalkAlgebra q p
  letI := nativeSpecStalkAlgebra B p
  letI := nativeSpecStalkLocalization B p
  letI := specStalk_scalarTower L B p
  exact (IsLocalization.algEquiv p.asIdeal.primeCompl ((Z).presheaf.stalk p) T).restrictScalars L

/-- EVERY original affine representative retains its SAME canonical prime-localization image. -/
theorem stalkEquiv_germ (b : B) :
    letI := Scheme.stalkAlgebra q p
    stalkEquiv L B p ((StructureSheaf.toStalk B p) b) = algebraMap B T b := by
  let := Scheme.stalkAlgebra q p
  let := nativeSpecStalkAlgebra B p
  let := nativeSpecStalkLocalization B p
  let := specStalk_scalarTower L B p
  exact (IsLocalization.algEquiv p.asIdeal.primeCompl ((Z).presheaf.stalk p) T).commutes b

theorem stalkEquiv_isLocalHom :
    letI := Scheme.stalkAlgebra q p
    IsLocalHom (stalkEquiv L B p).toRingHom := by
  let := Scheme.stalkAlgebra q p
  exact Algebra.CompletionLocalMap.instIsLocalHomRingEquivToRingHom (stalkEquiv L B p).toRingEquiv

attribute [local instance] stalkEquiv_isLocalHom

/-- The SAME native spectrum completion is the completion of its actual prime localization, preserving all coefficients. -/
def completedEquiv :
    letI := Scheme.completedLocalRingAlgebra q p
    (Z).completedLocalRing p ≃ₐ[L] AdicCompletion (maximalIdeal T) T := by
  letI := Scheme.stalkAlgebra q p
  letI := Scheme.completedLocalRingAlgebra q p
  letI : IsLocalHom (stalkEquiv L B p).toRingHom :=
    Algebra.CompletionLocalMap.instIsLocalHomRingEquivToRingHom (stalkEquiv L B p).toRingEquiv
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv (stalkEquiv L B p).toRingEquiv) ?_
  intro l
  change Algebra.CompletionLocalMap.completionMap (stalkEquiv L B p).toRingHom
    (algebraMap ((Z).presheaf.stalk p) ((Z).completedLocalRing p)
      (algebraMap L ((Z).presheaf.stalk p) l)) = _
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap T (AdicCompletion (maximalIdeal T) T))
    ((stalkEquiv L B p).commutes l)

/-- The WHOLE completed equivalence is the canonical native completion of the SAME original stalk localization map. -/
theorem completedEquiv_toRingHom :
    letI := Scheme.stalkAlgebra q p
    letI := Scheme.completedLocalRingAlgebra q p
    (completedEquiv L B p).toRingHom =
      Algebra.CompletionLocalMap.completionMap (stalkEquiv L B p).toRingHom := by
  let := Scheme.stalkAlgebra q p
  let := Scheme.completedLocalRingAlgebra q p
  rfl

/-- EVERY actual native stalk representative retains its actual completion/localization image. -/
theorem completedEquiv_original (t : (Z).presheaf.stalk p) :
    letI := Scheme.stalkAlgebra q p
    letI := Scheme.completedLocalRingAlgebra q p
    completedEquiv L B p ((Z).toCompletedLocalRing p t) =
      algebraMap T (AdicCompletion (maximalIdeal T) T) (stalkEquiv L B p t) := by
  let := Scheme.stalkAlgebra q p
  let := Scheme.completedLocalRingAlgebra q p
  exact Algebra.CompletionLocalMap.completionMap_algebraMap (stalkEquiv L B p).toRingHom t

end DeJongAlterations.Geometry.NodeCompletedLocalSpecLocalization

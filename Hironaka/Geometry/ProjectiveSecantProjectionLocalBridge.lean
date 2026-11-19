import Hironaka.Geometry.ProjectiveSecantProjectionUnramifiedStalk
import Hironaka.Geometry.ResidueExtensionLiftResidueFields

/-!
# Exact native affine chart-to-stalk comparisons in the reverse direction
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native original Spec-stalk unramifiedness implies native unramifiedness of the literal original algebra at that SAME original prime. -/
theorem isUnramifiedAt_of_spec_stalkMap {R S : CommRingCat.{u}} (β : R ⟶ S)
    (Q : PrimeSpectrum S) (h : ((Spec.map β).stalkMap Q).hom.FormallyUnramified) :
    letI := β.hom.toAlgebra
    Algebra.IsUnramifiedAt R Q.asIdeal := by
  let : Algebra R S := β.hom.toAlgebra
  let P : PrimeSpectrum R := PrimeSpectrum.comap β.hom Q
  let : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  let : Algebra (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  rw [← Scheme.localRingHom_comp_stalkIso β Q] at h
  have hc := (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso (Spec.stalkIso R P).hom
    (CommRingCat.ofHom (Localization.localRingHom P.asIdeal Q.asIdeal β.hom rfl) ≫ (Spec.stalkIso S Q).inv)).mp h
  have hl := (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
    (CommRingCat.ofHom (Localization.localRingHom P.asIdeal Q.asIdeal β.hom rfl)) (Spec.stalkIso S Q).inv).mp hc
  let : Algebra.FormallyUnramified (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := hl
  exact Algebra.FormallyUnramified.comp R (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal)

/-- Exact actual native affine chart triangles transport actual original scheme stalk-unramifiedness back to the literal whole original Spec-map stalk. -/
theorem chart_stalkMap_formallyUnramified_of_original
    {X Y : Scheme.{u}} (f : X ⟶ Y) {R S : CommRingCat.{u}}
    (a : Spec S ⟶ X) [IsOpenImmersion a] (b : Spec R ⟶ Y) [IsOpenImmersion b]
    (β : R ⟶ S) (htriangle : a ≫ f = Spec.map β ≫ b) (Q : PrimeSpectrum S)
    (h : (f.stalkMap (a Q)).hom.FormallyUnramified) :
    ((Spec.map β).stalkMap Q).hom.FormallyUnramified := by
  have hc : ((a ≫ f).stalkMap Q).hom.FormallyUnramified := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso
      (f.stalkMap (a Q)) (a.stalkMap Q)).mpr h
  rw [htriangle, Scheme.Hom.stalkMap_comp] at hc
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    (b.stalkMap ((Spec.map β) Q)) ((Spec.map β).stalkMap Q)).mp hc

/-- Exact actual original affine chart triangles also transport actual original residue-field isomorphisms back to the literal whole original Spec-map residue field. -/
theorem chart_residueFieldMap_isIso_of_original
    {X Y : Scheme.{u}} (f : X ⟶ Y) {R S : CommRingCat.{u}}
    (a : Spec S ⟶ X) [IsOpenImmersion a] (b : Spec R ⟶ Y) [IsOpenImmersion b]
    (β : R ⟶ S) (htriangle : a ≫ f = Spec.map β ≫ b) (Q : PrimeSpectrum S)
    [IsIso (f.residueFieldMap (a Q))] : IsIso ((Spec.map β).residueFieldMap Q) := by
  have hc : IsIso ((a ≫ f).residueFieldMap Q) := by
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  rw [htriangle, Scheme.residueFieldMap_comp] at hc
  let := hc
  exact IsIso.of_isIso_comp_left (b.residueFieldMap ((Spec.map β) Q)) _

/-- The same actual native Spec residue-field isomorphism gives surjectivity of the actual original ideal residue-field map, with the whole native residue triangle retained. -/
theorem spec_ideal_residueFieldMap_surjective {R S : CommRingCat.{u}} (β : R ⟶ S)
    (Q : PrimeSpectrum S) [IsIso ((Spec.map β).residueFieldMap Q)] :
    Function.Surjective (Ideal.ResidueField.map (PrimeSpectrum.comap β.hom Q).asIdeal Q.asIdeal β.hom rfl) := by
  have he := ResidueExtensionLift.spec_residueFieldIso_naturality β Q
  have hi : IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map ((Spec.map β) Q).asIdeal Q.asIdeal β.hom rfl)) := by
    rw [← he]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom
    (Ideal.ResidueField.map ((Spec.map β) Q).asIdeal Q.asIdeal β.hom rfl))).2

end Hironaka.Geometry.ProjectiveSecant

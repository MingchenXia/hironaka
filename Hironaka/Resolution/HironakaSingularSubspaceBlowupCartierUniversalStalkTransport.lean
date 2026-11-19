import Hironaka.Resolution.HironakaSingularIdealInvertibleModule
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Standard original invertible ideal stalks transport to actual open charts

Actual stalk maps and their genuine open-immersion isomorphisms retain the
SAME original target ideal. No chosen chart lift, ideal equality, rank or
regular-generator certificate is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-stalk-transport.tex`.
-/

set_option autoImplicit false

open Set CategoryTheory AlgebraicGeometry

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalStalkTransport

open HironakaSingularIdealInvertibleModule

noncomputable section

/-- A genuine ring equivalence transports nonzerodivisors without any
integral-domain or reduced-ring hypothesis. -/
theorem isRegular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {alpha : R} (hreg : IsRegular alpha) : IsRegular (e alpha) := by
  have hleft : IsLeftRegular (e alpha) := by
    intro b c hbc
    change e alpha * b = e alpha * c at hbc
    apply e.symm.injective
    apply hreg.left
    have h := congrArg e.symm hbc
    simpa only [map_mul, e.symm_apply_apply] using h
  exact ⟨hleft, fun b c hbc => hleft (by simpa only [mul_comm] using hbc)⟩

/-- The explicit Cartier version transports the SAME actual pulled ideal
through the original open-chart stalk isomorphism. -/
theorem exists_regular_generator_on_open_chart_of_cartier
    {U X Z : LocallyRingedSpace} (i : U ⟶ X) [LocallyRingedSpace.IsOpenImmersion i]
    (F : X ⟶ Z) (u : U)
    (I : Ideal (Z.presheaf.stalk (F.base (i.base u))).carrier)
    {alpha : (X.presheaf.stalk (i.base u)).carrier} (hreg : IsRegular alpha)
    (hspan : Ideal.map (F.stalkMap (i.base u)).hom I = Ideal.span {alpha}) :
    ∃ beta : (U.presheaf.stalk u).carrier,
      IsRegular beta ∧ Ideal.map ((i ≫ F).stalkMap u).hom I = Ideal.span {beta} := by
  let P : (X.presheaf.stalk (i.base u)).carrier →+* (U.presheaf.stalk u).carrier :=
    (i.stalkMap u).hom
  let Q : (Z.presheaf.stalk (F.base (i.base u))).carrier →+*
      (X.presheaf.stalk (i.base u)).carrier := (F.stalkMap (i.base u)).hom
  let H : (Z.presheaf.stalk (F.base (i.base u))).carrier →+* (U.presheaf.stalk u).carrier :=
    ((i ≫ F).stalkMap u).hom
  let e := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  have hcomp : H = P.comp Q := by
    apply RingHom.ext
    intro r
    exact ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp i F u) r
  change ∃ alpha : (U.presheaf.stalk u).carrier,
    IsRegular alpha ∧ Ideal.map H I = Ideal.span {alpha}
  refine ⟨e alpha, isRegular_map_ringEquiv e hreg, ?_⟩
  rw [hcomp, ← Ideal.map_map]
  have hspan' : Ideal.map Q I = Ideal.span {alpha} := hspan
  rw [hspan', Ideal.map_span, Set.image_singleton]
  rfl

/-- Standard Module.Invertible of an original actual pulled ideal internally
produces the principal regular form of the SAME ideal on a genuine open chart. -/
theorem exists_regular_generator_on_open_chart
    {U X Z : LocallyRingedSpace} (i : U ⟶ X) [LocallyRingedSpace.IsOpenImmersion i]
    (F : X ⟶ Z) (u : U)
    (I : Ideal (Z.presheaf.stalk (F.base (i.base u))).carrier)
    (hInv : Module.Invertible (X.presheaf.stalk (i.base u)).carrier
      (Ideal.map (F.stalkMap (i.base u)).hom I)) :
    ∃ alpha : (U.presheaf.stalk u).carrier,
      IsRegular alpha ∧ Ideal.map ((i ≫ F).stalkMap u).hom I = Ideal.span {alpha} := by
  obtain ⟨alpha, _, hspan, hreg⟩ := exists_regular_generator _ hInv
  exact exists_regular_generator_on_open_chart_of_cartier i F u I hreg hspan

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalStalkTransport

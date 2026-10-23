import DeJongAlterations.Geometry.SteinGeometricIntegrality

/-!
# The actual generic fibre after an integral dominant base change

Canonical residue-field factorization and native Cartesian pasting
apply the original generic geometric-integrality hypothesis directly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Any actual field-valued point over the original generic point has an integral actual pullback. -/
theorem isIntegral_of_genericFieldPoint {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) (h : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    {L : Type u} [Field L] (e : Spec (.of L) ⟶ S)
    (he : ∀ z, e z = genericPoint S)
    {Q : Scheme.{u}} (fst : Q ⟶ X) (snd : Q ⟶ Spec (.of L))
    (hpb : IsPullback fst snd f e) : IsIntegral Q := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L S).symm.surjective e
  have hs : s = genericPoint S := by
    simpa [Scheme.SpecToEquivOfField] using he (IsLocalRing.closedPoint L)
  subst s
  let q : Q ⟶ f.fiber (genericPoint S) :=
    pullback.lift fst (snd ≫ Spec.map φ) (by simp [hpb.w, Scheme.SpecToEquivOfField])
  apply h.geometrically_isIntegral (Spec.map φ) q snd
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hpb
  refine .flip (.of_bot (.flip ?_) ?_
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (genericPoint S))).flip)
  · convert! hpb
    simp [q]
  · simp [q, Scheme.Hom.fiberToSpecResidueField]

/-- The native generic fibre of the original Cartesian projection is integral. -/
theorem genericFiber_isIntegral {X S Y : Scheme.{u}} [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) (h : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (g : Y ⟶ S) [IsDominant g] :
    IsIntegral ((pullback.snd f g).fiber (genericPoint Y)) := by
  let p := pullback.snd f g
  let e := Y.fromSpecResidueField (genericPoint Y) ≫ g
  have he : ∀ z, e z = genericPoint S := by
    intro z
    simp only [e, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact genericPoint_map_of_isDominant g
  exact isIntegral_of_genericFieldPoint f h e he
    (p.fiberι (genericPoint Y) ≫ pullback.fst f g) (p.fiberToSpecResidueField (genericPoint Y))
    ((IsPullback.of_hasPullback p (Y.fromSpecResidueField (genericPoint Y))).paste_horiz
      (IsPullback.of_hasPullback f g))

end DeJongAlterations.Geometry.CurveFibrationBaseChange

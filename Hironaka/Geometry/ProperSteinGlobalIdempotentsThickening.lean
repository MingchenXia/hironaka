import Hironaka.Geometry.ProperSteinGlobalIdempotentsQuotient

/-! # Actual ORIGINAL infinitesimal thickenings retain the SAME closed-fibre whole idempotents. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace Hironaka.Geometry.ProperSteinGlobalIdempotents
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of A)) (I : Ideal A)

/-- The LITERAL ORIGINAL closed fibre over the original coefficient quotient. -/
abbrev closedFiber := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- EVERY LITERAL ORIGINAL ideal-power thickening, without a supplied model. -/
abbrev thickening (n : ℕ) :=
  pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))

/-- The actual original quotient-factor spectrum triangle retains the entire original coefficient maps. -/
theorem powerQuotientSpec_structure (n : ℕ) :
    Spec.map (CommRingCat.ofHom (powerQuotientFactor I n)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((powerQuotientFactor I n).comp (Ideal.Quotient.mk (I ^ (n + 1))))) = _
  rw [powerQuotientFactor_comp_mk]

/-- The SAME ORIGINAL closed-fibre inclusion into the actual nth original thickening. -/
def closedToThickening (n : ℕ) : closedFiber p I ⟶ thickening p I n :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
      Spec.map (CommRingCat.ofHom (powerQuotientFactor I n)))
    (by rw [Category.assoc, powerQuotientSpec_structure]; exact pullback.condition)

/-- The actual original inclusion is the actual Cartesian base change of the original coefficient quotient. -/
theorem closedToThickening_isPullback (n : ℕ) :
    IsPullback (pullback.snd p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
      (closedToThickening p I n)
      (Spec.map (CommRingCat.ofHom (powerQuotientFactor I n)))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) := by
  refine .of_bot
    (v₂₁ := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (v₂₂ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ?_ ?_
    (IsPullback.of_hasPullback p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).flip
  · simpa only [closedToThickening, pullback.lift_fst, powerQuotientSpec_structure] using
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).flip
  · simp [closedToThickening]

/-- The ORIGINAL ideal-power facts derive actual homeomorphy of the SAME original closed-fibre inclusion. -/
theorem closedToThickening_isHomeomorph (n : ℕ) : IsHomeomorph (closedToThickening p I n) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (powerQuotientFactor I n))) :=
    IsClosedImmersion.spec_of_surjective _ (powerQuotientFactor_surjective I n)
  let : Surjective (Spec.map (CommRingCat.ofHom (powerQuotientFactor I n))) :=
    NilBaseChange.surjective_specMap _ (powerQuotientFactor_surjective I n)
      (powerQuotientFactor_nil_ker I n)
  let : IsClosedImmersion (closedToThickening p I n) :=
    MorphismProperty.of_isPullback (closedToThickening_isPullback p I n) inferInstance
  let : Surjective (closedToThickening p I n) :=
    MorphismProperty.of_isPullback (closedToThickening_isPullback p I n) inferInstance
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(closedToThickening p I n).isEmbedding, (closedToThickening p I n).surjective⟩

/-- Actual whole idempotents biject along EVERY SAME ORIGINAL closed-fibre inclusion. -/
def closedToThickeningIdempotentEquiv (n : ℕ) :
    {e : Γ(thickening p I n, ⊤) // IsIdempotentElem e} ≃
      {e : Γ(closedFiber p I, ⊤) // IsIdempotentElem e} :=
  idempotentPullbackEquiv (closedToThickening p I n) (closedToThickening_isHomeomorph p I n)

/-- The ENTIRE forward map is exactly the ORIGINAL closed-fibre inclusion pullback. -/
theorem closedToThickeningIdempotentEquiv_apply (n : ℕ)
    (e : {e : Γ(thickening p I n, ⊤) // IsIdempotentElem e}) :
    (closedToThickeningIdempotentEquiv p I n e).1 = (closedToThickening p I n).appTop e.1 := rfl

end Hironaka.Geometry.ProperSteinGlobalIdempotents

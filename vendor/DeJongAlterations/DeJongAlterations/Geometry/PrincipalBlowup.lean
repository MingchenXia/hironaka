import DeJongAlterations.Geometry.AffineBlowupCover

/-!
# The native blowup of a nonzero principal ideal

The actual `g*T` chart covers the entire Proj of the Rees algebra of `(g)`.
Over a domain, its fraction-coordinate algebra is the coefficient ring whenever `g ≠ 0`.
Consequently the original native blowup structure map is an isomorphism over all of `Spec R`.
-/

open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.PrincipalBlowup

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (g : R)

/-- The actual `g*T` chart is the whole native blowup of the intrinsically principal ideal. -/
theorem principalChart_eq_top :
    affineBlowupChartOpen (Ideal.span ({g} : Set R)) g
      (Ideal.mem_span_singleton_self g) = ⊤ := by
  apply top_unique
  rw [← iSup_affineBlowupChartOpen (Ideal.span ({g} : Set R))]
  apply iSup_le
  intro a
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp a.property
  have H : reesDegreeOne (Ideal.span ({g} : Set R)) a a.property =
      algebraMap R (reesAlgebra (Ideal.span ({g} : Set R))) r *
        reesDegreeOne (Ideal.span ({g} : Set R)) g (Ideal.mem_span_singleton_self g) := by
    apply Subtype.ext
    change monomial 1 (a : R) = C r * monomial 1 g
    rw [C_mul_monomial, hr]
  change Proj.basicOpen (reesGrading (Ideal.span ({g} : Set R)))
      (reesDegreeOne (Ideal.span ({g} : Set R)) a a.property) ≤
    Proj.basicOpen (reesGrading (Ideal.span ({g} : Set R)))
      (reesDegreeOne (Ideal.span ({g} : Set R)) g (Ideal.mem_span_singleton_self g))
  rw [H, Proj.basicOpen_mul]
  exact inf_le_right

variable [IsDomain R] (hg0 : g ≠ 0)

include hg0

/-- All actual ideal ratios for a nonzero principal ideal are coefficients. -/
theorem principalFractionChart_eq_bot :
    affineBlowupFractionChart (Ideal.span ({g} : Set R)) g =
      (⊥ : Subalgebra R (FractionRing R)) := by
  apply le_antisymm ?_ bot_le
  apply Algebra.adjoin_le
  rintro _ ⟨a, rfl⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp a.property
  have hgK : algebraMap R (FractionRing R) g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hg0
  have H : algebraMap R (FractionRing R) (a : R) /
      algebraMap R (FractionRing R) g = algebraMap R (FractionRing R) r := by
    rw [← hr, map_mul, mul_div_cancel_right₀ _ hgK]
  change algebraMap R (FractionRing R) (a : R) /
    algebraMap R (FractionRing R) g ∈ (⊥ : Subalgebra R (FractionRing R))
  rw [H]
  exact (⊥ : Subalgebra R (FractionRing R)).algebraMap_mem r

/-- The literal coefficient map to the principal fraction chart is bijective. -/
theorem principalFractionChart_algebraMap_bijective :
    Function.Bijective (algebraMap R
      (affineBlowupFractionChart (Ideal.span ({g} : Set R)) g)) := by
  constructor
  · intro a b hab
    apply IsFractionRing.injective R (FractionRing R)
    exact congrArg (fun z : affineBlowupFractionChart (Ideal.span ({g} : Set R)) g =>
      (z : FractionRing R)) hab
  · intro a
    have ha : (a : FractionRing R) ∈ (⊥ : Subalgebra R (FractionRing R)) := by
      rw [← principalFractionChart_eq_bot g hg0]
      exact a.property
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp ha
    exact ⟨r, Subtype.ext hr⟩

/-- The actual coefficient map identifies the principal fraction chart with its coefficient ring. -/
def principalFractionChartCoefficientsEquiv : R ≃ₐ[R]
    affineBlowupFractionChart (Ideal.span ({g} : Set R)) g :=
  AlgEquiv.ofBijective (Algebra.ofId R _)
    (principalFractionChart_algebraMap_bijective g hg0)

/-- The actual principal fraction-chart inclusion is an isomorphism onto the whole blowup. -/
theorem principalChartInclusion_isIso :
    IsIso (affineBlowupChartInclusion (Ideal.span ({g} : Set R)) g
      (Ideal.mem_span_singleton_self g) hg0) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [affineBlowupFractionChartInclusion_opensRange, principalChart_eq_top]

/-- Blowing up a nonzero principal ideal is the original scheme over its entire affine base. -/
theorem affineBlowupStructure_span_singleton_isIso :
    IsIso (affineBlowupStructure (Ideal.span ({g} : Set R))) := by
  let i := affineBlowupChartInclusion (Ideal.span ({g} : Set R)) g
    (Ideal.mem_span_singleton_self g) hg0
  let : IsIso i := principalChartInclusion_isIso g hg0
  have : IsIso (i ≫ affineBlowupStructure (Ideal.span ({g} : Set R))) := by
    dsimp only [i]
    rw [affineBlowupChartInclusion_structure]
    change IsIso (Spec.map (principalFractionChartCoefficientsEquiv g hg0).toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  exact IsIso.of_isIso_comp_left (f := i) _

/-- The resulting native scheme isomorphism, with the original structure map as forward map. -/
def principalBlowupIso :
    affineBlowup (Ideal.span ({g} : Set R)) ≅ Spec (CommRingCat.of R) := by
  let := affineBlowupStructure_span_singleton_isIso g hg0
  exact asIso (affineBlowupStructure (Ideal.span ({g} : Set R)))

/-- The principal blowup comparison preserves the actual structure morphism exactly. -/
theorem principalBlowupIso_hom :
    (principalBlowupIso g hg0).hom = affineBlowupStructure (Ideal.span ({g} : Set R)) := rfl

end DeJongAlterations.Geometry.PrincipalBlowup

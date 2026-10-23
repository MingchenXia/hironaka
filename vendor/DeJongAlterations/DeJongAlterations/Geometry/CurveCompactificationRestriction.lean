import DeJongAlterations.Geometry.NormalCurveModification
import DeJongAlterations.Geometry.ModificationCenterBirational
import DeJongAlterations.Geometry.ModificationCenterOpen
import DeJongAlterations.Geometry.AffineBlowupBirational
import DeJongAlterations.Geometry.AlterationRestriction

/-!
# Actual modification restrictions and normal-open inverse lifts

These native comparisons construct the actual inverse lift of a normal open
through a finite birational morphism, preserving the original structure triangle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveCompactification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- Actual normality transports through an open immersion by its original stalk isomorphisms. -/
theorem isNormalScheme_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (hn : IsNormalScheme Y) : IsNormalScheme X := by
  intro x
  let := (hn (f x)).1
  let := (hn (f x)).2
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain e.symm.toRingHom e.symm.injective,
    IsIntegrallyClosed.of_equiv e⟩

/-- A modification remains an actual modification over every nonempty target open. -/
theorem isModification_morphismRestrict (f : X ⟶ Y) [hf : IsModification f]
    (U : Y.Opens) [Nonempty U] : IsModification (f ∣_ U) := by
  let := hf.sourceIntegral
  let := hf.targetIntegral
  let hr := IsAlteration.morphismRestrict f U
  let := hr.sourceIntegral
  let := hr.targetIntegral
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict
    (P := @IsDominant) (inferInstance : IsDominant f) U
  obtain ⟨W, hW, hIso⟩ := ModificationCenter.exists_dense_isomorphism_open f
  let := hIso
  let V := U.ι ⁻¹ᵁ W
  have hV : (V : Set U).Nonempty := by
    obtain ⟨y, hyU, hyW⟩ := hW.inter_open_nonempty U U.isOpen
      (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U))
    exact ⟨⟨y, hyU⟩, hyW⟩
  have hi : IsIso ((f ∣_ U) ∣_ V) := by
    apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U V)).mpr
    change IsIso (f ∣_ U.ι ''ᵁ V)
    exact ModificationCenter.isIso_restrict_of_le f (by
      rintro y ⟨x, hx, rfl⟩
      exact hx)
  let := hi
  exact {
    sourceIntegral := hr.sourceIntegral
    targetIntegral := hr.targetIntegral
    birational := birationalOver_id_of_isIso_morphismRestrict (f ∣_ U) V hV }

/-- A finite birational morphism is an isomorphism over an actual nonempty normal open. -/
theorem finite_modification_restrict_isIso (f : X ⟶ Y) [hf : IsModification f]
    [IsFinite f] (U : Y.Opens) [Nonempty U] (hn : IsNormalScheme U.toScheme) :
    IsIso (f ∣_ U) := by
  let hr := isModification_morphismRestrict f U
  let := hr.sourceIntegral
  let := hr.targetIntegral
  exact NormalCurveModification.isIso_of_finite_birational (f ∣_ U) hr.birational hn

end DeJongAlterations.Geometry.CurveCompactification

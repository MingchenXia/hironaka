/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.AffineBlowupIsomorphism
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The native affine blowup on the complement of its centre

The actual blowup map is an isomorphism over the complement of the native ideal-sheaf
support, for every ideal in a domain. If the ideal is nonzero, this open is nonempty
and dense. Finite generation is not required for this open isomorphism.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

set_option autoImplicit false

namespace DeJongAlterations

noncomputable section

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual open complement of the vanishing set of the blowup ideal. -/
def affineBlowupCenterComplement : (Spec (CommRingCat.of R)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩

/-- This open is exactly the complement of the support of the native centre ideal sheaf. -/
theorem affineBlowupCenterComplement_eq_support_compl :
    affineBlowupCenterComplement I =
      (Geometry.SpecIdealSheaf.specIdealSheaf R I).support.compl := by
  apply SetLike.coe_injective
  change (PrimeSpectrum.zeroLocus (I : Set R))ᶜ =
    ((Geometry.SpecIdealSheaf.specIdealSheaf R I).support : Set (Spec (CommRingCat.of R)))ᶜ
  rw [Geometry.ReducedClosedSubscheme.specIdealSheaf_support]
  rfl

/-- A point is off the centre exactly when it avoids some element of the actual ideal. -/
theorem mem_affineBlowupCenterComplement_iff (x : Spec (CommRingCat.of R)) :
    x ∈ affineBlowupCenterComplement I ↔ ∃ g ∈ I, g ∉ x.asIdeal := by
  classical
  change (¬ ∀ g, g ∈ I → g ∈ x.asIdeal) ↔ _
  simp only [not_forall, exists_prop]

/-- Every principal open from an ideal element is contained in the centre complement. -/
theorem basicOpen_le_affineBlowupCenterComplement {g : R} (hg : g ∈ I) :
    PrimeSpectrum.basicOpen g ≤ affineBlowupCenterComplement I := by
  intro x hx
  exact (mem_affineBlowupCenterComplement_iff I x).mpr ⟨g, hg, hx⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The principal opens of all ideal elements cover exactly the centre complement. -/
theorem affineBlowupCenterComplement_eq_iSup_basicOpen :
    affineBlowupCenterComplement I =
      ⨆ g : I, (PrimeSpectrum.basicOpen (g : R) : (Spec (CommRingCat.of R)).Opens) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := (mem_affineBlowupCenterComplement_iff I x).mp hx
    exact (le_iSup
      (fun a : I => (PrimeSpectrum.basicOpen (a : R) : (Spec (CommRingCat.of R)).Opens))
      ⟨g, hg⟩) hxg
  · exact iSup_le fun g => basicOpen_le_affineBlowupCenterComplement I g.property

set_option backward.isDefEq.respectTransparency false in
/-- Inside a larger open, restriction over an isomorphism open is still an isomorphism. -/
theorem isIso_morphismRestrict_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (hVU : V ≤ U) [IsIso (f ∣_ V)] :
    IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  have e := morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f himage
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mpr
    (inferInstanceAs (IsIso (f ∣_ V)))

variable [IsDomain R]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The native affine blowup is an isomorphism over the full complement of its centre.
This includes the empty open for the zero ideal and assumes no finite generation. -/
theorem affineBlowupStructure_centerComplement_isIso :
    IsIso (affineBlowupStructure I ∣_ affineBlowupCenterComplement I) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨g, hg, hxg⟩ := (mem_affineBlowupCenterComplement_iff I x.val).mp x.property
  have hg0 : g ≠ 0 := by
    intro h
    exact hxg (h ▸ x.val.asIdeal.zero_mem)
  let U := affineBlowupCenterComplement I
  let V := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen g
  refine ⟨V, hxg, ?_⟩
  have : IsIso (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen g) :=
    affineBlowupStructure_restrict_isIso I g hg hg0
  exact isIso_morphismRestrict_restrict_of_le (affineBlowupStructure I) U _
    (basicOpen_le_affineBlowupCenterComplement I hg)

/-- A nonzero ideal in a domain has nonempty centre complement, containing the zero prime. -/
theorem affineBlowupCenterComplement_nonempty (hI : I ≠ ⊥) :
    (affineBlowupCenterComplement I : Set (Spec (CommRingCat.of R))).Nonempty := by
  refine ⟨(⊥ : PrimeSpectrum R), ?_⟩
  change ¬ (I : Set R) ⊆ ((⊥ : PrimeSpectrum R).asIdeal : Set R)
  intro h
  exact hI (le_antisymm h bot_le)

/-- A nonzero ideal in a domain has dense centre complement. -/
theorem affineBlowupCenterComplement_dense (hI : I ≠ ⊥) :
    Dense (affineBlowupCenterComplement I : Set (Spec (CommRingCat.of R))) :=
  (affineBlowupCenterComplement I).isOpen.dense (affineBlowupCenterComplement_nonempty I hI)

/-- A native nonzero-ideal blowup has an actual dense nonempty target open of isomorphism. -/
theorem affineBlowupStructure_exists_dense_isomorphism_open (hI : I ≠ ⊥) :
    ∃ U : (Spec (CommRingCat.of R)).Opens,
      (U : Set (Spec (CommRingCat.of R))).Nonempty ∧
      Dense (U : Set (Spec (CommRingCat.of R))) ∧
      IsIso (affineBlowupStructure I ∣_ U) :=
  ⟨affineBlowupCenterComplement I, affineBlowupCenterComplement_nonempty I hI,
    affineBlowupCenterComplement_dense I hI, affineBlowupStructure_centerComplement_isIso I⟩

end

end DeJongAlterations

/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.BlowupCartier
import DeJongAlterations.Geometry.BlowupIntegral
import DeJongAlterations.Geometry.AffineBlowupModification
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# The actual global blowup away from its centre

The native global structure map is an isomorphism over the actual complement of the
ideal-sheaf support. For proper support this gives a native partial isomorphism over X.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations.Geometry.BlowupGluing

set_option autoImplicit false

namespace DeJongAlterations.Geometry.BlowupComplement

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The actual affine base chart pulls the global centre complement back to its actual
coordinate-ideal complement. -/
theorem fromSpec_preimage_supportComplement (U : X.affineOpens) :
    U.2.fromSpec ⁻¹ᵁ D.support.compl = affineBlowupCenterComplement (D.ideal U) := by
  rw [affineBlowupCenterComplement_eq_support_compl,
    ← BlowupCartier.comap_fromSpec D U, Scheme.IdealSheafData.support_comap]
  rfl

variable [IsIntegral X]

/-- On the intersection of the centre complement with a nonempty affine base open,
the actual global blowup map is an isomorphism. -/
theorem blowupStructure_restrict_affine_complement_isIso (U : X.AffineZariskiSite)
    [Nonempty U.1] :
    IsIso (blowupStructure D ∣_ (D.support.compl ⊓ U.1)) := by
  let I := D.ideal ⟨U.1, U.2⟩
  let i := U.2.fromSpec
  let j := chartInclusion D U
  let g := affineBlowupStructure I
  let π := blowupStructure D
  let V := D.support.compl ⊓ U.1
  have hiU : U.2.fromSpec ⁻¹ᵁ U.1 = ⊤ := by
    calc
      U.2.fromSpec ⁻¹ᵁ U.1 = U.2.fromSpec ⁻¹ᵁ U.2.fromSpec.opensRange :=
        congrArg (fun W : X.Opens => U.2.fromSpec ⁻¹ᵁ W) U.2.opensRange_fromSpec.symm
      _ = ⊤ := Scheme.Hom.preimage_opensRange U.2.fromSpec
  have hpre : i ⁻¹ᵁ V = affineBlowupCenterComplement I := by
    change (U.2.fromSpec ⁻¹ᵁ D.support.compl) ⊓ (U.2.fromSpec ⁻¹ᵁ U.1) = _
    rw [hiU, inf_top_eq]
    exact fromSpec_preimage_supportComplement D ⟨U.1, U.2⟩
  have hi : V ≤ i.opensRange := by
    rw [U.2.opensRange_fromSpec]
    exact inf_le_right
  have hj : π ⁻¹ᵁ V ≤ j.opensRange := by
    rw [chartInclusion_opensRange]
    exact fun x hx => hx.2
  have : IsIso (i ∣_ V) := isIso_morphismRestrict_of_le_opensRange i V hi
  have : IsIso (g ∣_ i ⁻¹ᵁ V) := by
    rw [hpre]
    exact affineBlowupStructure_centerComplement_isIso I
  have : IsIso ((g ≫ i) ∣_ V) := by
    rw [morphismRestrict_comp]
    infer_instance
  have hcomp : j ≫ π = g ≫ i := chartInclusion_structure D U
  have : IsIso ((j ≫ π) ∣_ V) := by rw [hcomp]; infer_instance
  have : IsIso (j ∣_ π ⁻¹ᵁ V) := isIso_morphismRestrict_of_le_opensRange j _ hj
  have : IsIso ((j ∣_ π ⁻¹ᵁ V) ≫ π ∣_ V) := by
    rw [← morphismRestrict_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (f := j ∣_ π ⁻¹ᵁ V) (π ∣_ V)

/-- The actual native global blowup is an isomorphism over the whole centre complement,
without finite generation or a proper-support hypothesis. -/
theorem blowupStructure_supportComplement_isIso :
    IsIso (blowupStructure D ∣_ D.support.compl) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨W, hW, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x.val) (U := ⊤) (by trivial)
  let U : X.AffineZariskiSite := ⟨W, hW⟩
  let : Nonempty U.1 := ⟨⟨x.val, hxW⟩⟩
  let V := D.support.compl ⊓ U.1
  refine ⟨(Scheme.Opens.ι (X := X) D.support.compl) ⁻¹ᵁ V, ⟨x.property, hxW⟩, ?_⟩
  have : IsIso (blowupStructure D ∣_ V) :=
    blowupStructure_restrict_affine_complement_isIso D U
  exact isIso_morphismRestrict_restrict_of_le (blowupStructure D) D.support.compl V inf_le_left

/-- A proper centre support misses the actual generic point of the integral base. -/
theorem supportComplement_nonempty (hD : D.support ≠ ⊤) :
    (D.support.compl : Set X).Nonempty :=
  ⟨genericPoint X, IntegralIdeal.genericPoint_not_mem_support D hD⟩

/-- The actual complement of a proper centre is dense in the integral base. -/
theorem supportComplement_dense (hD : D.support ≠ ⊤) :
    Dense (D.support.compl : Set X) :=
  D.support.compl.isOpen.dense (supportComplement_nonempty D hD)

/-- The actual source open of the complement isomorphism is nonempty for proper support. -/
theorem preimage_supportComplement_nonempty (hD : D.support ≠ ⊤) :
    (blowupStructure D ⁻¹ᵁ D.support.compl : Set (blowup D)).Nonempty := by
  let := blowupStructure_supportComplement_isIso D
  obtain ⟨y, hy⟩ := supportComplement_nonempty D hD
  obtain ⟨x, _⟩ := (blowupStructure D ∣_ D.support.compl).surjective ⟨y, hy⟩
  exact ⟨x.val, x.property⟩

/-- The actual source open of the complement isomorphism is dense in the integral blowup. -/
theorem preimage_supportComplement_dense (hD : D.support ≠ ⊤) :
    Dense (blowupStructure D ⁻¹ᵁ D.support.compl : Set (blowup D)) := by
  let := BlowupIntegral.isIntegral_blowup D hD
  exact (blowupStructure D ⁻¹ᵁ D.support.compl).isOpen.dense
    (preimage_supportComplement_nonempty D hD)

/-- The actual global blowup in a proper-support ideal is intrinsically birational over X,
via its genuine native complement partial isomorphism, with no finite-generation hypothesis. -/
theorem blowupStructure_birationalOver (hD : D.support ≠ ⊤) :
    Scheme.BirationalOver (blowupStructure D) (𝟙 X) := by
  let := blowupStructure_supportComplement_isIso D
  let e : (blowup D).PartialIso X :=
    { source := blowupStructure D ⁻¹ᵁ D.support.compl
      dense_source := preimage_supportComplement_dense D hD
      target := D.support.compl
      dense_target := supportComplement_dense D hD
      iso := asIso (blowupStructure D ∣_ D.support.compl) }
  refine ⟨e, ?_⟩
  change (blowupStructure D ∣_ D.support.compl) ≫
    (Scheme.Opens.ι (X := X) D.support.compl) ≫ 𝟙 X =
    (blowupStructure D ⁻¹ᵁ D.support.compl).ι ≫ blowupStructure D
  rw [Category.comp_id, morphismRestrict_ι]

end

end DeJongAlterations.Geometry.BlowupComplement

/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45F)
-/
import DeJongAlterations.StableModification.Global.Statements
import DeJongAlterations.StableModification.Gluing.MarksModel
import DeJongAlterations.StableModification.Gluing.MarksGeneric
import DeJongAlterations.StableModification.Gluing.SetupAssembly
import DeJongAlterations.StableModification.BlowDown.ContractionStein
import DeJongAlterations.StableModification.Curves.SemistableNormalScheme

/-!
# Uniqueness over a valuation ring: the setting

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), §4.5 and
Thm 1.2 over a valuation ring (T:3233–3266). This file collects the facts about the situation of
`Global.ValuationStableUniqueness` (`PLAN-T5.md` §2.2 step 11, node V3) that the uniqueness proof
uses and that are not stated elsewhere:

* `isIntegral_of_isEtaModification`, `isModification_of_isEtaModification`: the source of an
  η-modification of an integral flat curve over a valuation ring of finite height is integral
  (its generic fibre is a schematically dense integral open);
* `eq_of_isEtaModification`, `isSmoothAt_of_isEtaModification`: an η-modification is injective
  on the generic fibres and preserves smoothness there;
* `isNormalScheme_of_isEtaModification`: a nodal η-modification of a curve with
  smooth generic fibre is normal (lane SS's `isNormalScheme_of_isNodalCurve_spec`);
* `isSepClosed_fractionRing_quotient`, `isAlgClosed_residueField`, `infinite_residueField`: the
  residue fields of a valuation ring of an algebraically closed field.

Blueprint: `sm-gluing-uniqueness.tex`, `lem:sm-gu-setting`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.UniquenessVal

open DeJong (IsNodalCurve IsSmoothAt)

set_option backward.isDefEq.respectTransparency false

section Eta

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C X : Scheme.{u}} (φ : C ⟶ Spec (.of V))

local notation "G" => BlowDown.genericOpen V

/-- **The source of an η-modification is integral**: for `C` integral and flat over `V`, an
η-modification `β : X ⟶ C` with `β ≫ φ` flat has integral source. The generic fibre
`(β ≫ φ)⁻¹(η)` is isomorphic to the integral open `φ⁻¹(η)` of `C`, and it is schematically dense
in `X` (flat base change of the schematically dense generic point of `Spec V`). -/
theorem isIntegral_of_isEtaModification [IsIntegral C] [Flat φ] (β : X ⟶ C)
    (hβ : Curves.IsEtaModification β φ) [Flat (β ≫ φ)] : IsIntegral X := by
  have hiso := BlowDown.isIso_restrict_genericOpen φ β hβ
  have hgen : φ (genericPoint C) = genericPoint (Spec (.of V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact apply_genericPoint_eq_bot_of_flat φ
  have : Nonempty (φ ⁻¹ᵁ G).toScheme := ⟨⟨genericPoint C, hgen⟩⟩
  have : IsIntegral (φ ⁻¹ᵁ G).toScheme := isIntegral_of_isOpenImmersion (φ ⁻¹ᵁ G).ι
  have : Nonempty ((β ≫ φ) ⁻¹ᵁ G).toScheme :=
    ⟨inv (β ∣_ (φ ⁻¹ᵁ G)) (Nonempty.some inferInstance)⟩
  have : IsIntegral ((β ≫ φ) ⁻¹ᵁ G).toScheme :=
    isIntegral_of_isOpenImmersion (β ∣_ (φ ⁻¹ᵁ G))
  have hG : IsSchemeTheoreticallyDominant (G).ι :=
    Curves.isSchemeTheoreticallyDominant_ι_of_nonempty _ ⟨_, rfl⟩
  have : IsSchemeTheoreticallyDominant ((β ≫ φ) ⁻¹ᵁ G).ι :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (β ≫ φ) G)
  have : QuasiCompact ((β ≫ φ) ⁻¹ᵁ G).ι :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (isPullback_morphismRestrict (β ≫ φ) G) inferInstance
  exact DeJong.isIntegral_of_isSchemeTheoreticallyDominant ((β ≫ φ) ⁻¹ᵁ G).ι

/-- An η-modification of an integral flat curve over `V` with flat source is a modification. -/
theorem isModification_of_isEtaModification [IsIntegral C] [Flat φ] (β : X ⟶ C)
    (hβ : Curves.IsEtaModification β φ) [Flat (β ≫ φ)] : IsModification β := by
  have := isIntegral_of_isEtaModification φ β hβ
  exact hβ.toIsSchematicModification.isModification

/-- **An η-modification is injective on the generic fibre.** -/
theorem eq_of_isEtaModification (β : X ⟶ C) (hβ : Curves.IsEtaModification β φ) {x x' : X}
    (hx : (β ≫ φ) x = genericPoint (Spec (.of V))) (h : β x = β x') : x = x' := by
  have := BlowDown.isIso_restrict_genericOpen φ β hβ
  exact Gluing.StableVal.eq_of_isIso_restrict β (φ ⁻¹ᵁ G) h hx

/-- **An η-modification preserves smoothness over the generic point.** -/
theorem isSmoothAt_of_isEtaModification (β : X ⟶ C) (hβ : Curves.IsEtaModification β φ)
    (hC : ∀ c : C, φ c = genericPoint (Spec (.of V)) → IsSmoothAt φ c) (x : X)
    (hx : (β ≫ φ) x = genericPoint (Spec (.of V))) : IsSmoothAt (β ≫ φ) x := by
  have := BlowDown.isIso_restrict_genericOpen φ β hβ
  exact Gluing.StableVal.isSmoothAt_of_mem_isomorphismOpen β φ (V := φ ⁻¹ᵁ G) hx (hC _ hx)

/-- **A nodal η-modification of a curve with smooth generic fibre is normal** (lane SS's
`Curves.SemistableNormal.isNormalScheme_of_isNodalCurve_spec`: nodal over the integrally closed
`V` and smooth over the generic point). -/
theorem isNormalScheme_of_isEtaModification (β : X ⟶ C) (hβ : Curves.IsEtaModification β φ)
    [IsNodalCurve (β ≫ φ)]
    (hC : ∀ c : C, φ c = genericPoint (Spec (.of V)) → IsSmoothAt φ c) : IsNormalScheme X := by
  refine Curves.SemistableNormal.isNormalScheme_of_isNodalCurve_spec (β ≫ φ) fun x hx => ?_
  refine isSmoothAt_of_isEtaModification φ β hβ hC x ?_
  rw [genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext hx

end Eta

section Residue

variable {K : Type u} [Field K] [IsAlgClosed K] (W : ValuationSubring K)

/-- All `Frac(W/𝔭)` are separably closed (`Cohomology.Connected.isSepClosed_fractionRing_quotient`). -/
theorem isSepClosed_fractionRing_quotient (P : PrimeSpectrum W) :
    IsSepClosed (FractionRing (W ⧸ P.asIdeal)) :=
  Cohomology.Connected.isSepClosed_fractionRing_quotient K P

/-- All residue fields of `Spec W` are algebraically closed (lane T44A3's
`NoClosedExc.isAlgClosed_residueField_of_isAlgClosed`). -/
theorem isAlgClosed_residueField (s : Spec (.of W)) :
    IsAlgClosed ((Spec (.of W)).residueField s) := by
  have := BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed K s
  exact IsAlgClosed.of_ringEquiv _ _
    (Scheme.Spec.residueFieldIso (CommRingCat.of W) s).commRingCatIsoToRingEquiv.symm

/-- The residue field of `W` is algebraically closed. -/
theorem isAlgClosed_localResidueField : IsAlgClosed (IsLocalRing.ResidueField W) := by
  have := isAlgClosed_residueField W (IsLocalRing.closedPoint W)
  exact IsAlgClosed.of_ringEquiv _ _ (BlowDown.residueFieldClosedPointEquiv (V := W)).symm

/-- The residue field of `W` is infinite. -/
theorem infinite_residueField : Infinite (IsLocalRing.ResidueField W) := by
  have := isAlgClosed_localResidueField W
  infer_instance

end Residue

end DeJongAlterations.StableModification.Gluing.UniquenessVal

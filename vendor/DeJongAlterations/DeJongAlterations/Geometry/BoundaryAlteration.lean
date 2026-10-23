import DeJongAlterations.Geometry.BlowupCartier
import DeJongAlterations.Geometry.BlowupAlteration
import DeJongAlterations.Geometry.BlowupComplement

/-!
# A genuine global alteration carrying an exact Cartier boundary

The witnesses are the actual native blowup of the vanishing ideal, its
structure map, and the full pulled-back ideal. Relative projectivity is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.BoundaryAlteration

universe u

variable {X : Scheme.{u}}

open BlowupGluing

/-- The native vanishing ideal has exactly the prescribed closed support. -/
theorem vanishingIdeal_support (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-- A proper closed subset supplies an actual ideal with proper support. -/
theorem vanishingIdeal_support_ne_top (Z : Closeds X) (hZ : Z ≠ ⊤) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support ≠ ⊤ := by
  rw [vanishingIdeal_support]
  exact hZ

/-- The actual native blowup of the vanishing ideal is an alteration carrying
the full inverse-image ideal as an effective Cartier boundary. -/
theorem canonical_blowup_boundary [IsIntegral X] [IsLocallyNoetherian X]
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    IsAlteration (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)) ∧
      IsEffectiveCartierDivisor ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))) ∧
      ((Scheme.IdealSheafData.vanishingIdeal Z).comap
        (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z))).support =
          Z.preimage (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)).continuous := by
  exact ⟨BlowupAlteration.blowupStructure_isAlteration _
    (vanishingIdeal_support_ne_top Z hZ),
    BlowupCartier.vanishingIdeal_blowup_cartier Z⟩

/-- Every proper closed boundary on a locally Noetherian integral scheme has
an alteration whose exact inverse-image ideal is effective Cartier. -/
theorem exists_alteration_cartierPreimage [IsIntegral X] [IsLocallyNoetherian X]
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (E : Y.IdealSheafData),
      IsAlteration f ∧ IsEffectiveCartierDivisor E ∧ E.support = Z.preimage f.continuous := by
  exact ⟨blowup (Scheme.IdealSheafData.vanishingIdeal Z),
    blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z),
    (Scheme.IdealSheafData.vanishingIdeal Z).comap
      (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)),
    canonical_blowup_boundary Z hZ⟩

/-- A proper-support native blowup is étale on the actual inverse image of
the centre complement, which is a dense open of its actual source. -/
theorem blowupStructure_isGenericallyEtale [IsIntegral X] (D : X.IdealSheafData)
    (hD : D.support ≠ ⊤) : IsGenericallyEtale (blowupStructure D) := by
  let : IsIso (blowupStructure D ∣_ D.support.compl) :=
    BlowupComplement.blowupStructure_supportComplement_isIso D
  refine ⟨blowupStructure D ⁻¹ᵁ D.support.compl,
    BlowupComplement.preimage_supportComplement_dense D hD, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- The canonical boundary alteration is generically étale on the actual
inverse image of the complement of the prescribed closed subset. -/
theorem canonical_blowup_boundary_genericallyEtale [IsIntegral X]
    (Z : Closeds X) (hZ : Z ≠ ⊤) :
    IsGenericallyEtale (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)) :=
  blowupStructure_isGenericallyEtale _ (vanishingIdeal_support_ne_top Z hZ)

/-- The same actual blowup witnesses both the Cartier boundary and generic
étaleness, with no additional certificates in the hypotheses. -/
theorem exists_genericallyEtale_alteration_cartierPreimage
    [IsIntegral X] [IsLocallyNoetherian X] (Z : Closeds X) (hZ : Z ≠ ⊤) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (E : Y.IdealSheafData),
      IsAlteration f ∧ IsGenericallyEtale f ∧ IsEffectiveCartierDivisor E ∧
        E.support = Z.preimage f.continuous := by
  refine ⟨blowup (Scheme.IdealSheafData.vanishingIdeal Z),
    blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z),
    (Scheme.IdealSheafData.vanishingIdeal Z).comap
      (blowupStructure (Scheme.IdealSheafData.vanishingIdeal Z)), ?_⟩
  obtain ⟨hf, hE, hs⟩ := canonical_blowup_boundary Z hZ
  exact ⟨hf, canonical_blowup_boundary_genericallyEtale Z hZ, hE, hs⟩

end DeJongAlterations.Geometry.BoundaryAlteration

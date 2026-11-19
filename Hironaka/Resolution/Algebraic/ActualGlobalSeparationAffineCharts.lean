import Hironaka.Resolution.Algebraic.ActualGlobalDimensionClopenPartition
import Hironaka.Scheme.BlowUp.FlatBaseChange

/-!
# Genuine affine pullback charts of the actual global separation blowup

Source-first proof: `actual-global-separation-affine-charts-20261102.tex`.
The actual global ideal comparison derives the blowup squares and actual
normalized-ideal identities.  Native affine group-open identification and
global piece purity remain separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalSeparationAffineCharts

noncomputable section
open ActualGlobalDimensionClopenPartition ActualIntrinsicComponentDimensions

variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [IsReduced X] in
theorem separationProjection_isProper : IsProper (separationProjection X) :=
  blowUp.isProper_π _

abbrev chartSpace (U : X.affineOpens) : Scheme.{u} :=
  affineBlowUp (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))

include p in
private theorem exists_chartMap (U : X.affineOpens) :
    ∃ φ : chartSpace U ⟶ separationSpace X,
      IsPullback φ (affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)))
        (separationProjection X) U.2.fromSpec := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  apply (blowUp.isBlowUp (ActualGlobalDimensionSeparationIdeal.separationIdeal X)).exists_isPullback_of_flat
    U.2.fromSpec
  rw [ActualGlobalDimensionIdealAffineComparison.separationIdeal_open_spectrum Γ(X, U) p U.2.fromSpec]
  exact affineBlowUp.isBlowUp _

def chartMap (U : X.affineOpens) : chartSpace U ⟶ separationSpace X :=
  Classical.choose (exists_chartMap p U)

theorem chartMap_isPullback (U : X.affineOpens) :
    IsPullback (chartMap p U)
      (affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)))
      (separationProjection X) U.2.fromSpec :=
  Classical.choose_spec (exists_chartMap p U)

instance chartMap_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion (chartMap p U) :=
  property_of_isPullback @IsOpenImmersion (chartMap_isPullback p U) inferInstance

theorem chartMap_range (U : X.affineOpens) :
    Set.range (chartMap p U) = separationProjection X ⁻¹' (U.1 : Set X) := by
  ext b
  constructor
  · rintro ⟨b', rfl⟩
    have hpoint := congrArg (fun f : chartSpace U ⟶ X => f b') (chartMap_isPullback p U).w
    change separationProjection X (chartMap p U b') ∈ U.1
    have hmem : separationProjection X (chartMap p U b') ∈ Set.range U.2.fromSpec :=
      ⟨affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)) b', hpoint.symm⟩
    rw [U.2.range_fromSpec] at hmem
    exact hmem
  · intro hb
    obtain ⟨a, ha⟩ : separationProjection X b ∈ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      exact hb
    obtain ⟨b', hb', _⟩ := Scheme.exists_preimage_of_isPullback
      (chartMap_isPullback p U) b a ha.symm
    exact ⟨b', hb'⟩

theorem chartMap_cover : (⨆ U : X.affineOpens, (chartMap p U).opensRange) = ⊤ := by
  apply top_le_iff.mp
  intro b _
  obtain ⟨U, hU⟩ := Scheme.IdealSheafData.exists_affineOpens_mem (separationProjection X b)
  apply Opens.mem_iSup.mpr
  refine ⟨U, ?_⟩
  change b ∈ Set.range (chartMap p U)
  rw [chartMap_range]
  exact hU

omit [IsReduced X] in
include p in
theorem complementaryIdeal_chart (U : X.affineOpens) (d : WithBot ℕ∞) :
    (complementaryIdeal X d).comap U.2.fromSpec =
      Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf Γ(X, U)
        (ActualGlobalDimensionIdealAffineComparison.dimensionComplement Γ(X, U) d) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [complementaryIdeal, Hironaka.Smooth.comap_vanishingIdeal_of_smooth,
    ActualGlobalDimensionSeparationIdeal.complementaryClosed_preimage p U.2.fromSpec,
    ActualGlobalDimensionIdealAffineComparison.complementaryIdeal_spec]

theorem exceptionalIdeal_chart (U : X.affineOpens) :
    (exceptionalIdeal X).comap (chartMap p U) =
      (Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf Γ(X, U)
        (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))).comap
          (affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [exceptionalIdeal, ← comap_comp, (chartMap_isPullback p U).w, comap_comp,
    ActualGlobalDimensionIdealAffineComparison.separationIdeal_open_spectrum Γ(X, U) p U.2.fromSpec]

def affineNormalizedIdeal (U : X.affineOpens) (d : WithBot ℕ∞) : (chartSpace U).IdealSheafData :=
  ((Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf Γ(X, U)
      (ActualGlobalDimensionIdealAffineComparison.dimensionComplement Γ(X, U) d)).comap
        (affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U)))).colon
    ((Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf Γ(X, U)
      (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))).comap
        (affineBlowUp.π (ActualDimensionGroupBlowup.dimensionSeparationIdeal Γ(X, U))))

theorem normalizedIdeal_chart (U : X.affineOpens) (d : dimensionIndex X) :
    (normalizedIdeal X d).comap (chartMap p U) = affineNormalizedIdeal U d.val := by
  rw [normalizedIdeal_flat_pullback]
  rw [← comap_comp, (chartMap_isPullback p U).w, comap_comp,
    complementaryIdeal_chart p U d.val, exceptionalIdeal_chart]
  rfl

theorem dimensionPartOpen_chart (U : X.affineOpens) (d : dimensionIndex X) :
    chartMap p U ⁻¹ᵁ dimensionPartOpen X d =
      ⟨((affineNormalizedIdeal U d.val).support : Set (chartSpace U))ᶜ,
        (affineNormalizedIdeal U d.val).support.isClosed.isOpen_compl⟩ := by
  ext b
  change chartMap p U b ∉ (normalizedIdeal X d).support ↔
    b ∉ (affineNormalizedIdeal U d.val).support
  have hs := congrArg Scheme.IdealSheafData.support (normalizedIdeal_chart p U d)
  rw [support_comap] at hs
  apply not_congr
  change b ∈ ((normalizedIdeal X d).support).preimage (chartMap p U).continuous ↔
    b ∈ (affineNormalizedIdeal U d.val).support
  rw [hs]

end
end Hironaka.Resolution.Algebraic.ActualGlobalSeparationAffineCharts

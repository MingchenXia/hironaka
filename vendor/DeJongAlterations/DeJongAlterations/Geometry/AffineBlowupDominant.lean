import DeJongAlterations.Geometry.AffineBlowupChart

/-!
# Dominance and surjectivity of the native affine blowup

A nonzero ideal in a domain has a genuine nonzero-generator chart, whose
coefficient map embeds in the original fraction field. This proves dominance
without finite generation. Properness gives surjectivity for finitely
generated ideals.
-/

open CategoryTheory AlgebraicGeometry

namespace DeJongAlterations

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The fraction-chart coefficient map is injective through the original fraction field. -/
theorem affineBlowupFractionChart_algebraMap_injective (I : Ideal R) (g : R) :
    Function.Injective (algebraMap R (affineBlowupFractionChart I g)) := by
  intro a b hab
  apply IsFractionRing.injective R (FractionRing R)
  exact congrArg (fun x : affineBlowupFractionChart I g ↦ (x : FractionRing R)) hab

/-- A genuine nonzero-generator chart has dominant composition with the structure map. -/
theorem affineBlowupChartInclusion_comp_isDominant (I : Ideal R) (g : R)
    (hg : g ∈ I) (hg0 : g ≠ 0) :
    IsDominant (affineBlowupChartInclusion I g hg hg0 ≫ affineBlowupStructure I) := by
  rw [affineBlowupChartInclusion_structure]
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap R (affineBlowupFractionChart I g)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro a ha
  change algebraMap R (affineBlowupFractionChart I g) a = 0 at ha
  have ha0 : a = 0 := affineBlowupFractionChart_algebraMap_injective I g
    (by simpa only [map_zero] using ha)
  rw [ha0]
  exact Ideal.zero_mem _

/-- A nonzero ideal produces a dominant native blowup without a finiteness hypothesis. -/
theorem affineBlowupStructure_isDominant (I : Ideal R) (hI : I ≠ ⊥) :
    IsDominant (affineBlowupStructure I) := by
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra! hzero
    apply hI
    apply le_antisymm
    · intro a ha
      change a = 0
      exact hzero a ha
    · exact bot_le
  let := affineBlowupChartInclusion_comp_isDominant I g hg hg0
  exact IsDominant.of_comp (affineBlowupChartInclusion I g hg hg0) (affineBlowupStructure I)

/-- Finite generation adds properness, turning the dense blowup image into the whole base. -/
theorem affineBlowupStructure_surjective (I : Ideal R) (hI : I ≠ ⊥) (hfg : I.FG) :
    Function.Surjective (affineBlowupStructure I) := by
  let := affineBlowupStructure_isProper I hfg
  let := affineBlowupStructure_isDominant I hI
  exact (affineBlowupStructure I).surjective

end DeJongAlterations

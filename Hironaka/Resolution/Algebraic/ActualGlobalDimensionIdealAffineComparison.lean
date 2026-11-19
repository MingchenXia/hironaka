import Hironaka.Resolution.Algebraic.ActualGlobalDimensionSeparationIdeal
import Hironaka.Resolution.Algebraic.ActualDimensionGroupBlowup
import Hironaka.Geometry.ReducedClosedSubscheme

/-!
# Actual global dimension ideal in the original affine coordinates

Source-first proof: `actual-global-dimension-ideal-affine-comparison-20261102.tex`.
Actual quotient spectra identify intrinsic dimensions and reduced component
ideals.  This derives the global centre's exact equality with the frozen
affine dimension-separation centre on every actual open affine chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalDimensionIdealAffineComparison

noncomputable section
open ActualIntrinsicComponentDimensions

variable (R : Type u) [CommRing R]

def primeComponent (p : minimalPrimes R) : irreducibleComponents (Spec (.of R)) :=
  ⟨PrimeSpectrum.zeroLocus (p.val : Set R),
    by
      apply PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      rw [p.property.1.1.isRadical.radical]
      exact p.property⟩

theorem primeComponent_surjective (C : irreducibleComponents (Spec (.of R))) :
    ∃ p : minimalPrimes R, primeComponent R p = C := by
  have hC := C.property
  change C.val ∈ irreducibleComponents (PrimeSpectrum R) at hC
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes R] at hC
  obtain ⟨p, hp, hC⟩ := hC
  exact ⟨⟨p, hp⟩, Subtype.ext hC⟩

theorem primeComponent_dimension (p : minimalPrimes R) :
    componentDimension (primeComponent R p) = ActualDimensionGroupBlowup.componentDimension R p := by
  let f := Ideal.Quotient.mk p.val
  have hrange : Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (p.val : Set R) := by
    rw [range_comap_of_surjective (R ⧸ p.val) f Ideal.Quotient.mk_surjective]
    simp only [f, Ideal.mk_ker]
  let e : PrimeSpectrum (R ⧸ p.val) ≃ₜ PrimeSpectrum.zeroLocus (p.val : Set R) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ p.val) f
      Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans (.setCongr hrange)
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm.trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R ⧸ p.val))

theorem componentIdeal_prime (p : minimalPrimes R) :
    componentIdeal (primeComponent R p) = Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val := by
  have hs : (Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val).support = componentClosed (primeComponent R p) := by
    apply Closeds.ext
    exact Hironaka.Geometry.ReducedClosedSubscheme.specIdealSheaf_support R p.val
  have hr : (Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val).radical = Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val := by
    rw [Hironaka.Geometry.ReducedClosedSubscheme.specIdealSheaf_radical, p.property.1.1.isRadical.radical]
  calc
    componentIdeal (primeComponent R p) =
        Scheme.IdealSheafData.vanishingIdeal (Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val).support :=
      congrArg Scheme.IdealSheafData.vanishingIdeal hs.symm
    _ = (Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val).radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R p.val := hr

theorem dimension_ranges_eq :
    Set.range (componentDimension (X := Spec (.of R))) = Set.range (ActualDimensionGroupBlowup.componentDimension R) := by
  ext d
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨p, rfl⟩ := primeComponent_surjective R C
    exact ⟨p, (primeComponent_dimension R p).symm.trans hC⟩
  · rintro ⟨p, hp⟩
    exact ⟨primeComponent R p, (primeComponent_dimension R p).trans hp⟩

def dimensionComplement (d : WithBot ℕ∞) : Ideal R :=
  ⨅ p : minimalPrimes R, ⨅ (_ : ActualDimensionGroupBlowup.componentDimension R p ≠ d), p.val

private theorem complementaryClosed_eq_iSup [IsNoetherianRing R] (d : WithBot ℕ∞) :
    ActualGlobalDimensionSeparationIdeal.complementaryClosed (Spec (.of R)) d =
      ⨆ p : minimalPrimes R, ⨆ (_ : ActualDimensionGroupBlowup.componentDimension R p ≠ d),
        componentClosed (primeComponent R p) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨C, hC, hx⟩ := (ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed _ d x).mp hx
    obtain ⟨p, rfl⟩ := primeComponent_surjective R C
    have hp : ActualDimensionGroupBlowup.componentDimension R p ≠ d := by
      simpa only [primeComponent_dimension] using hC
    have hle : componentClosed (primeComponent R p) ≤
        ⨆ q : minimalPrimes R, ⨆ (_ : ActualDimensionGroupBlowup.componentDimension R q ≠ d),
          componentClosed (primeComponent R q) :=
      le_iSup_of_le p (le_iSup_of_le hp le_rfl)
    exact hle hx
  · refine iSup_le fun p => iSup_le fun hp => ?_
    intro x hx
    apply (ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed _ d x).mpr
    refine ⟨primeComponent R p, ?_, hx⟩
    simpa only [primeComponent_dimension] using hp

theorem complementaryIdeal_spec [IsNoetherianRing R] (d : WithBot ℕ∞) :
    Scheme.IdealSheafData.vanishingIdeal (ActualGlobalDimensionSeparationIdeal.complementaryClosed (Spec (.of R)) d) =
      Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (dimensionComplement R d) := by
  rw [complementaryClosed_eq_iSup]
  simp only [Scheme.IdealSheafData.vanishingIdeal_iSup]
  change (⨅ p : minimalPrimes R, ⨅ (_ : ActualDimensionGroupBlowup.componentDimension R p ≠ d),
    componentIdeal (primeComponent R p)) = _
  simp only [componentIdeal_prime, dimensionComplement, Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf, OrderIso.map_iInf]

theorem dimensionComplement_eq_native (d : ActualDimensionGroupBlowup.dimensionIndex R) :
    dimensionComplement R d.val = ActualDimensionGroupBlowup.complementIdeal R (ActualDimensionGroupBlowup.dimensionGroupIdeal R) d := by
  ext x
  simp only [dimensionComplement, ActualDimensionGroupBlowup.complementIdeal, ActualDimensionGroupBlowup.dimensionGroupIdeal, Ideal.mem_iInf]
  constructor
  · intro hx e hed p hpe
    apply hx p
    exact fun hpd => hed (Subtype.ext (hpe.symm.trans hpd))
  · intro hx p hpd
    let e : ActualDimensionGroupBlowup.dimensionIndex R := ⟨ActualDimensionGroupBlowup.componentDimension R p, ⟨p, rfl⟩⟩
    have hed : e ≠ d := fun h => hpd (congrArg Subtype.val h)
    exact hx e hed p rfl

theorem complementaryIdeal_native [IsNoetherianRing R] (d : ActualDimensionGroupBlowup.dimensionIndex R) :
    Scheme.IdealSheafData.vanishingIdeal (ActualGlobalDimensionSeparationIdeal.complementaryClosed (Spec (.of R)) d.val) =
      Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (ActualDimensionGroupBlowup.complementIdeal R (ActualDimensionGroupBlowup.dimensionGroupIdeal R) d) := by
  rw [complementaryIdeal_spec, dimensionComplement_eq_native]

theorem separationIdeal_spec [IsNoetherianRing R] [IsReduced R] :
    ActualGlobalDimensionSeparationIdeal.separationIdeal (Spec (.of R)) =
      Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (ActualDimensionGroupBlowup.dimensionSeparationIdeal R) := by
  rw [ActualGlobalDimensionSeparationIdeal.separationIdeal_eq_finite_sum]
  have hsum : Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (ActualDimensionGroupBlowup.dimensionSeparationIdeal R) =
      ⨆ d : ActualDimensionGroupBlowup.dimensionIndex R,
        Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (ActualDimensionGroupBlowup.complementIdeal R (ActualDimensionGroupBlowup.dimensionGroupIdeal R) d) := by
    exact (Hironaka.Geometry.SpecIdealSheaf.specIdealSheafEquiv R).symm.map_iSup _
  rw [hsum]
  apply le_antisymm
  · refine iSup_le fun d => ?_
    let e : ActualDimensionGroupBlowup.dimensionIndex R := ⟨d.val, (dimension_ranges_eq R) ▸ d.property⟩
    exact le_iSup_of_le e (le_of_eq (complementaryIdeal_native R e))
  · refine iSup_le fun d => ?_
    let e : dimensionIndex (Spec (.of R)) := ⟨d.val, (dimension_ranges_eq R).symm ▸ d.property⟩
    exact le_iSup_of_le e (le_of_eq (complementaryIdeal_native R d).symm)

theorem separationIdeal_open_spectrum [IsNoetherianRing R] [IsReduced R]
    {X : Scheme.{u}} [NoetherianSpace X] {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] :
    (ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap j = Hironaka.Geometry.SpecIdealSheaf.specIdealSheaf R (ActualDimensionGroupBlowup.dimensionSeparationIdeal R) := by
  rw [ActualGlobalDimensionSeparationIdeal.separationIdeal_open p j, separationIdeal_spec]

end
end Hironaka.Resolution.Algebraic.ActualGlobalDimensionIdealAffineComparison

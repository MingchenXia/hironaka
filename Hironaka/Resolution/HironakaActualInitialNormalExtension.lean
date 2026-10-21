/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHomogeneousInitialHS
import Mathlib.RingTheory.MvPowerSeries.Rename
import Hironaka.Resolution.HironakaActualInitialPolynomialContraction
import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives
import Hironaka.Resolution.HironakaDifferentialStableCylindricalIdeal

set_option autoImplicit false
open Set Filter Classical
namespace Hironaka.HironakaActualInitialNormalExtension
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaActualOriginalTaylorPolynomial
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalInitialDiagram
  HironakaActualHomogeneousInitialHS HironakaActualOriginalTaylorDerivatives
  HironakaActualFirstSymbolTangentClosure HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticVertexBasis
  Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreRealDomainOriginalStalkFreeness
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations

open HironakaActualInitialPolynomialContraction HironakaDifferentialStableCylindricalIdeal

/-- The actual normal-block polynomial and series embeddings form a genuine ring-hom commuting square. -/
theorem polynomialSeries_normalRename_square (d t : ℕ) :
    (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin (d+t)) ℂ →+*
      MvPowerSeries (Fin (d+t)) ℂ).comp
        (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom =
      (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t)) :
        MvPowerSeries (Fin t) ℂ →ₐ[ℂ] MvPowerSeries (Fin (d+t)) ℂ).toRingHom.comp
          MvPolynomial.coeToMvPowerSeries.ringHom := by
  apply RingHom.ext
  intro P
  exact (MvPowerSeries.rename_coe (Fin.natAdd d) P).symm

/-- BOTH whole normal polynomial extensions are the SAME actual formal ideal under the literal rename square. -/
theorem polynomialSeries_normalExtension_map (d t : ℕ)
    (L : Ideal (MvPolynomial (Fin t) ℂ)) :
    Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom
      (Ideal.map (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom L) =
      Ideal.map (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
        (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom L) := by
  rw [Ideal.map_map, Ideal.map_map, polynomialSeries_normalRename_square]

/-- Literal polynomial tangent stability of the SAME actual initial ideal implies its entire formal normal contraction-extension equality. -/
theorem actualHomogeneousInitialIdeal_eq_normal_extension_of_tangent_pderiv (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hD : ∀ (i : Fin d) (P : MvPolynomial (Fin (d+t)) ℂ),
      (P : MvPowerSeries (Fin (d+t)) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv (i.castAdd t) P : MvPowerSeries (Fin (d+t)) ℂ) ∈ actualHomogeneousInitialIdeal K) :
    actualHomogeneousInitialIdeal K =
      Ideal.map (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
        (Ideal.comap (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
          (actualHomogeneousInitialIdeal K)) := by
  let J := actualHomogeneousInitialIdeal K
  let ι : MvPolynomial (Fin (d+t)) ℂ →+* MvPowerSeries (Fin (d+t)) ℂ :=
    MvPolynomial.coeToMvPowerSeries.ringHom
  let ιt : MvPolynomial (Fin t) ℂ →+* MvPowerSeries (Fin t) ℂ :=
    MvPolynomial.coeToMvPowerSeries.ringHom
  let ν : MvPolynomial (Fin t) ℂ →+* MvPolynomial (Fin (d+t)) ℂ := (MvPolynomial.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
  let ρ := (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t)) :
    MvPowerSeries (Fin t) ℂ →ₐ[ℂ] MvPowerSeries (Fin (d+t)) ℂ).toRingHom
  let C := Ideal.comap ι J
  have hC : C = Ideal.map ν (Ideal.comap ν C) :=
    ideal_eq_normal_extension_of_tangent_pderiv_stable d t C (by
      intro i P hP
      exact hD i P hP)
  have hJ : J = Ideal.map ι C := actualHomogeneousInitialIdeal_eq_map_polynomial_comap K
  have he : J = Ideal.map ρ (Ideal.map ιt (Ideal.comap ν C)) := by
    calc J = Ideal.map ι C := hJ
         _ = Ideal.map ι (Ideal.map ν (Ideal.comap ν C)) := congrArg (Ideal.map ι) hC
         _ = Ideal.map ρ (Ideal.map ιt (Ideal.comap ν C)) := polynomialSeries_normalExtension_map d t _
  have hg := Ideal.map_comap_map (I := Ideal.map ιt (Ideal.comap ν C)) (f := ρ)
  rw [← he] at hg
  exact hg.symm

section OriginalCentre
open scoped Topology Manifold ContDiff
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original HSconstant centre geometry gives the SAME whole origin initial cone as its literal formal normal contraction-extension. -/
theorem exists_original_hs_constant_centre_initial_normal_extension
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i, DifferentiableOn ℂ (H i) U) ∧
        ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
          (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
              translatedIdeal H p (hhol p hp)) ∧
          let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) 0)
          let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
          actualHomogeneousInitialIdeal K0 =
            Ideal.map (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
              (Ideal.comap (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
                (actualHomogeneousInitialIdeal K0)) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hformal, hPolynomial⟩ :=
    HironakaActualHomogeneousInitialTangentDerivatives.exists_original_hs_constant_centre_initial_tangent_pderiv
      C x hreg A hA hhs
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  exact actualHomogeneousInitialIdeal_eq_normal_extension_of_tangent_pderiv d t _ hPolynomial

end OriginalCentre
end
end Hironaka.HironakaActualInitialNormalExtension

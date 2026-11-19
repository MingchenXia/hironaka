import Hironaka.Geometry.CurveFibrationBaseChangeBoundaryGenericallyEtale

/-!
# The full actual boundary-fibration transport in de Jong 4.15

The SAME whole reduced pullback and original projections retain all
projective/fibre and boundary conditions supplied by the paper. No
replacement model, generic-integrality or component-output certificate.
This is a transport theorem; the original fibration hypotheses are inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}}

/-- Source 4.15: transport the actual full boundary-fibration data to the SAME whole reduction. -/
theorem wholeReduction_with_boundary_of_paper_fibres [IsIntegral X] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (hpS : IsProjectiveOver p)
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hpX : IsProjectiveOver (f ≫ p))
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤)
    [IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f)]
    (hDGE : IsGenericallyEtale (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f))
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support)
    (g : Y ⟶ S) [hg : IsAlteration g] (hgEt : IsGenericallyEtale g)
    {n : ℕ} (e : Y ⟶ relativeSpace S n) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S n = g) :
    letI : IsProper p := hpS.isProper
    letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    letI : IsIntegral Y := hg.sourceIntegral
    let q := reductionι f g ≫ pullback.snd f g
    let φ := reductionι f g ≫ pullback.fst f g
    let E := D.comap φ
    (IsIntegral (reducedPullback f g) ∧
      IsVariety (q ≫ g ≫ p) ∧ IsProjectiveOver (q ≫ g ≫ p) ∧
      IsVariety (g ≫ p) ∧ IsProjectiveOver (g ≫ p) ∧
      IsAlteration φ ∧ IsGenericallyEtale φ ∧ GeometricallyConnected q ∧
      (∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) → topologicalKrullDim C = 1) ∧
      (∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y),
        Dense ((pullback.fst q a) ⁻¹' (q.smoothLocus : Set (reducedPullback f g)))) ∧
      Smooth (q.fiberToSpecResidueField (genericPoint Y)) ∧ IsProper q ∧
      (∃ (m : ℕ) (j : reducedPullback f g ⟶ relativeSpace Y m),
        IsClosedImmersion j ∧ j ≫ relativeStructure Y m = q) ∧
      IsClosedImmersion (reductionProjectiveEmbedding f g e he) ∧
      reductionProjectiveEmbedding f g e he ≫ relativeStructure X n = φ ∧
      φ ≫ f = q ≫ g) ∧
      IsEffectiveCartierDivisor E ∧ E.support ≠ ⊤ ∧
      E.support = D.support.preimage φ.continuous ∧
      IsReduced E.radical.subscheme ∧ E.radical.support = D.support.preimage φ.continuous ∧
      IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion E ≫ q) ∧
      IsGenericallyEtale (CartierBoundaryDominance.reducedBoundaryInclusion E ≫ q) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y)
        (C : Set (pullback q a : Scheme.{u})),
        C ∈ irreducibleComponents (pullback q a : Scheme.{u}) →
        ∃ v : Fin 3 → (pullback q a : Scheme.{u}), Function.Injective v ∧ ∀ i,
          v i ∈ C ∧ pullback.fst q a (v i) ∈ q.smoothLocus ∧
            pullback.fst q a (v i) ∈ E.support) := by
  let : IsProper p := hpS.isProper
  let : IsProper (f ≫ p) := hpX.isProper
  let : IsProper f := IsProper.of_comp f p
  let : IsVariety p := .mk
  let : IsVariety (f ≫ p) := .mk
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsIntegral Y := hg.sourceIntegral
  have hdata := wholeReduction_fibration_data_of_paper_fibres p hpS f hpX hsm hd g hgEt e he
  have hboundary := wholeReduction_cartierBoundary_of_paper_fibres f g hsm D hD hproper
  exact ⟨hdata, hboundary.1, hboundary.2.1, hboundary.2.2.1,
    hboundary.2.2.2.1, hboundary.2.2.2.2, reducedBoundary_isFinite f g D,
    reducedBoundary_isGenericallyEtale_of_paper_fibres p f hsm hd g D hD hDGE,
    reducedSecond_three_geometric_points f g D hthree⟩

end Hironaka.Geometry.CurveFibrationBaseChange

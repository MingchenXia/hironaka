import Hironaka.Geometry.CurveFibrationBaseChangeFullModel
import Hironaka.Geometry.CurveFibrationBaseChangeDensity

/-!
# The full actual4.15 transport from original native-fibre smooth density

No all-field density is supplied: it is derived internally from every
ORIGINAL native residue fibre by the universally open field coefficient map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}}

/-- Source4.15 full transport with density assumed only on the ORIGINAL native residue fibres. -/
theorem wholeReduction_with_boundary_of_native_fibre_density [IsIntegral X] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (hpS : IsProjectiveOver p)
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hpX : IsProjectiveOver (f ≫ p))
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ s : S, Dense ((f.fiberι s) ⁻¹' (f.smoothLocus : Set X)))
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
  exact wholeReduction_with_boundary_of_paper_fibres p hpS f hpX
    (fun _ _ a => original_smoothLocus_fieldFiber_dense f hsm a) hd
    D hD hproper hDGE hthree g hgEt e he

end Hironaka.Geometry.CurveFibrationBaseChange

import Hironaka.Geometry.CurveFibrationBaseChangeModel
import Hironaka.Geometry.CurveFibrationBaseChangeGenericIntegrality

/-!
# The actual whole-reduction model from the original paper fibre hypotheses

Generic geometric integrality is derived internally from properness,
all-fibre geometric connectedness, and original generic smoothness.
Every conclusion concerns the same whole actual reduction and projections.
Boundary finite generic etaleness and the three-point condition are separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}}

/-- The actual full fibration-data package from the original projective and fibre hypotheses. -/
theorem wholeReduction_fibration_data_of_paper_fibres [IsIntegral X] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (hpS : IsProjectiveOver p)
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hpX : IsProjectiveOver (f ≫ p))
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (g : Y ⟶ S) [hg : IsAlteration g] (hgEt : IsGenericallyEtale g)
    {n : ℕ} (e : Y ⟶ relativeSpace S n) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S n = g) :
    letI : IsProper p := hpS.isProper
    letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    letI : IsIntegral Y := hg.sourceIntegral
    let q := reductionι f g ≫ pullback.snd f g
    let φ := reductionι f g ≫ pullback.fst f g
    IsIntegral (reducedPullback f g) ∧
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
      φ ≫ f = q ≫ g := by
  let : IsProper p := hpS.isProper
  let : IsProper (f ≫ p) := hpX.isProper
  let : IsProper f := IsProper.of_comp f p
  exact wholeReduction_fibration_data p hpS f hpX
    (genericFiber_geometricallyIntegral_of_paper_fibres f) hsm hd g hgEt e he

/-- The same actual full Cartier boundary transport, with generic GI derived from the paper fibres. -/
theorem wholeReduction_cartierBoundary_of_paper_fibres [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsProper f]
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (g : Y ⟶ S) [IsAlteration g]
    (hsm : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)))
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤) :
    let φ := reductionι f g ≫ pullback.fst f g
    let E := D.comap φ
    IsEffectiveCartierDivisor E ∧ E.support ≠ ⊤ ∧
      E.support = D.support.preimage φ.continuous ∧
      IsReduced E.radical.subscheme ∧ E.radical.support = D.support.preimage φ.continuous :=
  wholeReduction_cartierBoundary f g (genericFiber_geometricallyIntegral_of_paper_fibres f)
    hsm D hD hproper

end Hironaka.Geometry.CurveFibrationBaseChange

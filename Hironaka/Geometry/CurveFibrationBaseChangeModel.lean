import Hironaka.Geometry.CurveFibrationBaseChangeProjective
import Hironaka.Geometry.CurveFibrationBaseChangeSmooth
import Hironaka.Geometry.CurveFibrationBaseChangeFibers
import Hironaka.Geometry.CartierDominantPullback

/-!
# The actual whole-reduction fibration-data consumer in source 4.15

All conclusions concern the SAME actual whole reduction and its original
projections. The original all-field smooth-density hypothesis is retained.
Original generic geometric integrality is explicit and is supplied by
the preceding genuine Stein-factor producer; no universal implication
from the other fibre hypotheses is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}}

/-- The same actual whole-reduction model retains the original projective and all-fibre data. -/
theorem wholeReduction_fibration_data [IsIntegral X] [IsIntegral S]
    (p : S ⟶ Spec (.of k)) (hpS : IsProjectiveOver p)
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hpX : IsProjectiveOver (f ≫ p))
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
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
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsIntegral Y := hg.sourceIntegral
  let : IsProper (f ≫ p) := hpX.isProper
  let : IsProper f := IsProper.of_comp f p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  let q := reductionι f g ≫ pullback.snd f g
  let φ := reductionι f g ≫ pullback.fst f g
  let : IsIntegral (reducedPullback f g) := reducedPullback_isIntegral f hη hsm g
  let : IsAlteration φ := reduction_first_isAlteration f g hη hsm
  have hq : IsProjectiveOver (q ≫ g ≫ p) := by
    have H := reducedFirst_comp_isProjective f g (f ≫ p) hpX e he
    have hw : φ ≫ (f ≫ p) = q ≫ g ≫ p := by
      rw [← Category.assoc, reductionι_triangle f g, Category.assoc]
    rwa [hw] at H
  have hy : IsProjectiveOver (g ≫ p) := by
    simpa only [← Category.assoc, he] using closed_into_relativeSpace_isProjective p hpS e
  let : IsProper (q ≫ g ≫ p) := hq.isProper
  let : IsProper (g ≫ p) := hy.isProper
  have hvT : IsVariety (q ≫ g ≫ p) := ⟨⟩
  have hvY : IsVariety (g ≫ p) := ⟨⟩
  let : IsProper q := by dsimp [q]; infer_instance
  obtain ⟨m, j, hj, hjf⟩ := exists_relativeEmbedding_of_isProjective p f hpX
  let := hj
  refine ⟨inferInstance, hvT, hq, hvY, hy, inferInstance,
    reduction_first_isGenericallyEtale f g hη hsm hgEt,
    reducedSecond_geometricallyConnected f g, ?_, ?_,
    reducedSecond_genericFiber_smooth f g, inferInstance,
    ⟨m, reducedSecondProjectiveEmbedding f g j hjf, inferInstance, by simp⟩,
    inferInstance, by simp, reductionι_triangle f g⟩
  · intro K _ a C hC
    exact reducedSecond_fieldFiber_components_dimension f g 1 hd a C hC
  · intro K _ a
    exact reducedSecond_smoothLocus_fieldFiber_dense f hsm g a

/-- The original full Cartier boundary, its actual reduced support and properness all survive. -/
theorem wholeReduction_cartierBoundary [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsDominant f]
    (g : Y ⟶ S) [hg : IsAlteration g]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)))
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D) (hproper : D.support ≠ ⊤) :
    let φ := reductionι f g ≫ pullback.fst f g
    let E := D.comap φ
    IsEffectiveCartierDivisor E ∧ E.support ≠ ⊤ ∧
      E.support = D.support.preimage φ.continuous ∧
      IsReduced E.radical.subscheme ∧ E.radical.support = D.support.preimage φ.continuous := by
  let : IsIntegral Y := hg.sourceIntegral
  let : IsIntegral (reducedPullback f g) := reducedPullback_isIntegral f hη hsm g
  let φ := reductionι f g ≫ pullback.fst f g
  let : IsAlteration φ := reduction_first_isAlteration f g hη hsm
  let E := D.comap φ
  have hdset : (D.support : Set X) ≠ Set.univ := by
    intro h
    apply hproper
    exact SetLike.coe_injective h
  have hE : E.support ≠ ⊤ := by
    intro h
    apply IsAlteration.preimage_ne_univ φ hdset
    have H := congrArg (fun Z : Closeds (reducedPullback f g) => (Z : Set (reducedPullback f g))) h
    change ((D.comap φ).support : Set (reducedPullback f g)) = Set.univ at H
    simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Closeds.coe_top] using H
  exact ⟨CartierDominantPullback.isEffectiveCartierDivisor_comap φ D hD, hE,
    Scheme.IdealSheafData.support_comap D φ,
    ReducedClosedSubscheme.isReduced_radical_subscheme E,
    (Scheme.IdealSheafData.support_radical E).trans (Scheme.IdealSheafData.support_comap D φ)⟩

end Hironaka.Geometry.CurveFibrationBaseChange

import Hironaka.Geometry.CartierBoundaryFiniteBaseChange
import Hironaka.Geometry.AlterationDominatingBaseChange

/-!
# Internally construct the actual altered model and prove its nonflat boundary dominance

The native reduced component is chosen internally above both original
generic points. Its actual projections retain the original Cartesian
triangle. Finiteness, original dimensions, Cartier pullback and all
new boundary-component dominance are derived for this same object.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundaryDominance

open CartierBoundaryComponentDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}} [IsIntegral Y]

/-- A genuine native dominant base-change component internally has finite Cartier boundary
with every actual component dominating the new base. No post-base-change output certificate
or flatness is assumed. This proves the dominance step, not the entire source 4.16 splitting. -/
theorem exists_finite_baseChange_model_boundary_dominant
    (p : S ⟶ Spec (.of k)) [IsVariety p] (f : X ⟶ S) [IsVariety (f ≫ p)] [IsDominant f]
    (hgen : topologicalKrullDim (f.fiber (genericPoint S)) = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (g : Y ⟶ S) [IsFinite g] [IsDominant g] :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsDominant (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧
      IsEffectiveCartierDivisor (D.comap (j ≫ pullback.fst f g)) ∧
      IsFinite (reducedBoundaryInclusion (D.comap (j ≫ pullback.fst f g)) ≫
        (j ≫ pullback.snd f g)) ∧
      ∀ C : DivisorComponent (D.comap (j ≫ pullback.fst f g)),
        IsDominant (componentInclusion (D.comap (j ≫ pullback.fst f g)) C ≫
          (j ≫ pullback.snd f g)) := by
  obtain ⟨T, j, hT, hj, hcomponent, hq, hb⟩ :=
    AlterationDominatingBaseChange.exists_dominating_reduced_component f g
  let := hT
  let := hj
  let := hq
  let := hb
  let q := j ≫ pullback.fst f g
  let b := j ≫ pullback.snd f g
  let : IsFinite q := by dsimp only [q]; infer_instance
  let : IsVariety (g ≫ p) := .mk
  let : IsVariety (q ≫ (f ≫ p)) := .mk
  have htriangle : b ≫ (g ≫ p) = q ≫ (f ≫ p) := by
    dsimp only [b, q]
    simp only [Category.assoc, pullback.condition_assoc]
  let : IsVariety (b ≫ (g ≫ p)) := by
    rw [htriangle]
    infer_instance
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  have hXdim := VarietyFunctionFieldDimension.dimension_eq_base_add_one p f hgen
  have hTdim := VarietyFunctionFieldDimension.dimension_eq_of_isFinite (f ≫ p) q
  have hYdim := VarietyFunctionFieldDimension.dimension_eq_of_isFinite p g
  have hdim : topologicalKrullDim T = topologicalKrullDim Y + 1 := by
    rw [hTdim, hYdim]
    exact hXdim
  have hcartier : IsEffectiveCartierDivisor (D.comap q) :=
    CartierDominantPullback.isEffectiveCartierDivisor_comap q D hD
  let : IsFinite (reducedBoundaryInclusion (D.comap q) ≫ b) :=
    reducedBoundary_isFinite_of_closed_baseChange f g D j
  refine ⟨T, j, hT, hj, hcomponent, hq, hb, isAlteration_of_isFinite q, hcartier,
    inferInstance, ?_⟩
  intro C
  exact component_isDominant_of_dimension (g ≫ p) b (D.comap q) hcartier hdim C

end Hironaka.Geometry.CartierBoundaryDominance

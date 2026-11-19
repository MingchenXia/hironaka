import Hironaka.Geometry.FiniteBirationalNormalSectionGeneric
import Hironaka.Geometry.FiniteBirationalNormalExtension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Whole actual pullback coverage by normalization sections

This proves the finite-flat integral-component case of the boundary
splitting step. The final existence theorem internally chooses its Galois
field and actual projective normalization. The output is exact coverage
of the actual fiber product by genuine closed-immersion section images.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem eq_univ_of_closed_contains_generic_pullback
    {P Y : Scheme.{u}} [IsIntegral Y] (q : P ⟶ Y) (hq : IsOpenMap q)
    (C : Set P) (hC : IsClosed C)
    (hgen : Set.range (pullback.fst q (Y.fromSpecStalk (genericPoint Y))) ⊆ C) :
    C = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hη : genericPoint Y ∈ q '' Cᶜ :=
    ((genericPoint_spec Y).mem_open_set_iff (hq _ hC.isOpen_compl)).mpr
      ⟨q x, trivial, x, hx, rfl⟩
  obtain ⟨y, hy, hqy⟩ := hη
  let a : Spec Y.functionField := IsLocalRing.closedPoint Y.functionField
  have ha : Y.fromSpecStalk (genericPoint Y) a = genericPoint Y :=
    Scheme.fromSpecStalk_closedPoint
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback y a (hqy.trans ha.symm)
  exact hy (hgen ⟨z, hz⟩)

variable {k : Type u} [Field k] {S T : Scheme.{u}} [IsIntegral T]
  (p : S ⟶ Spec (.of k)) [IsVariety p]
  (L : Type u) [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
  [Normal S.functionField L]
  (f : T ⟶ S) [IsDominant f] [IsFinite f] [Flat f]

include p in
/-- All actual normalization sections cover the entire original finite-flat component pullback. -/
theorem normalizationSections_cover
    (e : letI := functionFieldAlgebra f; T.functionField →ₐ[S.functionField] L) :
    letI := functionFieldAlgebra f
    ⋃ σ : T.functionField →ₐ[S.functionField] L,
      Set.range (normalizationSection f L σ) = Set.univ := by
  let := functionFieldAlgebra f
  let g := NormalizationInExtension.normalizationStructure S L
  let Y := NormalizationInExtension.normalization S L
  let : IsFinite g := NormalizationInExtension.normalizationStructure_isFinite L p
  let : IsVariety (g ≫ p) := NormalizationInExtension.normalization_isVariety p L
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ p)
  let : LocallyOfFinitePresentation (pullback.snd f g) := inferInstance
  let : UniversallyOpen (pullback.snd f g) := inferInstance
  let : FiniteDimensional S.functionField T.functionField := finite_functionField f
  let : Finite (T.functionField →ₐ[S.functionField] L) := inferInstance
  apply eq_univ_of_closed_contains_generic_pullback (pullback.snd f g)
    (pullback.snd f g).isOpenMap _
    (isClosed_iUnion_of_finite (fun σ => (normalizationSection f L σ).isClosedEmbedding.isClosed_range))
  rintro x ⟨z, rfl⟩
  let := functionFieldAlgebra g
  let U := NormalizationInExtension.comparisonChart S
  let eY := NormalizationInExtension.functionFieldAlgEquiv L U
  have hn : Normal S.functionField Y.functionField := Normal.of_algEquiv eY.symm
  have hcover := genericTensorFiber_covered f g hn (eY.symm.toAlgHom.comp e)
  have hz : z ∈ ⋃ σ : T.functionField →ₐ[S.functionField] Y.functionField,
      Set.range (genericEvaluationToFiber f g σ) := by
    rw [hcover]
    trivial
  obtain ⟨σ, a, rfl⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨eY.toAlgHom.comp σ, Y.fromSpecStalk (genericPoint Y) a, ?_⟩
  exact congrArg (fun h => h a) (normalizationSection_generic_evaluation L p f U σ)

end Hironaka.Geometry.FiniteBirationalNormal

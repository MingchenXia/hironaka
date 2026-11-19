import Hironaka.Geometry.CartierBoundarySectionComponents

/-!
# Actual generic coverage by the original component sections

This is a coverage theorem only over the actual new generic point.
It requires neither original boundary flatness nor component flatness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundarySection

open CartierBoundaryComponentDimension CartierBoundaryDominance FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S X : Scheme.{u}}
  (p : S ⟶ Spec (.of k)) [IsVariety p]
  (f : X ⟶ S) (D : X.IdealSheafData)
  [IsFinite (reducedBoundaryInclusion D ≫ f)]
  [∀ C : DivisorComponent D, IsDominant (componentInclusion D C ≫ f)]
  (L : Type u) [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
  [Normal S.functionField L]

/-- Every actual inverse-boundary point over the generic point is on a literal section there. -/
theorem ambientSection_generic_cover
    (e : ∀ C : DivisorComponent D, ComponentEmbeddings f D L C)
    (x : (pullback f (NormalizationInExtension.normalizationStructure S L) : Scheme.{u}))
    (hx : pullback.fst f (NormalizationInExtension.normalizationStructure S L) x ∈ D.support)
    (hy : pullback.snd f (NormalizationInExtension.normalizationStructure S L) x =
      genericPoint (NormalizationInExtension.normalization S L)) :
    ∃ (C : DivisorComponent D) (σ : ComponentEmbeddings f D L C),
      ambientSection f D L C σ (genericPoint (NormalizationInExtension.normalization S L)) = x := by
  let g := NormalizationInExtension.normalizationStructure S L
  let Y := NormalizationInExtension.normalization S L
  let : IsFinite g := NormalizationInExtension.normalizationStructure_isFinite L p
  obtain ⟨C, c, hc⟩ := components_cover D (pullback.fst f g x) hx
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_boundaryBaseChange (componentInclusion D C) f g) x c hc.symm
  let fC := componentInclusion D C ≫ f
  let η := Y.fromSpecStalk (genericPoint Y)
  let a0 : Spec Y.functionField := IsLocalRing.closedPoint Y.functionField
  have ha0 : η a0 = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hwy : pullback.snd fC g w = η a0 := by
    calc
      pullback.snd fC g w = pullback.snd f g (boundaryBaseChange (componentInclusion D C) f g w) :=
        (congrArg (fun h => h w) (boundaryBaseChange_snd (componentInclusion D C) f g)).symm
      _ = pullback.snd f g x := congrArg (pullback.snd f g) hw
      _ = η a0 := hy.trans ha0.symm
  obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback w a0 hwy
  let := functionFieldAlgebra fC
  let := functionFieldAlgebra g
  let U := NormalizationInExtension.comparisonChart S
  let eY := NormalizationInExtension.functionFieldAlgEquiv L U
  have hn : Normal S.functionField Y.functionField := Normal.of_algEquiv eY.symm
  have hcover := genericTensorFiber_covered fC g hn (eY.symm.toAlgHom.comp (e C))
  have hvcover : v ∈ ⋃ σ : (componentScheme D C).functionField →ₐ[S.functionField] Y.functionField,
      Set.range (genericEvaluationToFiber fC g σ) := by
    rw [hcover]
    trivial
  obtain ⟨σ, a, hσ⟩ := Set.mem_iUnion.mp hvcover
  have ha : η a = genericPoint Y := by
    have hea : a = a0 := @Subsingleton.elim (PrimeSpectrum Y.functionField) inferInstance a a0
    rw [hea]
    exact ha0
  refine ⟨C, eY.toAlgHom.comp σ, ?_⟩
  rw [← ha]
  change boundaryBaseChange (componentInclusion D C) f g
    (normalizationSection fC L (eY.toAlgHom.comp σ) (η a)) = x
  calc
    boundaryBaseChange (componentInclusion D C) f g
        (normalizationSection fC L (eY.toAlgHom.comp σ) (η a)) =
      boundaryBaseChange (componentInclusion D C) f g
        (pullback.fst (pullback.snd fC g) η (genericEvaluationToFiber fC g σ a)) := by
      exact congrArg (boundaryBaseChange (componentInclusion D C) f g)
        (congrArg (fun h => h a) (normalizationSection_generic_evaluation L p fC U σ))
    _ = boundaryBaseChange (componentInclusion D C) f g w := by rw [hσ, hv]
    _ = x := hw

omit [FiniteDimensional S.functionField L] [Normal S.functionField L] in
/-- The actual dependent family of all original component embeddings is finite. -/
theorem finite_componentSectionIndex [NoetherianSpace X] :
    Finite (Σ C : DivisorComponent D, ComponentEmbeddings f D L C) := by
  let : Finite (DivisorComponent D) := divisorComponent_finite D
  let (C : DivisorComponent D) := functionFieldAlgebra (componentInclusion D C ≫ f)
  let (C : DivisorComponent D) : FiniteDimensional S.functionField (componentScheme D C).functionField :=
    finite_functionField (componentInclusion D C ≫ f)
  let (C : DivisorComponent D) : Finite (ComponentEmbeddings f D L C) := inferInstance
  infer_instance

end Hironaka.Geometry.CartierBoundarySection

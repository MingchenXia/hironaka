import DeJongAlterations.Geometry.FiniteBirationalNormalReducedBaseChange
import DeJongAlterations.Geometry.FiniteBirationalNormalExtension

/-!
# Whole boundary coverage using only whole-boundary flatness

The actual intrinsic component maps need not be flat. Their actual
generic fibers are covered by the original field evaluations; openness
of the whole original finite flat boundary projection spreads this
to exact coverage of the whole actual pullback by genuine sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem closed_eq_univ_of_generic_pullback
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

variable {k : Type u} [Field k] {S Z : Scheme.{u}}
  (p : S ⟶ Spec (.of k)) [IsVariety p]
  (L : Type u) [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
  [Normal S.functionField L]
  (f : Z ⟶ S) [IsFinite f] [Flat f]

/-- A common normal field splits the whole native boundary pullback into genuine sections.
Only the original whole boundary map is assumed flat; components are internally constructed. -/
theorem reducedComponentSections_cover
    (e : ∀ C : irreducibleComponents Z, reducedComponentEmbeddings f L C) :
    ⋃ C : irreducibleComponents Z, ⋃ σ : reducedComponentEmbeddings f L C,
      Set.range (reducedComponentSection f L C σ) = Set.univ := by
  let g := NormalizationInExtension.normalizationStructure S L
  let Y := NormalizationInExtension.normalization S L
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace p
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian Z := ⟨⟩
  let : Fintype (irreducibleComponents Z) := NoetherianSpace.finite_irreducibleComponents.fintype
  let (C : irreducibleComponents Z) := functionFieldAlgebra (reducedComponentInclusion Z C ≫ f)
  let (C : irreducibleComponents Z) :
      FiniteDimensional S.functionField (reducedComponent Z C).functionField :=
    finite_functionField (reducedComponentInclusion Z C ≫ f)
  let (C : irreducibleComponents Z) : Finite (reducedComponentEmbeddings f L C) :=
    inferInstance
  let : IsFinite g := NormalizationInExtension.normalizationStructure_isFinite L p
  let : IsVariety (g ≫ p) := NormalizationInExtension.normalization_isVariety p L
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ p)
  let : LocallyOfFinitePresentation (pullback.snd f g) := inferInstance
  let : UniversallyOpen (pullback.snd f g) := inferInstance
  apply closed_eq_univ_of_generic_pullback (pullback.snd f g) (pullback.snd f g).isOpenMap _
    (isClosed_iUnion_of_finite (fun C => isClosed_iUnion_of_finite
      (fun σ => (reducedComponentSection f L C σ).isClosedEmbedding.isClosed_range)))
  rintro x ⟨z, rfl⟩
  let η := Y.fromSpecStalk (genericPoint Y)
  let q := pullback.snd f g
  have hwcover : pullback.fst q η z ∈
      ⋃ C : irreducibleComponents Z, Set.range (reducedComponentBaseChange f g C) := by
    rw [reducedComponentBaseChanges_cover]
    trivial
  obtain ⟨C, w, hw⟩ := Set.mem_iUnion.mp hwcover
  let fC := reducedComponentInclusion Z C ≫ f
  have hwy : pullback.snd fC g w = η (pullback.snd q η z) := by
    calc
      pullback.snd fC g w = q (reducedComponentBaseChange f g C w) :=
        (congrArg (fun h => h w) (reducedComponentBaseChange_snd f g C)).symm
      _ = q (pullback.fst q η z) := congrArg q hw
      _ = η (pullback.snd q η z) :=
        congrArg (fun h => h z) (pullback.condition (f := q) (g := η))
  obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback w (pullback.snd q η z) hwy
  let := functionFieldAlgebra g
  let U := NormalizationInExtension.comparisonChart S
  let eY := NormalizationInExtension.functionFieldAlgEquiv L U
  have hn : Normal S.functionField Y.functionField := Normal.of_algEquiv eY.symm
  have hcover := genericTensorFiber_covered fC g hn (eY.symm.toAlgHom.comp (e C))
  have hvcover : v ∈ ⋃ σ : (reducedComponent Z C).functionField →ₐ[S.functionField] Y.functionField,
      Set.range (genericEvaluationToFiber fC g σ) := by
    rw [hcover]
    trivial
  obtain ⟨σ, a, hσ⟩ := Set.mem_iUnion.mp hvcover
  refine Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr
    ⟨eY.toAlgHom.comp σ, η a, ?_⟩⟩
  change reducedComponentBaseChange f g C
    (normalizationSection fC L (eY.toAlgHom.comp σ) (η a)) = _
  calc
    reducedComponentBaseChange f g C
        (normalizationSection fC L (eY.toAlgHom.comp σ) (η a)) =
      reducedComponentBaseChange f g C
        (pullback.fst (pullback.snd fC g) η (genericEvaluationToFiber fC g σ a)) := by
      exact congrArg (reducedComponentBaseChange f g C)
        (congrArg (fun h => h a) (normalizationSection_generic_evaluation L p fC U σ))
    _ = reducedComponentBaseChange f g C w := by rw [hσ, hv]
    _ = pullback.fst q η z := hw

end DeJongAlterations.Geometry.FiniteBirationalNormal

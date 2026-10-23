import DeJongAlterations.Geometry.AlgebraicFieldFiniteModelRefinement
import DeJongAlterations.Geometry.AlgebraicFieldOriginalScalarModel

/-! Both ORIGINAL alteration/compactification arrows share actual models over ONE finite field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteSpanModel

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteModelRefinement
  AlgebraicFieldOriginalScalarModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A genuine scalar span INTERNALLY produces BOTH whole original arrow models over ONE
finite field, the SAME fixed target's actual finite scalar model, and a smooth regular third scheme. -/
theorem exists_smooth_span_over_fixed_target
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {A C B : Scheme.{u}} (pA : A ⟶ Spec (.of L)) (pC : C ⟶ Spec (.of L))
    (pB : B ⟶ Spec (.of L))
    [LocallyOfFinitePresentation pA] [QuasiCompact pA] [QuasiSeparated pA]
    [Smooth pB] [QuasiCompact pB] [QuasiSeparated pB]
    (a : A ⟶ C) (b : A ⟶ B) (ha : a ≫ pC = pA) (hb : b ≫ pB = pA)
    {i : Index k L} (rC : Model (diagram k L) (scalarCone k L) pC i) (hrC : rC.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (mA : Model (diagram k L) (scalarCone k L) pA j)
      (mC : Model (diagram k L) (scalarCone k L) pC j)
      (mB : Model (diagram k L) (scalarCone k L) pB j)
      (πC : mC.Y ⟶ rC.Y) (a₀ : mA.Y ⟶ mC.Y) (b₀ : mA.Y ⟶ mB.Y),
      mA.IsFP ∧ mC.IsFP ∧ mB.IsFP ∧ Smooth mB.fY ∧ IsRegularScheme mB.Y ∧
      IsPullback πC mC.fY rC.fY ((diagram k L).map h) ∧ IsFinite πC ∧
      mC.g ≫ πC = rC.g ∧
      a₀ ≫ mC.fY = mA.fY ∧ b₀ ≫ mB.fY = mA.fY ∧
      mA.g ≫ a₀ = a ≫ mC.g ∧ mA.g ≫ b₀ = b ≫ mB.g ∧
      IsPullback mA.g a a₀ mC.g ∧ IsPullback mA.g b b₀ mB.g := by
  obtain ⟨iA, tA, htA⟩ := exists_model (isLimitScalarCone k L) pA
  obtain ⟨iB, tB, htB⟩ := exists_model (isLimitScalarCone k L) pB
  let iAB := IsCofiltered.min iA iB
  let i₀ := IsCofiltered.min i iAB
  let gC : i₀ ⟶ i := IsCofiltered.minToLeft i iAB
  let gA : i₀ ⟶ iA := IsCofiltered.minToRight i iAB ≫ IsCofiltered.minToLeft iA iB
  let gB : i₀ ⟶ iB := IsCofiltered.minToRight i iAB ≫ IsCofiltered.minToRight iA iB
  let sA := tA.baseChange gA
  let sC := rC.baseChange gC
  let sB := tB.baseChange gB
  have hsA : sA.IsFP := htA.baseChange gA
  have hsC : sC.IsFP := hrC.baseChange gC
  have hsB : sB.IsFP := htB.baseChange gB
  obtain ⟨j₁, h₁, a₁, ha₁, hga₁, _⟩ := exists_arrow_refinement k L sA sC hsA hsC a ha
  let A₁ := sA.baseChange h₁
  let C₁ := sC.baseChange h₁
  let B₁ := sB.baseChange h₁
  have hA₁ : A₁.IsFP := hsA.baseChange h₁
  have hC₁ : C₁.IsFP := hsC.baseChange h₁
  have hB₁ : B₁.IsFP := hsB.baseChange h₁
  obtain ⟨j₂, h₂, b₂, hb₂, hgb₂, _⟩ := exists_arrow_refinement k L A₁ B₁ hA₁ hB₁ b hb
  let A₂ := A₁.baseChange h₂
  let C₂ := C₁.baseChange h₂
  let B₂ := B₁.baseChange h₂
  let a₂ := topBaseChange A₁ C₁ a₁ ha₁ (Over.mk h₂)
  have ha₂ : a₂ ≫ C₂.fY = A₂.fY := topBaseChange_snd _ _ _ _ _
  have hga₂ : A₂.g ≫ a₂ = a ≫ C₂.g := π_topBaseChange A₁ C₁ a₁ ha₁ a hga₁ ha _
  have hA₂ : A₂.IsFP := hA₁.baseChange h₂
  have hC₂ : C₂.IsFP := hC₁.baseChange h₂
  have hB₂ : B₂.IsFP := hB₁.baseChange h₂
  obtain ⟨j, h₃, hsmooth, hregular⟩ := exists_smooth_refinement k L B₂ hB₂
  let mA := A₂.baseChange h₃
  let mC := C₂.baseChange h₃
  let mB := B₂.baseChange h₃
  let a₀ := topBaseChange A₂ C₂ a₂ ha₂ (Over.mk h₃)
  let b₀ := topBaseChange A₂ B₂ b₂ hb₂ (Over.mk h₃)
  have ha₀ : a₀ ≫ mC.fY = mA.fY := topBaseChange_snd _ _ _ _ _
  have hb₀ : b₀ ≫ mB.fY = mA.fY := topBaseChange_snd _ _ _ _ _
  have hga₀ : mA.g ≫ a₀ = a ≫ mC.g := π_topBaseChange A₂ C₂ a₂ ha₂ a hga₂ ha _
  have hgb₀ : mA.g ≫ b₀ = b ≫ mB.g := π_topBaseChange A₂ B₂ b₂ hb₂ b hgb₂ hb _
  let h : j ⟶ i := h₃ ≫ h₂ ≫ h₁ ≫ gC
  let πC : mC.Y ⟶ rC.Y := pullback.fst C₂.fY ((diagram k L).map h₃) ≫
    pullback.fst C₁.fY ((diagram k L).map h₂) ≫
    pullback.fst sC.fY ((diagram k L).map h₁) ≫
    pullback.fst rC.fY ((diagram k L).map gC)
  have Hπ : IsPullback πC mC.fY rC.fY ((diagram k L).map h) := by
    have H := (IsPullback.of_hasPullback C₂.fY ((diagram k L).map h₃)).paste_horiz
      ((IsPullback.of_hasPullback C₁.fY ((diagram k L).map h₂)).paste_horiz
        ((IsPullback.of_hasPullback sC.fY ((diagram k L).map h₁)).paste_horiz
          (IsPullback.of_hasPullback rC.fY ((diagram k L).map gC))))
    simpa only [πC, mC, Model.baseChange, h, Functor.map_comp, Category.assoc] using H
  have hgπ : mC.g ≫ πC = rC.g := by
    simp [πC, mC, C₂, C₁, sC, Model.baseChange]
  let : FiniteDimensional k (levelField k L j) := levelField_finiteDimensional k L j
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite ((diagram k L).map h ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))) := by
    rw [diagram_map_coefficient]
    infer_instance
  let : IsFinite ((diagram k L).map h) := IsFinite.of_comp _
    (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))))
  let : IsFinite πC := MorphismProperty.of_isPullback Hπ.flip inferInstance
  refine ⟨j, h, mA, mC, mB, πC, a₀, b₀, hA₂.baseChange h₃, hC₂.baseChange h₃,
    hB₂.baseChange h₃, hsmooth, hregular, Hπ, inferInstance, hgπ, ha₀, hb₀, hga₀, hgb₀, ?_, ?_⟩
  · refine IsPullback.of_bot ?_ hga₀ mC.isPullback
    simpa only [ha, ha₀] using mA.isPullback
  · refine IsPullback.of_bot ?_ hgb₀ mB.isPullback
    simpa only [hb, hb₀] using mA.isPullback

end DeJongAlterations.Geometry.AlgebraicFieldFiniteSpanModel

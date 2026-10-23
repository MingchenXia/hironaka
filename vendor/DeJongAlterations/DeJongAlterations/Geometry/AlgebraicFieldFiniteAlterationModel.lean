import DeJongAlterations.Geometry.AlgebraicFieldFiniteSpanModel
import DeJongAlterations.Geometry.AlgebraicFieldFiniteProjectiveModel
import DeJongAlterations.Geometry.AlgebraicFieldFiniteIntegralModel
import DeJongAlterations.Geometry.AlterationScalarDescent

/-! One actual finite-field diagram retains the alteration and regular projective compactification. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteAlterationModel

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteSpanModel
  AlgebraicFieldFiniteProjectiveModel AlgebraicFieldOriginalScalarModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

private theorem finite_transition {i j : Index k L} (h : j ⟶ i) :
    IsFinite ((diagram k L).map h) := by
  let : FiniteDimensional k (levelField k L j) := levelField_finiteDimensional k L j
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite ((diagram k L).map h ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))) := by
    rw [diagram_map_coefficient]
    infer_instance
  exact IsFinite.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))))

private theorem scalar_model_cover {Y : Scheme.{u}} {p : Y ⟶ Spec (.of L)}
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) :
    Surjective m.g ∧ Flat m.g ∧ QuasiCompact m.g := by
  let c : Spec (.of L) ⟶ Spec (.of (levelField k L i)) :=
    Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom)
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Flat c := inferInstance
  let : QuasiCompact c := inferInstance
  have H : IsPullback m.g p m.fY c := by
    simpa only [scalarCone_π] using m.isPullback
  exact ⟨MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance⟩

/-- Original ACTUAL scalar alteration/open immersion/regular projective compactification
INTERNALLY produce the SAME entire geometric diagram over ONE actual finite field. -/
theorem exists_finite_alteration_model [PerfectField L]
    {A C B : Scheme.{u}} (pA : A ⟶ Spec (.of L)) (pC : C ⟶ Spec (.of L))
    (pB : B ⟶ Spec (.of L)) [IsVariety pA] [IsVariety pC] [IsVariety pB]
    (a : A ⟶ C) [IsAlteration a] (b : A ⟶ B) [IsOpenImmersion b]
    (ha : a ≫ pC = pA) (hb : b ≫ pB = pA)
    (hreg : IsRegularScheme B) (hproj : IsProjectiveOver pB)
    {i : Index k L} (rC : Model (diagram k L) (scalarCone k L) pC i) (hrC : rC.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (mA : Model (diagram k L) (scalarCone k L) pA j)
      (mC : Model (diagram k L) (scalarCone k L) pC j)
      (mB : Model (diagram k L) (scalarCone k L) pB j)
      (πC : mC.Y ⟶ rC.Y) (a₀ : mA.Y ⟶ mC.Y) (b₀ : mA.Y ⟶ mB.Y),
      mA.IsFP ∧ mC.IsFP ∧ mB.IsFP ∧
      IsVariety (k := levelField k L j) mA.fY ∧
      IsVariety (k := levelField k L j) mC.fY ∧
      IsVariety (k := levelField k L j) mB.fY ∧
      IsAlteration a₀ ∧ IsOpenImmersion b₀ ∧
      Smooth mB.fY ∧ IsRegularScheme mB.Y ∧
      IsProjectiveOver (k := levelField k L j) mB.fY ∧
      IsProjectiveOver (mB.fY ≫ Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) ∧
      IsPullback πC mC.fY rC.fY ((diagram k L).map h) ∧ IsFinite πC ∧
      mC.g ≫ πC = rC.g ∧
      a₀ ≫ mC.fY = mA.fY ∧ b₀ ≫ mB.fY = mA.fY ∧
      mA.g ≫ a₀ = a ≫ mC.g ∧ mA.g ≫ b₀ = b ≫ mB.g ∧
      IsPullback mA.g a a₀ mC.g ∧ IsPullback mA.g b b₀ mB.g := by
  let : Smooth pB := RegularSmoothConverse.smooth_of_isRegularScheme pB hreg
  let : LocallyOfFinitePresentation pA :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType pA
  obtain ⟨i₀, h₀, hsC⟩ := exists_isSeparated (isLimitScalarCone k L) rC hrC
  let sC := rC.baseChange h₀
  let : IsSeparated sC.fY := hsC
  obtain ⟨i₁, h₁, sA, tC, sB, π, a₁, b₁, hsA, htC, hsB, hsm, _, Hπ, hπfin,
      hgπ, ha₁, hb₁, hga₁, hgb₁, _, _⟩ :=
    exists_smooth_span_over_fixed_target k L pA pC pB a b ha hb sC (hrC.baseChange h₀)
  let : IsSeparated tC.fY := MorphismProperty.of_isPullback Hπ inferInstance
  let : Smooth sB.fY := hsm
  obtain ⟨j, h₂, hproj₂⟩ := exists_projective_refinement k L hproj sB hsB
  let mA := sA.baseChange h₂
  let mC := tC.baseChange h₂
  let mB := sB.baseChange h₂
  have hmA : mA.IsFP := hsA.baseChange h₂
  have hmC : mC.IsFP := htC.baseChange h₂
  have hmB : mB.IsFP := hsB.baseChange h₂
  let a₀ := topBaseChange sA tC a₁ ha₁ (Over.mk h₂)
  let b₀ := topBaseChange sA sB b₁ hb₁ (Over.mk h₂)
  have ha₀ : a₀ ≫ mC.fY = mA.fY := topBaseChange_snd _ _ _ _ _
  have hb₀ : b₀ ≫ mB.fY = mA.fY := topBaseChange_snd _ _ _ _ _
  have hga₀ : mA.g ≫ a₀ = a ≫ mC.g := π_topBaseChange sA tC a₁ ha₁ a hga₁ ha _
  have hgb₀ : mA.g ≫ b₀ = b ≫ mB.g := π_topBaseChange sA sB b₁ hb₁ b hgb₁ hb _
  have Ha : IsPullback mA.g a a₀ mC.g := by
    refine IsPullback.of_bot ?_ hga₀ mC.isPullback
    simpa only [ha, ha₀] using mA.isPullback
  have Hb : IsPullback mA.g b b₀ mB.g := by
    refine IsPullback.of_bot ?_ hgb₀ mB.isPullback
    simpa only [hb, hb₀] using mA.isPullback
  have HA := mA.isPullback
  have HC := mC.isPullback
  have HB := mB.isPullback
  rw [scalarCone_π] at HA HC HB
  let : IsIntegral mA.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom mA.fY HA
  let : IsIntegral mC.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom mC.fY HC
  let : IsIntegral mB.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom mB.fY HB
  obtain ⟨hbs, hbfl, hbqc⟩ := scalar_model_cover k L mB
  let := hbs
  let := hbfl
  let := hbqc
  let : IsOpenImmersion b₀ := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    Hb.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let : IsProper mB.fY := hproj₂.isProper
  let : LocallyOfFinitePresentation mA.fY := hmA.1
  let : QuasiCompact mA.fY := hmA.2.1
  let : IsSeparated mA.fY := by rw [← hb₀]; infer_instance
  let : IsVariety (k := levelField k L j) mA.fY := ⟨⟩
  let : IsSeparated mC.fY := by
    change IsSeparated (pullback.snd tC.fY ((diagram k L).map h₂))
    infer_instance
  let : LocallyOfFinitePresentation mC.fY := hmC.1
  let : QuasiCompact mC.fY := hmC.2.1
  let : IsVariety (k := levelField k L j) mC.fY := ⟨⟩
  let : LocallyOfFinitePresentation mB.fY := hmB.1
  let : QuasiCompact mB.fY := hmB.2.1
  let : IsVariety (k := levelField k L j) mB.fY := ⟨⟩
  let : IsSeparated (a₀ ≫ mC.fY) := by rw [ha₀]; infer_instance
  let : LocallyOfFiniteType (a₀ ≫ mC.fY) := by rw [ha₀]; infer_instance
  let : IsSeparated a₀ := IsSeparated.of_comp a₀ mC.fY
  let : LocallyOfFiniteType a₀ := locallyOfFiniteType_of_comp a₀ mC.fY
  obtain ⟨hcs, hcfl, hcqc⟩ := scalar_model_cover k L mC
  let := hcs
  let := hcfl
  let := hcqc
  let : IsAlteration a₀ := AlterationScalarDescent.isAlteration_of_isPullback Ha
  let h : j ⟶ i := h₂ ≫ h₁ ≫ h₀
  let πC : mC.Y ⟶ rC.Y := pullback.fst tC.fY ((diagram k L).map h₂) ≫ π ≫
    pullback.fst rC.fY ((diagram k L).map h₀)
  have HπC : IsPullback πC mC.fY rC.fY ((diagram k L).map h) := by
    have H := (IsPullback.of_hasPullback tC.fY ((diagram k L).map h₂)).paste_horiz
      (Hπ.paste_horiz (IsPullback.of_hasPullback rC.fY ((diagram k L).map h₀)))
    simpa only [πC, mC, Model.baseChange, h, Functor.map_comp, Category.assoc] using H
  have hgπC : mC.g ≫ πC = rC.g := by
    have hn : mC.g ≫ pullback.fst tC.fY ((diagram k L).map h₂) = tC.g := by
      simp [mC, Model.baseChange]
    have hp : mC.g ≫ pullback.fst tC.fY ((diagram k L).map h₂) ≫ π = sC.g := by
      rw [← Category.assoc, hn, hgπ]
    have hp' := congrArg (fun t => t ≫ pullback.fst rC.fY ((diagram k L).map h₀)) hp
    simpa [πC, sC, Model.baseChange, Category.assoc] using hp'
  let : IsFinite ((diagram k L).map h) := finite_transition k L h
  let : IsFinite πC := MorphismProperty.of_isPullback HπC.flip inferInstance
  let : Smooth mB.fY := by
    change Smooth (pullback.snd sB.fY ((diagram k L).map h₂))
    infer_instance
  let : FiniteDimensional k (levelField k L j) := levelField_finiteDimensional k L j
  refine ⟨j, h, mA, mC, mB, πC, a₀, b₀, hmA, hmC, hmB,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    RegularSmooth.isRegularScheme_of_smooth (K := levelField k L j) mB.fY,
    hproj₂, projective_over_original_field (k := k) (E := levelField k L j) mB.fY hproj₂,
    HπC, inferInstance, hgπC, ha₀, hb₀, hga₀, hgb₀, Ha, Hb⟩

end DeJongAlterations.Geometry.AlgebraicFieldFiniteAlterationModel

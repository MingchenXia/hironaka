import DeJongAlterations.Geometry.AlgebraicFieldFiniteAlterationModel
import DeJongAlterations.StableModification.Cohomology.Connected

/-! Every actual further finite-field refinement retains the SAME whole original alteration diagram. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldAlterationRefinement

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldOriginalScalarModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

private theorem cover {Y : Scheme.{u}} {p : Y ⟶ Spec (.of L)} {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) :
    Surjective m.g ∧ Flat m.g ∧ QuasiCompact m.g := by
  let c : Spec (.of L) ⟶ Spec (.of (levelField k L i)) :=
    Spec.map (CommRingCat.ofHom (levelField k L i).val.toRingHom)
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Flat c := inferInstance
  let : QuasiCompact c := inferInstance
  have H : IsPullback m.g p m.fY c := by simpa only [scalarCone_π] using m.isPullback
  exact ⟨MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance,
    MorphismProperty.of_isPullback H.flip inferInstance⟩

/-- Native further base change INTERNALLY retains every original alteration and compactification map. -/
theorem refine_diagram
    {A C B : Scheme.{u}} (pA : A ⟶ Spec (.of L)) (pC : C ⟶ Spec (.of L))
    (pB : B ⟶ Spec (.of L)) [IsVariety pA] [IsVariety pC] [IsVariety pB]
    (a : A ⟶ C) [IsAlteration a] (b : A ⟶ B) [IsOpenImmersion b]
    (ha : a ≫ pC = pA) (hb : b ≫ pB = pA)
    {i j : Index k L} (mA : Model (diagram k L) (scalarCone k L) pA i)
    (mC : Model (diagram k L) (scalarCone k L) pC i)
    (mB : Model (diagram k L) (scalarCone k L) pB i)
    (hmA : mA.IsFP) (hmC : mC.IsFP) (hmB : mB.IsFP)
    [IsVariety (k := levelField k L i) mA.fY]
    [IsVariety (k := levelField k L i) mC.fY]
    [IsVariety (k := levelField k L i) mB.fY] [Smooth mB.fY]
    (hproj : IsProjectiveOver mB.fY)
    (a₀ : mA.Y ⟶ mC.Y) (b₀ : mA.Y ⟶ mB.Y) [IsOpenImmersion b₀]
    (ha₀ : a₀ ≫ mC.fY = mA.fY) (hb₀ : b₀ ≫ mB.fY = mA.fY)
    (hga : mA.g ≫ a₀ = a ≫ mC.g) (hgb : mA.g ≫ b₀ = b ≫ mB.g) (h : j ⟶ i) :
    ∃ (a₁ : (mA.baseChange h).Y ⟶ (mC.baseChange h).Y)
      (b₁ : (mA.baseChange h).Y ⟶ (mB.baseChange h).Y),
      IsVariety (k := levelField k L j) (mA.baseChange h).fY ∧
      IsVariety (k := levelField k L j) (mC.baseChange h).fY ∧
      IsVariety (k := levelField k L j) (mB.baseChange h).fY ∧
      IsAlteration a₁ ∧ IsOpenImmersion b₁ ∧ Smooth (mB.baseChange h).fY ∧
      IsRegularScheme (mB.baseChange h).Y ∧
      IsProjectiveOver (mB.baseChange h).fY ∧
      IsProjectiveOver ((mB.baseChange h).fY ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) ∧
      IsFinite (pullback.fst mC.fY ((diagram k L).map h)) ∧
      a₁ ≫ (mC.baseChange h).fY = (mA.baseChange h).fY ∧
      b₁ ≫ (mB.baseChange h).fY = (mA.baseChange h).fY ∧
      (mA.baseChange h).g ≫ a₁ = a ≫ (mC.baseChange h).g ∧
      (mA.baseChange h).g ≫ b₁ = b ≫ (mB.baseChange h).g ∧
      IsPullback (mA.baseChange h).g a a₁ (mC.baseChange h).g ∧
      IsPullback (mA.baseChange h).g b b₁ (mB.baseChange h).g := by
  let MA := mA.baseChange h
  let MC := mC.baseChange h
  let MB := mB.baseChange h
  let a₁ := topBaseChange mA mC a₀ ha₀ (Over.mk h)
  let b₁ := topBaseChange mA mB b₀ hb₀ (Over.mk h)
  have ha₁ : a₁ ≫ MC.fY = MA.fY := topBaseChange_snd _ _ _ _ _
  have hb₁ : b₁ ≫ MB.fY = MA.fY := topBaseChange_snd _ _ _ _ _
  have hga₁ : MA.g ≫ a₁ = a ≫ MC.g := π_topBaseChange mA mC a₀ ha₀ a hga ha _
  have hgb₁ : MA.g ≫ b₁ = b ≫ MB.g := π_topBaseChange mA mB b₀ hb₀ b hgb hb _
  have Ha : IsPullback MA.g a a₁ MC.g := by
    refine IsPullback.of_bot ?_ hga₁ MC.isPullback
    simpa only [ha₁, ha] using MA.isPullback
  have Hb : IsPullback MA.g b b₁ MB.g := by
    refine IsPullback.of_bot ?_ hgb₁ MB.isPullback
    simpa only [hb₁, hb] using MA.isPullback
  let : IsOpenImmersion b₁ := MorphismProperty.of_isPullback
    (isPullback_topBaseChange mA mB b₀ hb₀ (Over.mk h)) inferInstance
  have hMA := hmA.baseChange h
  have hMC := hmC.baseChange h
  have hMB := hmB.baseChange h
  have hIA : IsIntegral MA.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom MA.fY (by simpa only [scalarCone_π] using MA.isPullback)
  have hIC : IsIntegral MC.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom MC.fY (by simpa only [scalarCone_π] using MC.isPullback)
  have hIB : IsIntegral MB.Y := AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback
    (levelField k L j).val.toRingHom MB.fY (by simpa only [scalarCone_π] using MB.isPullback)
  let := hIA
  let := hIC
  let := hIB
  let : IsSeparated mA.fY :=
    (inferInstance : IsVariety (k := levelField k L i) mA.fY).toIsSeparated
  let : IsSeparated mC.fY :=
    (inferInstance : IsVariety (k := levelField k L i) mC.fY).toIsSeparated
  let : IsSeparated mB.fY :=
    (inferInstance : IsVariety (k := levelField k L i) mB.fY).toIsSeparated
  let : IsSeparated MA.fY := by change IsSeparated (pullback.snd mA.fY _); infer_instance
  let : IsSeparated MC.fY := by change IsSeparated (pullback.snd mC.fY _); infer_instance
  let : IsSeparated MB.fY := by change IsSeparated (pullback.snd mB.fY _); infer_instance
  let : LocallyOfFinitePresentation MA.fY := hMA.1
  let : LocallyOfFinitePresentation MC.fY := hMC.1
  let : LocallyOfFinitePresentation MB.fY := hMB.1
  let : QuasiCompact MA.fY := hMA.2.1
  let : QuasiCompact MC.fY := hMC.2.1
  let : QuasiCompact MB.fY := hMB.2.1
  let : IsVariety (k := levelField k L j) MA.fY := ⟨⟩
  let : IsVariety (k := levelField k L j) MC.fY := ⟨⟩
  let : IsVariety (k := levelField k L j) MB.fY := ⟨⟩
  let : IsSeparated (a₁ ≫ MC.fY) := by rw [ha₁]; infer_instance
  let : LocallyOfFiniteType (a₁ ≫ MC.fY) := by rw [ha₁]; infer_instance
  let : IsSeparated a₁ := IsSeparated.of_comp a₁ MC.fY
  let : LocallyOfFiniteType a₁ := locallyOfFiniteType_of_comp a₁ MC.fY
  obtain ⟨hcSurj, hcFlat, hcQC⟩ := cover k L MC
  let := hcSurj
  let := hcFlat
  let := hcQC
  let : IsAlteration a₁ := AlterationScalarDescent.isAlteration_of_isPullback Ha
  let : Smooth MB.fY := by change Smooth (pullback.snd mB.fY _); infer_instance
  let φ : levelField k L i →+* levelField k L j := (Subalgebra.inclusion h.unop.le).toRingHom
  have hp : IsProjectiveOver MB.fY :=
    StableModification.Cohomology.Connected.isProjectiveOver_bcSnd φ hproj
  let : FiniteDimensional k (levelField k L j) := levelField_finiteDimensional k L j
  have hpK := AlgebraicFieldFiniteProjectiveModel.projective_over_original_field
    (k := k) (E := levelField k L j) MB.fY hp
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L j)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite ((diagram k L).map h ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i)))) := by
    rw [AlgebraicFieldOriginalScalarModel.diagram_map_coefficient]
    infer_instance
  let : IsFinite ((diagram k L).map h) := IsFinite.of_comp _
    (Spec.map (CommRingCat.ofHom (algebraMap k (levelField k L i))))
  refine ⟨a₁, b₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, RegularSmooth.isRegularScheme_of_smooth (K := levelField k L j) MB.fY,
    hp, hpK, inferInstance, ha₁, hb₁, hga₁, hgb₁, Ha, Hb⟩

end DeJongAlterations.Geometry.AlgebraicFieldAlterationRefinement

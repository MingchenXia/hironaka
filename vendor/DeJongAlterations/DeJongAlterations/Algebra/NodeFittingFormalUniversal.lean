import DeJongAlterations.Algebra.NodeFittingFormalDerivation
import DeJongAlterations.Algebra.NodeFittingFormalDensity
import DeJongAlterations.Algebra.NodeFittingModuleOneRelation

/-! # The actual formal gradient module universally represents Hausdorff derivations

The original native gradient relation is proved to vanish internally using
polynomial density and the actual derivation. No relation/Fitting certificate
is an input. Arbitrary commutative coefficients and all characteristics.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingFormalUniversal

open NodeFittingFormalDerivation NodeFittingFormalDensity NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable {R : Type u} [CommRing R]

section Series
variable {M : Type u} [AddCommGroup M] [Module (Series R) M] [Module R M]
  [IsScalarTower R (Series R) M]

/-- The actual native partial derivations with arbitrarily selected actual coordinate values. -/
def seriesWithValues (m : Fin 2 → M) : Derivation R (Series R) M :=
  (LinearMap.toSpanSingleton (Series R) M (m 0)).compDer (MvPowerSeries.pderiv R 0) +
    (LinearMap.toSpanSingleton (Series R) M (m 1)).compDer (MvPowerSeries.pderiv R 1)

/-- BOTH original coordinate values are the actually selected ones. -/
theorem seriesWithValues_coordinate (m : Fin 2 → M) (i : Fin 2) :
    seriesWithValues (R := R) m (MvPowerSeries.X i) = m i := by
  change MvPowerSeries.pderiv R 0 (MvPowerSeries.X i) • m 0 +
    MvPowerSeries.pderiv R 1 (MvPowerSeries.X i) • m 1 = m i
  fin_cases i <;> simp

/-- Actual variable-adic Hausdorffness proves the full formal chain rule internally. -/
theorem series_eq_withValues [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Series R) M) :
    D = seriesWithValues (R := R) (fun i => D (MvPowerSeries.X i)) := by
  apply derivation_ext_of_coordinate
  intro i
  rw [seriesWithValues_coordinate]

end Series

section Formal
variable (F : Series R) {M : Type u} [AddCommGroup M]
  [Module (Hypersurface F) M] [Module R M] [IsScalarTower R (Hypersurface F) M]

variable [Module (Series R) M] [IsScalarTower (Series R) (Hypersurface F) M]
  [IsScalarTower R (Series R) M]

omit [IsScalarTower R (Hypersurface F) M] [IsScalarTower R (Series R) M] in
/-- Actual quotient derivations into Hausdorff targets are determined by BOTH original coordinates. -/
theorem formalDerivation_ext [IsHausdorff (variableIdeal R) M]
    (D E : Derivation R (Hypersurface F) M)
    (h : ∀ i : Fin 2, D (quotientMap F (MvPowerSeries.X i)) =
      E (quotientMap F (MvPowerSeries.X i))) : D = E := by
  have he : D.compAlgebraMap (Series R) = E.compAlgebraMap (Series R) :=
    derivation_ext_of_coordinate _ _ h
  apply DFunLike.ext
  intro b
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact DFunLike.congr_fun he g

/-- The actual original coordinate values give a genuine linear map on the literal free module. -/
def evaluationLinearMap (D : Derivation R (Hypersurface F) M) :
    (Fin 2 → Hypersurface F) →ₗ[Hypersurface F] M :=
  (LinearMap.toSpanSingleton (Hypersurface F) M (D (quotientMap F (MvPowerSeries.X 0)))).comp
      (LinearMap.proj 0) +
    (LinearMap.toSpanSingleton (Hypersurface F) M (D (quotientMap F (MvPowerSeries.X 1)))).comp
      (LinearMap.proj 1)

omit [IsScalarTower R (Hypersurface F) M] [Module (Series R) M]
  [IsScalarTower (Series R) (Hypersurface F) M] [IsScalarTower R (Series R) M] in
/-- Evaluation retains each actual original coordinate value. -/
theorem evaluationLinearMap_coordinate (D : Derivation R (Hypersurface F) M) (i : Fin 2) :
    evaluationLinearMap F D (Pi.single i 1) = D (quotientMap F (MvPowerSeries.X i)) := by
  change (Pi.single i 1 : Fin 2 → Hypersurface F) 0 • D (quotientMap F (MvPowerSeries.X 0)) +
    (Pi.single i 1 : Fin 2 → Hypersurface F) 1 • D (quotientMap F (MvPowerSeries.X 1)) = _
  fin_cases i
  · simp
    exact zero_smul (Hypersurface F) (D (quotientMap F (MvPowerSeries.X 1)))
  · simp
    exact zero_smul (Hypersurface F) (D (quotientMap F (MvPowerSeries.X 0)))

omit [IsScalarTower R (Hypersurface F) M] in
/-- The ENTIRE actual gradient relation vanishes, proved from the SAME original equation and actual derivation. -/
theorem evaluationLinearMap_gradient [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) : evaluationLinearMap F D (gradient F) = 0 := by
  have he := DFunLike.congr_fun (series_eq_withValues (D.compAlgebraMap (Series R))) F
  change D (quotientMap F F) =
    MvPowerSeries.pderiv R 0 F • D (quotientMap F (MvPowerSeries.X 0)) +
      MvPowerSeries.pderiv R 1 F • D (quotientMap F (MvPowerSeries.X 1)) at he
  rw [show quotientMap F F = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton F)), map_zero] at he
  change algebraMap (Series R) (Hypersurface F) (MvPowerSeries.pderiv R 0 F) •
      D (quotientMap F (MvPowerSeries.X 0)) +
    algebraMap (Series R) (Hypersurface F) (MvPowerSeries.pderiv R 1 F) •
      D (quotientMap F (MvPowerSeries.X 1)) = 0
  rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
  exact he.symm

/-- The actual universal map is constructed from the internally proved WHOLE gradient kernel. -/
def universalLift [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) : GradientModule F →ₗ[Hypersurface F] M :=
  (Submodule.span (Hypersurface F) {gradient F}).liftQ (evaluationLinearMap F D)
    (Submodule.span_le.mpr (by
      rintro v rfl
      exact evaluationLinearMap_gradient F D))

/-- BOTH actual standard coordinate classes retain their original differential values. -/
theorem universalLift_coordinate [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) (i : Fin 2) :
    universalLift F D (coordinateClass F i) = D (quotientMap F (MvPowerSeries.X i)) :=
  evaluationLinearMap_coordinate F D i

/-- Genuine factorization on EVERY actual formal hypersurface element. -/
theorem universalLift_comp [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) :
    (universalLift F D).compDer (formalDerivation F) = D := by
  apply formalDerivation_ext F
  intro i
  change universalLift F D (formalDerivation F (quotientMap F (MvPowerSeries.X i))) = _
  rw [formalDerivation_coordinate, universalLift_coordinate]

omit [Module R M] [IsScalarTower R (Hypersurface F) M] [Module (Series R) M]
  [IsScalarTower (Series R) (Hypersurface F) M] [IsScalarTower R (Series R) M] in
/-- The actual original coordinate classes generate the WHOLE literal gradient module. -/
theorem gradientLinearMap_ext (L H : GradientModule F →ₗ[Hypersurface F] M)
    (h : ∀ i : Fin 2, L (coordinateClass F i) = H (coordinateClass F i)) : L = H := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  rw [hv, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_smul, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  change v 0 • L (coordinateClass F 0) + v 1 • L (coordinateClass F 1) =
    v 0 • H (coordinateClass F 0) + v 1 • H (coordinateClass F 1)
  rw [h 0, h 1]

/-- The actual formal differential factorization is UNIQUE on the entire native module. -/
theorem universalLift_unique [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) (L : GradientModule F →ₗ[Hypersurface F] M)
    (hL : L.compDer (formalDerivation F) = D) : L = universalLift F D := by
  apply gradientLinearMap_ext F
  intro i
  have h := DFunLike.congr_fun hL (quotientMap F (MvPowerSeries.X i))
  change L (formalDerivation F (quotientMap F (MvPowerSeries.X i))) = _ at h
  rw [formalDerivation_coordinate] at h
  exact h.trans (universalLift_coordinate F D i).symm

/-- The actual gradient module represents ALL actual derivations into actual variable-adically Hausdorff targets. -/
theorem existsUnique_factorization [IsHausdorff (variableIdeal R) M]
    (D : Derivation R (Hypersurface F) M) :
    ∃! L : GradientModule F →ₗ[Hypersurface F] M, L.compDer (formalDerivation F) = D := by
  exact ⟨universalLift F D, universalLift_comp F D, fun L hL => universalLift_unique F D L hL⟩

end Formal

/-- The literal actual quotient map and its ENTIRE native kernel give the original finite matrix presentation. -/
def gradientPresentation (F : Series R) :
    FiniteMatrixPresentation (R := Hypersurface F) (GradientModule F) :=
  oneRelationPresentation (Pi.basisFun (Hypersurface F) (Fin 2)) (gradient F)
    (Submodule.span (Hypersurface F) {gradient F}).mkQ
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)

/-- Native finite presentation is produced internally from the original gradient quotient. -/
instance gradient_finitePresentation (F : Series R) :
    Module.FinitePresentation (Hypersurface F) (GradientModule F) :=
  (gradientPresentation F).finitePresentation

/-- The ENTIRE intrinsic first Fitting ideal is exactly the original native formal derivative ideal. -/
theorem gradient_fittingIdeal (F : Series R) :
    fittingIdeal (R := Hypersurface F) (M := GradientModule F) 1 =
      Ideal.span {gradient F 0, gradient F 1} := by
  simpa using fittingIdeal_oneRelation (Pi.basisFun (Hypersurface F) (Fin 2)) (gradient F)
    (Submodule.span (Hypersurface F) {gradient F}).mkQ
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)

end DeJongAlterations.Algebra.NodeFittingFormalUniversal

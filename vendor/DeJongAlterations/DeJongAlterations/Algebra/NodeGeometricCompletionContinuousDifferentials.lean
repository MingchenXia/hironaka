import DeJongAlterations.Algebra.NodeGeometricCompletionCoherentDifferentials
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Universal continuous derivations of the actual completed ORIGINAL algebra, represented
by the completion of its ORIGINAL coherent differential module. Continuity uses the actual
inverse-limit coordinate kernels; no coefficient section or geometric normal form is assumed. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionContinuousDifferentials

open NodeGeometricCompletionDerivation NodeGeometricCompletionCoherentDifferentials

universe u

section ScalarTower

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M] (I : Ideal R)

/-- The native completed-ring action retains the entire original base scalar action. -/
instance completedScalarTower : IsScalarTower K (AdicCompletion I R) (AdicCompletion I M) where
  smul_assoc a r x := by
    apply AdicCompletion.ext
    intro n
    rw [AdicCompletion.smul_eval, AdicCompletion.val_smul_apply,
      AdicCompletion.val_smul_apply, AdicCompletion.smul_eval]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [← hb, ← hm]
    change Submodule.Quotient.mk ((a • b) • m) = Submodule.Quotient.mk (a • (b • m))
    rw [smul_assoc]

end ScalarTower

section LinearContinuity

variable {R M N : Type u} [CommRing R] (I : Ideal R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Every actual completed-linear map preserves the ORIGINAL adic coordinate kernels.
Finite generation of the ideal identifies these native kernels with its actual powers. -/
theorem completedLinearMap_filtration (hI : I.FG)
    (F : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (n : ℕ) (x : AdicCompletion I M) (hx : x.val n = 0) : (F x).val n = 0 := by
  have hmem : x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    exact hx
  have hle : Submodule.map (F.restrictScalars R)
      (I ^ n • ⊤ : Submodule R (AdicCompletion I M)) ≤
        (I ^ n • ⊤ : Submodule R (AdicCompletion I N)) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  have hy := hle (Submodule.mem_map_of_mem hmem)
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hI] at hy
  exact hy

end LinearContinuity

variable (K R N : Type u) [CommRing K] [CommRing R] [Algebra K R]
  [IsNoetherianRing R] [Algebra.EssFiniteType K R]
  [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower K R N]
  (I : Ideal R)

/-- The universal lift is constructed from the actual restriction to the ORIGINAL algebra,
its ORIGINAL universal differential, and the actual coherent tensor-completion comparison. -/
def continuousUniversalLift (E : Derivation K (AdicCompletion I R) (AdicCompletion I N)) :
    CompletedOmega K R I →ₗ[AdicCompletion I R] AdicCompletion I N :=
  (TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton (AdicCompletion I R) _
      (E.compAlgebraMap R).liftKaehlerDifferential)).comp
    (completedOmegaTensorEquiv K R I).symm.toLinearMap

/-- The actual universal lift retains every ORIGINAL differential value. -/
theorem continuousUniversalLift_original
    (E : Derivation K (AdicCompletion I R) (AdicCompletion I N)) (r : R) :
    continuousUniversalLift K R N I E
      (AdicCompletion.of I (KaehlerDifferential K R) (KaehlerDifferential.D K R r)) =
        E (algebraMap R (AdicCompletion I R) r) := by
  unfold continuousUniversalLift completedOmegaTensorEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of,
    TensorProduct.AlgebraTensorModule.lift_tmul]
  change (1 : AdicCompletion I R) •
    (E.compAlgebraMap R).liftKaehlerDifferential (KaehlerDifferential.D K R r) = _
  rw [one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Genuine universal factorization for EVERY actual continuous derivation on the completion.
Its target is an arbitrary native completed original module, not a supplied differential model. -/
theorem continuousUniversalLift_comp
    (E : Derivation K (AdicCompletion I R) (AdicCompletion I N))
    (hE : IsCoordinateContinuous I E) :
    (continuousUniversalLift K R N I E).compDer (completedUniversalDerivation K R I) = E := by
  apply continuousDerivation_ext I
  · intro n
    refine ⟨n + 1, fun x hx => ?_⟩
    exact completedLinearMap_filtration I (IsNoetherian.noetherian I)
      (continuousUniversalLift K R N I E) n _
        (completedUniversalDerivation_filtration K R I n x hx)
  · exact hE
  · intro r
    change continuousUniversalLift K R N I E
      (completedUniversalDerivation K R I (algebraMap R (AdicCompletion I R) r)) = _
    rw [completedUniversalDerivation_original, continuousUniversalLift_original]
    rfl

/-- The actual completed ORIGINAL universal differential determines a completed-linear map
uniquely, because the ORIGINAL universal differential generates the ORIGINAL coherent module. -/
theorem continuousUniversalLift_unique
    (F G : CompletedOmega K R I →ₗ[AdicCompletion I R] AdicCompletion I N)
    (h : F.compDer (completedUniversalDerivation K R I) =
      G.compDer (completedUniversalDerivation K R I)) : F = G := by
  have hOriginal : (F.restrictScalars R).comp (AdicCompletion.of I (KaehlerDifferential K R)) =
      (G.restrictScalars R).comp (AdicCompletion.of I (KaehlerDifferential K R)) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply DFunLike.ext
    intro r
    have hr := DFunLike.congr_fun h (algebraMap R (AdicCompletion I R) r)
    change F (completedUniversalDerivation K R I (algebraMap R (AdicCompletion I R) r)) =
      G (completedUniversalDerivation K R I (algebraMap R (AdicCompletion I R) r)) at hr
    change F (AdicCompletion.of I (KaehlerDifferential K R) (KaehlerDifferential.D K R r)) =
      G (AdicCompletion.of I (KaehlerDifferential K R) (KaehlerDifferential.D K R r))
    simpa only [completedUniversalDerivation_original] using hr
  apply LinearMap.ext
  intro ω
  obtain ⟨t, rfl⟩ := (completedOmegaTensorEquiv K R I).surjective ω
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a ω =>
    rw [completedOmegaTensorEquiv_tmul, F.map_smul, G.map_smul]
    exact congrArg (a • ·) (LinearMap.congr_fun hOriginal ω)
  | add t s ht hs =>
    rw [map_add, map_add, map_add, ht, hs]

/-- Existence and uniqueness of the actual continuous-differential universal map. -/
theorem existsUnique_continuous_factorization
    (E : Derivation K (AdicCompletion I R) (AdicCompletion I N))
    (hE : IsCoordinateContinuous I E) :
    ∃! F : CompletedOmega K R I →ₗ[AdicCompletion I R] AdicCompletion I N,
      F.compDer (completedUniversalDerivation K R I) = E := by
  refine ⟨continuousUniversalLift K R N I E, continuousUniversalLift_comp K R N I E hE, ?_⟩
  intro F hF
  apply continuousUniversalLift_unique K R N I
  exact hF.trans (continuousUniversalLift_comp K R N I E hE).symm

end DeJongAlterations.Algebra.NodeGeometricCompletionContinuousDifferentials

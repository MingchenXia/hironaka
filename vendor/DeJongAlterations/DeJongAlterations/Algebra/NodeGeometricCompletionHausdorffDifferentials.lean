import DeJongAlterations.Algebra.NodeGeometricCompletionContinuousDifferentials

/-! The completed ORIGINAL coherent differential module represents continuous derivations
into arbitrary adically Hausdorff modules over the actual completed original ring. This
form of the universal property supports transport under actual completed local algebra
isomorphisms, without an original morphism between two different presentations. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionHausdorffDifferentials

open NodeGeometricCompletionCoherentDifferentials NodeGeometricCompletionContinuousDifferentials

universe u

section Density

variable {K R P : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup P] [Module R P] [Module K P] (I : Ideal R)
  [Module (AdicCompletion I R) P] [IsHausdorff I P]

/-- Actual continuity for the defining source coordinate kernels and ORIGINAL target adic powers. -/
def IsAdicallyContinuous (E : AdicCompletion I R → P) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ x : AdicCompletion I R,
    x.val m = 0 → E x ∈ (I ^ n • ⊤ : Submodule R P)

/-- Original elements are dense for the actual continuous-derivation comparison. -/
theorem continuousDerivation_ext
    (E F : Derivation K (AdicCompletion I R) P)
    (hE : IsAdicallyContinuous I E) (hF : IsAdicallyContinuous I F)
    (hOriginal : ∀ r : R, E (AdicCompletion.of I R r) = F (AdicCompletion.of I R r)) :
    E = F := by
  apply DFunLike.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨m, hm⟩ := hE n
  obtain ⟨l, hl⟩ := hF n
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (x.val (m + l))
  have hzero (j : ℕ) (hj : j ≤ m + l) :
      (x - AdicCompletion.of I R r).val j = 0 := by
    rw [AdicCompletion.val_sub_apply]
    apply sub_eq_zero.mpr
    rw [← x.property hj, ← hr]
    exact AdicCompletion.transitionMap_ideal_mk I hj r
  have hEzero := hm (x - AdicCompletion.of I R r) (hzero m (Nat.le_add_right _ _))
  have hFzero := hl (x - AdicCompletion.of I R r) (hzero l (Nat.le_add_left _ _))
  rw [map_sub, hOriginal] at hEzero
  rw [map_sub] at hFzero
  rw [SModEq.sub_mem]
  convert Submodule.sub_mem _ hEzero hFzero using 1; abel

end Density

variable (K R P : Type u) [CommRing K] [CommRing R] [Algebra K R]
  [IsNoetherianRing R] [Algebra.EssFiniteType K R]
  [AddCommGroup P] [Module R P] [Module K P] [IsScalarTower K R P]
  (I : Ideal R) [Module (AdicCompletion I R) P] [IsScalarTower R (AdicCompletion I R) P]
  [IsScalarTower K (AdicCompletion I R) P]

/-- The actual lift uses the ORIGINAL universal differential and the actual tensor-completion map. -/
def universalLift (E : Derivation K (AdicCompletion I R) P) :
    CompletedOmega K R I →ₗ[AdicCompletion I R] P :=
  (TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton (AdicCompletion I R) _
      (E.compAlgebraMap R).liftKaehlerDifferential)).comp
    (completedOmegaTensorEquiv K R I).symm.toLinearMap

omit [IsScalarTower K (AdicCompletion I R) P] in
/-- The whole original differential square is retained. -/
theorem universalLift_original (E : Derivation K (AdicCompletion I R) P) (r : R) :
    universalLift K R P I E
      (AdicCompletion.of I (KaehlerDifferential K R) (KaehlerDifferential.D K R r)) =
        E (algebraMap R (AdicCompletion I R) r) := by
  unfold universalLift completedOmegaTensorEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of,
    TensorProduct.AlgebraTensorModule.lift_tmul]
  change (1 : AdicCompletion I R) •
    (E.compAlgebraMap R).liftKaehlerDifferential (KaehlerDifferential.D K R r) = _
  rw [one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

omit [Algebra.EssFiniteType K R] [Module K P] [IsScalarTower K R P]
  [IsScalarTower K (AdicCompletion I R) P] in
/-- Every actual completed-linear map sends the actual source coordinate kernel into the
ORIGINAL target adic power. -/
theorem completedLinearMap_filtration
    (F : CompletedOmega K R I →ₗ[AdicCompletion I R] P)
    (n : ℕ) (ω : CompletedOmega K R I) (hω : ω.val n = 0) :
    F ω ∈ (I ^ n • ⊤ : Submodule R P) := by
  have hmem : ω ∈ (I ^ n • ⊤ : Submodule R (CompletedOmega K R I)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
    exact hω
  have hle : Submodule.map (F.restrictScalars R)
      (I ^ n • ⊤ : Submodule R (CompletedOmega K R I)) ≤
        (I ^ n • ⊤ : Submodule R P) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact hle (Submodule.mem_map_of_mem hmem)

variable [IsHausdorff I P]

/-- Factorization of ANY actual continuous derivation into ANY actual adically Hausdorff target. -/
theorem universalLift_comp (E : Derivation K (AdicCompletion I R) P)
    (hE : IsAdicallyContinuous I E) :
    (universalLift K R P I E).compDer (completedUniversalDerivation K R I) = E := by
  apply continuousDerivation_ext I
  · intro n
    refine ⟨n + 1, fun x hx => ?_⟩
    exact completedLinearMap_filtration K R P I (universalLift K R P I E) n _
      (completedUniversalDerivation_filtration K R I n x hx)
  · exact hE
  · intro r
    change universalLift K R P I E
      (completedUniversalDerivation K R I (algebraMap R (AdicCompletion I R) r)) = _
    rw [completedUniversalDerivation_original, universalLift_original]
    rfl

omit [IsHausdorff I P] in
/-- Uniqueness uses the ORIGINAL coherent module generators and the actual completion map. -/
theorem universalLift_unique
    (F G : CompletedOmega K R I →ₗ[AdicCompletion I R] P)
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
  | add t s ht hs => rw [map_add, map_add, map_add, ht, hs]

/-- Universal continuous derivations of the actual completed ORIGINAL algebra are represented
by the completion of its ORIGINAL finite-presentation coherent differential module. -/
theorem existsUnique_factorization (E : Derivation K (AdicCompletion I R) P)
    (hE : IsAdicallyContinuous I E) :
    ∃! F : CompletedOmega K R I →ₗ[AdicCompletion I R] P,
      F.compDer (completedUniversalDerivation K R I) = E := by
  refine ⟨universalLift K R P I E, universalLift_comp K R P I E hE, ?_⟩
  intro F hF
  apply universalLift_unique K R P I
  exact hF.trans (universalLift_comp K R P I E hE).symm

end DeJongAlterations.Algebra.NodeGeometricCompletionHausdorffDifferentials

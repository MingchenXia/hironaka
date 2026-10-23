import DeJongAlterations.Algebra.CompletionFlatMapLevels

/-! Actual inverse-limit comparison for completion of the completed-base tensor ring. -/

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.Algebra.CompletionFlatMap

open CompletionRegularityBasics CompletionLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The actual finite completed coefficient maps commute with the original transitions. -/
theorem levelCoefficient_transition {m n : ℕ} (h : m ≤ n) (x : Completion A) :
    Ideal.Quotient.factorPow (maximalIdeal B) h (levelCoefficient A B n x) =
      levelCoefficient A B m x :=
  RingHom.congr_fun (completionMapLevel_compat (algebraMap A B) h) x

/-- The actual tensor maps commute with all original quotient transitions. -/
theorem tensorLevelMap_transition {m n : ℕ} (h : m ≤ n) (z : TensorRing A B) :
    Ideal.Quotient.factorPow (maximalIdeal B) h (tensorLevelMap A B n z) =
      tensorLevelMap A B m z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      rw [tensorLevelMap_tmul, tensorLevelMap_tmul, map_mul,
        levelCoefficient_transition, Ideal.Quotient.factor_mk]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The forward maps of the full tensor quotients are compatible with transitions. -/
theorem levelForward_transition {m n : ℕ} (h : m ≤ n)
    (z : TensorRing A B ⧸ tensorIdeal A B ^ n) :
    Ideal.Quotient.factorPow (maximalIdeal B) h (levelForward A B n z) =
      levelForward A B m (Ideal.Quotient.factorPow (tensorIdeal A B) h z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact tensorLevelMap_transition A B h z

omit [IsLocalHom (algebraMap A B)] in
/-- The literal original-target inclusions on quotients are compatible with transitions. -/
theorem levelBackward_transition {m n : ℕ} (h : m ≤ n)
    (b : B ⧸ maximalIdeal B ^ n) :
    Ideal.Quotient.factorPow (tensorIdeal A B) h (levelBackward A B n b) =
      levelBackward A B m (Ideal.Quotient.factorPow (maximalIdeal B) h b) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

private theorem tensorForwardLevels_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp
      ((levelForward A B n).comp (AdicCompletion.evalₐ (tensorIdeal A B) n).toRingHom) =
      (levelForward A B m).comp (AdicCompletion.evalₐ (tensorIdeal A B) m).toRingHom := by
  ext x
  change Ideal.Quotient.factorPow _ h (levelForward A B _ (AdicCompletion.evalₐ _ _ x)) = _
  rw [levelForward_transition, factorPow_evalₐ]
  rfl

omit [IsLocalHom (algebraMap A B)] in
private theorem tensorBackwardLevels_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (tensorIdeal A B) h).comp
      ((levelBackward A B n).comp (AdicCompletion.evalₐ (maximalIdeal B) n).toRingHom) =
      (levelBackward A B m).comp (AdicCompletion.evalₐ (maximalIdeal B) m).toRingHom := by
  ext x
  change Ideal.Quotient.factorPow _ h (levelBackward A B _ (AdicCompletion.evalₐ _ _ x)) = _
  rw [levelBackward_transition, factorPow_evalₐ]
  rfl

/-- The actual forward inverse-limit map from tensor completion to original target completion. -/
def tensorCompletionForward :
    AdicCompletion (tensorIdeal A B) (TensorRing A B) →+* Completion B :=
  AdicCompletion.liftRingHom (maximalIdeal B)
    (fun n ↦ (levelForward A B n).comp (AdicCompletion.evalₐ (tensorIdeal A B) n).toRingHom)
    (tensorForwardLevels_compatible A B)

/-- The actual inverse inverse-limit map, built from the original target inclusions. -/
def tensorCompletionBackward :
    Completion B →+* AdicCompletion (tensorIdeal A B) (TensorRing A B) :=
  AdicCompletion.liftRingHom (tensorIdeal A B)
    (fun n ↦ (levelBackward A B n).comp (AdicCompletion.evalₐ (maximalIdeal B) n).toRingHom)
    (tensorBackwardLevels_compatible A B)

/-- The forward comparison has its specified actual finite-level maps. -/
theorem eval_tensorCompletionForward (n : ℕ)
    (x : AdicCompletion (tensorIdeal A B) (TensorRing A B)) :
    AdicCompletion.evalₐ (maximalIdeal B) n (tensorCompletionForward A B x) =
      levelForward A B n (AdicCompletion.evalₐ (tensorIdeal A B) n x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _ (tensorForwardLevels_compatible A B) n x

omit [IsLocalHom (algebraMap A B)] in
/-- The backward comparison has its specified actual finite-level maps. -/
theorem eval_tensorCompletionBackward (n : ℕ) (x : Completion B) :
    AdicCompletion.evalₐ (tensorIdeal A B) n (tensorCompletionBackward A B x) =
      levelBackward A B n (AdicCompletion.evalₐ (maximalIdeal B) n x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _ (tensorBackwardLevels_compatible A B) n x

/-- The entire actual completed coefficient map is retained, not just its original dense coefficients. -/
theorem tensorCompletionForward_algebraMap (x : Completion A) :
    tensorCompletionForward A B
      (algebraMap (Completion A) (AdicCompletion (tensorIdeal A B) (TensorRing A B)) x) =
      completionMap (algebraMap A B) x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_tensorCompletionForward, evalₐ_completionMap]
  change levelForward A B n
    (AdicCompletion.evalₐ (tensorIdeal A B) n
      (AdicCompletion.of (tensorIdeal A B) (TensorRing A B) (x ⊗ₜ[A] 1))) = _
  rw [AdicCompletion.evalₐ_of]
  change tensorLevelMap A B n (x ⊗ₜ[A] 1) = _
  rw [tensorLevelMap_tmul, map_one, mul_one]
  rfl

/-- The actual tensor-completion forward and backward maps are inverse. -/
theorem tensorCompletionForward_tensorCompletionBackward (x : Completion B) :
    tensorCompletionForward A B (tensorCompletionBackward A B x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_tensorCompletionForward, eval_tensorCompletionBackward, levelForward_levelBackward]

variable [IsNoetherianRing A]

/-- The actual tensor-completion backward and forward maps are inverse. -/
theorem tensorCompletionBackward_tensorCompletionForward
    (x : AdicCompletion (tensorIdeal A B) (TensorRing A B)) :
    tensorCompletionBackward A B (tensorCompletionForward A B x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_tensorCompletionBackward, eval_tensorCompletionForward, levelBackward_levelForward]

/-- Genuine comparison of the literal tensor-ideal completion with the literal target completion. -/
def tensorCompletionEquiv :
    AdicCompletion (tensorIdeal A B) (TensorRing A B) ≃+* Completion B :=
  RingEquiv.ofRingHom (tensorCompletionForward A B) (tensorCompletionBackward A B)
    (RingHom.ext (tensorCompletionForward_tensorCompletionBackward A B))
    (RingHom.ext (tensorCompletionBackward_tensorCompletionForward A B))

/-- The actual comparison is over the literal induced completed coefficient map. -/
theorem tensorCompletionEquiv_comp_algebraMap :
    (tensorCompletionEquiv A B).toRingHom.comp
      (algebraMap (Completion A) (AdicCompletion (tensorIdeal A B) (TensorRing A B))) =
      completionMap (algebraMap A B) :=
  RingHom.ext (tensorCompletionForward_algebraMap A B)

end DeJongAlterations.Algebra.CompletionFlatMap

import DeJongAlterations.Algebra.NodeGeometricCompletionHausdorffDifferentials
import DeJongAlterations.Algebra.NodeCompletionPolynomial
import DeJongAlterations.Algebra.NodeFittingGeneralBaseChange

/-! Actual completion of the ORIGINAL polynomial hypersurface and its ORIGINAL differential
module along the canonical formal map. This is the formal-model side of the continuous
comparison; transport from an arbitrary original geometric stalk is separate. -/

noncomputable section

open TensorProduct

namespace DeJongAlterations.Algebra.NodeGeometricCompletionFormalModel

open NodeFittingGeneral NodeGeometricCompletionCoherentDifferentials

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K] (f : MvPolynomial (Fin 2) K)

local instance polynomialHypersurface_noetherian : IsNoetherianRing (PolynomialHypersurface f) :=
  isNoetherianRing_of_surjective (MvPolynomial (Fin 2) K) _ (Ideal.Quotient.mk (polynomialIdeal f))
    Ideal.Quotient.mk_surjective

/-- The actual original coordinate ideal, without a local or domain assumption on the hypersurface. -/
abbrev coordinateIdeal : Ideal (PolynomialHypersurface f) :=
  (MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk (polynomialIdeal f))

/-- The original equation becomes its literal original formal equation. -/
theorem formalIdeal_eq_map : Ideal.span {(f : NodeFormalMorse.Series K)} =
    (polynomialIdeal f).map
      (algebraMap (MvPolynomial (Fin 2) K) (NodeFormalMorse.Series K)) := by
  simp only [polynomialIdeal, Ideal.map_span, Set.image_singleton]
  rfl

/-- The actual quotient of the polynomial completion, retaining the ORIGINAL polynomial action. -/
def formalQuotientEquiv :
    (AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (MvPolynomial (Fin 2) K) ⧸
      (polynomialIdeal f).map (algebraMap (MvPolynomial (Fin 2) K)
        (AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (MvPolynomial (Fin 2) K))))
      ≃ₐ[MvPolynomial (Fin 2) K] FormalHypersurface f :=
  Ideal.quotientEquivAlg _ _ (NodeCompletion.polynomialCompletionEquiv K) (by
    rw [formalIdeal_eq_map, Ideal.map_map]
    have he : (NodeCompletion.polynomialCompletionEquiv K).toRingHom.comp
        (algebraMap (MvPolynomial (Fin 2) K)
          (AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (MvPolynomial (Fin 2) K))) =
        algebraMap (MvPolynomial (Fin 2) K) (NodeFormalMorse.Series K) := by
      apply RingHom.ext
      intro p
      exact (NodeCompletion.polynomialCompletionEquiv K).commutes p
    exact congrArg (fun g : MvPolynomial (Fin 2) K →+* NodeFormalMorse.Series K =>
      Ideal.map g (polynomialIdeal f)) he.symm)

/-- The actual completion is the literal formal hypersurface over the ORIGINAL coefficient field. -/
def completionEquiv :
    AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f) ≃ₐ[K] FormalHypersurface f :=
  ((AdicCompletion.quotientAlgEquiv
    (MvPolynomial.idealOfVars (Fin 2) K) (polynomialIdeal f)).symm.trans
      (formalQuotientEquiv K f)).restrictScalars K

/-- EVERY original polynomial quotient representative, not only both coordinate classes, is retained. -/
theorem completionEquiv_original (p : PolynomialHypersurface f) :
    completionEquiv K f (algebraMap (PolynomialHypersurface f)
      (AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f)) p) =
        polynomialToFormal f p := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective p
  change formalQuotientEquiv K f
    ((AdicCompletion.quotientAlgEquiv _ _).symm
      (AdicCompletion.of _ _ (Ideal.Quotient.mk _ g))) = _
  rw [← AdicCompletion.quotientAlgEquiv_of
    (MvPolynomial.idealOfVars (Fin 2) K) (polynomialIdeal f) g]
  rw [AlgEquiv.symm_apply_apply]
  change Ideal.Quotient.mk _ (NodeCompletion.polynomialCompletionEquiv K
    (AdicCompletion.of _ _ g)) = _
  rw [NodeCompletion.polynomialCompletionEquiv_of]
  rfl

/-- The SAME actual completed-ring equivalence is over the WHOLE original hypersurface map. -/
def completionOriginalAlgEquiv :
    AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f)
      ≃ₐ[PolynomialHypersurface f] FormalHypersurface f :=
  AlgEquiv.ofRingEquiv (f := (completionEquiv K f).toRingEquiv)
    (completionEquiv_original K f)

local instance completedOmega_scalarTower :
    IsScalarTower (PolynomialHypersurface f)
      (AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f))
      (CompletedOmega K (PolynomialHypersurface f) (coordinateIdeal K f)) where
  smul_assoc r a ω := by
    apply AdicCompletion.ext
    intro n
    rw [AdicCompletion.smul_eval, AdicCompletion.val_smul_apply,
      AdicCompletion.val_smul_apply, AdicCompletion.smul_eval, smul_assoc]

/-- Actual comparison of the completed ORIGINAL differential module with the ORIGINAL
polynomial differential module pulled along the canonical formal map. -/
def completedOmegaFormalEquiv :
    CompletedOmega K (PolynomialHypersurface f) (coordinateIdeal K f)
      ≃ₗ[PolynomialHypersurface f] FormalModelDifferentials f :=
  ((completedOmegaTensorEquiv K (PolynomialHypersurface f) (coordinateIdeal K f)).symm.restrictScalars
      (PolynomialHypersurface f)).trans
    (TensorProduct.congr (completionOriginalAlgEquiv K f).toLinearEquiv (LinearEquiv.refl _ _))

/-- Every ORIGINAL differential value is the actual pulled original value. -/
theorem completedOmegaFormalEquiv_original (ω : KaehlerDifferential K (PolynomialHypersurface f)) :
    completedOmegaFormalEquiv K f (AdicCompletion.of (coordinateIdeal K f)
      (KaehlerDifferential K (PolynomialHypersurface f)) ω) = 1 ⊗ₜ[PolynomialHypersurface f] ω := by
  unfold completedOmegaFormalEquiv completedOmegaTensorEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of, TensorProduct.congr_tmul,
    AlgEquiv.toLinearEquiv_apply, map_one, LinearEquiv.refl_apply]

/-- The comparison is equivariant for EVERY actual completed scalar, through the same
canonical completion equivalence. -/
theorem completedOmegaFormalEquiv_smul
    (a : AdicCompletion (coordinateIdeal K f) (PolynomialHypersurface f))
    (ω : CompletedOmega K (PolynomialHypersurface f) (coordinateIdeal K f)) :
    completedOmegaFormalEquiv K f (a • ω) =
      completionEquiv K f a • completedOmegaFormalEquiv K f ω := by
  obtain ⟨t, rfl⟩ := (completedOmegaTensorEquiv K (PolynomialHypersurface f)
    (coordinateIdeal K f)).surjective ω
  rw [← map_smul]
  simp only [completedOmegaFormalEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    simp only [smul_tmul', TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, map_mul, smul_eq_mul]
    rfl
  | add t s ht hs =>
    simp only [map_add, smul_add, ht, hs]

end DeJongAlterations.Algebra.NodeGeometricCompletionFormalModel

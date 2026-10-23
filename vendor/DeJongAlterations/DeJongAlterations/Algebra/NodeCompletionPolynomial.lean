import DeJongAlterations.Algebra.AdicCompletionTransportQuotient
import DeJongAlterations.Algebra.AdicCompletionTransportLocalization
import DeJongAlterations.Algebra.NodeChart
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Native completion of a polynomial hypersurface and the split node -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (K : Type u) [Field K]

abbrev PolynomialRing := MvPolynomial (Fin 2) K
abbrev SeriesRing := MvPowerSeries (Fin 2) K
abbrev nodeIdeal : Ideal (PolynomialRing K) := NodeChart.uChartIdeal K 0
abbrev Node := PolynomialRing K ⧸ nodeIdeal K
abbrev originIdeal : Ideal (Node K) :=
  (MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk (nodeIdeal K))
abbrev formalNodeIdeal : Ideal (SeriesRing K) :=
  Ideal.span {MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1}
abbrev FormalNode := SeriesRing K ⧸ formalNodeIdeal K

/-- The polynomial relation becomes exactly the native formal node relation. -/
theorem formalNodeIdeal_eq_map : formalNodeIdeal K =
    (nodeIdeal K).map (algebraMap (PolynomialRing K) (SeriesRing K)) := by
  rw [formalNodeIdeal]
  simp only [nodeIdeal, NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
  apply congrArg Ideal.span
  apply congrArg Set.singleton
  change MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 =
    ((MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (0 : K) : PolynomialRing K) :
      SeriesRing K)
  simp

/-- The actual completion of the polynomial ring is its native formal series algebra. -/
def polynomialCompletionEquiv :
    AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (PolynomialRing K) ≃ₐ[PolynomialRing K]
      SeriesRing K :=
  (MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) K).symm

@[simp]
theorem polynomialCompletionEquiv_of (f : PolynomialRing K) :
    polynomialCompletionEquiv K
      (AdicCompletion.of (MvPolynomial.idealOfVars (Fin 2) K) (PolynomialRing K) f) =
        (f : SeriesRing K) := by
  apply (MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) K).injective
  change (MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) K)
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) K).symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (MvPowerSeries.toAdicCompletion_coe f).symm

/-- The quotient of the actual polynomial completion is the literal formal node quotient. -/
def formalQuotientEquiv :
    ((AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (PolynomialRing K)) ⧸
      (nodeIdeal K).map (algebraMap (PolynomialRing K)
        (AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (PolynomialRing K)))) ≃ₐ[PolynomialRing K]
      FormalNode K :=
  Ideal.quotientEquivAlg _ _ (polynomialCompletionEquiv K) (by
    rw [formalNodeIdeal_eq_map, Ideal.map_map]
    have he : (polynomialCompletionEquiv K).toRingHom.comp
        (algebraMap (PolynomialRing K)
          (AdicCompletion (MvPolynomial.idealOfVars (Fin 2) K) (PolynomialRing K))) =
        algebraMap (PolynomialRing K) (SeriesRing K) := by
      apply RingHom.ext
      intro a
      exact (polynomialCompletionEquiv K).commutes a
    exact congrArg (fun f : PolynomialRing K →+* SeriesRing K =>
      Ideal.map f (nodeIdeal K)) he.symm)

/-- The completion of the actual polynomial node at the actual origin ideal. -/
def nodeAdicCompletionEquiv :
    AdicCompletion (originIdeal K) (Node K) ≃ₐ[K] FormalNode K :=
  ((AdicCompletion.quotientAlgEquiv
    (MvPolynomial.idealOfVars (Fin 2) K) (nodeIdeal K)).symm.trans
      (formalQuotientEquiv K)).restrictScalars K

@[simp]
theorem nodeAdicCompletionEquiv_coordinate (i : Fin 2) :
    nodeAdicCompletionEquiv K (AdicCompletion.of (originIdeal K) (Node K)
      (Ideal.Quotient.mk (nodeIdeal K) (MvPolynomial.X i))) =
        Ideal.Quotient.mk (formalNodeIdeal K) (MvPowerSeries.X i) := by
  change formalQuotientEquiv K
    ((AdicCompletion.quotientAlgEquiv _ _).symm
      (AdicCompletion.of _ _ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = _
  rw [← AdicCompletion.quotientAlgEquiv_of
    (MvPolynomial.idealOfVars (Fin 2) K) (nodeIdeal K) (MvPolynomial.X i)]
  rw [AlgEquiv.symm_apply_apply]
  change Ideal.Quotient.mk _ (polynomialCompletionEquiv K
    (AdicCompletion.of _ _ (MvPolynomial.X i))) = _
  rw [polynomialCompletionEquiv_of, MvPolynomial.coe_X]

/-- The origin ideal of the polynomial ring is the actual constant-coefficient kernel. -/
theorem idealOfVars_eq_ker_constantCoeff :
    MvPolynomial.idealOfVars (Fin 2) K =
      RingHom.ker (MvPolynomial.constantCoeff : PolynomialRing K →+* K) := by
  ext f
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) K),
    MvPolynomial.mem_pow_idealOfVars_iff', RingHom.mem_ker]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact h

instance polynomialOrigin_isMaximal : (MvPolynomial.idealOfVars (Fin 2) K).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _
    (fun k => ⟨MvPolynomial.C k, MvPolynomial.constantCoeff_C _ _⟩)

/-- The actual node equation vanishes at the rational polynomial origin. -/
theorem nodeIdeal_le_idealOfVars :
    nodeIdeal K ≤ MvPolynomial.idealOfVars (Fin 2) K := by
  rw [idealOfVars_eq_ker_constantCoeff]
  apply Ideal.span_le.mpr
  rintro f rfl
  simp

instance originIdeal_isMaximal : (originIdeal K).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by simpa using nodeIdeal_le_idealOfVars K)

/-- The actual local node ring is the actual localization at its rational origin. -/
abbrev LocalNode := Localization.AtPrime (originIdeal K)

/-- The actual completed local node ring, preserving its native coefficient field. -/
def localNodeCompletionEquiv :
    AdicCompletion (R := LocalNode K) (IsLocalRing.maximalIdeal (LocalNode K)) (LocalNode K) ≃ₐ[K]
      FormalNode K :=
  ((AdicCompletion.localizationAlgEquiv (originIdeal K) (LocalNode K)).symm.restrictScalars K).trans
    (nodeAdicCompletionEquiv K)

@[simp]
theorem localNodeCompletionEquiv_coordinate (i : Fin 2) :
    localNodeCompletionEquiv K
      (AdicCompletion.of (R := LocalNode K) _ (LocalNode K)
        (algebraMap (Node K) (LocalNode K)
          (Ideal.Quotient.mk (nodeIdeal K) (MvPolynomial.X i)))) =
      Ideal.Quotient.mk (formalNodeIdeal K) (MvPowerSeries.X i) := by
  change nodeAdicCompletionEquiv K
    ((AdicCompletion.localizationAlgEquiv (originIdeal K) (LocalNode K)).symm _) = _
  rw [← AdicCompletion.localizationAlgEquiv_of (originIdeal K) (LocalNode K)
    (Ideal.Quotient.mk (nodeIdeal K) (MvPolynomial.X i))]
  rw [AlgEquiv.symm_apply_apply]
  exact nodeAdicCompletionEquiv_coordinate K i

end DeJongAlterations.Algebra.NodeCompletion

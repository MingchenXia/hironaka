import TranscendentalNakamaye.Pending.HironakaActualInitialPivotNormality
import TranscendentalNakamaye.Pending.HironakaActualPersistentPointConeDerivatives

/-!
# Actual original zero-point HS persistence iff every canonical order persists

The actual coherent-cone tangent calculation discharges source derivative
stability internally. Whole current initial colons and canonical reduced-tail
normality then force all normalized canonical orders. ONE original analytic
canonical family is chosen before the full HS/order equivalence, with actual
quotient equations and the entire independently defined normalized ideal.
No tangent-stability, shadow, family, order or diagram certificate is input.
Scope: zero-direction point charts; arbitrary directions, relative maximal
standardness and the full current-history driver remain separate.
Blueprint: `hironaka-actual-zero-point-hs-order-criterion-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace TranscendentalNakamaye.Pending.HironakaActualZeroPointHSOrderCriterion
noncomputable section
open FirstPass HolGerm HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticStrictGenerators
  HironakaActualInitialPivotNormality HironakaActualPersistentPointConeDerivatives
  HironakaRelativeNormalMonomialBasis HironakaHolomorphicPointJets
  HironakaActualPointOrderRetainingHS HironakaActualOriginalFormalTaylor
  HironakaActualOriginalReducedVertexBasis HironakaActualAnalyticBlowupTaylor
  HironakaRelativeNormalIdeal HironakaRelativeNormalActualBaseJetDimension
  HironakaHolomorphicJetMonomialSpan HironakaActualFormalBlowupMemberGeneration
  HironakaActualOriginalFormalHSTransfer
variable {n : ℕ}

theorem original_zero_point_persistent_hs_orders
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n)
    (hPersist : ∀ ℓ,hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ) :
    ∀ (a : actualInitialVertices MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
      (H : MvPowerSeries (Fin n) ℂ),
      (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=actualFormalBlowup univ e (fun _ => 0)
        (actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) →
      H∈actualFormalCoordinateIdeal n univ^(normalExponentDegree a.val) := by
  exact original_zero_point_persistent_hs_orders_of_source_tangent_stable I e
    (initial_pderiv_of_zero_point_hs_persistence I e hPersist) hPersist

private theorem unshiftedTaylor_property_iff (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop) :
    P n (actualUnshiftedTaylorAlgHom n) ↔ P (0+n) (originalTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) ↔ P m f := by
    subst m
    rfl
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n)

private theorem originalTaylor_analytic_point_blowup (j : Fin n)
    (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom n (actualAnalyticBlowupPullback
      (actualTangentCentreVariables 0 n) (j.natAdd 0) (fun _ => 0) g)=
      actualFormalBlowup univ j (fun _ => 0) (originalTaylorAlgHom n g) := by
  let P (m : ℕ) (τ : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (hm : m=n) (e : Fin m) (g : HolGerm (ComplexModel m)),
      τ (actualAnalyticBlowupPullback univ e (fun _ => 0) g)=
        actualFormalBlowup univ (Fin.cast hm e) (fun _ => 0) (τ g)
  have h : P n (actualUnshiftedTaylorAlgHom n) := by
    intro hm e g
    have he : Fin.cast hm e=e := by apply Fin.ext; rfl
    rw [he]
    exact DFunLike.congr_fun (actualTaylor_analyticBlowupPullback univ e (fun _ => 0)) g
  have h' := ((unshiftedTaylor_property_iff n P).mp h) (Nat.zero_add n) (j.natAdd 0) g
  have he : Fin.cast (Nat.zero_add n) (j.natAdd 0)=j := by apply Fin.ext; simp
  have hA : actualTangentCentreVariables 0 n=univ := by
    ext i
    simp only [actualTangentCentreVariables,mem_range,mem_univ,iff_true]
    exact ⟨Fin.cast (Nat.zero_add n) i,Fin.ext (by simp)⟩
  simpa only [he,hA] using h'

private theorem originalTaylor_canonical_quotient_order
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n)
    (hPersist : ∀ ℓ,hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables 0 n) (j.natAdd 0) (fun _ => 0)) ℓ=
      hilbertSamuelValue I ℓ)
    (a : actualInitialVertices MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom I))
    (H : HolGerm (ComplexModel (0+n)))
    (hH : (coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) (fun _ => 0)
        (originalReducedVertexBasis I a)) :
    H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val) := by
  let P (m : ℕ) (τ : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (hm : m=n) (I : Ideal (HolGerm (ComplexModel m))) (e : Fin m),
      (∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ) →
      ∀ (a : actualInitialVertices MonomialOrder.degLex (Ideal.map τ.toRingHom I))
        (F : MvPowerSeries (Fin n) ℂ),
        (MvPowerSeries.X (Fin.cast hm e))^(normalExponentDegree a.val)*F=
          actualFormalBlowup univ (Fin.cast hm e) (fun _ => 0)
            (actualReducedVertexSeries MonomialOrder.degLex (Ideal.map τ.toRingHom I) a) →
        F∈actualFormalCoordinateIdeal n univ^(normalExponentDegree a.val)
  have h : P n (actualUnshiftedTaylorAlgHom n) := by
    intro hm I e hp
    have he : Fin.cast hm e=e := by apply Fin.ext; rfl
    rw [he]
    exact original_zero_point_persistent_hs_orders I e hp
  have hA : actualTangentCentreVariables 0 n=univ := by
    ext i
    simp only [actualTangentCentreVariables,mem_range,mem_univ,iff_true]
    exact ⟨Fin.cast (Nat.zero_add n) i,Fin.ext (by simp)⟩
  have hPersist' := hPersist
  rw [hA] at hPersist'
  have hp := ((unshiftedTaylor_property_iff n P).mp h) (Nat.zero_add n) I (j.natAdd 0) hPersist'
  have he : Fin.cast (Nat.zero_add n) (j.natAdd 0)=j := by apply Fin.ext; simp
  rw [he] at hp
  have hEq := congrArg (originalTaylorAlgHom n) hH
  rw [map_mul,map_pow,show originalTaylorAlgHom n (coordinateGerm (j.natAdd 0))=MvPowerSeries.X j by
      simpa only [normalCoordinate] using originalTaylorAlgHom_coordinate n j,originalTaylor_analytic_point_blowup,
    originalReducedVertexBasis_taylor] at hEq
  have hPow := hp a (originalTaylorAlgHom n H) hEq
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ H).mpr
  rw [show actualFormalCoordinateIdeal n univ=genuineFormalVariables n by
    simp [actualFormalCoordinateIdeal,genuineFormalVariables]] at hPow
  exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mp hPow

theorem exists_original_zero_point_hs_iff_orders_family
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) :
    ∃ H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (originalTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) (fun _ => 0)
          (originalReducedVertexBasis I a)) ∧
      actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables 0 n) (j.natAdd 0) (fun _ => 0)=Ideal.span (range H) ∧
      ((∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables 0 n)
          (j.natAdd 0) (fun _ => 0)) ℓ=hilbertSamuelValue I ℓ) ↔
        ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val)) := by
  obtain ⟨H,hH,hSpan,hForward⟩ := exists_original_point_order_retaining_hs_family I j (fun _ => 0)
  refine ⟨H,hH,hSpan,?_,?_⟩
  · intro hp a
    exact originalTaylor_canonical_quotient_order I j hp a (H a) (hH a)
  · exact hForward

end
end TranscendentalNakamaye.Pending.HironakaActualZeroPointHSOrderCriterion

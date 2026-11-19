import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! Actual polynomial source shears remove a blowup direction while retaining
the SAME actual analytic normalized quotient. Source coordinate functions,
both inverse identities and the whole germ pullback are constructed here.
The quotient is produced from the original genuine centre power, not supplied
as a compatibility certificate. The target coordinate itself is unchanged.

This lower analytic block does not assert current target monicity, transport
a historical selector, or close the pointed or whole historical phase. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualAnalyticDirectionRemovalQuotient

noncomputable section

open HolGerm HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalBlowupMemberGeneration HironakaActualAnalyticBlowupTaylor

variable {n : ℕ}

/-- The true PLUS source map; its inverse is obtained by replacing b by -b. -/
def actualAnalyticDirectionShear (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ComplexModel n → ComplexModel n :=
  fun z => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => z i + if i ∈ A \ {e} then b i * z e else 0)

theorem actualAnalyticDirectionShear_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (i : Fin n) :
    actualAnalyticDirectionShear A e b z i = z i + if i ∈ A \ {e} then b i * z e else 0 := rfl

theorem actualAnalyticDirectionShear_owner (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) : actualAnalyticDirectionShear A e b z e = z e := by
  simp [actualAnalyticDirectionShear_apply]

theorem actualAnalyticDirectionShear_coordinate_of_zero
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (i : Fin n) (hb : b i = 0)
    (z : ComplexModel n) : actualAnalyticDirectionShear A e b z i = z i := by
  simp [actualAnalyticDirectionShear_apply, hb]

theorem differentiable_actualAnalyticDirectionShear
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Differentiable ℂ (actualAnalyticDirectionShear A e b) := by
  have hp (i : Fin n) : Differentiable ℂ (fun z : ComplexModel n => z i) :=
    ((ContinuousLinearMap.proj i).comp
      (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).toContinuousLinearMap).differentiable
  have hc (i : Fin n) : Differentiable ℂ
      (fun z : ComplexModel n => z i + if i ∈ A \ {e} then b i * z e else 0) := by
    by_cases hi : i ∈ A \ {e}
    · simp only [if_pos hi]
      exact (hp i).add ((differentiable_const (b i)).mul (hp e))
    · simpa only [if_neg hi, add_zero] using hp i
  exact (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiable.comp
    (differentiable_pi.mpr hc)

theorem actualAnalyticDirectionShear_zero (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticDirectionShear A e b 0 = 0 := by
  ext i
  simp [actualAnalyticDirectionShear_apply]

theorem actualAnalyticDirectionShear_left_inverse
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) :
    actualAnalyticDirectionShear A e (fun i => -b i)
      (actualAnalyticDirectionShear A e b z) = z := by
  ext i
  by_cases hi : i ∈ A \ {e} <;>
    simp [actualAnalyticDirectionShear_apply, hi]

theorem actualAnalyticDirectionShear_right_inverse
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) :
    actualAnalyticDirectionShear A e b
      (actualAnalyticDirectionShear A e (fun i => -b i) z) = z := by
  simpa only [neg_neg] using actualAnalyticDirectionShear_left_inverse A e (fun i => -b i) z

/-- Actual entire function data, with both inverse PROOF fields produced. -/
def actualAnalyticDirectionShearLocalEquiv
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := actualAnalyticDirectionShear A e b
  invFun := actualAnalyticDirectionShear A e (fun i => -b i)
  toFun_holomorphic := (differentiable_actualAnalyticDirectionShear A e b).differentiableOn
  invFun_holomorphic := (differentiable_actualAnalyticDirectionShear A e (fun i => -b i)).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun z _ => actualAnalyticDirectionShear_left_inverse A e b z
  right_inv := fun z _ => actualAnalyticDirectionShear_right_inverse A e b z

/-- The whole genuine germ automorphism is PLUS-map pullback. Physical source
coordinates use the inverse MINUS map when removing a direction. -/
def actualAnalyticDirectionShearGermEquiv
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualAnalyticDirectionShearLocalEquiv A e b)
    (actualAnalyticDirectionShear_zero A e b)

/-- The literal polynomial factorization holds on EVERY point. -/
theorem actualAnalyticDirectionShear_zero_chart
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) :
    actualAnalyticDirectionShear A e b (actualAnalyticBlowupMap A e (fun _ => 0) z) =
      actualAnalyticBlowupMap A e b z := by
  ext i
  by_cases hi : i ∈ A
  · by_cases hie : i = e
    · subst i
      simp [actualAnalyticDirectionShear_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi]
    · simp [actualAnalyticDirectionShear_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi, hie]
      ring
  · simp [actualAnalyticDirectionShear_apply, actualAnalyticBlowupMap_apply,
      actualAnalyticBlowupCoordinate, hi]

/-- The actual MINUS change of source coordinates removes the direction;
the target coordinate z is unchanged. -/
theorem actualAnalyticDirectionShear_remove_direction
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) :
    actualAnalyticDirectionShear A e (fun i => -b i) (actualAnalyticBlowupMap A e b z) =
      actualAnalyticBlowupMap A e (fun _ => 0) z := by
  calc
    _ = actualAnalyticDirectionShear A e (fun i => -b i)
        (actualAnalyticDirectionShear A e b (actualAnalyticBlowupMap A e (fun _ => 0) z)) :=
      congrArg (actualAnalyticDirectionShear A e (fun i => -b i))
        (actualAnalyticDirectionShear_zero_chart A e b z).symm
    _ = _ := actualAnalyticDirectionShear_left_inverse A e b _

/-- Entire analytic germ pullbacks have the SAME real polynomial square.
No Taylor approximation or desired compatibility is assumed. -/
theorem actualAnalyticBlowupPullback_direction_shear
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
    actualAnalyticBlowupPullback A e b g =
      actualAnalyticBlowupPullback A e (fun _ => 0)
        (actualAnalyticDirectionShearGermEquiv A e b g) := by
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk g
  have h0 : (actualAnalyticDirectionShearLocalEquiv A e b).toFun 0 = 0 :=
    actualAnalyticDirectionShear_zero A e b
  change actualAnalyticBlowupPullback A e b (HolGerm.mk H hH) =
    actualAnalyticBlowupPullback A e (fun _ => 0)
      (localGermAlgEquiv (actualAnalyticDirectionShearLocalEquiv A e b) h0 (HolGerm.mk H hH))
  rw [localGermAlgEquiv_mk]
  unfold actualAnalyticBlowupPullback
  rw [compAlgHom_mk, compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    change H (actualAnalyticBlowupMap A e b z) =
      H (actualAnalyticDirectionShear A e b (actualAnalyticBlowupMap A e (fun _ => 0) z))
    exact congrArg H (actualAnalyticDirectionShear_zero_chart A e b z).symm

/-- ONLY the original actual centre power produces ONE actual holomorphic
quotient for BOTH the original direction chart and the zero chart of the SAME
source member after its real source change. Marks and analytic numerators are
retained; there is no caller quotient or target-order certificate. -/
theorem exists_actual_same_analytic_quotient_after_direction_removal
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (μ : ℕ) (g : HolGerm (ComplexModel n)) (hg : g ∈ actualAnalyticCoordinateIdeal A ^ μ) :
    ∃ N : HolGerm (ComplexModel n),
      (coordinateGerm e) ^ μ * N = actualAnalyticBlowupPullback A e b g ∧
      (coordinateGerm e) ^ μ * N = actualAnalyticBlowupPullback A e (fun _ => 0)
        (actualAnalyticDirectionShearGermEquiv A e b g) ∧
      actualUnshiftedTaylorAlgHom n N = actualNormalizedFormalMember A e he b μ
        (actualUnshiftedTaylorAlgHom n g) (actualTaylor_mem_coordinateCentre_pow A μ g hg) := by
  obtain ⟨N, hN, hTaylor⟩ := exists_actualAnalyticBlowup_quotient A e he b μ g hg
  refine ⟨N, hN, ?_, hTaylor⟩
  exact hN.trans (actualAnalyticBlowupPullback_direction_shear A e b g)

end

end Hironaka.HironakaActualAnalyticDirectionRemovalQuotient

import DeJongAlterations.Algebra.NodeFieldQuadraticPresentation
import DeJongAlterations.Algebra.NodeVariableMorseJacobian
import DeJongAlterations.Algebra.CompletionIdealQuotient

/-! # Native original quadratic-source local structure, residue coefficients and whole ideal powers

Source structures are internally derived from actual zero constant coefficient,
independently of the target/evaluation. The SAME actual quadratic surjection is
local and maps every native maximal-ideal power exactly. No principal-kernel or
classification isomorphism is assumed or asserted.
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldQuadraticSource

open NodeFormalMorse NodeVariableMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (K : Type u) [Field K]

/-- The entire original variable ideal is the SAME native formal-series maximal ideal. -/
theorem variableIdeal_eq_maximalIdeal : variableIdeal K = maximalIdeal (Series K) := by
  apply le_antisymm variableIdeal_le_maximalIdeal
  intro f hf
  apply mem_variableIdeal_of_constantCoeff_eq_zero
  by_contra hc
  exact hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc))

/-- Original zero constant INTERNALLY puts the whole original equation ideal in the native maximal ideal. -/
theorem equationIdeal_le_maximalIdeal (f : Series K) (hf : constantCoeff f = 0) :
    Ideal.span {f} ≤ maximalIdeal (Series K) := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact variableIdeal_le_maximalIdeal (mem_variableIdeal_of_constantCoeff_eq_zero hf)

/-- Nontriviality of the ACTUAL native quotient, with no supplied local-source certificate. -/
theorem equationNontrivial (f : Series K) (hf : constantCoeff f = 0) : Nontrivial (Equation f) :=
  CompletionIdealQuotient.quotientNontrivial _ (equationIdeal_le_maximalIdeal K f hf)

/-- Native local structure on the SAME actual original quotient, independent of any target algebra. -/
theorem equationLocalRing (f : Series K) (hf : constantCoeff f = 0) : IsLocalRing (Equation f) :=
  CompletionIdealQuotient.quotientLocalRing _ (equationIdeal_le_maximalIdeal K f hf)

/-- Native Noetherianity comes from the original native field-series ring and actual quotient surjectivity. -/
theorem equationNoetherian (f : Series K) : IsNoetherianRing (Equation f) :=
  isNoetherianRing_of_surjective (Series K) _ (Ideal.Quotient.mk (Ideal.span {f}))
    Ideal.Quotient.mk_surjective

/-- The WHOLE native quotient maximal ideal is exactly the actual original variable-ideal image. -/
theorem equation_maximalIdeal (f : Series K) (hf : constantCoeff f = 0) :
    letI := equationLocalRing K f hf
    maximalIdeal (Equation f) = (variableIdeal K).map (Ideal.Quotient.mk (Ideal.span {f})) := by
  let := equationLocalRing K f hf
  rw [variableIdeal_eq_maximalIdeal K]
  exact (map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
    Ideal.Quotient.mk_surjective).symm

/-- EVERY entire original variable-ideal power has its exact SAME native quotient maximal-power image. -/
theorem equation_variable_pow_map (f : Series K) (hf : constantCoeff f = 0) (n : ℕ) :
    letI := equationLocalRing K f hf
    (variableIdeal K ^ n).map (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal (Equation f) ^ n := by
  let := equationLocalRing K f hf
  rw [Ideal.map_pow, ← equation_maximalIdeal K f hf]

/-- The actual constant map's ENTIRE kernel is the actual native source maximal ideal. -/
theorem equationConstantMap_kernel (f : Series K) (hf : constantCoeff f = 0) :
    letI := equationLocalRing K f hf
    RingHom.ker (equationConstantMap f hf).toRingHom = maximalIdeal (Equation f) := by
  let := equationLocalRing K f hf
  rw [equation_maximalIdeal K f hf]
  change RingHom.ker (Ideal.Quotient.lift _ (seriesConstantMap (K := K)).toRingHom _) = _
  rw [Ideal.ker_quotient_lift, seriesConstantMap_kernel]

/-- Genuine native source residue equivalence from the actual original constant map, without a new coefficient action. -/
def residueEquiv (f : Series K) (hf : constantCoeff f = 0) :
    letI := equationLocalRing K f hf
    ResidueField (Equation f) ≃ₐ[K] K := by
  let := equationLocalRing K f hf
  exact (Ideal.quotientEquivAlgOfEq K (equationConstantMap_kernel K f hf).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (equationConstantMap_surjective f hf))

/-- EVERY actual original quotient element follows its actual original constant evaluation. -/
theorem residueEquiv_mk (f : Series K) (hf : constantCoeff f = 0) (a : Equation f) :
    letI := equationLocalRing K f hf
    residueEquiv K f hf (residue (Equation f) a) = equationConstantMap f hf a := by
  rfl

/-- EVERY original series representative retains its actual original native residue coefficient. -/
theorem residueEquiv_original (f : Series K) (hf : constantCoeff f = 0) (a : Series K) :
    letI := equationLocalRing K f hf
    residueEquiv K f hf (residue (Equation f) (Ideal.Quotient.mk _ a)) = constantCoeff a := by
  let := equationLocalRing K f hf
  rw [residueEquiv_mk]
  rfl

/-- The SAME actual forward original coefficient-residue map is bijective. -/
theorem equation_residue_coefficient_bijective (f : Series K) (hf : constantCoeff f = 0) :
    letI := equationLocalRing K f hf
    Function.Bijective ((residue (Equation f)).comp (algebraMap K (Equation f))) := by
  let := equationLocalRing K f hf
  let E := residueEquiv K f hf
  change Function.Bijective (algebraMap K (ResidueField (Equation f)))
  constructor
  · intro a b hab
    exact (E.commutes a).symm.trans ((congrArg E hab).trans (E.commutes b))
  · intro a
    refine ⟨E a, ?_⟩
    apply E.injective
    exact E.commutes (E a)

/-- The extracted original quadratic jet has zero original constant INTERNALLY, without any relation input. -/
theorem quadraticJet_constantCoeff (g : Series K) : constantCoeff (quadraticJet g) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [NodeVariableMorse.quadraticJet, map_add, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- The literal original quadratic source, independent of every target or evaluation map. -/
abbrev QuadraticSource (g : Series K) := Equation (quadraticJet g)

instance quadraticSource_nontrivial (g : Series K) : Nontrivial (QuadraticSource K g) :=
  equationNontrivial K _ (quadraticJet_constantCoeff K g)

instance quadraticSource_isLocalRing (g : Series K) : IsLocalRing (QuadraticSource K g) :=
  equationLocalRing K _ (quadraticJet_constantCoeff K g)

instance quadraticSource_isNoetherianRing (g : Series K) : IsNoetherianRing (QuadraticSource K g) :=
  equationNoetherian K _

/-- The ENTIRE native maximal ideal of the SAME actual original quadratic source. -/
theorem quadraticSource_maximalIdeal (g : Series K) :
    maximalIdeal (QuadraticSource K g) =
      (variableIdeal K).map (Ideal.Quotient.mk (Ideal.span {quadraticJet g})) :=
  equation_maximalIdeal K _ (quadraticJet_constantCoeff K g)

/-- ALL original variable-ideal powers map exactly to SAME original quadratic-source maximal powers. -/
theorem quadraticSource_variable_pow_map (g : Series K) (n : ℕ) :
    (variableIdeal K ^ n).map (Ideal.Quotient.mk (Ideal.span {quadraticJet g})) =
      maximalIdeal (QuadraticSource K g) ^ n :=
  equation_variable_pow_map K _ (quadraticJet_constantCoeff K g) n

/-- Actual original coefficient-residue bijectivity of the SAME quadratic source, independent of any target. -/
theorem quadraticSource_residue_coefficient_bijective (g : Series K) :
    Function.Bijective ((residue (QuadraticSource K g)).comp (algebraMap K (QuadraticSource K g))) :=
  equation_residue_coefficient_bijective K _ (quadraticJet_constantCoeff K g)

section ActualMap

open NodeFieldCotangentGeneratorsPresentation NodeFieldQuadraticPresentation

variable (C : Type v) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
  [Algebra K C] [IsAdicComplete (maximalIdeal C) C]
  (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
  (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3)
  (g : Series K) (hg : g ∈ RingHom.ker (evaluation K C hres hdim).toRingHom)
  (hΔ : jetDiscriminant g ≠ 0)

/-- The SAME actual quadratic surjection is natively local, with source structures derived internally. -/
instance quadraticQuotientMap_isLocalHom :
    IsLocalHom (quadraticQuotientMap K C hres hdim g hg hΔ).toRingHom :=
  IsLocalHom.of_surjective _ (quadraticQuotientMap_surjective K C hres hdim g hg hΔ)

/-- The SAME actual surjection maps its WHOLE native source maximal ideal exactly to the original target maximal ideal. -/
theorem quadraticQuotientMap_maximalIdeal_image :
    (maximalIdeal (QuadraticSource K g)).map (quadraticQuotientMap K C hres hdim g hg hΔ).toRingHom =
      maximalIdeal C :=
  map_maximalIdeal_of_surjective _ (quadraticQuotientMap_surjective K C hres hdim g hg hΔ)

/-- ALL native maximal-ideal powers have the exact original image under the SAME actual map. -/
theorem quadraticQuotientMap_maximalIdeal_pow_image (n : ℕ) :
    (maximalIdeal (QuadraticSource K g) ^ n).map
      (quadraticQuotientMap K C hres hdim g hg hΔ).toRingHom = maximalIdeal C ^ n := by
  rw [Ideal.map_pow, quadraticQuotientMap_maximalIdeal_image]

end ActualMap

end DeJongAlterations.Algebra.NodeFieldQuadraticSource

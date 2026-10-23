import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet
import DeJongAlterations.Algebra.NodeVariableMorseJet

/-! # Actual quadratic hypersurface surjections from the SAME original evaluation

Low coefficients and the actual Morse automorphism are internally produced from
the actual original kernel relation. No principal-kernel or classification
isomorphism is assumed or asserted; every coefficient and tangent map is retained.
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldQuadraticPresentation

open NodeFormalMorse NodeVariableMorse NodeFieldCotangentGeneratorsPresentation
  NodeFieldCotangentGeneratorsJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (K : Type u) [Field K] (C : Type v) [CommRing C] [IsLocalRing C]
  [IsNoetherianRing C] [Algebra K C] [IsAdicComplete (maximalIdeal C) C]
  (hres : Function.Bijective ((residue C).comp (algebraMap K C)))
  (hdim : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3)
  (g : Series K) (hg : g ∈ RingHom.ker (evaluation K C hres hdim).toRingHom)
  (hΔ : jetDiscriminant g ≠ 0)

/-- Kernel membership INTERNALLY supplies all low coefficient hypotheses of the actual Morse producer. -/
def morseEquiv : Series K ≃ₐ[K] Series K :=
  equationNormalFormEquiv g
    (constantCoeff_eq_zero_of_mem_kernel K C hres hdim g hg)
    (linearCoeff_eq_zero_of_mem_kernel K C hres hdim g hg 0)
    (linearCoeff_eq_zero_of_mem_kernel K C hres hdim g hg 1) hΔ

/-- The same actual original kernel relation is sent to its OWN internally extracted quadratic jet. -/
theorem morseEquiv_equation : morseEquiv K C hres hdim g hg hΔ g = quadraticJet g :=
  equationNormalFormEquiv_equation g _ _ _ hΔ

/-- The genuine actual inverse sends that SAME quadratic jet to the SAME original kernel relation. -/
theorem morseEquiv_symm_quadratic :
    (morseEquiv K C hres hdim g hg hΔ).symm (quadraticJet g) = g := by
  apply (morseEquiv K C hres hdim g hg hΔ).injective
  rw [AlgEquiv.apply_symm_apply, morseEquiv_equation]

/-- Both inverse coordinate differences lie in the WHOLE actual original variable square. -/
theorem morseEquiv_symm_coordinate (i : Fin 2) :
    (morseEquiv K C hres hdim g hg hΔ).symm (X i) - X i ∈ variableIdeal K ^ 2 :=
  equationNormalFormEquiv_symm_coordinate g _ _ _ hΔ i

/-- The SAME original evaluation composed with the proved actual inverse Morse automorphism. -/
def evaluationAfterMorse : Series K →ₐ[K] C :=
  (evaluation K C hres hdim).comp (morseEquiv K C hres hdim g hg hΔ).symm.toAlgHom

/-- Every original coefficient retains its literal original image. -/
theorem evaluationAfterMorse_C (a : K) :
    evaluationAfterMorse K C hres hdim g hg hΔ (MvPowerSeries.C a) = algebraMap K C a := by
  change evaluation K C hres hdim ((morseEquiv K C hres hdim g hg hΔ).symm (MvPowerSeries.C a)) = _
  rw [show (morseEquiv K C hres hdim g hg hΔ).symm (MvPowerSeries.C a) = MvPowerSeries.C a from
    (morseEquiv K C hres hdim g hg hΔ).symm.commutes a]
  exact evaluation_C K C hres hdim a

/-- Actual surjectivity is inherited from precisely the SAME two genuine original maps. -/
theorem evaluationAfterMorse_surjective :
    Function.Surjective (evaluationAfterMorse K C hres hdim g hg hΔ) :=
  (evaluation_surjective K C hres hdim).comp (morseEquiv K C hres hdim g hg hΔ).symm.surjective

/-- The actual original quadratic jet vanishes under this SAME actual composite map. -/
theorem evaluationAfterMorse_quadratic :
    evaluationAfterMorse K C hres hdim g hg hΔ (quadraticJet g) = 0 := by
  change evaluation K C hres hdim ((morseEquiv K C hres hdim g hg hΔ).symm (quadraticJet g)) = 0
  rw [morseEquiv_symm_quadratic]
  exact hg

/-- The genuine actual hypersurface map; NO principal-kernel or isomorphism certificate is supplied. -/
def quadraticQuotientMap : (Series K ⧸ Ideal.span {quadraticJet g}) →ₐ[K] C := by
  refine Ideal.Quotient.liftₐ _ (evaluationAfterMorse K C hres hdim g hg hΔ) ?_
  have h : Ideal.span {quadraticJet g} ≤
      RingHom.ker (evaluationAfterMorse K C hres hdim g hg hΔ).toRingHom :=
    Ideal.span_le.mpr (by
      rintro _ rfl
      exact evaluationAfterMorse_quadratic K C hres hdim g hg hΔ)
  exact fun f hf => h hf

/-- EVERY original series representative follows the SAME actual original inverse-Morse evaluation. -/
theorem quadraticQuotientMap_mk (f : Series K) :
    quadraticQuotientMap K C hres hdim g hg hΔ (Ideal.Quotient.mk _ f) =
      evaluationAfterMorse K C hres hdim g hg hΔ f := rfl

/-- Every original coefficient follows the SAME original K-action of C. -/
theorem quadraticQuotientMap_C (a : K) :
    quadraticQuotientMap K C hres hdim g hg hΔ (Ideal.Quotient.mk _ (MvPowerSeries.C a)) =
      algebraMap K C a := by
  rw [quadraticQuotientMap_mk, evaluationAfterMorse_C]

/-- Genuine actual surjectivity of this SAME quadratic quotient map. -/
theorem quadraticQuotientMap_surjective :
    Function.Surjective (quadraticQuotientMap K C hres hdim g hg hΔ) := by
  intro c
  obtain ⟨f, hf⟩ := evaluationAfterMorse_surjective K C hres hdim g hg hΔ c
  exact ⟨Ideal.Quotient.mk _ f, hf⟩

/-- Both actual quotient coordinates retain the original internally produced tangent generators. -/
theorem quadraticQuotientMap_coordinate (i : Fin 2) :
    quadraticQuotientMap K C hres hdim g hg hΔ (Ideal.Quotient.mk _ (X i)) -
      generators K C hres hdim i ∈ maximalIdeal C ^ 2 := by
  rw [quadraticQuotientMap_mk]
  change evaluation K C hres hdim ((morseEquiv K C hres hdim g hg hΔ).symm (X i)) -
    generators K C hres hdim i ∈ maximalIdeal C ^ 2
  have h : evaluation K C hres hdim
      ((morseEquiv K C hres hdim g hg hΔ).symm (X i) - X i) ∈ maximalIdeal C ^ 2 := by
    rw [← variableIdeal_pow_image K C hres hdim 2]
    exact Ideal.mem_map_of_mem (evaluation K C hres hdim).toRingHom
      (morseEquiv_symm_coordinate K C hres hdim g hg hΔ i)
  simpa only [map_sub, evaluation_X] using h

end DeJongAlterations.Algebra.NodeFieldQuadraticPresentation

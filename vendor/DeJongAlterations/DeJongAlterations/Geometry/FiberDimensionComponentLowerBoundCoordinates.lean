import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Actual polynomial normalization coordinates lifted from a prime fiber quotient

Field normalization of the literal fiber quotient is rescaled by actual
coefficient units. Native fiber denominator clearing lifts its variables to
the original algebra, with the whole polynomial coefficient square proved.
No normalization, dimension or finite-map output is a caller premise.
The componentwise geometric lower bound remains a separate producer.
-/

noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Scaling each variable by its own actual coefficient unit is a genuine algebra automorphism. -/
def scaleVariables {K : Type*} [CommRing K] {ι : Type*} (c : ι → Kˣ) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (aeval fun i => C (c i : K) * X i)
    (aeval fun i => C (((c i)⁻¹ : Kˣ) : K) * X i)
    (by ext i; simp) (by ext i; simp)

@[simp]
theorem scaleVariables_X {K : Type*} [CommRing K] {ι : Type*} (c : ι → Kˣ) (i : ι) :
    scaleVariables c (X i) = C (c i : K) * X i := by
  simp [scaleVariables]

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The original algebra maps literally through the actual tensor fiber and its prime quotient. -/
def fiberQuotientMap (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber A)) :
    A →ₐ[R] (p.Fiber A ⧸ Q) :=
  (Ideal.Quotient.mkₐ R Q).comp Algebra.TensorProduct.includeRight

/-- Every actual prime fiber quotient internally constructs finite normalization coordinates
lifted to the original algebra, with its actual dimension and exact coefficient square. -/
theorem exists_lifted_finite_normalization_coordinates [Algebra.FiniteType R A]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber A)) [Q.IsPrime] :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] A)
      (g : MvPolynomial (Fin d) p.ResidueField →ₐ[p.ResidueField] (p.Fiber A ⧸ Q)),
      Function.Injective g ∧
      RingHom.Finite (A := MvPolynomial (Fin d) p.ResidueField) (B := p.Fiber A ⧸ Q) g.toRingHom ∧
      ringKrullDim (p.Fiber A ⧸ Q) = d ∧
      g.toRingHom.comp (MvPolynomial.map (algebraMap R p.ResidueField)) =
        (fiberQuotientMap R A p Q).toRingHom.comp f.toRingHom := by
  classical
  let B : Type u := p.Fiber A
  let C : Type u := B ⧸ Q
  let : CommRing B := inferInstance
  let : CommRing C := inferInstance
  let : Algebra p.ResidueField C := inferInstance
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg p.ResidueField C
  have hlift (i : Fin d) : ∃ b : B, Ideal.Quotient.mk Q b = g (X i) :=
    Ideal.Quotient.mk_surjective _
  choose b hb using hlift
  choose r hr a ha using (fun i => Ideal.Fiber.exists_smul_eq_one_tmul (p := p) (b i))
  have hri (i : Fin d) : algebraMap R p.ResidueField (r i) ≠ 0 := by
    simpa only [ne_eq, Ideal.algebraMap_residueField_eq_zero] using hr i
  let c (i : Fin d) : p.ResidueFieldˣ := Units.mk0 (algebraMap R p.ResidueField (r i)) (hri i)
  let g' : MvPolynomial (Fin d) p.ResidueField →ₐ[p.ResidueField] C :=
    g.comp (scaleVariables c).toAlgHom
  let f : MvPolynomial (Fin d) R →ₐ[R] A := aeval a
  have ha' (i : Fin d) : fiberQuotientMap R A p Q (a i) =
      algebraMap p.ResidueField C (algebraMap R p.ResidueField (r i)) * g (X i) := by
    calc
      fiberQuotientMap R A p Q (a i) = (Ideal.Quotient.mkₐ R Q) (r i • b i) := by
        rw [ha i]
        rfl
      _ = r i • g (X i) := by
        rw [map_smul]
        change r i • Ideal.Quotient.mk Q (b i) = r i • g (X i)
        rw [hb i]
      _ = _ := by rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R p.ResidueField C]
  have hcomp : g'.toRingHom.comp (MvPolynomial.map (algebraMap R p.ResidueField)) =
      (fiberQuotientMap R A p Q).toRingHom.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro s
      simp only [RingHom.comp_apply, map_C]
      change g' (algebraMap p.ResidueField _ (algebraMap R p.ResidueField s)) =
        fiberQuotientMap R A p Q (f (algebraMap R _ s))
      rw [g'.commutes, f.commutes, (fiberQuotientMap R A p Q).commutes]
      exact (IsScalarTower.algebraMap_apply R p.ResidueField C s).symm
    · intro i
      change g' (MvPolynomial.map (algebraMap R p.ResidueField) (X i)) =
        fiberQuotientMap R A p Q (f (X i))
      simpa [g', f, scaleVariables, c] using (ha' i).symm
  have hg' : Function.Injective g' := hg.comp (scaleVariables c).injective
  have hfin' : g'.toRingHom.Finite :=
    hfin.comp (AlgHom.Finite.of_surjective _ (scaleVariables c).surjective)
  have hdim : ringKrullDim C = d := by
    have hP : ringKrullDim (MvPolynomial (Fin d) p.ResidueField) = d := by simp
    apply le_antisymm
    · exact (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral
        g'.toRingHom hfin'.to_isIntegral).trans_eq hP
    · exact hP ▸ Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective
        g'.toRingHom hfin'.to_isIntegral hg'
  exact ⟨d, f, g', hg', hfin', hdim, hcomp⟩

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundCoordinates

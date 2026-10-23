/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularSmoothConverseResidue
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Actual cotangent Jacobians of polynomial localizations

The perfect-field residue splitting gives injectivity of the actual local
cotangent-to-partial-derivatives map. Its coordinates and derivations are
constructed from the genuine localized differential module.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential Module

namespace DeJongAlterations.Algebra.RegularSmoothConverseJacobian

variable {k ι : Type*} [CommRing k]

/-- The actual differential basis obtained by localizing polynomial differentials. -/
def localizedKaehlerBasis (p : Ideal (MvPolynomial ι k)) [p.IsPrime] :
    Basis ι (Localization.AtPrime p) Ω[Localization.AtPrime p⁄k] := by
  let : Algebra.FormallyEtale (MvPolynomial ι k) (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  exact ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange (Localization.AtPrime p)).map
    (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) (Localization.AtPrime p))

/-- Coordinate functionals of the actual localized differential basis are actual derivations. -/
def coordinateDerivation (p : Ideal (MvPolynomial ι k)) [p.IsPrime] (i : ι) :
    Derivation k (Localization.AtPrime p) (Localization.AtPrime p) :=
  KaehlerDifferential.linearMapEquivDerivation k (Localization.AtPrime p)
    ((Finsupp.lapply i).comp (localizedKaehlerBasis p).repr.toLinearMap)

@[simp]
theorem coordinateDerivation_algebraMap (p : Ideal (MvPolynomial ι k)) [p.IsPrime]
    (i : ι) (f : MvPolynomial ι k) :
    coordinateDerivation p i (algebraMap (MvPolynomial ι k) (Localization.AtPrime p) f) =
      algebraMap (MvPolynomial ι k) (Localization.AtPrime p) (MvPolynomial.pderiv i f) := by
  let L := Localization.AtPrime p
  let : Algebra.FormallyEtale (MvPolynomial ι k) L :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  let e := tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) L
  change ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange L).repr
    (e.symm (KaehlerDifferential.D k L (algebraMap (MvPolynomial ι k) L f))) i = _
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- The actual local cotangent space mapped to all residue partial-derivative coordinates. -/
def localizedCotangentJacobian [Finite ι] (p : Ideal (MvPolynomial ι k)) [p.IsPrime] :
    CotangentSpace (Localization.AtPrime p) →ₗ[ResidueField (Localization.AtPrime p)]
      (ι → ResidueField (Localization.AtPrime p)) :=
  (Finsupp.linearEquivFunOnFinite _ _ ι).toLinearMap.comp
    (((localizedKaehlerBasis p).baseChange (ResidueField (Localization.AtPrime p))).repr.toLinearMap.comp
      (RegularSmoothConverseResidue.residueCotangentMap (k := k)))

@[simp]
theorem localizedCotangentJacobian_toCotangent [Finite ι] (p : Ideal (MvPolynomial ι k))
    [p.IsPrime] (x : maximalIdeal (Localization.AtPrime p)) (i : ι) :
    localizedCotangentJacobian p ((maximalIdeal (Localization.AtPrime p)).toCotangent x) i =
      residue (Localization.AtPrime p) (coordinateDerivation p i x) := by
  change (((localizedKaehlerBasis p).baseChange (ResidueField (Localization.AtPrime p))).repr
    (RegularSmoothConverseResidue.residueCotangentMap (k := k)
      ((maximalIdeal (Localization.AtPrime p)).toCotangent x))) i = _
  rw [RegularSmoothConverseResidue.residueCotangentMap_toCotangent, Basis.baseChange_repr_tmul]
  change (localizedKaehlerBasis p).repr (KaehlerDifferential.D k (Localization.AtPrime p) x) i •
    (1 : ResidueField (Localization.AtPrime p)) = _
  simp only [Algebra.smul_def, mul_one, ResidueField.algebraMap_eq]
  rfl

/-- Over a perfect field the actual localized cotangent Jacobian is injective. -/
theorem localizedCotangentJacobian_injective {K : Type*} [Field K] [PerfectField K] [Finite ι]
    (p : Ideal (MvPolynomial ι K)) [p.IsPrime] :
    Function.Injective (localizedCotangentJacobian p) := by
  let L := Localization.AtPrime p
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K (MvPolynomial ι K) L
  exact (Finsupp.linearEquivFunOnFinite (ResidueField L) (ResidueField L) ι).injective.comp
    (((localizedKaehlerBasis p).baseChange (ResidueField L)).repr.injective.comp
      (RegularSmoothConverseResidue.residueCotangentMap_injective K L))

/-- Over a perfect field actual ambient cotangent independence is exactly Jacobian independence. -/
theorem linearIndependent_cotangent_iff_derivatives {K σ : Type*} [Field K] [PerfectField K]
    [Finite ι] (p : Ideal (MvPolynomial ι K)) [p.IsPrime]
    (t : σ → maximalIdeal (Localization.AtPrime p)) :
    LinearIndependent (ResidueField (Localization.AtPrime p))
      (fun j ↦ (maximalIdeal (Localization.AtPrime p)).toCotangent (t j)) ↔
      LinearIndependent (ResidueField (Localization.AtPrime p))
        (fun j i ↦ residue (Localization.AtPrime p) (coordinateDerivation p i (t j))) := by
  let F := localizedCotangentJacobian p
  have hF : Set.InjOn F
      (Submodule.span (ResidueField (Localization.AtPrime p))
        (Set.range fun j ↦ (maximalIdeal (Localization.AtPrime p)).toCotangent (t j))) :=
    fun _ _ _ _ h ↦ localizedCotangentJacobian_injective p h
  have hvec : F ∘ (fun j ↦ (maximalIdeal (Localization.AtPrime p)).toCotangent (t j)) =
      (fun j i ↦ residue (Localization.AtPrime p) (coordinateDerivation p i (t j))) := by
    funext j i
    exact localizedCotangentJacobian_toCotangent p (t j) i
  rw [← hvec]
  exact (F.linearIndependent_iff_of_injOn hF).symm

end DeJongAlterations.Algebra.RegularSmoothConverseJacobian

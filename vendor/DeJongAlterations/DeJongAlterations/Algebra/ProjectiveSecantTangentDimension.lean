import DeJongAlterations.Algebra.ProjectiveSecantTangentJacobian

/-!
# The original rational polynomial point internally determines the full ambient cotangent dimension
-/

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential

namespace DeJongAlterations.Algebra.ProjectiveSecant

open RegularSmoothConverseResidue RegularSmoothConverseJacobian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual residue differential vanishing gives genuine surjectivity of the original cotangent comparison. -/
theorem residueCotangentMap_surjective_of_formallyEtale {k P : Type*}
    [CommRing k] [CommRing P] [Algebra k P] [IsLocalRing P]
    [Algebra.FormallyEtale k (ResidueField P)] :
    Function.Surjective (residueCotangentMap (k := k) (R := P)) := by
  intro z
  have hz : mapBaseChange k P (ResidueField P) z = 0 := Subsingleton.elim _ _
  obtain ⟨w, hw⟩ := (exact_kerCotangentToTensor_mapBaseChange k P (ResidueField P) residue_surjective z).mp hz
  refine ⟨(residueKernelCotangentEquiv (R := P)).symm w, ?_⟩
  change kerCotangentToTensor k P (ResidueField P)
    (residueKernelCotangentEquiv ((residueKernelCotangentEquiv (R := P)).symm w)) = z
  rw [LinearEquiv.apply_symm_apply, hw]

variable {k ι : Type*} [Field k] [Finite ι]

/-- The whole original rational-point Jacobian is genuinely bijective over every original field. -/
theorem rational_localizedCotangentJacobian_bijective (e : MvPolynomial ι k →ₐ[k] k) :
    Function.Bijective (localizedCotangentJacobian (rationalPointIdeal e)) := by
  refine ⟨rational_localizedCotangentJacobian_injective e, ?_⟩
  let p := rationalPointIdeal e
  let P := Localization.AtPrime p
  exact (Finsupp.linearEquivFunOnFinite (ResidueField P) (ResidueField P) ι).surjective.comp
    (((localizedKaehlerBasis p).baseChange (ResidueField P)).repr.surjective.comp
      residueCotangentMap_surjective_of_formallyEtale)

/-- The actual original rational-point cotangent space has its actual coordinate-basis dimension. -/
theorem rational_localizedCotangent_finrank (e : MvPolynomial ι k →ₐ[k] k) :
    Module.finrank (ResidueField (Localization.AtPrime (rationalPointIdeal e)))
      (CotangentSpace (Localization.AtPrime (rationalPointIdeal e))) = Nat.card ι := by
  classical
  let := Fintype.ofFinite ι
  let p := rationalPointIdeal e
  let P := Localization.AtPrime p
  let h := LinearEquiv.ofBijective (localizedCotangentJacobian p) (rational_localizedCotangentJacobian_bijective e)
  calc
    _ = Module.finrank (ResidueField P) (ι → ResidueField P) := h.finrank_eq
    _ = _ := by simp

/-- The original rational ambient point's regular-local Krull dimension is produced internally from its actual coordinates. -/
theorem rational_localization_dimension (e : MvPolynomial ι k →ₐ[k] k) :
    ringKrullDim (Localization.AtPrime (rationalPointIdeal e)) = Nat.card ι := by
  rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime (rationalPointIdeal e))).mp inferInstance,
    rational_localizedCotangent_finrank]

end DeJongAlterations.Algebra.ProjectiveSecant

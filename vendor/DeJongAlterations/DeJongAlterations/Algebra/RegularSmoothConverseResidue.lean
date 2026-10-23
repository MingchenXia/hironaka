/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.RegularSmooth
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Local
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual residue cotangent sequence over a perfect field

Perfectness constructs an actual first-order residue-field section and a
retraction of the actual local cotangent map, without assuming the local
algebra smooth. The presentation-kernel map in the regular/smooth converse
is a distinct remaining obligation.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential

namespace DeJongAlterations.Algebra.RegularSmoothConverseResidue

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [IsLocalRing R]

private theorem residueAlgebraMap_ker :
    RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
  rw [ResidueField.algebraMap_eq, ker_residue]

/-- Identify the native kernel cotangent of the actual residue map with the maximal cotangent. -/
def residueKernelCotangentEquiv :
    CotangentSpace R ≃ₗ[R] (RingHom.ker (algebraMap R (ResidueField R))).Cotangent :=
  Ideal.Cotangent.equivOfEq _ _ residueAlgebraMap_ker.symm

/-- The actual residue-valued cotangent map `[x] ↦ 1 ⊗ dx`. -/
def residueCotangentMap :
    CotangentSpace R →ₗ[ResidueField R] (ResidueField R ⊗[R] Ω[R⁄k]) :=
  ((kerCotangentToTensor k R (ResidueField R)).comp
    residueKernelCotangentEquiv.toLinearMap).extendScalarsOfSurjective residue_surjective

@[simp]
theorem residueCotangentMap_toCotangent (x : maximalIdeal R) :
    residueCotangentMap (k := k) ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D k R (x : R) := by
  simp only [residueCotangentMap, LinearMap.extendScalarsOfSurjective_apply,
    LinearMap.comp_apply, residueKernelCotangentEquiv]
  rfl

/-- Exactness uses the actual residue map and needs no regularity hypothesis. -/
theorem residueCotangentMap_exact :
    Function.Exact (residueCotangentMap (k := k) (R := R))
      (mapBaseChange k R (ResidueField R)) := by
  let e := residueKernelCotangentEquiv (R := R)
  intro z
  have h := exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) residue_surjective z
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := h.mp hz
    refine ⟨e.symm y, ?_⟩
    change kerCotangentToTensor k R (ResidueField R) (e (e.symm y)) = z
    simpa only [e.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    exact h.mpr ⟨e y, rfl⟩

variable (K R : Type*) [Field K] [PerfectField K] [CommRing R] [Algebra K R]
    [IsLocalRing R] [Algebra.EssFiniteType K R]

private instance residue_essFiniteType : Algebra.EssFiniteType K (ResidueField R) :=
  Algebra.EssFiniteType.comp K R (ResidueField R)

/-- Perfectness constructs a genuine section of the actual first-order residue thickening. -/
def residueFirstOrderSection :
    ResidueField R →ₐ[K] R ⧸ RingHom.ker (algebraMap R (ResidueField R)) ^ 2 := by
  let f := IsScalarTower.toAlgHom K R (ResidueField R)
  let g := f.kerSquareLift
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective x
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩
  have hnil : IsNilpotent (RingHom.ker g.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  exact Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K (ResidueField R)) g hg hnil

@[simp]
theorem residueFirstOrderSection_comp :
    (IsScalarTower.toAlgHom K R (ResidueField R)).kerSquareLift.comp
      (residueFirstOrderSection K R) = AlgHom.id K (ResidueField R) := by
  exact Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

/-- A retraction supplied by perfectness, with no assumption that the actual local ring is smooth. -/
def residueCotangentRetraction :
    (ResidueField R ⊗[R] Ω[R⁄K]) →ₗ[ResidueField R] CotangentSpace R := by
  let e := retractionKerCotangentToTensorEquivSection (R := K) (P := R)
    (S := ResidueField R) residue_surjective
  let l := e.symm ⟨residueFirstOrderSection K R, residueFirstOrderSection_comp K R⟩
  exact (residueKernelCotangentEquiv.symm.toLinearMap.comp l.val).extendScalarsOfSurjective
    residue_surjective

theorem residueCotangentRetraction_comp :
    (residueCotangentRetraction K R).comp (residueCotangentMap (k := K)) = LinearMap.id := by
  let e := retractionKerCotangentToTensorEquivSection (R := K) (P := R)
    (S := ResidueField R) residue_surjective
  let l := e.symm ⟨residueFirstOrderSection K R, residueFirstOrderSection_comp K R⟩
  ext x
  change residueKernelCotangentEquiv.symm
    (l.val (kerCotangentToTensor K R (ResidueField R) (residueKernelCotangentEquiv x))) = x
  rw [show l.val (kerCotangentToTensor K R (ResidueField R) (residueKernelCotangentEquiv x)) =
    residueKernelCotangentEquiv x from LinearMap.congr_fun l.property _]
  exact residueKernelCotangentEquiv.symm_apply_apply x

/-- The actual local cotangent map is injective over a perfect field. -/
theorem residueCotangentMap_injective : Function.Injective (residueCotangentMap (k := K) (R := R)) :=
  Function.LeftInverse.injective (f := residueCotangentMap (k := K) (R := R))
    (g := residueCotangentRetraction K R) (fun x ↦ by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (residueCotangentRetraction_comp K R) x)

/-- Actual cotangent and residue-field differentials account for the whole differential fiber. -/
theorem finrank_residueTensorKaehler_eq :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] Ω[R⁄K]) =
      Module.finrank (ResidueField R) (CotangentSpace R) +
        Module.finrank (ResidueField R) Ω[ResidueField R⁄K] := by
  let g := mapBaseChange K R (ResidueField R)
  have hsurj : Function.Surjective g := mapBaseChange_surjective K R (ResidueField R)
    residue_surjective
  have hker : g.ker = (residueCotangentMap (k := K) (R := R)).range := by
    ext z
    exact residueCotangentMap_exact z
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj (residueCotangentMap_injective K R)] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- Regularity gives the intrinsic differential dimension formula, without assuming smoothness. -/
theorem finrank_residueTensorKaehler_eq_of_isRegularLocalRing (K' A : Type*)
    [Field K'] [PerfectField K'] [CommRing A] [Algebra K' A] [Algebra.EssFiniteType K' A]
    [IsRegularLocalRing A] :
    (Module.finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄K']) : WithBot ℕ∞) =
      ringKrullDim A + (Module.finrank (ResidueField A) Ω[ResidueField A⁄K'] : WithBot ℕ∞) := by
  rw [finrank_residueTensorKaehler_eq K' A, Nat.cast_add]
  rw [(IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance]

end DeJongAlterations.Algebra.RegularSmoothConverseResidue

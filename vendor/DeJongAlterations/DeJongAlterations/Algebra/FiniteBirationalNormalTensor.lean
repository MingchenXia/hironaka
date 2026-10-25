import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual evaluation primes of a normal field tensor product

Normality forces any conjugate embedding into an extension of the normal
field to land in that same field. Applying this to the actual fraction
field of each tensor prime quotient identifies that prime as an actual
evaluation kernel. No tensor splitting or prime comparison is supplied.
-/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace DeJongAlterations.Algebra.FiniteBirationalNormalTensor

universe u

variable {K E L F : Type u} [Field K] [Field E] [Field L] [Field F]
  [Algebra K E] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
  [FiniteDimensional K E] [hL : Normal K L]

/-- Every actual conjugate of a field already contained in a normal field
lands in that same normal field. -/
theorem image_mem_range (e : E →ₐ[K] L) (φ : E →ₐ[K] F) (x : E) :
    φ x ∈ (algebraMap L F).range := by
  have hs : ((minpoly K x).map (algebraMap K L)).Splits := by
    simpa only [minpoly.algHom_eq e e.injective] using hL.splits (e x)
  apply minpoly.mem_range_of_degree_eq_one L
  refine (hs.of_dvd (map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := K) x)))
    (minpoly.dvd L _ ?_)).degree_eq_one_of_irreducible
      (minpoly.irreducible ((Algebra.IsIntegral.isIntegral (R := K) x).map φ).tower_top)
  simp only [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]

/-- The factor is constructed inside the actual image subalgebra of the actual field inclusion. -/
theorem exists_factor (e : E →ₐ[K] L) (φ : E →ₐ[K] F) :
    ∃ σ : E →ₐ[K] L, (IsScalarTower.toAlgHom K L F).comp σ = φ := by
  let q := φ.codRestrict (IsScalarTower.toAlgHom K L F).range
    (fun x => image_mem_range e φ x)
  let i := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L F)
  refine ⟨i.symm.toAlgHom.comp q, ?_⟩
  ext x
  exact congrArg Subtype.val (i.apply_symm_apply (q x))

/-- The actual tensor evaluation associated to an original field embedding. -/
def tensorEvaluation (σ : E →ₐ[K] L) : (L ⊗[K] E) →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) σ (fun _ _ => Commute.all _ _)

omit [FiniteDimensional K E] hL in
@[simp]
theorem tensorEvaluation_tmul (σ : E →ₐ[K] L) (l : L) (x : E) :
    tensorEvaluation σ (l ⊗ₜ[K] x) = l * σ x := rfl

/-- Every actual prime of the field tensor product is the exact kernel of
an internally produced evaluation map. -/
theorem exists_tensorEvaluation_kernel (e : E →ₐ[K] L)
    (P : PrimeSpectrum (L ⊗[K] E)) :
    ∃ σ : E →ₐ[K] L, RingHom.ker (tensorEvaluation σ).toRingHom = P.asIdeal := by
  let R := L ⊗[K] E
  let Q := R ⧸ P.asIdeal
  let F := FractionRing Q
  let q : R →ₐ[L] F := (IsScalarTower.toAlgHom L Q F).comp (Ideal.Quotient.mkₐ L P.asIdeal)
  let φ : E →ₐ[K] F := (q.restrictScalars K).comp Algebra.TensorProduct.includeRight
  obtain ⟨σ, hσ⟩ := exists_factor e φ
  have hq : (IsScalarTower.toAlgHom L L F).comp (tensorEvaluation σ) = q := by
    apply (Algebra.TensorProduct.liftEquivRight K L E F).symm.injective
    ext x
    change algebraMap L F (tensorEvaluation σ (1 ⊗ₜ[K] x)) = q (1 ⊗ₜ[K] x)
    rw [tensorEvaluation_tmul, one_mul]
    exact AlgHom.congr_fun hσ x
  refine ⟨σ, ?_⟩
  ext z
  change tensorEvaluation σ z = 0 ↔ z ∈ P.asIdeal
  have H : q z = 0 ↔ z ∈ P.asIdeal := by
    change algebraMap Q F (Ideal.Quotient.mk P.asIdeal z) = 0 ↔ z ∈ P.asIdeal
    rw [map_eq_zero_iff _ (IsFractionRing.injective Q F), Ideal.Quotient.eq_zero_iff_mem]
  rw [← H, ← AlgHom.congr_fun hq z]
  exact (map_eq_zero_iff _ (algebraMap L F).injective).symm

/-- Every actual tensor prime is the actual spectrum image of an evaluation map. -/
theorem exists_tensorEvaluation_comap (e : E →ₐ[K] L)
    (P : PrimeSpectrum (L ⊗[K] E)) :
    ∃ σ : E →ₐ[K] L,
      PrimeSpectrum.comap (tensorEvaluation σ).toRingHom (⊥ : PrimeSpectrum L) = P := by
  obtain ⟨σ, hσ⟩ := exists_tensorEvaluation_kernel e P
  refine ⟨σ, ?_⟩
  apply PrimeSpectrum.ext
  exact hσ

/-- The actual evaluation spectrum maps jointly cover the entire tensor spectrum. -/
theorem iUnion_range_tensorEvaluation (e : E →ₐ[K] L) :
    ⋃ σ : E →ₐ[K] L, Set.range (PrimeSpectrum.comap (tensorEvaluation σ).toRingHom) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro P
  obtain ⟨σ, hσ⟩ := exists_tensorEvaluation_comap e P
  exact Set.mem_iUnion.mpr ⟨σ, ⊥, hσ⟩

end DeJongAlterations.Algebra.FiniteBirationalNormalTensor

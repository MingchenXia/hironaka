/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalAssociatedGraded
import Hironaka.Resolution.HironakaRelativeNormalNearbyUniformRanks
import Mathlib.RingTheory.TensorProduct.Quotient
/-! # Whole original fibre Hilbert--Samuel algebra dictionary

The genuine original base-fibre ideal is the WHOLE image of the base
maximal ideal under actual tangent pullback. Relative Hadamard decomposition
proves that adding the normal ideal gives the actual ambient maximal ideal.
Every power comparison retains that base-fibre ideal on BOTH sides.
Actual quotient projection and residue-balanced tensor maps, with genuine
inverse original numerator maps, identify complex residue tensors with the
whole fibre-power quotient as complex algebras.

Only original coherence supplies the existing ENTIRE Hilbert--Samuel sequence
of the genuine fibre ideal on the SAME analytic open as the original-input
uniform ranks. This target is hilbertSamuelValue (I_a + R*m_B), with the
literal original whole quotient and original complex scalars. For positive
base dimension it is not ambient hilbertSamuelValue I_a: the latter retains
mixed tangent degrees. No support-containing centre, sheaf normal-flatness,
ambient mixed-degree dictionary, blowup HS descent, or resolution driver is
asserted here. The open meets every origin neighbourhood and is not required
to contain the origin.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum TensorProduct
namespace Hironaka.HironakaRelativeNormalFibreHilbertSamuel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
/-- The literal whole image of the actual original base maximal ideal. -/
def originalBaseMaximalIdeal (d t : ℕ) : Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.map (tangentPullback d t).toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))

@[simp] theorem eval_tangentPullback (d t : ℕ) (g : HolGerm (ComplexModel d)) :
    HolGerm.eval (tangentPullback d t g) = HolGerm.eval g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold tangentPullback
    rw [compAlgHom_mk]
    change f (tangentProjection d t 0) = f 0
    rw [map_zero]

@[simp] theorem eval_planeTrace (d t : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    HolGerm.eval (planeTrace d t g) = HolGerm.eval g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold planeTrace
    rw [compAlgHom_mk]
    change f (tangentInclusion d t 0) = f 0
    rw [map_zero]

/-- Actual relative Hadamard decomposition gives the entire split-coordinate maximal ideal. -/
theorem baseMaximalIdeal_sup_normalIdeal (d t : ℕ) :
    originalBaseMaximalIdeal d t ⊔ normalIdeal d t =
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) := by
  apply le_antisymm
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro g hg
      apply (HolGerm.mem_maximalIdeal_iff _).mpr
      change HolGerm.eval (tangentPullback d t g) = 0
      rw [eval_tangentPullback]
      exact (HolGerm.mem_maximalIdeal_iff _).mp hg
    · apply Ideal.span_le.mpr
      rintro g ⟨i, rfl⟩
      apply (HolGerm.mem_maximalIdeal_iff _).mpr
      change (0 : ComplexModel (d+t)) (i.natAdd d) = 0
      rfl
  · intro g hg
    obtain ⟨h, he⟩ := exists_relative_decomposition d t g
    rw [he]
    apply (originalBaseMaximalIdeal d t ⊔ normalIdeal d t).add_mem
    · apply (show originalBaseMaximalIdeal d t ≤ originalBaseMaximalIdeal d t ⊔ normalIdeal d t from le_sup_left)
      apply Ideal.mem_map_of_mem (tangentPullback d t).toRingHom
      apply (HolGerm.mem_maximalIdeal_iff _).mpr
      rw [eval_planeTrace]
      exact (HolGerm.mem_maximalIdeal_iff _).mp hg
    · apply (show normalIdeal d t ≤ originalBaseMaximalIdeal d t ⊔ normalIdeal d t from le_sup_right)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Passing to the true quotient by M proves every power identity with M retained. -/
theorem ideal_sup_power_absorbed {R : Type*} [CommRing R] (M J : Ideal R) (s : ℕ) :
    M ⊔ (M ⊔ J) ^ s = M ⊔ J ^ s := by
  have hmap : Ideal.map (Ideal.Quotient.mk M) ((M ⊔ J) ^ s) =
      Ideal.map (Ideal.Quotient.mk M) (J ^ s) := by
    rw [Ideal.map_pow, Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self]
    simp
  have he := congrArg (Ideal.comap (Ideal.Quotient.mk M)) hmap
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective] at he
  change (M ⊔ J) ^ s ⊔ RingHom.ker (Ideal.Quotient.mk M) =
    J ^ s ⊔ RingHom.ker (Ideal.Quotient.mk M) at he
  rw [Ideal.mk_ker] at he
  simpa only [sup_comm] using he

/-- The original FIBRE ideal's full maximal-ideal-power quotient equals its actual normal-power quotient. -/
theorem fibreMaximalIdeal_power_eq (d t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (I ⊔ originalBaseMaximalIdeal d t) ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s =
      (I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s := by
  rw [← baseMaximalIdeal_sup_normalIdeal, sup_assoc, ideal_sup_power_absorbed, ← sup_assoc]

open HironakaRelativeNormalNearbyUniformRanks HironakaRelativeNormalUniformTruncations
attribute [local instance] baseGermResidueAlgebra

/-- The genuine whole original normal-power quotient on the actual base fibre. -/
abbrev originalFibrePowerQuotient (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :=
  HolGerm (ComplexModel (d+t)) ⧸ ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s)

/-- Actual base coefficients act on the fibre quotient by genuine origin evaluation. -/
@[instance_reducible] def fibrePowerBaseAlgebra (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (originalFibrePowerQuotient d t I s) :=
  ((algebraMap ℂ (originalFibrePowerQuotient d t I s)).comp
    (HolGerm.eval : HolGerm (ComplexModel d) →+* ℂ)).toAlgebra

/-- The actual original normal-power quotient projects to the genuine fibre quotient. -/
def originalFibreTruncationProjection (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    letI := tangentAlgebra d t
    letI := fibrePowerBaseAlgebra d t I s
    originalNormalTruncation d t I s →ₐ[HolGerm (ComplexModel d)] originalFibrePowerQuotient d t I s := by
  letI := tangentAlgebra d t
  letI := fibrePowerBaseAlgebra d t I s
  let Q := (I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s
  have hQ : I ⊔ normalIdeal d t ^ s ≤ Q :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine { Ideal.Quotient.factor hQ with commutes' := ?_ }
  intro b
  change Ideal.Quotient.mk Q (tangentPullback d t b) =
    Ideal.Quotient.mk Q (HolGerm.constHom (HolGerm.eval b))
  apply Ideal.Quotient.eq.mpr
  have hb : b - algebraMap ℂ (HolGerm (ComplexModel d)) (HolGerm.eval b) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    change HolGerm.eval (b - HolGerm.constHom (HolGerm.eval b)) = 0
    rw [map_sub, HolGerm.eval_constHom, sub_self]
  have hmap := Ideal.mem_map_of_mem (tangentPullback d t).toRingHom hb
  change tangentPullback d t (b - algebraMap ℂ (HolGerm (ComplexModel d)) (HolGerm.eval b)) ∈
    originalBaseMaximalIdeal d t at hmap
  rw [map_sub, (tangentPullback d t).commutes] at hmap
  exact (show originalBaseMaximalIdeal d t ≤ Q from le_sup_right.trans le_sup_left) hmap

/-- The tensor universal property gives the actual complex-algebra map to the whole fibre-power quotient. -/
def originalNormalFibreTruncationAlgHom (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    letI := tangentAlgebra d t
    (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s) →ₐ[ℂ]
      originalFibrePowerQuotient d t I s := by
  letI := tangentAlgebra d t
  letI := fibrePowerBaseAlgebra d t I s
  letI : SMul (HolGerm (ComplexModel d)) (originalFibrePowerQuotient d t I s) :=
    (fibrePowerBaseAlgebra d t I s).toSMul
  letI : SMul ℂ (originalFibrePowerQuotient d t I s) :=
    (inferInstance : Algebra ℂ (originalFibrePowerQuotient d t I s)).toSMul
  letI : Module (HolGerm (ComplexModel d)) (originalFibrePowerQuotient d t I s) :=
    (fibrePowerBaseAlgebra d t I s).toModule
  letI : IsScalarTower (HolGerm (ComplexModel d)) ℂ (originalFibrePowerQuotient d t I s) :=
    IsScalarTower.of_algebraMap_eq (R := HolGerm (ComplexModel d)) (S := ℂ)
      (A := originalFibrePowerQuotient d t I s) (fun _ => rfl)
  exact AlgHom.liftEquiv (HolGerm (ComplexModel d)) ℂ (originalNormalTruncation d t I s)
    (originalFibrePowerQuotient d t I s) (originalFibreTruncationProjection d t I s)

theorem originalNormalFibreTruncationAlgHom_tmul_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) (c : ℂ)
    (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    originalNormalFibreTruncationAlgHom d t I s
      (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g) =
        c • Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) g := by
  let := tangentAlgebra d t
  dsimp only
  rfl

/-- Every actual original germ maps to its genuine one-tensor original normal-power class. -/
def originalToFibreTensorBase (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    letI := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₐ[HolGerm (ComplexModel d)]
      (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s) :=
  letI := tangentAlgebra d t
  (Algebra.TensorProduct.includeRight : originalNormalTruncation d t I s →ₐ[HolGerm (ComplexModel d)]
      (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s)).comp
    (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (I ⊔ normalIdeal d t ^ s))

/-- Actual quotient membership and tensor balancing kill the entire true fibre ideal. -/
theorem originalToFibreTensorBase_kernel (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    let := tangentAlgebra d t
    ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) ≤
      RingHom.ker (originalToFibreTensorBase d t I s).toRingHom := by
  let := tangentAlgebra d t
  let G := originalToFibreTensorBase d t I s
  have hnormal : I ⊔ normalIdeal d t ^ s ≤ RingHom.ker G.toRingHom := by
    intro g hg
    change (1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, TensorProduct.tmul_zero]
  have hbase : originalBaseMaximalIdeal d t ≤ RingHom.ker G.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change G (tangentPullback d t b) = 0
    have hsc := G.commutes b
    change G (tangentPullback d t b) =
      (HolGerm.eval b) ⊗ₜ[HolGerm (ComplexModel d)] (1 : originalNormalTruncation d t I s) at hsc
    rw [hsc, (HolGerm.mem_maximalIdeal_iff b).mp hb, TensorProduct.zero_tmul]
  exact sup_le (sup_le (le_sup_left.trans hnormal) hbase) (le_sup_right.trans hnormal)

/-- The actual whole original fibre class maps back to its genuine residue tensor class. -/
def originalNormalFibreTruncationInverseAlgHom (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    letI := tangentAlgebra d t
    originalFibrePowerQuotient d t I s →ₐ[ℂ]
      (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s) := by
  letI := tangentAlgebra d t
  let G := originalToFibreTensorBase d t I s
  let L := Ideal.Quotient.lift ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s)
    G.toRingHom (originalToFibreTensorBase_kernel d t I s)
  refine { L with commutes' := ?_ }
  intro c
  change G (algebraMap ℂ (HolGerm (ComplexModel (d+t))) c) = _
  calc
    G (algebraMap ℂ (HolGerm (ComplexModel (d+t))) c) =
        G (tangentPullback d t (algebraMap ℂ (HolGerm (ComplexModel d)) c)) := by
      rw [(tangentPullback d t).commutes]
    _ = algebraMap (HolGerm (ComplexModel d))
        (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s)
          (algebraMap ℂ (HolGerm (ComplexModel d)) c) := G.commutes _
    _ = algebraMap ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s) c := rfl

/-- The true inverse retains every actual original quotient numerator literally. -/
theorem originalNormalFibreTruncationInverseAlgHom_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    originalNormalFibreTruncationInverseAlgHom d t I s
      (Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) g) =
        (1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g := by
  let := tangentAlgebra d t
  rfl

/-- Genuine inverse maps identify the residue tensor with the original whole fibre-power algebra. -/
def originalNormalFibreTruncationAlgEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) :
    letI := tangentAlgebra d t
    (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I s) ≃ₐ[ℂ]
      originalFibrePowerQuotient d t I s := by
  letI := tangentAlgebra d t
  refine AlgEquiv.ofAlgHom (originalNormalFibreTruncationAlgHom d t I s)
    (originalNormalFibreTruncationInverseAlgHom d t I s) ?_ ?_
  · apply AlgHom.ext
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
    change originalNormalFibreTruncationAlgHom d t I s
      (originalNormalFibreTruncationInverseAlgHom d t I s
        (Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) g)) = _
    rw [originalNormalFibreTruncationInverseAlgHom_mk, originalNormalFibreTruncationAlgHom_tmul_mk,
      one_smul]
    rfl
  · apply AlgHom.ext
    intro z
    change originalNormalFibreTruncationInverseAlgHom d t I s
      (originalNormalFibreTruncationAlgHom d t I s z) = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c q =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [originalNormalFibreTruncationAlgHom_tmul_mk, map_smul,
        originalNormalFibreTruncationInverseAlgHom_mk]
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' (R := HolGerm (ComplexModel d)) c (1 : ℂ)
          (Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g))
    | add z w hz hw => simp only [map_add, hz, hw]

/-- Every forward pure tensor numerator is its actual original fibre class. -/
theorem originalNormalFibreTruncationAlgEquiv_tmul_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ) (c : ℂ)
    (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    originalNormalFibreTruncationAlgEquiv d t I s
      (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g) =
        c • Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) g := by
  let := tangentAlgebra d t
  exact originalNormalFibreTruncationAlgHom_tmul_mk d t I s c g

/-- Every inverse whole fibre numerator retains its literal one-tensor original class. -/
theorem originalNormalFibreTruncationAlgEquiv_symm_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (s : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    (originalNormalFibreTruncationAlgEquiv d t I s).symm
      (Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d t) ⊔ normalIdeal d t ^ s) g) =
        (1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ s) g := by
  let := tangentAlgebra d t
  exact originalNormalFibreTruncationInverseAlgHom_mk d t I s g

open HironakaHolomorphicPointJets HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations

/-- Original coherence supplies the EXISTING entire Hilbert--Samuel sequence of the genuine FIBRE ideal on one open. -/
theorem exists_original_nearby_whole_fibre_hilbertSamuel_open (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ ℓ : ℕ,
        hilbertSamuelValue
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a)) ⊔
            originalBaseMaximalIdeal d t) ℓ = ∑ i ∈ Finset.range (ℓ+1), r i := by
  let := tangentAlgebra d t
  obtain ⟨U, r, hU, hmeet, _hdegree, _htrunc, hfibre⟩ :=
    exists_original_nearby_all_fibre_truncation_dimension_open d t I hI
  refine ⟨U, r, hU, hmeet, ?_⟩
  intro a ha ℓ
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  let E := originalNormalFibreTruncationAlgEquiv d t Ia (ℓ+1)
  calc
    hilbertSamuelValue (Ia ⊔ originalBaseMaximalIdeal d t) ℓ =
        Module.finrank ℂ (originalFibrePowerQuotient d t Ia (ℓ+1)) := by
      unfold hilbertSamuelValue
      rw [fibreMaximalIdeal_power_eq]
    _ = Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t Ia (ℓ+1)) :=
      E.toLinearEquiv.finrank_eq.symm
    _ = ∑ i ∈ Finset.range (ℓ+1), r i := (hfibre a ha (ℓ+1)).2

end
end Hironaka.HironakaRelativeNormalFibreHilbertSamuel

import DeJongAlterations.Algebra.NodeFormalMorseCoefficientLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual finitely generated coefficient ideals in formal power series

The finite-generation hypothesis is used in the reverse direction. Without it,
no equality between coefficientwise membership and an extended ideal is claimed.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {A : Type u} [CommRing A] {σ : Type v}

/-- Membership in the actual extended ideal implies original coefficient membership. -/
theorem coeff_mem_of_mem_extended (I : Ideal A) {f : MvPowerSeries σ A}
    (hf : f ∈ I.map (MvPowerSeries.C : A →+* MvPowerSeries σ A)) :
    ∀ d, coeff d f ∈ I := by
  have hle : I.map (MvPowerSeries.C : A →+* MvPowerSeries σ A) ≤
      RingHom.ker (MvPowerSeries.map (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change MvPowerSeries.map (Ideal.Quotient.mk I) (C a) = 0
    rw [MvPowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hz : MvPowerSeries.map (Ideal.Quotient.mk I) f = 0 := hle hf
  intro d
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [coeff_map, map_zero] using congrArg (coeff d) hz

/-- Finite original generators give an actual finite series decomposition inside the extended ideal. -/
theorem mem_extended_of_coeff_mem (I : Ideal A) (hI : I.FG) (f : MvPowerSeries σ A)
    (hf : ∀ d, coeff d f ∈ I) :
    f ∈ I.map (MvPowerSeries.C : A →+* MvPowerSeries σ A) := by
  classical
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hcoeff (d : σ →₀ ℕ) : ∃ c : Fin n → A, ∑ i, c i * a i = coeff d f := by
    have hm : coeff d f ∈ Submodule.span A (Set.range a) := ha.symm ▸ hf d
    simpa only [smul_eq_mul] using (Submodule.mem_span_range_iff_exists_fun A).mp hm
  choose c hc using hcoeff
  let g (i : Fin n) : MvPowerSeries σ A := fun d => c d i
  have he : f = ∑ i, C (a i) * g i := by
    apply MvPowerSeries.ext
    intro d
    rw [map_sum]
    simp only [coeff_C_mul]
    change coeff d f = ∑ i, a i * c d i
    simpa only [mul_comm] using (hc d).symm
  rw [he]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_right
  apply Ideal.mem_map_of_mem
  exact ha ▸ Submodule.subset_span (Set.mem_range_self i)

/-- Exactly under finite generation, coefficientwise membership equals actual extended-ideal membership. -/
theorem mem_extended_iff (I : Ideal A) (hI : I.FG) (f : MvPowerSeries σ A) :
    f ∈ I.map (MvPowerSeries.C : A →+* MvPowerSeries σ A) ↔ ∀ d, coeff d f ∈ I :=
  ⟨coeff_mem_of_mem_extended I, mem_extended_of_coeff_mem I hI f⟩

/-- Coefficient change along any actual surjection is itself surjective on formal series. -/
theorem map_surjective {B : Type*} [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  intro g
  choose a ha using fun d => hf (coeff d g)
  refine ⟨fun d => a d, ?_⟩
  ext d
  exact ha d

/-- The actual kernel of coefficient reduction is the extended ideal, using its finite generators. -/
theorem ker_coefficientReduction (I : Ideal A) (hI : I.FG) :
    RingHom.ker (MvPowerSeries.map (σ := σ) (Ideal.Quotient.mk I)) =
      I.map (MvPowerSeries.C : A →+* MvPowerSeries σ A) := by
  ext f
  rw [mem_extended_iff I hI]
  change MvPowerSeries.map (Ideal.Quotient.mk I) f = 0 ↔ _
  constructor
  · intro hf d
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [coeff_map, map_zero] using congrArg (coeff d) hf
  · intro hf
    ext d
    rw [coeff_map, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf d)

/-- The literal coefficient reduction with its original A-algebra structure. -/
def coefficientReduction (I : Ideal A) :
    MvPowerSeries σ A →ₐ[A] MvPowerSeries σ (A ⧸ I) :=
  MvPowerSeries.mapAlgHom (Ideal.Quotient.mkₐ A I)

/-- The actual quotient by the extended ideal is the literal quotient-coefficient series ring. -/
def coefficientQuotientEquiv (I : Ideal A) (hI : I.FG) :
    (MvPowerSeries σ A ⧸ I.map C) ≃ₐ[A] MvPowerSeries σ (A ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq A (ker_coefficientReduction (σ := σ) I hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := coefficientReduction I) (map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective))

@[simp]
theorem coefficientQuotientEquiv_mk (I : Ideal A) (hI : I.FG) (f : MvPowerSeries σ A) :
    coefficientQuotientEquiv I hI (Ideal.Quotient.mk (I.map C) f) =
      MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  unfold coefficientQuotientEquiv
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end DeJongAlterations.Algebra.NodeFlatPresentation

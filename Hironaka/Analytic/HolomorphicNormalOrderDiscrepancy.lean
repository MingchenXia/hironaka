import Hironaka.Analytic.DemaillyApproximantDivisorialLelong
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Analytic.CoordinateDensityGeneral
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Multiplicity

set_option autoImplicit false

/-!
# Actual finite normal order of nonzero holomorphic germs

No normal exponent, unit, or discrepancy factorization is an input.
The local geometric consumer retains the actual nonzero Jacobian germ;
it does not assert that arbitrary maps are nondegenerate or supply a
uniform discrepancy bound over a whole divisor.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HolomorphicNormalOrderDiscrepancy

open DivisorialMultiplierOrder DivisorialChangeOfVariables
  DemaillyApproximantDivisorialLelong

/-- Noetherian local-germ separation internally supplies a finite normal
order and a holomorphic factor nonzero frequently on the hyperplane. -/
theorem exists_finite_normal_order_of_nonzero_germ
    {m : ℕ} {G : ComplexModel (m + 1) → ℂ}
    (hG : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ G z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), G z ≠ 0) :
    ∃ k : ℕ, ∃ H : ComplexModel (m + 1) → ℂ,
      (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z) ∧
      G =ᶠ[𝓝 0] (fun z => z (Fin.last m) ^ k * H z) ∧
      ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z (Fin.last m) = 0 ∧ H z ≠ 0 := by
  classical
  let R := HolGerm (ComplexModel (m + 1))
  let : IsNoetherianRing R := isNoetherianRing_holGerm_euclidean (m + 1)
  let g : R := HolGerm.mk G hG
  have hcoord : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z : ComplexModel (m + 1) => z (Fin.last m)) z :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiableAt
  let t : R := HolGerm.mk (fun z => z (Fin.last m)) hcoord
  have hg : g ≠ 0 := by
    intro hzero
    have heq : G =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun _ => (0 : ℂ) :=
      HolGerm.mk_eq_mk_iff.mp (hzero.trans HolGerm.mk_zero.symm)
    obtain ⟨z, hz, hz0⟩ := (hne.and_eventually heq).exists
    exact hz hz0
  let M : Ideal R := IsLocalRing.maximalIdeal R
  have htM : t ∈ M := by
    rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
    simp
  have hfinite : FiniteMultiplicity t g := by
    by_contra hnot
    have hall := FiniteMultiplicity.not_iff_forall.mp hnot
    have hmem : g ∈ ⨅ N : ℕ, M ^ N := by
      refine (Submodule.mem_iInf _).mpr fun N => ?_
      obtain ⟨q, hq⟩ := hall N
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htM N)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing M (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
      at hmem
    exact hg hmem
  obtain ⟨h, hfactor, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk h
  refine ⟨multiplicity t g, H, hH, ?_, ?_⟩
  · change HolGerm.mk G hG = HolGerm.mk (fun z => z (Fin.last m)) hcoord ^
      multiplicity t g * HolGerm.mk H hH at hfactor
    rw [← HolGerm.mk_pow, ← HolGerm.mk_mul] at hfactor
    exact HolGerm.mk_eq_mk_iff.mp hfactor
  · by_contra hnonzero
    have hvanish : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        z (Fin.last m) = 0 → H z = 0 := by
      filter_upwards [Filter.not_frequently.mp hnonzero] with z hz
      intro hlast
      by_contra hHz
      exact hz ⟨hlast, hHz⟩
    obtain ⟨Q, hQ, hEQ⟩ := exists_eq_last_mul_of_eq_zero (by simp) hH hvanish
    apply hnot
    refine ⟨HolGerm.mk Q hQ, ?_⟩
    change HolGerm.mk H hH = HolGerm.mk (fun z => z (Fin.last m)) hcoord * HolGerm.mk Q hQ
    rw [← HolGerm.mk_mul, HolGerm.mk_eq_mk_iff]
    exact hEQ

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (complexJacobian F) U := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (Hironaka.MongeAmpere.coordinateVector j)) i) U :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (Hironaka.differentiableOn_fderiv_apply_of_isOpen hF hU
        (Hironaka.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (Hironaka.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← Hironaka.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [Hironaka.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ U).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih

/-- Actual holomorphy and a nonzero actual Jacobian germ supply a finite
local log-discrepancy bound without a factorization or exponent input. -/
theorem exists_logDiscrepancyLE_of_nonzero_jacobian_germ
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      complexJacobian (flatCoordMap π Φ) z ≠ 0) :
    ∃ A : ℕ, LogDiscrepancyLE m π E x A := by
  have hU := Φ.isOpen_flatDomain hπ.continuous
  have hJ := differentiableOn_complexJacobian hU (Φ.differentiableOn_flatCoordMap hπ)
  have hJnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (complexJacobian (flatCoordMap π Φ)) z := by
    filter_upwards [hU.mem_nhds (Φ.zero_mem_flatDomain π)] with z hz
    exact hJ.differentiableAt (hU.mem_nhds hz)
  obtain ⟨k, H, hH, hfactor, hnonzero⟩ :=
    exists_finite_normal_order_of_nonzero_germ hJnear hne
  exact ⟨k + 1, Φ, k, H, le_rfl, hH, hfactor, hnonzero⟩

end Hironaka.HolomorphicNormalOrderDiscrepancy

/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.HolomorphicGenericRank
import Hironaka.Analytic.HolomorphicAnalytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false

/-!
# The generic rank of a holomorphic map

Blueprint `rem:generic-rank` (Demailly, *Complex analytic and differential geometry*, II.8.3:
the maximum of the rank is attained on a dense open set).  Let `G` be holomorphic on a connected
open set `U` of a finite-dimensional complex normed space and let the rank of `dG` attain its
maximum `r` at `z₁ ∈ U`.

* `eventually_finrank_range_le`: the rank of a continuous family of linear maps is lower
  semicontinuous (a linearly independent family of images stays independent nearby,
  `LinearIndependent.eventually`).
* `isOpen_maxRank`: `{z ∈ U | rank dG_z = r}` is open.
* `subset_closure_maxRank`: it is dense in `U`.  With `dG_{z₁} vᵢ = bᵢ` a basis of `range dG_{z₁}`
  and functionals `ℓⱼ` dual to it, `h(z) = det (ℓⱼ (dG_z vᵢ))` is holomorphic on `U`, equals `1` at
  `z₁` and vanishes where the rank is `< r` (the `dG_z vᵢ` are then dependent); by the identity
  theorem it cannot vanish on a nonempty open subset of the connected `U`.
-/

open Set Filter Topology Module

noncomputable section

namespace Hironaka.HolomorphicGenericRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]


/-- **The maximal-rank set is dense** in a connected open set: if the rank of `dG` is maximal at
`z₁`, every point of `U` is a limit of points where it is maximal. -/
theorem subset_closure_maxRank {G : E → F} {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hG : DifferentiableOn ℂ G U) {z₁ : E} (hz₁ : z₁ ∈ U)
    (hmax : ∀ z ∈ U, finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) ≤
      finrank ℂ (LinearMap.range ((fderiv ℂ G z₁ : E →L[ℂ] F) : E →ₗ[ℂ] F))) :
    U ⊆ closure {z ∈ U | finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) =
      finrank ℂ (LinearMap.range ((fderiv ℂ G z₁ : E →L[ℂ] F) : E →ₗ[ℂ] F))} := by
  classical
  set R := LinearMap.range ((fderiv ℂ G z₁ : E →L[ℂ] F) : E →ₗ[ℂ] F) with hR
  set r := finrank ℂ R with hr
  set b := Module.finBasis ℂ R
  have hpre : ∀ i, ∃ v : E, fderiv ℂ G z₁ v = (b i : F) := fun i => (b i).2
  choose v hv using hpre
  obtain ⟨R', hR'⟩ := R.exists_isCompl
  -- functionals dual to the basis `b`
  let ℓ : Fin r → F →L[ℂ] ℂ := fun j =>
    ((b.coord j).comp (Submodule.projectionOnto R R' hR')).toContinuousLinearMap
  have hℓ : ∀ i j, ℓ j (b i : F) = if i = j then 1 else 0 := by
    intro i j
    simp only [ℓ, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
      Submodule.projectionOnto_apply_left, Basis.coord_apply, Basis.repr_self]
    rw [Finsupp.single_apply]
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  let Mz : E → Matrix (Fin r) (Fin r) ℂ := fun z => Matrix.of fun i j => ℓ j (fderiv ℂ G z (v i))
  let h : E → ℂ := fun z => (Mz z).det
  have hdiff : DifferentiableOn ℂ h U := by
    have hentry : ∀ i j, DifferentiableOn ℂ (fun z => Mz z i j) U := fun i j =>
      (ℓ j).differentiable.comp_differentiableOn
        (Hironaka.differentiableOn_fderiv_apply_of_isOpen hG hU (v i))
    have hdet : h = fun z => ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
        ∏ a : Fin r, Mz z (σ a) a := by
      funext z
      simp only [h, Matrix.det_apply]
    rw [hdet]
    refine DifferentiableOn.fun_sum fun σ _ => (?_ : DifferentiableOn ℂ _ U).const_smul _
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a u ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih
  have hz₁' : h z₁ = 1 := by
    have : Mz z₁ = 1 := by
      ext i j
      simp only [Mz, Matrix.of_apply, hv, hℓ, Matrix.one_apply]
    simp [h, this]
  -- `h` vanishes where the rank drops
  have hzero : ∀ z ∈ U, finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) < r →
      h z = 0 := by
    intro z hz hlt
    have hdep : ¬ LinearIndependent ℂ (fun i => (⟨fderiv ℂ G z (v i), LinearMap.mem_range_self _ _⟩ :
        LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F))) := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      omega
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨c, hc, i₀, hi₀⟩ := hdep
    refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨c, fun h0 => hi₀ (by simp [h0]), ?_⟩
    funext j
    have hc' : ∑ i, c i • fderiv ℂ G z (v i) = 0 := by
      have := congrArg Subtype.val hc
      simpa using this
    have := congrArg (ℓ j) hc'
    simpa [Matrix.vecMul, dotProduct, Mz, map_sum, mul_comm] using this
  -- density by the identity theorem
  intro z hz
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hVU : V ∩ U ∈ 𝓝 z := Filter.inter_mem hV (hU.mem_nhds hz)
  have hzero' : h =ᶠ[𝓝 z] 0 := by
    filter_upwards [hVU] with y hy
    refine hzero y hy.2 (lt_of_le_of_ne (hmax y hy.2) fun heq => ?_)
    have : y ∈ V ∩ {z ∈ U | finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) :
        E →ₗ[ℂ] F)) = r} := ⟨hy.1, hy.2, heq⟩
    rw [hne] at this
    exact this
  have hanal := HolomorphicAnalytic.analyticOnNhd_of_differentiableOn hU hdiff
  have := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz hzero' hz₁
  rw [hz₁'] at this
  exact one_ne_zero this

end Hironaka.HolomorphicGenericRank
end

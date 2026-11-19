import Hironaka.Coherence.OkaRelationSheaf

/-! # Generation of relations at a point propagates to a neighbourhood (Oka)

If holomorphic relations `τ_k` of a holomorphic matrix `A` generate the relations of `A` at `x`, they
generate them at every point of a neighbourhood of `x` (`exists_generatesRelationsOn`): Oka's
generators `σ_l` near `x` are combinations `σ_l = ∑ c_{lk} τ_k` near `x`, hence on an open
neighbourhood, and every relation at a nearby point is a combination of the `σ_l`. This turns the
pointwise generation obtained from Nakayama (`HironakaG10FlatRelationLift`) into exact starts on open
sets (`OkaRelationSheaf.GeneratesRelationsOn`), as needed to lift finite resolutions of a fibre.
BP: hironaka-g10-flat-generation-locus.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatGenerationLocus
noncomputable section
open OkaRelationSheaf

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **Generation at a point propagates to an open neighbourhood.** -/
theorem exists_generatesRelationsOn (hX : OkaProperty X) {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁]
    {μ : Type*} [Fintype μ] {A : ι₀ → ι₁ → X → ℂ} {x : X} (hA : ∀ i j, HolAt (A i j) x)
    {τ : μ → ι₁ → X → ℂ} (hτ : ∀ k j, HolAt (τ k j) x)
    (hτrel : ∀ k i, ∀ᶠ y in 𝓝 x, ∑ j, τ k j y * A i j y = 0)
    (hgen : ∀ a, IsRelationAt A x a → IsCombinationAt τ x a) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ (∀ i j, DifferentiableOn ℂ (A i j) V) ∧
      GeneratesRelationsOn A V τ := by
  obtain ⟨U, hU, hxU, ν, _, σ, hσ⟩ := hX ι₀ ι₁ A x hA
  have hσx : ∀ l j, HolAt (σ l j) x := fun l j => holAt_of_differentiableOn hU (hσ.1 l j) hxU
  have hσrel : ∀ l, IsRelationAt A x (σ l) := fun l => ⟨hσx l, fun i => by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hσ.2.1 l i y hy⟩
  choose c hc hcσ using fun l => hgen (σ l) (hσrel l)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (∀ i j, DifferentiableAt ℂ (A i j) y) ∧
      (∀ k j, DifferentiableAt ℂ (τ k j) y) ∧ (∀ l k, DifferentiableAt ℂ (c l k) y) ∧
      (∀ k i, ∑ j, τ k j y * A i j y = 0) ∧
      ∀ l j, σ l j y = ∑ k, c l k y * τ k j y := by
    refine (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and ?_
    refine (eventually_all.2 fun i => eventually_all.2 fun j => hA i j).and ?_
    refine (eventually_all.2 fun k => eventually_all.2 fun j => hτ k j).and ?_
    refine (eventually_all.2 fun l => eventually_all.2 fun k => hc l k).and ?_
    exact (eventually_all.2 fun k => eventually_all.2 fun i => hτrel k i).and
      (eventually_all.2 fun l => eventually_all.2 fun j => hcσ l j)
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1 hev
  refine ⟨V, hVo, hxV, fun i j y hy => ((hV y hy).2.1 i j).differentiableWithinAt,
    fun k j y hy => ((hV y hy).2.2.1 k j).differentiableWithinAt,
    fun k i y hy => (hV y hy).2.2.2.2.1 k i, fun y hy a ha => ?_⟩
  obtain ⟨lam, hlam, hlamσ⟩ := hσ.2.2 y (hV y hy).1 a ha
  refine ⟨fun k z => ∑ l, lam l z * c l k z, fun k => HolAt.fintype_sum fun l =>
    (hlam l).mul (holAt_of_differentiableOn hVo
      (fun z hz => ((hV z hz).2.2.2.1 l k).differentiableWithinAt) hy), fun j => ?_⟩
  have hev2 : ∀ᶠ z in 𝓝 y, a j z = ∑ l, lam l z * σ l j z ∧ z ∈ V :=
    (hlamσ j).and (hVo.mem_nhds hy)
  filter_upwards [hev2] with z ⟨h1, hz⟩
  rw [h1]
  simp_rw [(hV z hz).2.2.2.2.2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end
end Hironaka.HironakaG10FlatGenerationLocus

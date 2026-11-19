import Hironaka.Resolution.HironakaG10FlatSliceResolution
import Hironaka.Resolution.HironakaG10LocFibreOpen

/-! The one-parameter exact-fibre criterion gives coordinate regularity on
the cokernel. No higher-dimensional stalk flatness criterion is assumed.
Blueprint: `hironaka-g10-fibre-regular-criterion.tex`. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FibreRegularCriterion
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatSliceResolution
  HironakaG10LocFibreOpen HironakaG10LocSheafExact

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

omit [Fintype ι₀] in
/-- Exactness of the fibre of a holomorphic complex forces the parameter
coordinate to be a non-zero-divisor on the cokernel of its last map. -/
theorem regularAt_of_slice_exact
    {G : ι₁ → ι₂ → ℂ × P → ℂ} {F : ι₀ → ι₁ → ℂ × P → ℂ} {z₀ : P}
    (hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀))
    (hG : ∀ j k, HolAt (G j k) ((0 : ℂ), z₀))
    (hcomp : ∀ i k, ∀ᶠ x in 𝓝 ((0 : ℂ), z₀), ∑ j, F i j x * G j k x = 0)
    (hfib : ∀ a : ι₁ → P → ℂ, IsRelationAt (sliceZero F) z₀ a →
      IsCombinationAt (columns (sliceZero G)) z₀ a) :
    RegularAt F (fun x => x.1) ((0 : ℂ), z₀) := by
  let y : ℂ × P := (0, z₀)
  intro c hc hwc
  obtain ⟨a, ha, hac⟩ := hwc
  have hafib : IsRelationAt (sliceZero F) z₀ (fun j z => a j (0, z)) := by
    refine ⟨fun j => HolAt.comp_zero_prod (ha j), fun i => ?_⟩
    filter_upwards [(tendsto_zero_prod z₀).eventually (hac i)] with z hz
    simpa only [zero_mul, columns, sliceZero] using hz.symm
  obtain ⟨b, hb, hab⟩ := hfib _ hafib
  let u : ι₁ → ℂ × P → ℂ := fun j x => a j x - ∑ k, b k x.2 * G j k x
  have hub (j : ι₁) : HolAt (u j) y :=
    (ha j).sub (HolAt.fintype_sum fun k =>
      ((hb k).comp (f := b k) continuous_snd fun _ => differentiableAt_snd).mul (hG j k))
  have hu0 (j : ι₁) : ∀ᶠ z in 𝓝 z₀, u j (0, z) = 0 := by
    filter_upwards [hab j] with z hz
    exact sub_eq_zero.mpr hz
  choose a' ha' hdiv using fun j => exists_eq_fst_mul (hub j) rfl (hu0 j)
  refine ⟨a', ha', fun i => ?_⟩
  have hdelta : HolAt (fun x => c i x - ∑ j, a' j x * F i j x) y :=
    (hc i).sub (HolAt.fintype_sum fun j => (ha' j).mul (hF i j))
  have hzero : ∀ᶠ x in 𝓝 y, x.1 * (c i x - ∑ j, a' j x * F i j x) = 0 := by
    filter_upwards [hac i, eventually_all.2 hdiv, eventually_all.2 (fun k => hcomp i k)]
      with x hcx hdx hFGx
    have hGb : ∑ j, (∑ k, b k x.2 * G j k x) * F i j x = 0 := by
      calc
        _ = ∑ k, b k x.2 * ∑ j, F i j x * G j k x := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := Finset.sum_eq_zero fun k _ => by rw [hFGx k, mul_zero]
    have hFa : ∑ j, a j x * F i j x = x.1 * ∑ j, a' j x * F i j x := by
      calc
        _ = ∑ j, (u j x + ∑ k, b k x.2 * G j k x) * F i j x := by
          exact Finset.sum_congr rfl fun j _ => by dsimp [u]; ring
        _ = ∑ j, (x.1 * a' j x + ∑ k, b k x.2 * G j k x) * F i j x := by
          exact Finset.sum_congr rfl fun j _ => by rw [hdx j]
        _ = x.1 * (∑ j, a' j x * F i j x) +
            ∑ j, (∑ k, b k x.2 * G j k x) * F i j x := by
          simp_rw [add_mul, Finset.sum_add_distrib]
          rw [Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by rw [hGb, add_zero]
    change x.1 * c i x = ∑ j, a j x * F i j x at hcx
    rw [mul_sub, hcx, hFa, sub_self]
  have hz := nonZeroDivisorAt_fst y _ hdelta hzero
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

/-- For an actual exact start, fibre exactness is equivalent to coordinate
regularity of the presented cokernel. -/
theorem slice_exact_iff_regularAt
    {U : Set (ℂ × P)} {G : ι₁ → ι₂ → ℂ × P → ℂ} {F : ι₀ → ι₁ → ℂ × P → ℂ}
    (h : ExactStartOn U G F) (hU : IsOpen U) {z₀ : P} (hz₀ : ((0 : ℂ), z₀) ∈ U) :
    (∀ a : ι₁ → P → ℂ, IsRelationAt (sliceZero F) z₀ a →
      IsCombinationAt (columns (sliceZero G)) z₀ a) ↔
      RegularAt F (fun x => x.1) ((0 : ℂ), z₀) := by
  constructor
  · exact regularAt_of_slice_exact
      (fun i j => holAt_of_differentiableOn hU (h.holF i j) hz₀)
      (fun j k => holAt_of_differentiableOn hU (h.holG j k) hz₀)
      (fun i k => Filter.mem_of_superset (hU.mem_nhds hz₀) fun x hx => h.comp i k x hx)
  · intro hreg a ha
    exact isCombinationAt_slice h hU hz₀ hreg a ha

/-- The one-parameter exact-start predicate has exactly the expected
coordinate non-zero-divisor meaning. This does not assert `Module.Flat`. -/
theorem fibreFlatAt_iff_coordinate_regular
    (hX : OkaProperty (ℂ × P)) {a b : ℕ} (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P)
    (hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀)) :
    FibreFlatAt F ((0 : ℂ), z₀) ↔ RegularAt F (fun x => x.1) ((0 : ℂ), z₀) := by
  constructor
  · rintro ⟨c, G, U, hU, hyU, hstart, hfib⟩
    exact (slice_exact_iff_regularAt hstart hU hyU).mp hfib
  · intro hreg
    obtain ⟨U, hU, hyU, c, G, hstart⟩ := exists_exactStartOn hX F ((0 : ℂ), z₀) hF
    exact ⟨c, G, U, hU, hyU, hstart, (slice_exact_iff_regularAt hstart hU hyU).mpr hreg⟩

end
end Hironaka.HironakaG10FibreRegularCriterion

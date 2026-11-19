import Hironaka.Resolution.HironakaG8TransverseCarrierIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.GiraudAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Flat-coordinate field calculus (G8 lane, run 0079)

Blueprint: `hironaka-g8-resume-flat-field-calculus.tex`.

Reusable calculus for holomorphic vector fields written in flat coordinates `ψ = Φ ∘ e` of a local
holomorphic coordinate system `Φ`:

* `flatPartial_flatCoord`: `∂ψ_m/∂ψ_r = δ_{rm}` on the flat domain;
* `fieldDeriv_comp_eventuallyEq_sum_flatPartial`: the chain rule THROUGH a holomorphic map `π`:
  `ξ'(f ∘ π) = ∑_m ξ'(ψ_m ∘ π) · (∂f/∂ψ_m) ∘ π` near `y`, for any field `ξ'` on the source of `π`;
* `combField`: the field `∑_r a_r ∂/∂ψ_r`, with `fieldDeriv_combField` and its value on flat coordinates;
* `fieldDeriv_add_const`, `fieldDeriv_mul_eventuallyEq`: affine shifts and the Leibniz rule;
* `isTangentField_of_coordinate`: a field is tangent to a set cut out by flat coordinates `ψ_t` (`t ∈ T`) as soon as
  it maps each `ψ_t` into the vanishing ideal of the set (whole Hadamard decomposition).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8FlatFieldCalculus

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
open Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong
  Hironaka.DerivativeIdealAlongCoherent Hironaka.DerivativeIdealAlongEtale
  Hironaka.DerivativeIdealInvariance
  Hironaka.GiraudAlong Hironaka.BlowupFlatCoordinates
  Hironaka.NormalCrossings Hironaka.RelativePrincipalizationSpan
  Hironaka.HironakaG8TransverseCarrierIdeal

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

section Flat

variable {x : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- `∂ψ_m/∂ψ_r = δ_{rm}` on the flat domain. -/
theorem flatPartial_flatCoord (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) (r m : Fin n)
    {q : X} (hq : q ∈ flatDomain Φ) :
    flatPartial Φ r (flatCoord Φ m) q = if m = r then 1 else 0 := by
  rw [flatPartial_eq hq (holomorphicAt_flatCoord Φ m hq) r]
  have hloc : flatCoord Φ m ∘ flatInv Φ =ᶠ[𝓝 (flatMap Φ q)] fun w : ComplexModel n => w m := by
    filter_upwards [Φ.isOpen_target.mem_nhds (flatMap_mem_target hq)] with w hw
    show flatMap Φ (flatInv Φ w) m = w m
    rw [flatMap_flatInv hw hΦsrc]
  rw [hloc.fderiv_eq]
  have hd : HasFDerivAt (fun w : ComplexModel n => w m)
      (EuclideanSpace.proj (𝕜 := ℂ) m : ComplexModel n →L[ℂ] ℂ) (flatMap Φ q) :=
    (EuclideanSpace.proj (𝕜 := ℂ) m).hasFDerivAt
  rw [hd.fderiv]
  simp

/-- The field `∑_r a_r ∂/∂ψ_r`, written in the preferred chart at `x`. -/
def combField (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (a : Fin n → X → ℂ) : Fin n → X → ℂ :=
  fun m p => ∑ r, a r p * flatField Φ (EuclideanSpace.single r 1) m p

theorem fieldDeriv_combField (a : Fin n → X → ℂ) (h : X → ℂ) (p : X) :
    fieldDeriv (complexChartAt (n := n) x) (combField Φ a) h p = ∑ r, a r p * flatPartial Φ r h p := by
  simp only [fieldDeriv, combField, flatPartial, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => by ring

theorem holomorphicAt_combField {a : Fin n → X → ℂ} {p : X} (hp : p ∈ flatDomain Φ)
    (ha : ∀ r, HolomorphicAt n (a r) p) (m : Fin n) : HolomorphicAt n (combField Φ a m) p :=
  HolomorphicAt.sum _ fun r _ => (ha r).mul (holomorphicAt_flatField _ m hp)

/-- The combination field on a flat coordinate is its coefficient. -/
theorem fieldDeriv_combField_flatCoord (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (a : Fin n → X → ℂ) (l : Fin n) {p : X} (hp : p ∈ flatDomain Φ) :
    fieldDeriv (complexChartAt (n := n) x) (combField Φ a) (flatCoord Φ l) p = a l p := by
  rw [fieldDeriv_combField]
  simp only [flatPartial_flatCoord hΦsrc _ l hp, mul_ite, mul_one, mul_zero]
  simp

end Flat

section Algebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An additive constant does not change a field derivative. -/
theorem fieldDeriv_add_const (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ) (c : ℂ) :
    fieldDeriv e ξ (fun p => f p + c) = fieldDeriv e ξ f := by
  funext p
  simp only [fieldDeriv, chartDeriv]
  congr 1
  funext m
  congr 1
  have : (fun p => f p + c) ∘ e.val.symm = fun w => (f ∘ e.val.symm) w + c := rfl
  rw [this, fderiv_add_const]

/-- The field derivative of a constant vanishes. -/
theorem fieldDeriv_const_fun (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (c : ℂ) :
    fieldDeriv e ξ (fun _ => c) = fun _ => 0 := by
  funext p
  simp [fieldDeriv, chartDeriv, Function.comp_def]

/-- **The Leibniz rule** for a product of two germs. -/
theorem fieldDeriv_mul_eventuallyEq {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {y : M}
    (hy : y ∈ e.val.source) {a s : M → ℂ} (ha : HolomorphicAt n a y) (hs : HolomorphicAt n s y) :
    fieldDeriv e ξ (fun p => a p * s p) =ᶠ[𝓝 y] fun p =>
      fieldDeriv e ξ a p * s p + a p * fieldDeriv e ξ s p := by
  have h := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ) (f := fun p => a p * s p) (K := 1)
    (a := fun _ => a) (s := fun _ => s) hy
    (fun _ => ha) (fun _ => hs) (Eventually.of_forall fun p => by simp)
  filter_upwards [h] with p hp
  simpa using hp

end Algebra

section Chain

variable {x : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- **Chain rule through a holomorphic map in flat coordinates**: for every field `ξ'` near `y`,
`ξ'(f ∘ π) = ∑_m ξ'(ψ_m ∘ π) · (∂f/∂ψ_m) ∘ π` near `y`. -/
theorem fieldDeriv_comp_eventuallyEq_sum_flatPartial
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) {π : Y → X} {y : Y}
    (hπ : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π p)
    (hy : π y ∈ flatDomain Φ) (e' : ComplexChart n Y) (hy' : y ∈ e'.val.source)
    (ξ' : Fin n → Y → ℂ) {f : X → ℂ} (hf : HolomorphicAt n f (π y)) :
    fieldDeriv e' ξ' (f ∘ π) =ᶠ[𝓝 y] fun p =>
      ∑ m, fieldDeriv e' ξ' (flatCoord Φ m ∘ π) p * flatPartial Φ m f (π p) := by
  set e := complexChartAt (n := n) x
  have hye : π y ∈ e.val.source := hy.1
  have hcf := fun k : Fin n => chartDeriv_comp_eventuallyEq_sum_of_eventually e e' hπ hy' hye hf
    (EuclideanSpace.single k (1 : ℂ))
  have hcx := fun (k m : Fin n) => chartDeriv_comp_eventuallyEq_sum_of_eventually e e' hπ hy' hye
    (holomorphicAt_flatCoord Φ m hy) (EuclideanSpace.single k (1 : ℂ))
  have hπc : ContinuousAt π y := hπ.self_of_nhds.continuousAt
  filter_upwards [eventually_all.2 hcf, eventually_all.2 fun k => eventually_all.2 (hcx k),
    hπc.eventually ((isOpen_flatDomain Φ).mem_nhds hy), hπc.eventually hf.eventually_nhds]
    with p hpf hpx hpF hfp
  have hflat : ∀ j : Fin n, chartDeriv e (EuclideanSpace.single j 1) f (π p) =
      ∑ m, chartDeriv e (EuclideanSpace.single j 1) (flatCoord Φ m) (π p) * flatPartial Φ m f (π p) := by
    intro j
    rw [chartDeriv_eq_sum_flat hΦsrc e _ hpF.1 hpF hfp]
    exact Finset.sum_congr rfl fun m _ => by rw [flatPartial_eq hpF hfp m]
  simp only [fieldDeriv, hpf, hpx, hflat, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

end Chain

section Tangency

variable {y₀ : X} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}

/-- **Tangency to a set cut out by flat coordinates.**  If `H` is, on the flat domain of `Θ`, the set where the
coordinates `ψ_t` (`t ∈ T`) vanish, a holomorphic field at a point of the flat domain is tangent to `H` there as
soon as it maps every `ψ_t` into the vanishing ideal of `H`. -/
theorem isTangentField_of_coordinate (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (T : Finset (Fin n)) {H : Set X}
    (hH : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ u ∈ Θ.source →
      (u ∈ H ↔ Θ.toFun (chartAt (ComplexModel n) y₀ u) ∈ coordSubspace T))
    {e : ComplexChart n X} {ξ : Fin n → X → ℂ} {u : X} (hu : u ∈ flatDomain Θ)
    (hue : u ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) u)
    (hT : ∀ t ∈ T, (vanishingIdeal (n := n) H).mem u (fieldDeriv e ξ (flatCoord Θ t))) :
    IsTangentField H e ξ u := by
  refine ⟨hue, hξ, fun g hg => ?_⟩
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ :=
    (mem_vanishingIdeal_iff_coordinate_span Θ hΘsrc T H hH hu g).mp hg
  choose a ha using hs
  have hsh : ∀ i, HolomorphicAt n (s i) u := by
    intro i
    rw [← ha i]
    by_cases hai : a i ∈ T
    · simp only [hai, if_true]
      exact holomorphicAt_flatCoord Θ _ hu
    · simp only [hai, if_false]
      exact holomorphicAt_const 0
  have hs0 : ∀ i, ∀ᶠ q in 𝓝 u, q ∈ H → s i q = 0 := by
    intro i
    rw [← ha i]
    by_cases hai : a i ∈ T
    · simp only [hai, if_true]
      filter_upwards [(isOpen_flatDomain Θ).mem_nhds hu] with q hq hqH
      exact (hH hq.1 hq.2).mp hqH (a i) hai
    · simp only [hai, if_false]
      exact Eventually.of_forall fun _ => by simp
  have hds0 : ∀ i, ∀ᶠ q in 𝓝 u, q ∈ H → fieldDeriv e ξ (s i) q = 0 := by
    intro i
    rw [← ha i]
    by_cases hai : a i ∈ T
    · simp only [hai, if_true]
      exact (hT (a i) hai).2
    · simp only [hai, if_false, fieldDeriv_const_fun]
      exact Eventually.of_forall fun _ => by simp
  have hprod := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ) hue hc hsh hsum
  refine ⟨holomorphicAt_fieldDeriv hue hξ hg.1, ?_⟩
  filter_upwards [hprod, eventually_all.2 hs0, eventually_all.2 hds0] with q hq h1 h2 hqH
  rw [hq]
  simp [h1 _ hqH, h2 _ hqH]

end Tangency

end

end Hironaka.HironakaG8FlatFieldCalculus

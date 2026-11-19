import Hironaka.Analytic.AnalyticGluingProof
import Hironaka.Analytic.BoundedGlobalTruncation

set_option autoImplicit false

/-!
# The maximum of two Kähler currents in one class

Source: Boucksom, *Divisorial Zariski decompositions*, proof of Theorem 3.17
(`T = θ + ddᶜ max(φ₁, φ₂)` has Lelong numbers `min(ν(T₁,x), ν(T₂,x))`); Copy-4,
`sec:nK`.

For two Kähler currents `S = θ_S + ddᶜu_S ≥ ω_S` and `T = θ_T + ddᶜu_T ≥ ω_T`
in the same class on a compact manifold, write `θ_S = θ_T + ddᶜh` with `h`
chart-smooth and pick a Kähler form `ω' ≤ ω_S, ω_T`.  Then
`R = θ_S + ddᶜ max(u_S, u_T - h) ≥ ω'` is a Kähler current in the class, and its
Lelong numbers are bounded by those of `S` and of `T`:

* `lelongNumber_le_of_eventually_le`: `u ≤ v` near `x` gives `ν(v, x) ≤ ν(u, x)`;
* `lelongNumber_sub_le`: subtracting a real function continuous at `x` does not
  increase the Lelong number;
* `exists_kahlerCurrent_lelongNumber_le_both`: the Kähler current `R`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology ENNReal NNReal

namespace Hironaka.KahlerCurrentMax

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Chart-smooth functions are continuous.  (Same proof as
`GlobalSlotStokes.ChartSmooth.continuous`, which sits behind a heavy import.) -/
theorem continuous_of_chartSmooth {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hc : ContinuousAt (fun z => f (e.val.symm z)) (e.val x) :=
    ((hf e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz)
  have hcomp : ContinuousAt ((fun z => f (e.val.symm z)) ∘ e.val) x :=
    hc.comp (e.val.continuousAt hx)
  refine hcomp.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.val.left_inv hy]

omit [IsComplexManifold n M] in
/-- A potential that is larger near `x` has a smaller Lelong number at `x`. -/
theorem lelongNumber_le_of_eventually_le {u v : M → EReal} {x : M}
    (h : ∀ᶠ y in 𝓝[≠] x, u y ≤ v y) :
    lelongNumber (n := n) v x ≤ lelongNumber (n := n) u x := by
  unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨C, hC⟩ := hγ
  exact le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ
    ⟨C, (h.and hC).mono fun y hy => hy.1.trans hy.2⟩ le_rfl

omit [IsComplexManifold n M] in
/-- Subtracting a real function continuous at `x` does not increase the Lelong
number at `x`. -/
theorem lelongNumber_sub_le {u : M → EReal} {h : M → ℝ} {x : M}
    (hh : ContinuousAt h x) :
    lelongNumber (n := n) (fun y => u y - (h y : EReal)) x ≤ lelongNumber (n := n) u x := by
  unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨C, hC⟩ := hγ
  have hbound : ∀ᶠ y in 𝓝[≠] x, h y ≤ h x + 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hh.eventually (gt_mem_nhds (lt_add_one (h x)))).mono fun _ hy => hy.le)
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ ⟨C + (h x + 1), ?_⟩ le_rfl
  filter_upwards [hC, hbound] with y hy hhy
  have hsplit : u y = (u y - (h y : EReal)) + (h y : EReal) := by
    rw [EReal.sub_add_cancel]
  rw [hsplit]
  calc (u y - (h y : EReal)) + (h y : EReal)
      ≤ (((γ : ℝ) * Real.log
          ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
            EReal) + ((h x + 1 : ℝ) : EReal) :=
        add_le_add hy (EReal.coe_le_coe_iff.mpr hhy)
    _ = _ := by rw [← EReal.coe_add]; ring_nf

/-- **The maximum of two Kähler currents.**  On a compact manifold, two Kähler
currents in one class are dominated, in the sense of Lelong numbers, by a third
Kähler current in the class: `R = θ_S + ddᶜ max(u_S, u_T - h)`. -/
theorem exists_kahlerCurrent_lelongNumber_le_both [CompactSpace M]
    {alpha : RealBottChern n M} (S T : KahlerCurrent alpha) :
    ∃ R : KahlerCurrent alpha, ∀ x : M,
      lelongNumber (n := n) R.potential x ≤ lelongNumber (n := n) S.potential x ∧
        lelongNumber (n := n) R.potential x ≤ lelongNumber (n := n) T.potential x := by
  obtain ⟨ω', hSω, hTω⟩ :=
    AnalyticGluingProof.exists_kahlerBackground_le_both S.lowerBound T.lowerBound
  have hrel : ClosedRealOneOneForm.BottChernRel T.representative S.representative :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mp (T.represents.trans S.represents.symm)
  obtain ⟨h, hh, heq⟩ := hrel
  have hS : IsThetaPshPotential (S.representative - ω'.form).val S.potential := by
    have := LocalPotentials.isThetaPshPotential_add_of_semipositive S.strictlyPsh hSω
    rwa [sub_add_sub_cancel] at this
  have hT : ThetaPlurisubharmonic (T.representative - ω'.form).val T.potential := by
    have := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive T.strictlyPsh.1 hTω
    rwa [sub_add_sub_cancel] at this
  have hT' : ThetaPlurisubharmonic (S.representative - ω'.form).val
      (fun y => T.potential y - (h y : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh ?_ hT
    intro e z hz
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg, heq e z hz]
    abel
  let R : KahlerCurrent alpha :=
    { representative := S.representative
      represents := S.represents
      potential := fun y => max (S.potential y) (T.potential y - (h y : EReal))
      lowerBound := ω'
      strictlyPsh := by
        refine ⟨BoundedGlobalProduct.ThetaPlurisubharmonic.max hS.1 hT', ?_⟩
        intro x U hU hx
        obtain ⟨y, hyU, hy⟩ := hS.2 x U hU hx
        exact ⟨y, hyU, ne_bot_of_le_ne_bot hy (le_max_left _ _)⟩ }
  refine ⟨R, fun x => ⟨?_, ?_⟩⟩
  · exact lelongNumber_le_of_eventually_le (Eventually.of_forall fun y => le_max_left _ _)
  · refine (lelongNumber_le_of_eventually_le
      (u := fun y => T.potential y - (h y : EReal))
      (Eventually.of_forall fun y => le_max_right _ _)).trans ?_
    exact lelongNumber_sub_le (continuous_of_chartSmooth hh).continuousAt

end

end Hironaka.KahlerCurrentMax

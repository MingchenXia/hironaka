import Hironaka.Resolution.HironakaG4GammaCorrection
import Hironaka.Resolution.HironakaG4WeightedBinomialChart
import Hironaka.Resolution.HironakaG4PrincipalMemberLocus

/-! Construct the Gamma weighted chart from the actual smooth trace equation. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4GammaChartFromTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates GiraudAlong HironakaG34CoordinateScaling
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4WeightedBinomialChart
  HironakaG4GammaCorrection HironakaG4SmoothMemberJet HironakaG4PrincipalMemberLocus

variable {n : ℕ} {X : CMfd.{u} n}

/-- A centered prepared chart and a Gamma trace factorization construct the
actual weighted-binomial chart and preserve every tracked divisor equation. -/
theorem exists_gamma_chart_of_trace (hn : 0 < n) {N H : Set X} {E L : List (Set X)} {x : X}
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxH : x ∈ H)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (S : Finset (Fin n)) (m : Fin E.length → Option (Fin n)) (hm : DivisorMasksValid S m)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ GiraudAlong.flatMap Φ y ∈ coordSubspace S)
    (hE : ∀ i y, y ∈ flatDomain Φ → (y ∈ E.get i ↔
      GiraudAlong.flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (t : Fin n) (ht : t ∉ S) (c : Fin n → ℕ) (hc : ∀ i ∈ S, c i = 0)
    {f a : X → ℂ} (hf : HolomorphicAt n f x) (ha : HolomorphicAt n a x) (ha0 : a x ≠ 0)
    (hF : ∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g)
    (hd0 : (∏ b : Fin n, (GiraudAlong.flatMap Φ x) b ^ c b) = 0)
    (htrace : ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y *
      ((GiraudAlong.flatMap Φ y) t * ∏ b : Fin n, (GiraudAlong.flatMap Φ y) b ^ c b)) :
    ∃ (s : Fin n) (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      s ∈ S ∧ t ≠ s ∧ c s = 0 ∧ Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ GiraudAlong.flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ E.get i ↔
        GiraudAlong.flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (GiraudAlong.flatMap Ψ y) = 0 := by
  let ψ := flatInv Φ
  let f' : ComplexModel n → ℂ := f ∘ ψ
  let a' : ComplexModel n → ℂ := a ∘ ψ
  let d' : ComplexModel n → ℂ := fun z => ∏ b : Fin n, z b ^ c b
  have hψ0 : ψ 0 = x := flatInv_zero h0
  have htarget : (0 : ComplexModel n) ∈ Φ.target := zero_mem_target h0
  have hψ : Tendsto ψ (𝓝 0) (𝓝 x) := by
    have hh := (continuousAt_flatInv htarget hsrc).tendsto
    change Tendsto ψ (𝓝 0) (𝓝 (ψ 0)) at hh
    simpa only [hψ0] using hh
  have hdf := smooth_member_principal_flat_jet_ne_zero hn hL hHL hxH hf hF Φ hsrc h0
  have hmember := eventually_mem_iff_principal_generator_zero hn hL hHL hxH hf hF
  have hEv : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Φ.target ∧
      HolomorphicAt n f (ψ z) ∧ HolomorphicAt n a (ψ z) ∧ a (ψ z) ≠ 0 ∧
      (ψ z ∈ N → f (ψ z) = a (ψ z) * ((GiraudAlong.flatMap Φ (ψ z)) t *
        ∏ b : Fin n, (GiraudAlong.flatMap Φ (ψ z)) b ^ c b)) ∧
      (ψ z ∈ H ↔ f (ψ z) = 0) := by
    filter_upwards [Φ.isOpen_target.mem_nhds htarget, hψ.eventually hf.eventually,
      hψ.eventually ha.eventually, hψ.eventually (ha.continuousAt.eventually_ne ha0),
      hψ.eventually htrace, hψ.eventually hmember] with z hz hzf hza hzne htr hmem
    exact ⟨hz, hzf, hza, hzne, htr, hmem⟩
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp hEv
  have hf' : DifferentiableOn ℂ f' U := by
    intro z hz
    exact (differentiableAt_comp_flatInv (hUsub hz).1 hsrc (hUsub hz).2.1).differentiableWithinAt
  have ha' : DifferentiableOn ℂ a' U := by
    intro z hz
    exact (differentiableAt_comp_flatInv (hUsub hz).1 hsrc (hUsub hz).2.2.1).differentiableWithinAt
  have hd' : DifferentiableOn ℂ d' U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    dsimp [d']
    fun_prop
  have hf0' : f' 0 = 0 := by simpa [f', hψ0] using hdf.1
  have ha0' : a' 0 ≠ 0 := by simpa [a', hψ0] using ha0
  have hd0' : d' 0 = 0 := by
    have hflat0 : GiraudAlong.flatMap Φ x = 0 := h0
    rw [hflat0] at hd0
    exact hd0
  have hdf' : fderiv ℂ f' 0 ≠ 0 := hdf.2
  have htrace' : ∀ z ∈ U, z ∈ coordSubspace S → f' z = a' z * (z t * d' z) := by
    intro z hz hzS
    have hzu := hUsub hz
    have hψz := flatInv_mem_flatDomain hzu.1 hsrc
    have hmap : GiraudAlong.flatMap Φ (ψ z) = z := flatMap_flatInv hzu.1 hsrc
    have hzN : ψ z ∈ N := (hN (ψ z) hψz).mpr (by rw [hmap]; exact hzS)
    have hh := hzu.2.2.2.2.1 hzN
    rw [hmap] at hh
    exact hh
  obtain ⟨V, g, s, hV, h0V, hVU, hg, hg0, hs, hsderiv, hvan, hEq⟩ :=
    exists_gamma_normal_correction hU h0U hf' ha' hd' hf0' ha0' hd0' hdf' S t htrace'
  have hst : t ≠ s := fun h => ht (h ▸ hs)
  have hcs : c s = 0 := hc s hs
  have hH : ∀ y ∈ flatDomain Φ, GiraudAlong.flatMap Φ y ∈ V →
      (y ∈ H ↔ g (GiraudAlong.flatMap Φ y) + (GiraudAlong.flatMap Φ y) t *
        ∏ b : Fin n, (GiraudAlong.flatMap Φ y) b ^ c b = 0) := by
    intro y hy hyV
    have hyU := hVU hyV
    have hEqy := hEq _ hyV
    have hmem := (hUsub hyU).2.2.2.2.2
    have hne := (hUsub hyU).2.2.2.1
    dsimp only [ψ, f', a', Function.comp_apply] at hmem hne hEqy
    rw [flatInv_flatMap hy] at hmem hne hEqy
    change y ∈ H ↔ g (GiraudAlong.flatMap Φ y) + (GiraudAlong.flatMap Φ y) t * d' (GiraudAlong.flatMap Φ y) = 0
    rw [hmem, hEqy, mul_eq_zero, or_iff_right hne]
  obtain ⟨Ψ, hΨsrc, hΨ0, hΨN, hΨE, hΨH⟩ :=
    exists_weighted_binomial_chart Φ hsrc h0 S m hm hN hE s t c hs hst hcs
      g V hV h0V hg hg0 hvan hsderiv hH
  exact ⟨s, Ψ, hs, hst, hcs, hΨsrc, hΨ0, hΨN, hΨE, hΨH⟩

end
end Hironaka.HironakaG4GammaChartFromTrace

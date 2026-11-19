import Hironaka.Resolution.HironakaG4UnitCoordinateReplacement
import Hironaka.Resolution.HironakaG4PrincipalMemberLocus
import Hironaka.Resolution.HironakaG4WeightedBinomialChart

/-! A unit residual trace gives a simultaneous old-member coordinate chart. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4UnitMemberChart
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates GiraudAlong HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalDivisorMasks HironakaG4UnitCoordinateReplacement HironakaG4PrincipalMemberLocus
  HironakaG4SmoothMemberJet

variable {n : ℕ} {X : CMfd.{u} n}

/-- When the selected member's relative trace is a unit times the free
slice coordinate, straighten that actual member while keeping the carrier
and every other optional singleton boundary equation. -/
theorem exists_unit_trace_member_chart (hn : 0 < n) {N H : Set X} {E L : List (Set X)} {x : X}
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxH : x ∈ H)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (S : Finset (Fin n)) (m : Fin E.length → Option (Fin n))
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S)
    (hE : ∀ i y, y ∈ flatDomain Φ → (y ∈ E.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))))
    (t : Fin n) (ht : t ∉ S) (hmt : ∀ i, m i ≠ some t)
    {f a : X → ℂ} (hf : HolomorphicAt n f x) (ha : HolomorphicAt n a x) (ha0 : a x ≠ 0)
    (hF : ∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g)
    (htrace : ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * (flatMap Φ y) t) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ E.get i ↔
        flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ flatMap Ψ y t = 0 := by
  let ψ := flatInv Φ
  let f' : ComplexModel n → ℂ := f ∘ ψ
  let a' : ComplexModel n → ℂ := a ∘ ψ
  have hψ0 : ψ 0 = x := flatInv_zero h0
  have htarget : (0 : ComplexModel n) ∈ Φ.target := zero_mem_target h0
  have hψ : Tendsto ψ (𝓝 0) (𝓝 x) := by
    have hh := (continuousAt_flatInv htarget hsrc).tendsto
    change Tendsto ψ (𝓝 0) (𝓝 (ψ 0)) at hh
    simpa only [hψ0] using hh
  have hf0 := (smooth_member_principal_flat_jet_ne_zero hn hL hHL hxH hf hF Φ hsrc h0).1
  have hmember := eventually_mem_iff_principal_generator_zero hn hL hHL hxH hf hF
  have hEv : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Φ.target ∧
      HolomorphicAt n f (ψ z) ∧ HolomorphicAt n a (ψ z) ∧
      (ψ z ∈ N → f (ψ z) = a (ψ z) * (flatMap Φ (ψ z)) t) ∧
      (ψ z ∈ H ↔ f (ψ z) = 0) := by
    filter_upwards [Φ.isOpen_target.mem_nhds htarget, hψ.eventually hf.eventually,
      hψ.eventually ha.eventually, hψ.eventually htrace, hψ.eventually hmember] with z hz hzf hza htr hmem
    exact ⟨hz,hzf,hza,htr,hmem⟩
  obtain ⟨U,hUsub,hU,h0U⟩ := mem_nhds_iff.mp hEv
  have hfU : DifferentiableOn ℂ f' U := by
    intro z hz
    exact (differentiableAt_comp_flatInv (hUsub hz).1 hsrc (hUsub hz).2.1).differentiableWithinAt
  have haψ : HolomorphicAt n a (flatInv Φ 0) := by
    change HolomorphicAt n a (ψ 0)
    rw [hψ0]
    exact ha
  have haU : DifferentiableAt ℂ a' 0 :=
    differentiableAt_comp_flatInv htarget hsrc haψ
  have hf0' : f' 0 = 0 := by simpa [f',hψ0] using hf0
  have ha0' : a' 0 ≠ 0 := by simpa [a',hψ0] using ha0
  have htrace' : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ coordSubspace S →
      f' z = a' z * ((1 : ComplexModel n → ℂ) z * z t) := by
    filter_upwards [hU.mem_nhds h0U] with z hz hzS
    have hzu := hUsub hz
    have hψz := flatInv_mem_flatDomain hzu.1 hsrc
    have hmap : flatMap Φ (ψ z) = z := flatMap_flatInv hzu.1 hsrc
    have hzN : ψ z ∈ N := (hN (ψ z) hψz).mpr (by rw [hmap]; exact hzS)
    have hh := hzu.2.2.2.1 hzN
    rw [hmap] at hh
    simpa [f',a',Function.comp_apply] using hh
  obtain ⟨Θ,hΘU,hΘ0,hΘt,hΘother,hΘN⟩ := exists_unit_trace_coordinate_replacement
    hU h0U hfU hf0' S t ht haU (differentiableAt_const 1) ha0' (by simp) htrace'
  let Ψ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ Θ h0
  refine ⟨Ψ,fun w hw => hsrc hw.1,?_,?_,?_,?_⟩
  · change Θ.toFun (Φ.toFun (chartAt (ComplexModel n) x x)) = 0
    rw [h0,hΘ0]
  · intro y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1,hy.2.1⟩
    change y ∈ N ↔ Θ.toFun (flatMap Φ y) ∈ coordSubspace S
    exact (hN y hyΦ).trans (hΘN _)
  · intro i y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1,hy.2.1⟩
    change y ∈ E.get i ↔ Θ.toFun (flatMap Φ y) ∈ optionalCoordLocus ((m i).map (fun k => {k}))
    cases hmi : m i with
    | none => simpa [hmi,optionalCoordLocus] using hE i y hyΦ
    | some k =>
      have hkt : k ≠ t := by intro h; subst k; exact hmt i hmi
      have heq := hΘother (flatMap Φ y) k hkt
      simpa [hmi,optionalCoordLocus,coordSubspace,heq] using hE i y hyΦ
  · intro y hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1,hy.2.1⟩
    have hyΘ : flatMap Φ y ∈ Θ.source := hy.2.2
    have hmem := (hUsub (hΘU hyΘ)).2.2.2.2
    dsimp only [ψ,f',Function.comp_apply] at hmem
    rw [flatInv_flatMap hyΦ] at hmem
    change y ∈ H ↔ Θ.toFun (flatMap Φ y) t = 0
    rw [hΘt]
    simpa only [f',Function.comp_apply,ψ,flatInv_flatMap hyΦ] using hmem

end
end Hironaka.HironakaG4UnitMemberChart

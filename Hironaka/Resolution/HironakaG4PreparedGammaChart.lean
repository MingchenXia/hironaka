import Hironaka.Resolution.HironakaG4GammaChartFromTrace
import Hironaka.Resolution.HironakaG4WindowResidualTrace
import Hironaka.Resolution.HironakaG4BornExponentVector

/-! Construct the weighted Gamma chart from a prepared slice and residual factorization. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4PreparedGammaChart
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates GiraudAlong DivisorExponentAlong MonomialPartAlong
  RestrictedIdealExtension RelativePrincipalizationSpan HironakaG34CoordinateScaling
  HironakaG4OptionalBoundaryTransform HironakaG4OptionalDivisorMasks HironakaG4GammaChartFromTrace
  HironakaG4WindowResidualTrace HironakaG4BornExponentVector

variable {n : ℕ} {X : CMfd.{u} n}

/-- The protected slice geometry and actual residual factorization produce the
weighted Gamma chart, including every distinct transverse tracked divisor. -/
theorem exists_prepared_gamma_chart (hn : 0 < n)
    {N Haux H : Set X} {F B L : List (Set X)} {J : GermIdeal n X} {x : X}
    (hN : IsClosedSubmanifold n N) (hEF : IsSNCDivisor n (Haux :: F))
    (hTF : IsTransverse n N (Haux :: F)) (hBsub : B.Sublist (Haux :: F))
    (hL : IsSNCDivisor n L) (hHL : H ∈ L) (hxN : x ∈ N) (hxHaux : x ∈ Haux)
    (hI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnz : ∀ y ∈ N, IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) y)
    (hfactor : restrictOn n N (vanishingIdeal (n := n) H) = restrictOn n N
      ((monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mul J))
    (hgamma : ¬ (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) B).mem x 1)
    (hJZ : ∀ g, J.mem x g ↔ (vanishingIdeal (n := n) (N ∩ Haux)).mem x g) :
    ∃ (S : Finset (Fin n)) (m : Fin (Haux :: F).length → Option (Fin n))
      (s t : Fin n) (c : Fin n → ℕ)
      (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      DivisorMasksValid S m ∧ m ⟨0, by simp⟩ = some t ∧ s ∈ S ∧ t ∉ S ∧ t ≠ s ∧ c s = 0 ∧
      Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Ψ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ GiraudAlong.flatMap Ψ y ∈ coordSubspace S) ∧
      (∀ i y, y ∈ flatDomain Ψ → (y ∈ (Haux :: F).get i ↔
        GiraudAlong.flatMap Ψ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
      ∀ y ∈ flatDomain Ψ, y ∈ H ↔ binomial s t c (GiraudAlong.flatMap Ψ y) = 0 := by
  obtain ⟨k, Φ, p, σ, t, f, a, hsrc, h0, hp0, ht, hσk, hpk, hinj, hflat, hNflat,
    hf, ha, hax, hF, hd, heq⟩ := exists_window_gamma_trace hn hN hEF hTF hBsub hL hHL
      hxN hxHaux hI hnz hfactor hgamma hJZ
  let S : Finset (Fin n) := Finset.univ.filter fun j => k ≤ j.val
  let m : Fin (Haux :: F).length → Option (Fin n) := fun i => if x ∈ (Haux :: F).get i then some (p i) else none
  have hm : DivisorMasksValid S m := by
    constructor
    · intro i j hj hjs
      change (if x ∈ (Haux :: F).get i then some (p i) else none) = some j at hj
      by_cases hi : x ∈ (Haux :: F).get i
      · rw [if_pos hi] at hj
        have he : p i = j := Option.some.inj hj
        subst j
        have := hpk i hi
        have := (Finset.mem_filter.mp hjs).2
        omega
      · rw [if_neg hi] at hj
        contradiction
    · intro i j b hi hj
      change (if x ∈ (Haux :: F).get i then some (p i) else none) = some b at hi
      change (if x ∈ (Haux :: F).get j then some (p j) else none) = some b at hj
      by_cases hxi : x ∈ (Haux :: F).get i
      · by_cases hxj : x ∈ (Haux :: F).get j
        · rw [if_pos hxi] at hi
          rw [if_pos hxj] at hj
          apply hinj hxi hxj
          exact (Option.some.inj hi).trans (Option.some.inj hj).symm
        · rw [if_neg hxj] at hj
          contradiction
      · rw [if_neg hxi] at hi
        contradiction
  have hN' : ∀ y ∈ flatDomain Φ, y ∈ N ↔ GiraudAlong.flatMap Φ y ∈ coordSubspace S := by
    intro y hy
    rw [coordSubspace_eq_complexCoordinatePlane]
    exact hNflat hy.1 hy.2
  have hE' : ∀ i y, y ∈ flatDomain Φ → (y ∈ (Haux :: F).get i ↔
      GiraudAlong.flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k}))) := by
    intro i y hy
    have hh := hflat y hy i
    change y ∈ (Haux :: F).get i ↔ GiraudAlong.flatMap Φ y ∈
      optionalCoordLocus (((if x ∈ (Haux :: F).get i then some (p i) else none) : Option (Fin n)).map (fun k => {k}))
    by_cases hi : x ∈ (Haux :: F).get i
    · rw [if_pos hi]
      simp only [hi, true_and] at hh
      simpa [optionalCoordLocus, coordSubspace, flatCoord, GiraudAlong.flatMap] using hh
    · rw [if_neg hi]
      simp only [hi, false_and, iff_false] at hh
      simpa [optionalCoordLocus] using hh
  let T : Finset (Fin B.length) := Finset.univ.filter fun i => x ∈ B.get i
  let e : Fin B.length → ℕ := fun i => divExpAlong n N
    (restrictOn n N (vanishingIdeal (n := n) H)) (B.get i) x
  let c : Fin n → ℕ := coordinateExponent T σ e
  have hc : ∀ i ∈ S, c i = 0 := by
    intro i hi
    apply coordinateExponent_eq_zero_of_avoided T σ e i
    intro j hj hji
    have hlt := hσk j (Finset.mem_filter.mp hj).2
    have hge := (Finset.mem_filter.mp hi).2
    rw [hji] at hlt
    omega
  have htS : t ∉ S := by simp [S]; omega
  have hm0 : m ⟨0, by simp⟩ = some t := by
    change (if x ∈ (Haux :: F).get ⟨0, by simp⟩ then some (p ⟨0, by simp⟩) else none) = some t
    have hxHead : x ∈ (Haux :: F).get ⟨0, by simp⟩ := hxHaux
    rw [if_pos hxHead, hp0]
  have hprod (y : X) : (∏ i ∈ T, flatCoord Φ (σ i) y ^ e i) =
      ∏ b : Fin n, (GiraudAlong.flatMap Φ y) b ^ c b := by
    simpa [c, flatCoord, GiraudAlong.flatMap] using indexed_product_eq_coordinate_monomial T σ e (GiraudAlong.flatMap Φ y)
  have hdzero : (∏ b : Fin n, (GiraudAlong.flatMap Φ x) b ^ c b) = 0 := by
    rw [← hprod]
    exact hd
  have htrace : ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y *
      ((GiraudAlong.flatMap Φ y) t * ∏ b : Fin n, (GiraudAlong.flatMap Φ y) b ^ c b) := by
    filter_upwards [heq] with y hy hyN
    rw [← hprod]
    have hh := hy hyN
    change f y = a y * ((∏ i ∈ T, flatCoord Φ (σ i) y ^ e i) * flatCoord Φ t y) at hh
    rw [hh]
    simp only [flatCoord, GiraudAlong.flatMap]
    ring
  have hfx : f x = 0 := by
    have hh := heq.self_of_nhds hxN
    rw [hd] at hh
    simpa using hh
  have hxH : x ∈ H := by
    have hzero : x ∈ (vanishingIdeal (n := n) H).zeroLocus := by
      intro g hg
      obtain ⟨_, b, hb, hbg⟩ := isInSpanAt_eq_iff.mp ((hF g).mp hg)
      simpa [hfx] using hbg.self_of_nhds
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hL.1 H hHL)] at hzero
    exact hzero
  obtain ⟨s, Ψ, hs, hst, hcs, hΨsrc, hΨ0, hΨN, hΨE, hΨH⟩ :=
    exists_gamma_chart_of_trace hn hL hHL hxH Φ hsrc h0 S m hm hN' hE' t htS c hc hf ha hax hF hdzero htrace
  exact ⟨S, m, s, t, c, Ψ, hm, hm0, hs, htS, hst, hcs, hΨsrc, hΨ0, hΨN, hΨE, hΨH⟩

end
end Hironaka.HironakaG4PreparedGammaChart

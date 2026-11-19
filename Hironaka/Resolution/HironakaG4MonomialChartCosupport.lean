import Hironaka.Resolution.HironakaG4CommonMonomialChart
import Hironaka.Resolution.HironakaSharpActualRelativeProductOrder
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.MonomialPartAlong

set_option autoImplicit false

/-! Exact real marked cosupport from a genuine shared monomial coordinate chart.
Blueprint: `hironaka-g4-monomial-chart-cosupport.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4MonomialChartCosupport

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates BlowupSNCTransform MonomialCase MonomialPart
  MonomialPartAlong DivisorExponentAlong GermIdealOrder IdealWeightPowers OrderTaylor
  RelativePrincipalizationSpan MonomialBlowupAlongChart InvertibleIdealQuotient
  HironakaSharpActualRelativeProductOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual relative order of a finite coordinate monomial is its true total
weight. The exact adapted retraction retains arbitrary repeated free factors. -/
theorem vanishesToOrderOn_coordinate_monomial_iff {N : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hx : x ∈ N) {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (σ : ι → Fin n) (a : ι → ℕ) (hσk : ∀ i ∈ T, (σ i).val < k)
    (hzero : ∀ i ∈ T, flatCoord Φ (σ i) x = 0) (q : ℕ) :
    VanishesToOrderOn n N x q (fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i) ↔
      q ≤ ∑ i ∈ T, a i := by
  let p : X → ℂ := fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i
  have hxD := mem_flatDomain_self Φ
  have hpow := prod_flatCoord_pow_order Φ σ a hxD T hzero
  have hr : IsLocalRetraction n N (flatRetract Φ k) x :=
    isLocalRetraction_flatRetract hsrc hNflat hxD hx
  have hpr : p ∘ flatRetract Φ k =ᶠ[𝓝 x] p := by
    have hev := (eventually_all_finset T).mpr fun i hi =>
      eventually_flatMap_flatRetract hsrc hNflat hxD hx (hσk i hi)
    filter_upwards [hev] with y hy
    exact Finset.prod_congr rfl fun i hi => congrArg (· ^ a i) (hy i hi).2
  constructor
  · intro hq
    by_contra hlt
    have hpq := mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp hq) hpr
    exact hpow.2 (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg)
      (by omega : (∑ i ∈ T, a i) + 1 ≤ q) x p hpq)
  · intro hq
    refine ⟨p, ?_, Eventually.of_forall fun _ _ => rfl⟩
    exact idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) hq x p hpow.1

/-- Both whole relative ideal directions identify the genuine marked cosupport
with the actual sum of incident coordinate exponents, for every marking. -/
theorem cosupport_coordinate_monomial_iff {N : Set X} {I : GermIdeal n X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hx : x ∈ N) {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (σ : ι → Fin n) (a : ι → ℕ) (hσk : ∀ i ∈ T, (σ i).val < k)
    (hzero : ∀ i ∈ T, flatCoord Φ (σ i) x = 0)
    (hI : ∀ g, I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N
      (· = fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i) x g) (q : ℕ) :
    x ∈ cosupport n N I q ↔ q ≤ ∑ i ∈ T, a i := by
  have hp : HolomorphicAt n (fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i) x :=
    holomorphicAt_finset_prod T fun i _ =>
      CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) (mem_flatDomain_self Φ)) (a i)
  exact (cosupport_relative_principal_iff_vanishes hx hp hI q).trans
    (vanishesToOrderOn_coordinate_monomial_iff Φ k hsrc hNflat hx T σ a hσk hzero q)

/-- Genuine holomorphic W coordinates and the actual whole ideal dictionary
compute actual cosupport. The recentering is purely geometric and row-independent. -/
theorem cosupport_raw_coordinate_monomial_iff {N U : Set X} {I : GermIdeal n X} {z : X}
    (W : X → ComplexModel n) (hU : IsOpen U) (hzU : z ∈ U)
    (hWs : ∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W y)
    (hinj : Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
      (chartAt (ComplexModel n) z z)))
    (k : ℕ) (hNflat : ∀ y ∈ U, y ∈ N ↔ W y ∈ complexCoordinatePlane n k) (hz : z ∈ N)
    {ι : Type*} [DecidableEq ι] (T : Finset ι) (σ : ι → Fin n) (a : ι → ℕ)
    (hσk : ∀ i ∈ T, (σ i).val < k) (hzero : ∀ i ∈ T, W z (σ i) = 0)
    (hI : ∀ g, I.mem z g ↔ HolomorphicAt n g z ∧ IsInSpanOnAt (n := n) N
      (· = fun y => ∏ i ∈ T, W y (σ i) ^ a i) z g) (q : ℕ) :
    z ∈ cosupport n N I q ↔ q ≤ ∑ i ∈ T, a i := by
  obtain ⟨Φ, hsrc, h0, hΦ⟩ := exists_recentred_coords hU hWs hzU hinj
  have hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Φ.source →
      y ∈ U ∧ ∀ t, flatCoord Φ t y = W y t - W z t := by
    intro y hy hyΦ
    obtain ⟨hyU, hΦy⟩ := hΦ hy hyΦ
    refine ⟨hyU, fun t => ?_⟩
    change Φ.toFun ((complexChartAt (n := n) z).val y) t = _
    rw [hΦy, PiLp.sub_apply]
  have hzplane := (hNflat z hzU).mp hz
  have hNΦ : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n k) := by
    intro y hy hyΦ
    obtain ⟨hyU, heq⟩ := hflat hy hyΦ
    rw [hNflat y hyU]
    constructor
    · intro hp t ht
      change flatCoord Φ t y = 0
      rw [heq t, hp t ht, hzplane t ht, sub_zero]
    · intro hp t ht
      have hh : flatCoord Φ t y = 0 := hp t ht
      rw [heq t, hzplane t ht, sub_zero] at hh
      exact hh
  have hproduct : (fun y => ∏ i ∈ T, W y (σ i) ^ a i) =ᶠ[𝓝 z]
      (fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i) := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    apply Finset.prod_congr rfl
    intro i hi
    rw [(hflat hy.1 hy.2).2 (σ i), hzero i hi, sub_zero]
  have hIΦ (g : X → ℂ) : I.mem z g ↔ HolomorphicAt n g z ∧ IsInSpanOnAt (n := n) N
      (· = fun y => ∏ i ∈ T, flatCoord Φ (σ i) y ^ a i) z g :=
    (hI g).trans (and_congr_right fun _ => isInSpanOnAt_eq_congr hproduct g)
  have hzeroΦ : ∀ i ∈ T, flatCoord Φ (σ i) z = 0 := by
    intro i _hi
    change Φ.toFun ((complexChartAt (n := n) z).val z) (σ i) = 0
    rw [h0]
    rfl
  exact cosupport_coordinate_monomial_iff Φ k hsrc hNΦ hz T σ a hσk hzeroΦ hIΦ q

end

end Hironaka.HironakaG4MonomialChartCosupport

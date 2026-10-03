/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalDerivativeMonomial
import Hironaka.MarkedIdeal.HomogenizedGlueingAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Blowup.NestedFlattening
import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.MarkedIdeal.NormalTaylorOrder
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPushforward
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Normal derivatives along a submanifold: flat charts of a pair `S ⊆ N`

For `N = M` these are `NormalDerivativeChart` / `NormalDerivativeMonomial`.

Along `N` the coefficients of the source are the derivatives in the directions normal to `S` and tangent to `N`: in a
chart in which `S = ℂ^{k_S} × 0` and `N = ℂ^{k_N} × 0`, the directions `e_l`, `k_S ≤ l < k_N`.

* **The plane retraction** `P = planeProj k_N` (kill the coordinates `≥ k_N`): `∂^L (F ∘ P) = (∂^L F) ∘ P` for directions
  `< k_N` (`iterDeriv_comp_planeProj`) and `∂^L (F ∘ P) = 0` as soon as `L` has a direction `≥ k_N`
  (`iterDeriv_comp_planeProj_eq_zero`); hence functions agreeing on the plane have the same derivatives along the plane
  (`iterDeriv_eventuallyEq_on_plane`).
* **Order along `N` from the derivatives** (`FlatChart.vanishesToOrderOn_of_nd`): in a flat chart of `S` in which `N` is
  `ℂ^{k_N} × 0`, if each derivative `∂^L g` (`L` in `[k_S, k_N)`, `|L| < μ`) vanishes to order `μ - |L|` along `S`, then `g`
  vanishes to order `μ` along `N` (apply `NormalTaylorOrder` to `g ∘ ψ⁻¹ ∘ P ∘ ψ`, which agrees with `g` on `N`).
* **Derivatives tangent to `N` of germs of `𝔞`** lie in the derivative ideals along `N`
  (`FlatChart.nd_mem_iterDerivIdealAlong`).
* **Nested charts of a pair** (`FlatChart.exists_nested_pair`): the product-form refinement of `FlatChart.exists_nested`
  (only the coordinates `< k_S` change) keeps `N = ℂ^{k_N} × 0` for `k_N ≥ k_S`.
* **The strict transforms of `S ⊆ N` in one monomial chart** (`exists_local_geoStrictTransform_pair`).
* **The monomial identity along `N'`** (`nd_monomial_identity_along`): if `g ∘ π = W_j^d h'` only on `N'`, then
  `W_j^d ∂^L h' = W_j^{|L|} (∂^L g) ∘ π` on `N'`, for the directions of `L` in `[k_C, k_N) \ {j}`.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NormalDerivativeAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolomorphicTaylorTail NormalTaylorOrder NormalDerivativeChart NormalDerivativeMonomial BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity GermIdealOrder IdealWeightPowers DerivativeIdeal DerivativeIdealAlong GiraudAlong DerivativeIdealAlongCoherent

noncomputable section

/-! ### The plane retraction -/

section Model

variable {n : ℕ}

theorem plane_mono {k k' : ℕ} (hkk' : k ≤ k') :
    complexCoordinatePlane n k ⊆ complexCoordinatePlane n k' := fun _ hw i hi => hw i (le_trans hkk' hi)

/-- `P (v + t eₗ) = P v + t eₗ` for a tangential direction `l < k`. -/
theorem planeProj_add_smul_bv {k : ℕ} {l : Fin n} (hl : l.1 < k) (v : ComplexModel n) (t : ℂ) :
    planeProj k (v + t • bv l) = planeProj k v + t • bv l := by
  rw [map_add, map_smul, planeProj_of_mem (single_mem_complexCoordinatePlane hl)]

/-- `P (v + t eₗ) = P v` for a normal direction `l ≥ k`. -/
theorem planeProj_add_smul_bv_of_le {k : ℕ} {l : Fin n} (hl : k ≤ l.1) (v : ComplexModel n) (t : ℂ) :
    planeProj k (v + t • bv l) = planeProj k v := by
  rw [map_add, map_smul, planeProj_bv hl, smul_zero, add_zero]

/-- **Derivatives tangent to the plane commute with the plane retraction**: `∂^L (F ∘ P) = (∂^L F) ∘ P` for directions
`< k_N`. -/
theorem iterDeriv_comp_planeProj {kN : ℕ} {F : ComplexModel n → ℂ} {V : Set (ComplexModel n)} (hV : IsOpen V)
    (hF : DifferentiableOn ℂ F V) (L : List (Fin n)) (hL : ∀ l ∈ L, l.1 < kN) {v : ComplexModel n}
    (hv : planeProj kN v ∈ V) :
    iterDeriv (L.map bv) (fun u => F (planeProj kN u)) v = iterDeriv (L.map bv) F (planeProj kN v) :=
  iterDeriv_comp_translate (Ψ := planeProj kN) (U := planeProj kN ⁻¹' V) (hV.preimage (planeProj kN).continuous) hV
    (planeProj kN).differentiable.differentiableOn (fun _ hu => hu) hF L
    (fun l hl v t => planeProj_add_smul_bv (hL l hl) v t) v hv

/-- **A normal derivative of a function of the plane coordinates vanishes**: `∂^L (F ∘ P) = 0` as soon as `L` has a
direction `≥ k_N`. -/
theorem iterDeriv_comp_planeProj_eq_zero {kN : ℕ} {F : ComplexModel n → ℂ} {V : Set (ComplexModel n)}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) :
    ∀ L : List (Fin n), (∃ l ∈ L, kN ≤ l.1) → ∀ v, planeProj kN v ∈ V →
      iterDeriv (L.map bv) (fun u => F (planeProj kN u)) v = 0
  | [], h, _, _ => by simp at h
  | l :: L, h, v, hv => by
    have hUo : IsOpen (planeProj kN ⁻¹' V) := hV.preimage (planeProj kN).continuous
    simp only [List.map_cons, iterDeriv_cons, dirDeriv]
    by_cases hL : ∃ l' ∈ L, kN ≤ l'.1
    · have heq : iterDeriv (L.map bv) (fun u => F (planeProj kN u)) =ᶠ[𝓝 v] fun _ => 0 :=
        eventually_of_mem (hUo.mem_nhds hv) fun w hw => iterDeriv_comp_planeProj_eq_zero hV hF L hL w hw
      rw [heq.fderiv_eq]
      simp
    · push Not at hL
      have hl : kN ≤ l.1 := by
        obtain ⟨l', hl', hl'k⟩ := h
        rcases List.mem_cons.mp hl' with rfl | hmem
        · exact hl'k
        · exact absurd hl'k (not_le.mpr (hL l' hmem))
      have heq : iterDeriv (L.map bv) (fun u => F (planeProj kN u)) =ᶠ[𝓝 v]
          fun w => iterDeriv (L.map bv) F (planeProj kN w) :=
        eventually_of_mem (hUo.mem_nhds hv) fun w hw => iterDeriv_comp_planeProj hV hF L hL hw
      have hdL := differentiableOn_iterDeriv hF hV (L.map bv)
      have hd1 : DifferentiableAt ℂ (fun w => iterDeriv (L.map bv) F (planeProj kN w)) v :=
        ((hdL _ hv).differentiableAt (hV.mem_nhds hv)).comp v (planeProj kN).differentiableAt
      rw [heq.fderiv_eq, fderiv_apply_eq_of_line (g := fun _ => iterDeriv (L.map bv) F (planeProj kN v))
        (a := 0) (b := 0) hd1 (differentiableAt_const _)
        (fun t => by simp only [planeProj_add_smul_bv_of_le hl])]
      simp

/-- **Functions agreeing on the plane have the same derivatives along the plane** (directions `< k_N`), at the points
of the plane near `0`. -/
theorem iterDeriv_eventuallyEq_on_plane {kN : ℕ} {F G : ComplexModel n → ℂ} {V : Set (ComplexModel n)}
    (hV : IsOpen V) (h0 : (0 : ComplexModel n) ∈ V) (hF : DifferentiableOn ℂ F V) (hG : DifferentiableOn ℂ G V)
    (hFG : ∀ᶠ u in 𝓝 (0 : ComplexModel n), u ∈ complexCoordinatePlane n kN → F u = G u)
    (L : List (Fin n)) (hL : ∀ l ∈ L, l.1 < kN) :
    ∀ᶠ u in 𝓝 (0 : ComplexModel n), u ∈ complexCoordinatePlane n kN →
      iterDeriv (L.map bv) F u = iterDeriv (L.map bv) G u := by
  have hP : Tendsto (planeProj (n := n) kN) (𝓝 0) (𝓝 0) := by
    simpa using (planeProj (n := n) kN).continuous.tendsto 0
  have hcomp : (fun u => F (planeProj kN u)) =ᶠ[𝓝 (0 : ComplexModel n)] fun u => G (planeProj kN u) := by
    filter_upwards [hP.eventually hFG] with u hu using hu (planeProj_mem kN u)
  have hI := iterDeriv_congr_of_eventuallyEq hcomp (L.map bv)
  filter_upwards [hI, hP.eventually (hV.mem_nhds h0)] with u hu hPu huP
  have e1 := iterDeriv_comp_planeProj hV hF L hL hPu
  have e2 := iterDeriv_comp_planeProj hV hG L hL hPu
  rw [planeProj_of_mem huP] at e1 e2
  rw [← e1, ← e2]
  exact hu

end Model

/-! ### Flat charts of a pair `S ⊆ N` -/

section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The order along `N` from the derivatives normal to `S` and tangent to `N`**: let `c` be a flat chart for `S`
(plane `ℂ^{k_S} × 0`) at `p` in which the points of `N` near `p` lie in `ℂ^{k_N} × 0`, `k_S ≤ k_N`.  If for every list `L`
of directions in `[k_S, k_N)` with `|L| < μ` the derivative `∂^L g` vanishes to order `μ - |L|` along `S` at `p`, then
`g` vanishes to order `μ` along `N` at `p`. -/
theorem FlatChart.vanishesToOrderOn_of_nd {S N : Set M} {p : M} {kS kN : ℕ} (c : FlatChart n S p kS)
    (hk : kS ≤ kN) (hN : ∀ᶠ y in 𝓝 p, y ∈ N → c.ψ y ∈ complexCoordinatePlane n kN)
    {g : M → ℂ} (hg : HolomorphicAt n g p) {μ : ℕ}
    (hL : ∀ L : List (Fin n), NormalIdx kS L → (∀ l ∈ L, l.1 < kN) → L.length < μ →
      VanishesToOrderOn n S p (μ - L.length) (c.nd L g)) :
    VanishesToOrderOn n N p μ g := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (c.eventually_differentiableAt_comp_inv hg)
  have hFU : DifferentiableOn ℂ (fun u => g (c.inv u)) (ball 0 r) := fun z hz => (hball z hz).differentiableWithinAt
  have hP : Tendsto (fun y => planeProj kN (c.ψ y)) (𝓝 p) (𝓝 0) := by
    have h := ((planeProj (n := n) kN).continuous.tendsto 0).comp c.tendsto_ψ
    rw [map_zero] at h
    exact h
  have hPV : ∀ᶠ y in 𝓝 p, planeProj kN (c.ψ y) ∈ ball (0 : ComplexModel n) r :=
    hP.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
  -- `h = g ∘ ψ⁻¹ ∘ P ∘ ψ`
  have hhol : HolomorphicAt n (fun y => g (c.inv (planeProj kN (c.ψ y)))) p := by
    filter_upwards [c.eventually_mdifferentiableAt_ψ, hPV] with y hy hyb
    have hFd : DifferentiableAt ℂ (fun u => g (c.inv (planeProj kN u))) (c.ψ y) :=
      ((hFU _ hyb).differentiableAt (isOpen_ball.mem_nhds hyb)).comp _ (planeProj kN).differentiableAt
    exact hFd.mdifferentiableAt.comp y hy
  have hmem : (idealPow (pointIdeal n p) μ).mem p (fun y => g (c.inv (planeProj kN (c.ψ y)))) := by
    refine c.mem_idealPow_of_vanishesToOrderOn hhol fun L hLn hLlen => ?_
    have hloc : (fun u => g (c.inv (planeProj kN (c.ψ (c.inv u))))) =ᶠ[𝓝 (0 : ComplexModel n)]
        fun u => g (c.inv (planeProj kN u)) := by
      filter_upwards [c.eventually_ψ_inv] with u hu
      rw [hu]
    have hI := iterDeriv_congr_of_eventuallyEq hloc (L.map bv)
    have hnd : c.nd L (fun y => g (c.inv (planeProj kN (c.ψ y)))) =ᶠ[𝓝 p]
        fun y => iterDeriv (L.map bv) (fun u => g (c.inv (planeProj kN u))) (c.ψ y) := by
      filter_upwards [c.tendsto_ψ.eventually hI] with y hy
      exact hy
    by_cases hlt : ∀ l ∈ L, l.1 < kN
    · obtain ⟨H, hH, hgH⟩ := hL L hLn hlt hLlen
      refine ⟨H, hH, ?_⟩
      filter_upwards [hnd, hgH, hPV, c.eventually_flat] with y h1 h2 h3 h4 hyS
      rw [h1, iterDeriv_comp_planeProj (F := fun u => g (c.inv u)) isOpen_ball hFU L hlt h3]
      have hψS : c.ψ y ∈ complexCoordinatePlane n kN := plane_mono hk (h4.mp hyS)
      rw [planeProj_of_mem hψS]
      exact h2 hyS
    · push Not at hlt
      obtain ⟨l, hl, hlk⟩ := hlt
      refine ⟨fun _ => 0, GiraudAlong.zero_mem_idealPow _ p _, ?_⟩
      filter_upwards [hnd, hPV] with y h1 h3 _
      rw [h1]
      exact iterDeriv_comp_planeProj_eq_zero (F := fun u => g (c.inv u)) isOpen_ball hFU L ⟨l, hl, hlk⟩ _ h3
  refine ⟨_, hmem, ?_⟩
  filter_upwards [hN, c.eventually_inv_ψ] with y hyN hinv hy
  simp only [planeProj_of_mem (hyN hy), hinv]

/-- **Iterated tangential coordinate derivatives along lists lie in the iterated derivative ideals along `N`**: for a
flat chart `ψ = Θ ∘ e` of `N` at `x` (plane `ℂᵏ × 0`), directions `l < k` and `F` with `F ∘ ψ ∈ 𝔞_x`,
`(∂^L F) ∘ ψ ∈ 𝓓_N^{|L|}(𝔞)_x` (the list form of `HomogenizedGlueingAlong.iterDeriv_comp_flatMap_mem`). -/
theorem iterDeriv_comp_flatMap_mem_list {x : M} {Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target) {N : Set M} {k : ℕ}
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Θ.source →
      (y ∈ N ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    {𝔞 : GermIdeal n M} (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {F : ComplexModel n → ℂ}
    (hFW : 𝔞.mem x (F ∘ flatMap Θ)) :
    ∀ L : List (Fin n), (∀ l ∈ L, l.1 < k) →
      (iterDerivIdealAlong N 𝔞 L.length).mem x (iterDeriv (L.map bv) F ∘ flatMap Θ)
  | [], _ => hFW
  | l :: L, hL => by
    have hprev := iterDeriv_comp_flatMap_mem_list hΘsrc hflat h𝔞 hFW L
      (fun l' hl' => hL l' (List.mem_cons_of_mem l hl'))
    have hGW : HolomorphicAt n (iterDeriv (L.map bv) F ∘ flatMap Θ) x :=
      holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 L.length x _ hprev
    have hx0 : x ∈ flatDomain Θ := mem_flatDomain_self Θ
    have hξ : IsTangentField N (complexChartAt (n := n) x) (flatField Θ (bv l)) x :=
      isTangentField_flatField hΘsrc hflat (single_mem_complexCoordinatePlane (hL l List.mem_cons_self)) hx0
    have hgen : IsInSpanAt (n := n) (DerivGenAlong N (iterDerivIdealAlong N 𝔞 L.length) x) x
        (fieldDeriv (complexChartAt (n := n) x) (flatField Θ (bv l)) (iterDeriv (L.map bv) F ∘ flatMap Θ)) :=
      InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inr ⟨_, _, _, hξ, hprev, rfl⟩))
        (holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt hGW)
    show IsInSpanAt (n := n) (DerivGenAlong N (iterDerivIdealAlong N 𝔞 L.length) x) x _
    refine DerivativeIdeal.isInSpanAt_congr hgen ?_
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds hx0, hGW.eventually_nhds] with p hp hGp
    rw [HomogenizedGlueingAlong.fieldDeriv_flatField_comp hΘsrc hp hGp (bv l)]
    rfl

/-- **Derivatives tangent to `N` of germs of `𝔞` lie in the derivative ideals along `N`**: in a flat chart `c` (for any
`S`) in which `N` is the plane `ℂ^{k_N} × 0`, for a coherent `𝔞`, `g ∈ 𝔞_p` and directions `l < k_N`,
`∂^L g ∈ 𝓓_N^{|L|}(𝔞)_p`. -/
theorem FlatChart.nd_mem_iterDerivIdealAlong {S N : Set M} {p : M} {kS kN : ℕ} (c : FlatChart n S p kS)
    (hN : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c.Φ.source →
      (y ∈ N ↔ c.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN))
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {g : M → ℂ} (hg : 𝔞.mem p g) (L : List (Fin n))
    (hL : ∀ l ∈ L, l.1 < kN) : (iterDerivIdealAlong N 𝔞 L.length).mem p (c.nd L g) := by
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hFW : 𝔞.mem p ((fun u => g (c.inv u)) ∘ flatMap c.Φ) :=
    mem_congr_of_isCoherent h𝔞 hg (by
      filter_upwards [c.eventually_inv_ψ] with y hy
      show g y = g (c.inv (c.ψ y))
      rw [hy])
  exact iterDeriv_comp_flatMap_mem_list c.src hN hhol hFW L hL

/-- `T(u) = Φm(P u) + (u - P u)` does not change the coordinates `≥ k_S`. -/
theorem prodTo_apply_of_le {kS : ℕ} {Φm : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)}
    (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kS ↔ Φm.toFun u ∈ complexCoordinatePlane n kS))
    {u : ComplexModel n} (hu : planeProj kS u ∈ Φm.source) {i : Fin n} (hi : kS ≤ i.1) :
    prodTo Φm kS u i = u i := by
  have h1 : Φm.toFun (planeProj kS u) ∈ complexCoordinatePlane n kS := (hplane _ hu).mp (planeProj_mem kS u)
  simp only [prodTo, PiLp.add_apply, PiLp.sub_apply, h1 i hi, planeProj_apply, if_neg (not_lt.mpr hi)]
  ring

/-- Hence it preserves every plane `ℂ^{k_N} × 0` with `k_N ≥ k_S`. -/
theorem prodTo_mem_plane_iff {kS kN : ℕ} (hk : kS ≤ kN) {Φm : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)}
    (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kS ↔ Φm.toFun u ∈ complexCoordinatePlane n kS))
    {u : ComplexModel n} (hu : planeProj kS u ∈ Φm.source) :
    prodTo Φm kS u ∈ complexCoordinatePlane n kN ↔ u ∈ complexCoordinatePlane n kN := by
  constructor
  · intro h i hi
    rw [← prodTo_apply_of_le hplane hu (le_trans hk hi)]
    exact h i hi
  · intro h i hi
    rw [prodTo_apply_of_le hplane hu (le_trans hk hi)]
    exact h i hi

/-- **Nested flat charts of a pair in product form**: a flat chart `c` for `S` (plane `ℂ^{k_S} × 0`) at `p` in which
`N` is the plane `ℂ^{k_N} × 0` (`k_S ≤ k_N`), and a submanifold `C ⊆ S` regular of dimension `k_C ≤ k_S` at `p`, give a
flat chart `c'` for `S` at `p` in which also `C` is `ℂ^{k_C} × 0` and still `N` is `ℂ^{k_N} × 0`, with the same normal
derivatives (only the coordinates `< k_S` change). -/
theorem FlatChart.exists_nested_pair {S C N : Set M} {p : M} {kS kC kN : ℕ} (c : FlatChart n S p kS)
    (hkC : kC ≤ kS) (hkS : kS ≤ n) (hk : kS ≤ kN) (hC : RegularAtDim (n := n) C p kC) (hCS : C ⊆ S)
    (hN : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c.Φ.source →
      (y ∈ N ↔ c.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN)) :
    ∃ c' : FlatChart n S p kS,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c'.Φ.source →
        (y ∈ C ↔ c'.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kC)) ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c'.Φ.source →
        (y ∈ N ↔ c'.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN)) ∧
      ∀ L : List (Fin n), NormalIdx kS L → ∀ f : M → ℂ, HolomorphicAt n f p →
        c'.nd L f =ᶠ[𝓝 p] c.nd L f := by
  set e := chartAt (ComplexModel n) p with he
  obtain ⟨-, -, Θ, -, hΘ0, hΘC0⟩ := hC
  have hΘC : ∀ {y : M}, y ∈ e.source → e y ∈ Θ.source →
      (y ∈ C ↔ Θ.toFun (e y) ∈ complexCoordinatePlane n kC) := fun hy h => hΘC0 hy h
  have h0t := c.zero_mem_target
  have hinv0 : c.Φ.invFun 0 = e p := by rw [← c.zero]; exact c.Φ.left_inv _ c.Φ.center_mem_source
  set Θ' := RegularAtDimTransport.LocalHolomorphicEquivAt.comp (RegularPatchPushforward.symmAt c.Φ h0t) Θ hinv0
    with hΘ'
  have hΘ'0 : Θ'.toFun 0 = 0 := by
    show Θ.toFun (c.Φ.invFun 0) = 0
    rw [hinv0]; exact hΘ0
  set C' : Set (ComplexModel n) := {u | c.inv u ∈ C} with hC'
  have hpt : ∀ u ∈ c.Φ.target, e.symm (c.Φ.invFun u) ∈ e.source ∧ e (e.symm (c.Φ.invFun u)) = c.Φ.invFun u :=
    fun u hu => ⟨e.map_target (c.src (c.Φ.mapsTo_invFun hu)), e.right_inv (c.src (c.Φ.mapsTo_invFun hu))⟩
  have hΘ'C : ∀ u ∈ Θ'.source, (u ∈ C' ↔ Θ'.toFun u ∈ complexCoordinatePlane n kC) := by
    intro u hu
    obtain ⟨hy, h2⟩ := hpt u hu.1
    have := hΘC hy (by rw [h2]; exact hu.2)
    rw [h2] at this
    exact this
  have hCN : ∀ u ∈ Θ'.source, u ∈ C' → u ∈ complexCoordinatePlane n kS := by
    intro u hu huC
    obtain ⟨hy, h2⟩ := hpt u hu.1
    have := (c.flat hy (by rw [h2]; exact c.Φ.mapsTo_invFun hu.1)).mp (hCS huC)
    rwa [h2, c.Φ.right_inv _ hu.1] at this
  obtain ⟨Φm, -, hΦm0, hΦm⟩ := NestedFlattening.exists_nested_flattening_model hkC hkS Θ' hΘ'0 hΘ'C hCN
  have hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kS ↔
      Φm.toFun u ∈ complexCoordinatePlane n kS) := fun u hu => (hΦm u hu).2
  set T := prodEquiv Φm hplane with hT
  have hT0 : T.toFun 0 = 0 := by
    show prodTo Φm kS 0 = 0
    simp [prodTo, hΦm0]
  have hTplane : ∀ u, planeProj kS u ∈ Φm.source →
      (u ∈ complexCoordinatePlane n kS ↔ T.toFun u ∈ complexCoordinatePlane n kS) := by
    intro u hu
    rw [mem_plane_iff_sub_planeProj, mem_plane_iff_sub_planeProj]
    show _ ↔ prodTo Φm kS u - planeProj kS (prodTo Φm kS u) = 0
    rw [prodTo_sub_planeProj hplane hu]
  set Φ'' := RegularAtDimTransport.LocalHolomorphicEquivAt.comp c.Φ T c.zero with hΦ''
  refine ⟨⟨Φ'', fun u hu => c.src hu.1, by show T.toFun (c.Φ.toFun (e p)) = 0; rw [c.zero, hT0], ?_⟩,
    ?_, ?_, ?_⟩
  · intro y hy hyΦ
    rw [c.flat hy hyΦ.1]
    exact hTplane _ hyΦ.2
  · intro y hy hyΦ
    show y ∈ C ↔ prodTo Φm kS (c.Φ.toFun (e y)) ∈ complexCoordinatePlane n kC
    have hyinv : c.inv (c.Φ.toFun (e y)) = y := flatInverse_flat c.Φ ⟨hy, hyΦ.1⟩
    have hPΦ : planeProj kS (c.Φ.toFun (e y)) ∈ Φm.source := hyΦ.2
    by_cases hup : c.Φ.toFun (e y) ∈ complexCoordinatePlane n kS
    · have hPu := planeProj_of_mem hup
      rw [hPu] at hPΦ
      have hTu : prodTo Φm kS (c.Φ.toFun (e y)) = Φm.toFun (c.Φ.toFun (e y)) := by
        simp only [prodTo, hPu, sub_self, add_zero]
      rw [hTu, ← (hΦm _ hPΦ).1]
      show y ∈ C ↔ c.inv (c.Φ.toFun (e y)) ∈ C
      rw [hyinv]
    · have hyC : y ∉ C := fun h => hup ((c.flat hy hyΦ.1).mp (hCS h))
      have hTn : prodTo Φm kS (c.Φ.toFun (e y)) ∉ complexCoordinatePlane n kS :=
        fun h => hup ((hTplane _ hyΦ.2).mpr h)
      refine iff_of_false hyC fun h => hTn fun i hi => h i (le_trans hkC hi)
  · intro y hy hyΦ
    show y ∈ N ↔ prodTo Φm kS (c.Φ.toFun (e y)) ∈ complexCoordinatePlane n kN
    rw [hN hy hyΦ.1, prodTo_mem_plane_iff hk hplane hyΦ.2]
  · intro L hL f hf
    exact FlatChart.nd_eventuallyEq_of_prod c hplane _ rfl rfl hL hf

/-- **A flat chart from a holomorphic map with injective derivative**, with its domain recorded:
`NormalDerivativeChart`'s chart `c` with `c.ψ = W` on the whole domain, which lies in `O`. -/
theorem FlatChart.exists_of_map' {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] {S' : Set Z} {z : Z} {k : ℕ} {W : Z → ComplexModel n} {O : Set Z} (hO : IsOpen O)
    (hzO : z ∈ O) (hW : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W y) (hWz : W z = 0)
    (hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)))
    (hflat : ∀ y ∈ O, (y ∈ S' ↔ W y ∈ complexCoordinatePlane n k)) :
    ∃ c : FlatChart n S' z k, c.ψ =ᶠ[𝓝 z] W ∧
      ∀ {y : Z}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ c.Φ.source →
        y ∈ O ∧ c.Φ.toFun (chartAt (ComplexModel n) z y) = W y := by
  set e := chartAt (ComplexModel n) z with he
  set Nset : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
  have hzN : e z ∈ Nset := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ (fun ζ => W (e.symm ζ)) Nset := fun ζ hζ => by
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) (chart_mem_atlas (ComplexModel n) z) hζ.1
    exact (mdifferentiableAt_iff_differentiableAt.mp ((hW _ hζ.2).comp _ h1)).differentiableWithinAt
  obtain ⟨Θ, hΘN, hΘF, -⟩ := Hironaka.exists_localHolomorphicEquivAt hNo hzN hFd hinj
  have hdom : ∀ {y : Z}, y ∈ e.source → e y ∈ Θ.source → y ∈ O ∧ Θ.toFun (e y) = W y := by
    intro y hy hyΘ
    have hyO : y ∈ O := by
      have h := (hΘN hyΘ).2
      rwa [mem_preimage, e.left_inv hy] at h
    refine ⟨hyO, ?_⟩
    rw [hΘF]
    show W (e.symm (e y)) = W y
    rw [e.left_inv hy]
  refine ⟨⟨Θ, fun ζ hζ => (hΘN hζ).1, ?_, ?_⟩, ?_, fun hy hyΘ => hdom hy hyΘ⟩
  · rw [hΘF]
    show W (e.symm (e z)) = 0
    rw [e.left_inv (mem_chart_source _ z)]; exact hWz
  · intro y hy hyΘ
    obtain ⟨hyO, hΘy⟩ := hdom hy hyΘ
    rw [hΘy]; exact hflat y hyO
  · filter_upwards [e.open_source.mem_nhds (mem_chart_source _ z)] with y hy
    show Θ.toFun (e y) = W y
    rw [hΘF]
    show W (e.symm (e y)) = W y
    rw [e.left_inv hy]

end Chart

/-! ### The strict transforms of a pair in one monomial chart -/

section Strict

open BlowupStrictSubmanifold BlowupFibreDirection NestedFlattening Hironaka.RegularLocusDense

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The strict transform in a given monomial chart**: for the local inverse `W` on `O` of the monomial chart `j` of nested
coordinates `Φ` (`C = ℂ^{k_C} × 0`), every `N` that is a plane `ℂ^{k_N} × 0` in `Φ` has
`u ∈ N' ⟺ j < k_N ∧ W u ∈ ℂ^{k_N} × 0` on `O` (the proof of `BlowupStrictSubmanifold.exists_local_geoStrictTransform`,
for a chart fixed in advance). -/
theorem mem_geoStrictTransform_iff_of_monomial (hπ : IsBlowupAlong n C π) {y₀ : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {kC kN : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kC))
    {N : Set X}
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kN))
    {j : Fin n} (hj : kC ≤ j.1) {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWeq : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧
      monomial kC j (W z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z')))
    (hℓ : ∀ ℓ : LiftedOpen.{u} (monomialDomain Φ kC j) → Y,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
        π ∘ ℓ = monomialChart Φ kC j → ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ kC j,
          ℓ (LiftedOpen.mk _ (W z') hw) = z') :
    ∀ u ∈ O, (u ∈ geoStrictTransform π C N ↔ (j.1 < kN ∧ W u ∈ complexCoordinatePlane n kN)) := by
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hNu : ∀ u ∈ O, (π u ∈ N ↔ monomial kC j (W u) ∈ complexCoordinatePlane n kN) :=
    fun u hu => by rw [hflatN (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2]
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflatC hj
  intro u hu
  by_cases hjN : j.1 < kN
  · simp only [hjN, true_and]
    constructor
    · intro hcl
      by_contra hWu
      have hWc : ContinuousAt W u := (hWs u hu).continuousAt
      have hopen : IsOpen (complexCoordinatePlane n kN)ᶜ := by
        have : IsClosed (complexCoordinatePlane n kN) := by
          have : complexCoordinatePlane n kN = ⋂ i : Fin n, ⋂ (_ : kN ≤ i.1), {w | w i = 0} := by
            ext w; simp [complexCoordinatePlane]
          rw [this]
          exact isClosed_iInter fun i => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)) continuous_const
        exact this.isOpen_compl
      have hev : ∀ᶠ u' in 𝓝 u, u' ∈ O ∧ W u' ∉ complexCoordinatePlane n kN :=
        (hO.eventually_mem hu).and (hWc.eventually_mem (hopen.mem_nhds hWu))
      obtain ⟨u', hu'mem, hu'A⟩ := mem_closure_iff_nhds.mp hcl _ hev
      obtain ⟨hu'O, hu'W⟩ := hu'mem
      obtain ⟨hNu', hCu'⟩ := hu'A
      have h1 := (hNu u' hu'O).mp hNu'
      rcases (monomial_mem_plane_iff_of_lt hj hjN).mp h1 with h0 | hP
      · exact hCu' ((hCu u' hu'O).mpr h0)
      · exact hu'W hP
    · intro hWu
      by_cases hWj : W u j = 0
      · rw [geoStrictTransform, mem_closure_iff_nhds]
        intro U hU
        have hp : W u ∈ monomialDomain Φ kC j := hWmem u hu
        set p : LiftedOpen.{u} (monomialDomain Φ kC j) := LiftedOpen.mk _ (W u) hp with hpdef
        have hℓp : ℓ p = u := hℓ ℓ hℓs hℓπ u hu hp
        have hpre : ℓ ⁻¹' U ∈ 𝓝 p := hℓs.continuous.continuousAt.preimage_mem_nhds (by
          rw [hℓp]; exact hU)
        have himg : LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∈ 𝓝 (W u) := by
          have := (LiftedOpen.isOpenEmbedding_toModel (S := monomialDomain Φ kC j)).map_nhds_eq p
          rw [← LiftedOpen.toModel_mk (S := monomialDomain Φ kC j) (W u) hp, ← this]
          exact image_mem_map hpre
        set e_j : ComplexModel n := EuclideanSpace.single j 1 with he_j
        have hcurve : Tendsto (fun t : ℂ => W u + t • e_j) (𝓝 0) (𝓝 (W u)) := by
          have : Continuous (fun t : ℂ => W u + t • e_j) := continuous_const.add
            (continuous_id.smul continuous_const)
          simpa using this.tendsto 0
        have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∧
            t ≠ 0 :=
          (show ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) from
            mem_nhdsWithin_of_mem_nhds (hcurve himg)).and self_mem_nhdsWithin
        obtain ⟨t, ⟨q, hqU, hqt⟩, ht0⟩ := hev.exists
        refine ⟨ℓ q, hqU, ?_⟩
        have hπq : π (ℓ q) = monomialChart Φ kC j q := congrFun hℓπ q
        have hqmem : LiftedOpen.toModel _ q ∈ monomialDomain Φ kC j := LiftedOpen.toModel_mem _ q
        have hmon : monomial kC j (LiftedOpen.toModel _ q) ∈ Φ.target := hqmem
        have hsrc : π (ℓ q) ∈ flatDomain Φ := by
          rw [hπq]; exact monomialChart_mem_flatDomain hΦsrc q
        have hcoord : Φ.toFun (chartAt (ComplexModel n) y₀ (π (ℓ q))) =
            monomial kC j (LiftedOpen.toModel _ q) := by
          rw [hπq, monomialChart, (chartAt (ComplexModel n) y₀).right_inv (hΦsrc
            (Φ.mapsTo_invFun hmon)), Φ.right_inv _ hmon]
        have hwq : LiftedOpen.toModel _ q = W u + t • e_j := hqt
        have hwqj : LiftedOpen.toModel _ q j = t := by
          rw [hwq]; simp [he_j, hWj]
        have hwqP : LiftedOpen.toModel _ q ∈ complexCoordinatePlane n kN := by
          rw [hwq]
          intro i hi
          have hij : i ≠ j := fun h => by rw [h] at hi; omega
          simp [he_j, hWu i hi, hij]
        refine ⟨?_, ?_⟩
        · rw [hflatN hsrc.1 hsrc.2, hcoord, monomial_mem_plane_iff_of_lt hj hjN]
          exact Or.inr hwqP
        · rw [hflatC hsrc.1 hsrc.2, hcoord, monomial_mem_plane_iff hj, hwqj]
          exact ht0
      · exact subset_closure ⟨(hNu u hu).mpr ((monomial_mem_plane_iff_of_lt hj hjN).mpr
          (Or.inr hWu)), fun hC' => hWj ((hCu u hu).mp hC')⟩
  · simp only [hjN, false_and, iff_false]
    intro hcl
    obtain ⟨u', hu'O, hu'A⟩ := mem_closure_iff_nhds.mp hcl O (hO.mem_nhds hu)
    obtain ⟨hNu', hCu'⟩ := hu'A
    exact hCu' ((hCu u' hu'O).mpr
      (eq_zero_of_monomial_mem_plane (not_lt.mp hjN) ((hNu u' hu'O).mp hNu')))

/-- **The strict transforms of a pair `S ⊆ N` in one monomial chart**: at a point `z` over the flat domain of
coordinates `Φ` in which `C = ℂ^{k_C} × 0`, `S = ℂ^{k_S} × 0` and `N = ℂ^{k_N} × 0`, there is one monomial chart
`j ≥ k_C`, with local inverse `W` on an open `O ∋ z`, describing both strict transforms:
`u ∈ S' ⟺ j < k_S ∧ W u ∈ ℂ^{k_S} × 0` and `u ∈ N' ⟺ j < k_N ∧ W u ∈ ℂ^{k_N} × 0` on `O`. -/
theorem exists_local_geoStrictTransform_pair (hπ : IsBlowupAlong n C π) {S N : Set X}
    {y₀ : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}
    {kC kS kN : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kC))
    (hflatS : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ S ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kS))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n kN))
    {z : Y} (hz : π z ∈ flatDomain Φ) :
    ∃ j : Fin n, kC ≤ j.1 ∧ ∃ O : Set Y, IsOpen O ∧ z ∈ O ∧ ∃ W : Y → ComplexModel n,
      (∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') ∧
      (∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j) ∧
      (∀ z' ∈ O, π z' ∈ flatDomain Φ ∧
        monomial kC j (W z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z'))) ∧
      (∀ ℓ : LiftedOpen.{u} (monomialDomain Φ kC j) → Y,
        ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
          π ∘ ℓ = monomialChart Φ kC j → ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ kC j,
            ℓ (LiftedOpen.mk _ (W z') hw) = z') ∧
      (∀ u ∈ O, (u ∈ geoStrictTransform π C S ↔ (j.1 < kS ∧ W u ∈ complexCoordinatePlane n kS))) ∧
      ∀ u ∈ O, (u ∈ geoStrictTransform π C N ↔ (j.1 < kN ∧ W u ∈ complexCoordinatePlane n kN)) := by
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ := exists_monomialLocalInverse hπ hΦsrc hflatC hz
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  exact ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hWeq, hℓ,
    mem_geoStrictTransform_iff_of_monomial hπ hΦsrc hflatC hflatS hj hO hWs hWeq hℓ,
    mem_geoStrictTransform_iff_of_monomial hπ hΦsrc hflatC hflatN hj hO hWs hWeq hℓ⟩

end Strict

/-! ### The monomial identity along the strict transform -/

section Monomial

variable {n : ℕ} {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The normal derivatives through a monomial chart, along `N'`.**  Let `c''` be a flat chart at `π z`, `W` coordinates
near `z` with `c''.ψ ∘ π = σⱼ ∘ W` on an open `O ∋ z`, and `c'` a flat chart at `z` with `c'.ψ = W - W z` near `z`, in
which `N'` is the plane `ℂ^{k_N} × 0` near `z`.  If `g ∘ π = Wⱼ^d · h'` on `N'` near `z`, then for directions `L` in
`[k_C, k_N) \ {j}`, `Wⱼ^d · ∂^L h' = Wⱼ^{|L|} · (∂^L g) ∘ π` on `N'` near `z`. -/
theorem nd_monomial_identity_along {π : Z → Y} (hπ : Continuous π) {z : Z} {S : Set Y} {S'' : Set Z}
    {k'' k' kC kN : ℕ} (c'' : FlatChart n S (π z) k'') (c' : FlatChart n S'' z k') {W : Z → ComplexModel n}
    {O : Set Z} (hO : IsOpen O) (hzO : z ∈ O) {j : Fin n}
    (hWeq : ∀ z' ∈ O, c''.ψ (π z') = monomial kC j (W z')) (hc' : c'.ψ =ᶠ[𝓝 z] fun y => W y - W z)
    {N' : Set Z} (hN' : ∀ᶠ y in 𝓝 z, (y ∈ N' ↔ c'.ψ y ∈ complexCoordinatePlane n kN))
    {d : ℕ} {g : Y → ℂ} {h' : Z → ℂ} (hg : HolomorphicAt n g (π z)) (hh' : HolomorphicAt n h' z)
    (hrel : ∀ᶠ y in 𝓝 z, y ∈ N' → g (π y) = W y j ^ d * h' y) (L : List (Fin n))
    (hL : ∀ l ∈ L, l ≠ j ∧ kC ≤ l.1 ∧ l.1 < kN) :
    ∀ᶠ z' in 𝓝 z, z' ∈ N' → W z' j ^ d * c'.nd L h' z' = W z' j ^ L.length * c''.nd L g (π z') := by
  have hσc : Continuous (monomial (n := n) kC j) := (contDiff_monomial kC j).continuous
  have hσd : Differentiable ℂ (monomial (n := n) kC j) := (contDiff_monomial kC j).differentiable (by simp)
  have hσa : monomial kC j (W z) = 0 := by rw [← hWeq z hzO]; exact c''.ψ_self
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.mp (c''.eventually_differentiableAt_comp_inv hg)
  have hG₀ : DifferentiableOn ℂ (fun w => g (c''.inv w)) (ball 0 r₁) := fun w hw =>
    (hball₁ w hw).differentiableWithinAt
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.eventually_nhds_iff_ball.mp (c'.eventually_differentiableAt_comp_inv hh')
  have hH : DifferentiableOn ℂ (fun u => h' (c'.inv u)) (ball 0 r₀) := fun u hu =>
    (hball₀ u hu).differentiableWithinAt
  obtain ⟨U, hU⟩ : ∃ U : Set (ComplexModel n), U = monomial kC j ⁻¹' ball 0 r₁ := ⟨_, rfl⟩
  have hUo : IsOpen U := hU ▸ isOpen_ball.preimage hσc
  have hUσ : MapsTo (monomial (n := n) kC j) U (ball 0 r₁) := fun w hw => by rw [hU] at hw; exact hw
  have hGσ : DifferentiableOn ℂ (fun w => g (c''.inv (monomial kC j w))) U := fun w hw =>
    (((hG₀ _ (hUσ hw)).differentiableAt (isOpen_ball.mem_nhds (hUσ hw))).comp w (hσd w)).differentiableWithinAt
  have hW'inv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), W (c'.inv u) - W z = u := by
    filter_upwards [c'.eventually_ψ_inv, c'.tendsto_inv.eventually hc'] with u hu hu'
    rw [← hu']; exact hu
  have hinv : Tendsto c'.inv (𝓝 (0 : ComplexModel n)) (𝓝 z) := c'.tendsto_inv
  have hπinv : Tendsto (fun u => π (c'.inv u)) (𝓝 (0 : ComplexModel n)) (𝓝 (π z)) :=
    (hπ.tendsto z).comp hinv
  -- the two sides agree on the plane `ℂ^{k_N} × 0` near `0`
  have hid : ∀ᶠ u in 𝓝 (0 : ComplexModel n), u ∈ complexCoordinatePlane n kN →
      (fun u => (u + W z) j ^ d * h' (c'.inv u)) u = (fun u => g (c''.inv (monomial kC j (u + W z)))) u := by
    filter_upwards [hW'inv, hinv.eventually (hO.mem_nhds hzO), hinv.eventually hrel,
      hπinv.eventually c''.eventually_inv_ψ, hinv.eventually hN', c'.eventually_ψ_inv] with u hu huO hurel huinv
      huN hψu huP
    have hmemN : c'.inv u ∈ N' := huN.mpr (by rw [hψu]; exact huP)
    have hu' : W (c'.inv u) - W z = u := hu
    have hWu : W (c'.inv u) = u + W z := sub_eq_iff_eq_add.mp hu'
    show (u + W z) j ^ d * h' (c'.inv u) = g (c''.inv (monomial kC j (u + W z)))
    rw [← hWu, ← hurel hmemN, ← hWeq _ huO, huinv]
  have hcd : Differentiable ℂ (fun u : ComplexModel n => (u + W z) j ^ d) := fun u =>
    (((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt).comp u
      (differentiableAt_id.add_const (W z))).pow d
  obtain ⟨V, hV⟩ : ∃ V : Set (ComplexModel n), V = ball 0 r₀ ∩ (fun u => u + W z) ⁻¹' U := ⟨_, rfl⟩
  have hVo : IsOpen V := hV ▸ isOpen_ball.inter (hUo.preimage (continuous_add_const (W z)))
  have h0V : (0 : ComplexModel n) ∈ V := by
    rw [hV]
    refine ⟨mem_ball_self hr₀, ?_⟩
    show 0 + W z ∈ U
    rw [hU, Set.mem_preimage, zero_add, hσa]; exact mem_ball_self hr₁
  have hF₁ : DifferentiableOn ℂ (fun u => (u + W z) j ^ d * h' (c'.inv u)) V := fun u hu => by
    rw [hV] at hu
    exact ((hcd u).mul ((hH u hu.1).differentiableAt (isOpen_ball.mem_nhds hu.1))).differentiableWithinAt
  have hF₂ : DifferentiableOn ℂ (fun u => g (c''.inv (monomial kC j (u + W z)))) V := fun u hu => by
    rw [hV] at hu
    have h2 : DifferentiableAt ℂ (fun w => g (c''.inv (monomial kC j w))) (u + W z) :=
      (hGσ _ hu.2).differentiableAt (hUo.mem_nhds hu.2)
    exact (h2.comp u (differentiableAt_id.add_const (W z))).differentiableWithinAt
  have hI := iterDeriv_eventuallyEq_on_plane hVo h0V hF₁ hF₂ hid L (fun l hl => (hL l hl).2.2)
  have ht : Tendsto c'.ψ (𝓝 z) (𝓝 (0 : ComplexModel n)) := c'.tendsto_ψ
  have hshift : ∀ᶠ z' in 𝓝 z, c'.ψ z' + W z ∈ U := by
    have hcont : ContinuousAt (fun u : ComplexModel n => u + W z) 0 := (continuous_add_const (W z)).continuousAt
    have h0 : (0 : ComplexModel n) + W z ∈ U := by
      rw [hU, Set.mem_preimage, zero_add, hσa]; exact mem_ball_self hr₁
    exact ht.eventually (hcont.eventually (hUo.mem_nhds h0))
  have hLj : ∀ l ∈ L, ∀ (w : ComplexModel n) (t : ℂ), (fun u : ComplexModel n => (u + W z) j ^ d) (w + t • bv l) =
      (fun u : ComplexModel n => (u + W z) j ^ d) w := fun l hl w t => by
    have hjl : j ≠ l := Ne.symm (hL l hl).1
    simp [bv, hjl]
  filter_upwards [ht.eventually hI, ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr₀)), hshift, hc',
    hO.mem_nhds hzO, hN'] with z' h1 h2 h3 h4 hz'O hz'N hz'
  have h1' := h1 (hz'N.mp hz')
  have hlhs := iterDeriv_mul_of_const isOpen_ball hcd hH L hLj (c'.ψ z') h2
  have hrhs1 := iterDeriv_comp_add hUo hGσ (W z) L h3
  have hrhs2 := iterDeriv_comp_monomial (G := fun w => g (c''.inv w)) hUo isOpen_ball hUσ hG₀ L
    (fun l hl => ⟨(hL l hl).1, (hL l hl).2.1⟩) (c'.ψ z' + W z) h3
  have h4' : c'.ψ z' = W z' - W z := h4
  have hWz' : c'.ψ z' + W z = W z' := by rw [h4']; abel
  simp only [FlatChart.nd]
  rw [hlhs, hrhs1, hrhs2, hWz'] at h1'
  rw [hWeq z' hz'O]
  simpa [hWz'] using h1'

end Monomial

end

end Hironaka.NormalDerivativeAlong

/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.NestedFlattening
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.MarkedIdeal.NormalTaylorOrder
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPushforward
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Normal derivatives through the monomial charts of a blowup

Source: Włodarczyk 2005, proof of Lemma `le:S`; GGT 2008, proof of Proposition 5.6.4: in the chart `x'ᵢ = xᵢ / y_m`
of the blowup along a centre inside `S = {x = 0}`, the controlled transform `f' = y_m^{-μ} σ^* f` has normal
coefficients `c'_α = y_m^{|α| - μ} σ^* c_α`.

In `ℂⁿ`, for the monomial map `σⱼ` (`σⱼ(w)ᵢ = wᵢ wⱼ` for `i ≥ k`, `i ≠ j`) and directions `eₗ` with `l ≠ j`, `k ≤ l`:
* `monomial_add_smul_single`: `σⱼ(w + t eₗ) = σⱼ(w) + t wⱼ eₗ`;
* `iterDeriv_comp_monomial`: `∂^L (G ∘ σⱼ) = wⱼ^{|L|} (∂^L G) ∘ σⱼ`;

Nested flat charts in product form (`FlatChart.exists_nested`): given a flat chart for `S` (plane `ℂ^{k_N} × 0`) at
`p` and a submanifold `C ⊆ S` through `p`, there is a flat chart for `S` in which also `C` is the plane
`ℂ^{k_C} × 0`, obtained by changing only the tangential coordinates (`T(a, t) = (τ(a), t)`); the normal derivatives
are unchanged.  (A general change of flat chart mixes tangential derivatives into the normal ones; the proof of
`le:S` needs the normal ones.)
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.NormalDerivativeMonomial

open Hironaka.HolomorphicIdealSheaves Hironaka.RegularLocusDense HolomorphicTaylorTail NormalTaylorOrder BlowupMonomialCharts

noncomputable section

section Model

variable {n : ℕ}

/-- **Derivatives along lines**: if `f (w + t v) = g (a + t b)` for all `t`, then `Df(w) v = Dg(a) b`. -/
theorem fderiv_apply_eq_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {w a v b : E}
    (hf : DifferentiableAt ℂ f w) (hg : DifferentiableAt ℂ g a) (h : ∀ t : ℂ, f (w + t • v) = g (a + t • b)) :
    fderiv ℂ f w v = fderiv ℂ g a b := by
  have hl : ∀ (c d : E), HasDerivAt (fun t : ℂ => c + t • d) d 0 := fun c d => by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const d).const_add c
  have h1 : HasDerivAt (fun t : ℂ => f (w + t • v)) (fderiv ℂ f w v) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) (hl w v) (by simp)
  have h2 : HasDerivAt (fun t : ℂ => g (a + t • b)) (fderiv ℂ g a b) 0 :=
    hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) (hl a b) (by simp)
  have hfg : (fun t : ℂ => f (w + t • v)) = fun t => g (a + t • b) := funext h
  rw [hfg] at h1
  exact h1.unique h2

/-- `σⱼ(w + t eₗ) = σⱼ(w) + t wⱼ eₗ` for `l ≠ j`, `k ≤ l`. -/
theorem monomial_add_smul_single {k : ℕ} {j l : Fin n} (hlj : l ≠ j) (hkl : k ≤ l.1) (w : ComplexModel n)
    (t : ℂ) : monomial k j (w + t • bv l) = monomial k j w + t • (w j • bv l) := by
  ext i
  have hj : (bv l : ComplexModel n) j = 0 := by simp [bv, Ne.symm hlj]
  simp only [monomial_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hj, mul_zero, add_zero]
  by_cases hil : i = l
  · subst hil
    simp [bv, hkl, hlj]
    ring
  · have hb : (bv l : ComplexModel n) i = 0 := by simp [bv, hil]
    simp only [hb, mul_zero, add_zero]

/-- **Normal derivatives through a monomial chart**: on an open `U` with `σⱼ(U) ⊆ V` and `G` holomorphic on `V`, for
directions `eₗ` with `l ≠ j`, `k ≤ l`: `∂^L (G ∘ σⱼ)(w) = wⱼ^{|L|} (∂^L G)(σⱼ w)`. -/
theorem iterDeriv_comp_monomial {k : ℕ} {j : Fin n} {G : ComplexModel n → ℂ} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : MapsTo (monomial k j) U V) (hG : DifferentiableOn ℂ G V) :
    ∀ L : List (Fin n), (∀ l ∈ L, l ≠ j ∧ k ≤ l.1) → ∀ w ∈ U,
      iterDeriv (L.map bv) (fun w => G (monomial k j w)) w =
        w j ^ L.length * iterDeriv (L.map bv) G (monomial k j w)
  | [], _, w, _ => by simp
  | l :: L, hL, w, hw => by
    have hLt : ∀ l' ∈ L, l' ≠ j ∧ k ≤ l'.1 := fun l' hl' => hL l' (List.mem_cons_of_mem l hl')
    have hl := hL l List.mem_cons_self
    have hσ : Continuous (monomial k j) := (contDiff_monomial k j).continuous
    have hσd : Differentiable ℂ (monomial k j) := (contDiff_monomial k j).differentiable (by simp)
    have hdL := differentiableOn_iterDeriv hG hV (L.map bv)
    have heq : iterDeriv (L.map bv) (fun w => G (monomial k j w)) =ᶠ[𝓝 w]
        fun w' => w' j ^ L.length * iterDeriv (L.map bv) G (monomial k j w') :=
      eventually_of_mem (hU.mem_nhds hw) fun w' hw' => iterDeriv_comp_monomial hU hV hUV hG L hLt w' hw'
    have hσw : monomial k j w ∈ V := hUV hw
    have hd1 : DifferentiableAt ℂ (fun w' : ComplexModel n => w' j ^ L.length * iterDeriv (L.map bv) G
        (monomial k j w')) w := by
      have hp : DifferentiableAt ℂ (fun w' : ComplexModel n => w' j ^ L.length) w :=
        ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt).pow _
      exact hp.mul (((hdL _ hσw).differentiableAt (hV.mem_nhds hσw)).comp w (hσd w))
    have hd2 : DifferentiableAt ℂ (fun u => w j ^ L.length * iterDeriv (L.map bv) G u) (monomial k j w) :=
      ((hdL _ hσw).differentiableAt (hV.mem_nhds hσw)).const_mul _
    simp only [List.map_cons, iterDeriv_cons, dirDeriv, List.length_cons]
    rw [heq.fderiv_eq, fderiv_apply_eq_of_line hd1 hd2 (fun t => ?_)]
    · rw [fderiv_const_mul ((hdL _ hσw).differentiableAt (hV.mem_nhds hσw)), FunLike.coe_smul, Pi.smul_apply,
        ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    · have hwj : (w + t • bv l) j = w j := by simp [bv, Ne.symm hl.1]
      simp only [hwj, monomial_add_smul_single hl.1 hl.2]

/-- **Normal derivatives ignore a factor that is constant along the directions** (e.g. `wⱼ^m`, `l ≠ j`): on an open
`U` where `H` is holomorphic, `∂^L (c H) = c ∂^L H` if `c (w + t eₗ) = c w` for the directions of `L`. -/
theorem iterDeriv_mul_of_const {c H : ComplexModel n → ℂ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hc : Differentiable ℂ c) (hH : DifferentiableOn ℂ H U) :
    ∀ L : List (Fin n), (∀ l ∈ L, ∀ (w : ComplexModel n) (t : ℂ), c (w + t • bv l) = c w) → ∀ w ∈ U,
      iterDeriv (L.map bv) (fun w => c w * H w) w = c w * iterDeriv (L.map bv) H w
  | [], _, w, _ => rfl
  | l :: L, hL, w, hw => by
    have hLt : ∀ l' ∈ L, ∀ (w : ComplexModel n) (t : ℂ), c (w + t • bv l') = c w :=
      fun l' hl' => hL l' (List.mem_cons_of_mem l hl')
    have hl := hL l List.mem_cons_self
    have hdL := differentiableOn_iterDeriv hH hU (L.map bv)
    have heq : iterDeriv (L.map bv) (fun w => c w * H w) =ᶠ[𝓝 w]
        fun w' => c w' * iterDeriv (L.map bv) H w' :=
      eventually_of_mem (hU.mem_nhds hw) fun w' hw' => iterDeriv_mul_of_const hU hc hH L hLt w' hw'
    have hd1 : DifferentiableAt ℂ (fun w' : ComplexModel n => c w' * iterDeriv (L.map bv) H w') w :=
      (hc w).mul ((hdL w hw).differentiableAt (hU.mem_nhds hw))
    have hd2 : DifferentiableAt ℂ (fun u => c w * iterDeriv (L.map bv) H u) w :=
      ((hdL w hw).differentiableAt (hU.mem_nhds hw)).const_mul _
    simp only [List.map_cons, iterDeriv_cons, dirDeriv]
    rw [heq.fderiv_eq, fderiv_apply_eq_of_line (b := bv l) hd1 hd2 (fun t => by rw [hl w t])]
    rw [fderiv_const_mul ((hdL w hw).differentiableAt (hU.mem_nhds hw)), FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]

/-- Iterated derivatives only depend on the germ. -/
theorem iterDeriv_congr_of_eventuallyEq {F G : ComplexModel n → ℂ} {u : ComplexModel n} (h : F =ᶠ[𝓝 u] G) :
    ∀ L : List (ComplexModel n), iterDeriv L F =ᶠ[𝓝 u] iterDeriv L G
  | [] => h
  | v :: L => by
    have hL := iterDeriv_congr_of_eventuallyEq h L
    filter_upwards [hL.eventually_nhds] with w hw
    simp only [iterDeriv_cons, dirDeriv]
    rw [Filter.EventuallyEq.fderiv_eq (show iterDeriv L F =ᶠ[𝓝 w] iterDeriv L G from hw)]

/-- **Normal derivatives are invariant under maps that translate along the normal directions**: if
`Ψ (v + t eₗ) = Ψ v + t eₗ` for the directions of `L`, then `∂^L (F ∘ Ψ) = (∂^L F) ∘ Ψ`. -/
theorem iterDeriv_comp_translate {Ψ : ComplexModel n → ComplexModel n} {F : ComplexModel n → ℂ}
    {U V : Set (ComplexModel n)} (hU : IsOpen U) (hV : IsOpen V) (hΨ : DifferentiableOn ℂ Ψ U)
    (hUV : MapsTo Ψ U V) (hF : DifferentiableOn ℂ F V) :
    ∀ L : List (Fin n), (∀ l ∈ L, ∀ (v : ComplexModel n) (t : ℂ), Ψ (v + t • bv l) = Ψ v + t • bv l) →
      ∀ v ∈ U, iterDeriv (L.map bv) (fun v => F (Ψ v)) v = iterDeriv (L.map bv) F (Ψ v)
  | [], _, v, _ => rfl
  | l :: L, hL, v, hv => by
    have hLt : ∀ l' ∈ L, ∀ (v : ComplexModel n) (t : ℂ), Ψ (v + t • bv l') = Ψ v + t • bv l' :=
      fun l' hl' => hL l' (List.mem_cons_of_mem l hl')
    have hl := hL l List.mem_cons_self
    have hdL := differentiableOn_iterDeriv hF hV (L.map bv)
    have heq : iterDeriv (L.map bv) (fun v => F (Ψ v)) =ᶠ[𝓝 v] fun v' => iterDeriv (L.map bv) F (Ψ v') :=
      eventually_of_mem (hU.mem_nhds hv) fun v' hv' => iterDeriv_comp_translate hU hV hΨ hUV hF L hLt v' hv'
    have hΨv : Ψ v ∈ V := hUV hv
    have hd1 : DifferentiableAt ℂ (fun v' => iterDeriv (L.map bv) F (Ψ v')) v :=
      ((hdL _ hΨv).differentiableAt (hV.mem_nhds hΨv)).comp v ((hΨ v hv).differentiableAt (hU.mem_nhds hv))
    have hd2 : DifferentiableAt ℂ (iterDeriv (L.map bv) F) (Ψ v) := (hdL _ hΨv).differentiableAt (hV.mem_nhds hΨv)
    simp only [List.map_cons, iterDeriv_cons, dirDeriv]
    rw [heq.fderiv_eq, fderiv_apply_eq_of_line hd1 hd2 (fun t => by rw [hl v t])]

/-- **Iterated derivatives commute with translations.** -/
theorem iterDeriv_comp_add {F : ComplexModel n → ℂ} {V : Set (ComplexModel n)} (hV : IsOpen V)
    (hF : DifferentiableOn ℂ F V) (a : ComplexModel n) (L : List (Fin n)) {u : ComplexModel n} (hu : u + a ∈ V) :
    iterDeriv (L.map bv) (fun u => F (u + a)) u = iterDeriv (L.map bv) F (u + a) :=
  iterDeriv_comp_translate (Ψ := fun u => u + a) (U := (fun u => u + a) ⁻¹' V) (hV.preimage (continuous_add_const a))
    hV ((differentiable_id.add_const a).differentiableOn) (fun _ hv => hv) hF L
    (fun _ _ v t => by abel) u hu

/-- The projection onto the plane `ℂᵏ × 0` (kill the coordinates `i ≥ k`). -/
def planeProj (k : ℕ) : ComplexModel n →L[ℂ] ComplexModel n :=
  (coordinateInclusion n k).comp (coordinateProjection n k)

theorem planeProj_apply (k : ℕ) (u : ComplexModel n) (i : Fin n) :
    planeProj k u i = if i.1 < k then u i else 0 := by
  simp only [planeProj, ContinuousLinearMap.comp_apply, coordinateInclusion_apply, coordinateProjection_apply]
  by_cases h : i.1 < k
  · simp [h]
  · simp [h]

theorem planeProj_mem (k : ℕ) (u : ComplexModel n) : planeProj k u ∈ complexCoordinatePlane n k :=
  fun i hi => by rw [planeProj_apply, if_neg (not_lt.mpr hi)]

theorem planeProj_of_mem {k : ℕ} {u : ComplexModel n} (hu : u ∈ complexCoordinatePlane n k) : planeProj k u = u := by
  ext i
  rw [planeProj_apply]
  split_ifs with h
  · rfl
  · exact (hu i (not_lt.mp h)).symm

theorem planeProj_planeProj (k : ℕ) (u : ComplexModel n) : planeProj k (planeProj k u) = planeProj k u :=
  planeProj_of_mem (planeProj_mem k u)

theorem planeProj_bv {k : ℕ} {l : Fin n} (hl : k ≤ l.1) : planeProj k (bv l) = 0 := by
  ext i
  rw [planeProj_apply]
  split_ifs with h
  · have : i ≠ l := fun e => by subst e; omega
    simp [bv, this]
  · rfl

theorem mem_plane_iff_sub_planeProj {k : ℕ} {u : ComplexModel n} :
    u ∈ complexCoordinatePlane n k ↔ u - planeProj k u = 0 := by
  constructor
  · intro hu; rw [planeProj_of_mem hu, sub_self]
  · intro h
    have h' : u = planeProj k u := sub_eq_zero.mp h
    rw [h']; exact planeProj_mem k u

end Model

/-! ### Product-form change of the tangential coordinates -/

section ProductForm

variable {n : ℕ} {kN : ℕ} (Φm : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))

/-- `T(u) = Φm(P u) + (u - P u)`: `Φm` on the plane, the identity on the normal coordinates. -/
def prodTo (kN : ℕ) (u : ComplexModel n) : ComplexModel n :=
  Φm.toFun (planeProj kN u) + (u - planeProj kN u)

/-- `T⁻¹(v) = Φm⁻¹(P v) + (v - P v)`. -/
def prodInv (kN : ℕ) (v : ComplexModel n) : ComplexModel n :=
  Φm.invFun (planeProj kN v) + (v - planeProj kN v)

variable {Φm}

theorem planeProj_prodTo (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔
      Φm.toFun u ∈ complexCoordinatePlane n kN)) {u : ComplexModel n} (hu : planeProj kN u ∈ Φm.source) :
    planeProj kN (prodTo Φm kN u) = Φm.toFun (planeProj kN u) := by
  have h1 : Φm.toFun (planeProj kN u) ∈ complexCoordinatePlane n kN :=
    (hplane _ hu).mp (planeProj_mem kN u)
  simp only [prodTo, map_add, map_sub, planeProj_planeProj, sub_self, add_zero, planeProj_of_mem h1]

theorem planeProj_prodInv (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔
      Φm.toFun u ∈ complexCoordinatePlane n kN)) {v : ComplexModel n} (hv : planeProj kN v ∈ Φm.target) :
    planeProj kN (prodInv Φm kN v) = Φm.invFun (planeProj kN v) := by
  have h0 : Φm.invFun (planeProj kN v) ∈ Φm.source := Φm.mapsTo_invFun hv
  have h1 : Φm.invFun (planeProj kN v) ∈ complexCoordinatePlane n kN := by
    refine (hplane _ h0).mpr ?_
    rw [Φm.right_inv _ hv]; exact planeProj_mem kN v
  simp only [prodInv, map_add, map_sub, planeProj_planeProj, sub_self, add_zero, planeProj_of_mem h1]

theorem prodTo_sub_planeProj (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔
      Φm.toFun u ∈ complexCoordinatePlane n kN)) {u : ComplexModel n} (hu : planeProj kN u ∈ Φm.source) :
    prodTo Φm kN u - planeProj kN (prodTo Φm kN u) = u - planeProj kN u := by
  rw [planeProj_prodTo hplane hu]; simp only [prodTo]; abel

theorem prodInv_prodTo (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔
      Φm.toFun u ∈ complexCoordinatePlane n kN)) {u : ComplexModel n} (hu : planeProj kN u ∈ Φm.source) :
    prodInv Φm kN (prodTo Φm kN u) = u := by
  rw [prodInv, planeProj_prodTo hplane hu, Φm.left_inv _ hu]
  simp only [prodTo]
  abel

/-- **The product-form local biholomorphism** `T(a, t) = (Φm(a), t)` at `0`. -/
def prodEquiv (Φm : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔ Φm.toFun u ∈ complexCoordinatePlane n kN)) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := planeProj kN ⁻¹' Φm.source
  target := planeProj kN ⁻¹' Φm.target
  isOpen_source := Φm.isOpen_source.preimage (planeProj kN).continuous
  isOpen_target := Φm.isOpen_target.preimage (planeProj kN).continuous
  center_mem_source := by simp only [mem_preimage, map_zero]; exact Φm.center_mem_source
  toFun := prodTo Φm kN
  invFun := prodInv Φm kN
  toFun_holomorphic := by
    intro u hu
    have h1 : DifferentiableAt ℂ (fun u => Φm.toFun (planeProj kN u)) u :=
      (Φm.toFun_holomorphic.differentiableAt (Φm.isOpen_source.mem_nhds hu)).comp u
        (planeProj kN).differentiableAt
    exact (h1.add (differentiableAt_id.sub (planeProj kN).differentiableAt)).differentiableWithinAt
  invFun_holomorphic := by
    intro v hv
    have h1 : DifferentiableAt ℂ (fun v => Φm.invFun (planeProj kN v)) v :=
      (Φm.invFun_holomorphic.differentiableAt (Φm.isOpen_target.mem_nhds hv)).comp v
        (planeProj kN).differentiableAt
    exact (h1.add (differentiableAt_id.sub (planeProj kN).differentiableAt)).differentiableWithinAt
  mapsTo_toFun := fun u hu => by
    show planeProj kN (prodTo Φm kN u) ∈ Φm.target
    rw [planeProj_prodTo hplane hu]; exact Φm.mapsTo_toFun hu
  mapsTo_invFun := fun v hv => by
    show planeProj kN (prodInv Φm kN v) ∈ Φm.source
    rw [planeProj_prodInv hplane hv]; exact Φm.mapsTo_invFun hv
  left_inv := fun u hu => prodInv_prodTo hplane hu
  right_inv := fun v hv => by
    show prodTo Φm kN (prodInv Φm kN v) = v
    have h0 : Φm.invFun (planeProj kN v) ∈ Φm.source := Φm.mapsTo_invFun hv
    have hp : planeProj kN (prodInv Φm kN v) ∈ Φm.source := by
      rw [planeProj_prodInv hplane hv]; exact h0
    have h := prodTo_sub_planeProj hplane hp
    simp only [prodTo] at h ⊢
    rw [planeProj_prodInv hplane hv, Φm.right_inv _ hv] at h ⊢
    simp only [prodInv] at h ⊢
    abel

theorem prodInv_add_smul_bv {l : Fin n} (hl : kN ≤ l.1) (v : ComplexModel n) (t : ℂ) :
    prodInv Φm kN (v + t • bv l) = prodInv Φm kN v + t • bv l := by
  simp only [prodInv, map_add, map_smul, planeProj_bv hl, smul_zero, add_zero]
  abel

end ProductForm

/-! ### Nested flat charts in product form -/

section Nested

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

open NormalDerivativeChart BlowupFlatCoordinates

/-- Normal derivatives in a flat chart `c'` whose coordinates are `T ∘ ψ` for the product-form `T` agree with those
of `c`. -/
theorem FlatChart.nd_eventuallyEq_of_prod {S : Set M} {p : M} {kN : ℕ} (c : FlatChart n S p kN)
    {Φm : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)}
    (hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔ Φm.toFun u ∈ complexCoordinatePlane n kN))
    (c' : FlatChart n S p kN) (hto : c'.Φ.toFun = fun z => prodTo Φm kN (c.Φ.toFun z))
    (hinv : c'.Φ.invFun = fun u => c.Φ.invFun (prodInv Φm kN u)) {L : List (Fin n)} (hL : NormalIdx kN L)
    {f : M → ℂ} (hf : HolomorphicAt n f p) : c'.nd L f =ᶠ[𝓝 p] c.nd L f := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (c.eventually_differentiableAt_comp_inv hf)
  have hFU : DifferentiableOn ℂ (fun u => f (c.inv u)) (ball 0 r) := fun z hz =>
    (hball z hz).differentiableWithinAt
  obtain ⟨Tt, hTt⟩ : ∃ Tt : Set (ComplexModel n), Tt = planeProj kN ⁻¹' Φm.target := ⟨_, rfl⟩
  have hTto : IsOpen Tt := hTt ▸ Φm.isOpen_target.preimage (planeProj kN).continuous
  have hΨd : DifferentiableOn ℂ (prodInv Φm kN) Tt := fun v hv => by
    rw [hTt] at hv
    exact ((((Φm.invFun_holomorphic.differentiableAt (Φm.isOpen_target.mem_nhds hv)).comp v
      (planeProj kN).differentiableAt)).add
      (differentiableAt_id.sub (planeProj kN).differentiableAt)).differentiableWithinAt
  obtain ⟨U, hUdef⟩ : ∃ U : Set (ComplexModel n), U = Tt ∩ prodInv Φm kN ⁻¹' ball 0 r := ⟨_, rfl⟩
  have hUo : IsOpen U := hUdef ▸ hΨd.continuousOn.isOpen_inter_preimage hTto isOpen_ball
  have hUT : U ⊆ Tt := hUdef ▸ inter_subset_left
  have hUmaps : MapsTo (prodInv Φm kN) U (ball 0 r) := fun v hv => by
    rw [hUdef] at hv; exact hv.2
  have htrans := iterDeriv_comp_translate (Ψ := prodInv Φm kN) hUo isOpen_ball
    (hΨd.mono hUT) hUmaps hFU L (fun l hl v t => prodInv_add_smul_bv (hL l hl) v t)
  have hTs : ∀ᶠ y in 𝓝 p, planeProj kN (c.ψ y) ∈ Φm.source ∧ c.ψ y ∈ ball (0 : ComplexModel n) r := by
    have h0 : planeProj kN (0 : ComplexModel n) ∈ Φm.source := by
      rw [map_zero]; exact Φm.center_mem_source
    have h1 : planeProj kN ⁻¹' Φm.source ∈ 𝓝 (0 : ComplexModel n) :=
      (Φm.isOpen_source.preimage (planeProj kN).continuous).mem_nhds h0
    exact c.tendsto_ψ.eventually ((eventually_mem_set.mpr h1).and (isOpen_ball.mem_nhds (mem_ball_self hr)))
  filter_upwards [hTs] with y hy
  have hli : prodInv Φm kN (prodTo Φm kN (c.ψ y)) = c.ψ y := prodInv_prodTo hplane hy.1
  have hmem : prodTo Φm kN (c.ψ y) ∈ U := by
    rw [hUdef, hTt]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, planeProj_prodTo hplane hy.1]; exact Φm.mapsTo_toFun hy.1
    · rw [Set.mem_preimage, hli]; exact hy.2
  have hψ' : c'.ψ y = prodTo Φm kN (c.ψ y) := by
    simp only [FlatChart.ψ, hto]
  have hinv' : c'.inv = fun u => c.inv (prodInv Φm kN u) := by
    funext u; simp only [FlatChart.inv, hinv]
  simp only [FlatChart.nd]
  rw [hψ', hinv', htrans _ hmem, hli]

/-- **Nested flat charts in product form**: a flat chart `c` for `S` (plane `ℂ^{k_N} × 0`) at `p` and a submanifold
`C ⊆ S` regular of dimension `k_C ≤ k_N` at `p` give a flat chart `c'` for `S` at `p` in which also `C` is the plane
`ℂ^{k_C} × 0`, with the SAME normal derivatives (`c'` changes only the tangential coordinates). -/
theorem FlatChart.exists_nested {S C : Set M} {p : M} {kN kC : ℕ} (c : FlatChart n S p kN) (hkC : kC ≤ kN)
    (hkN : kN ≤ n) (hC : RegularAtDim (n := n) C p kC) (hCS : C ⊆ S) :
    ∃ c' : FlatChart n S p kN,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c'.Φ.source →
        (y ∈ C ↔ c'.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kC)) ∧
      ∀ L : List (Fin n), NormalIdx kN L → ∀ f : M → ℂ, HolomorphicAt n f p →
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
  have hCN : ∀ u ∈ Θ'.source, u ∈ C' → u ∈ complexCoordinatePlane n kN := by
    intro u hu huC
    obtain ⟨hy, h2⟩ := hpt u hu.1
    have := (c.flat hy (by rw [h2]; exact c.Φ.mapsTo_invFun hu.1)).mp (hCS huC)
    rwa [h2, c.Φ.right_inv _ hu.1] at this
  obtain ⟨Φm, -, hΦm0, hΦm⟩ := NestedFlattening.exists_nested_flattening_model hkC hkN Θ' hΘ'0 hΘ'C hCN
  have hplane : ∀ u ∈ Φm.source, (u ∈ complexCoordinatePlane n kN ↔
      Φm.toFun u ∈ complexCoordinatePlane n kN) := fun u hu => (hΦm u hu).2
  set T := prodEquiv Φm hplane with hT
  have hT0 : T.toFun 0 = 0 := by
    show prodTo Φm kN 0 = 0
    simp [prodTo, hΦm0]
  have hTplane : ∀ u, planeProj kN u ∈ Φm.source →
      (u ∈ complexCoordinatePlane n kN ↔ T.toFun u ∈ complexCoordinatePlane n kN) := by
    intro u hu
    rw [mem_plane_iff_sub_planeProj, mem_plane_iff_sub_planeProj]
    show _ ↔ prodTo Φm kN u - planeProj kN (prodTo Φm kN u) = 0
    rw [prodTo_sub_planeProj hplane hu]
  set Φ'' := RegularAtDimTransport.LocalHolomorphicEquivAt.comp c.Φ T c.zero with hΦ''
  refine ⟨⟨Φ'', fun u hu => c.src hu.1, by show T.toFun (c.Φ.toFun (e p)) = 0; rw [c.zero, hT0], ?_⟩, ?_, ?_⟩
  · intro y hy hyΦ
    rw [c.flat hy hyΦ.1]
    exact hTplane _ hyΦ.2
  · intro y hy hyΦ
    show y ∈ C ↔ prodTo Φm kN (c.Φ.toFun (e y)) ∈ complexCoordinatePlane n kC
    have hyinv : c.inv (c.Φ.toFun (e y)) = y := flatInverse_flat c.Φ ⟨hy, hyΦ.1⟩
    have hPΦ : planeProj kN (c.Φ.toFun (e y)) ∈ Φm.source := hyΦ.2
    by_cases hup : c.Φ.toFun (e y) ∈ complexCoordinatePlane n kN
    · have hPu := planeProj_of_mem hup
      rw [hPu] at hPΦ
      have hTu : prodTo Φm kN (c.Φ.toFun (e y)) = Φm.toFun (c.Φ.toFun (e y)) := by
        simp only [prodTo, hPu, sub_self, add_zero]
      rw [hTu, ← (hΦm _ hPΦ).1]
      show y ∈ C ↔ c.inv (c.Φ.toFun (e y)) ∈ C
      rw [hyinv]
    · have hyC : y ∉ C := fun h => hup ((c.flat hy hyΦ.1).mp (hCS h))
      have hTn : prodTo Φm kN (c.Φ.toFun (e y)) ∉ complexCoordinatePlane n kN :=
        fun h => hup ((hTplane _ hyΦ.2).mpr h)
      refine iff_of_false hyC fun h => hTn fun i hi => h i (le_trans hkC hi)
  · intro L hL f hf
    exact FlatChart.nd_eventuallyEq_of_prod c hplane _ rfl rfl hL hf

end Nested

end

end Hironaka.NormalDerivativeMonomial

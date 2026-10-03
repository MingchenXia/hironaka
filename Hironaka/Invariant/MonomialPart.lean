/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponent
import Hironaka.Invariant.MemberPullback
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.CodimOneCentre
import Hironaka.Invariant.BoundaryCount
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.GermOrderProduct
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial and nonmonomial parts of an ideal

* `exists_eq_mul_pow_of_mem_idealPow`: if `𝓘 = (u)` at `y`, the germs of `𝓘^a` at `y` are the multiples of `u^a`.
* `frequently_flatMap_ne_zero`: in flat coordinates, points where a chosen set of coordinates is nonzero and the others
  are unchanged accumulate at every point.
* **Simultaneous divisibility** `exists_eq_mul_prod_of_forall`: in a chart in which the sets `A_i` (`i ∈ T`) are the
  distinct coordinate hyperplanes `{w_{σ i} = 0}` (submanifolds at their points), a germ divisible by each `u_i^{a_i}`
  (`u_i` the coordinate) is divisible by `∏ u_i^{a_i}`.  The coordinate hyperplanes are pairwise non-associate primes;
  formally, by induction on `T`, the cofactor `c'` of `∏_{T'} u^a` lies in `𝔪_z^{a_j}` at the points `z` of `A_j` near
  points of `A_j` off the other hyperplanes, and the identity principle along `A_j`
  (`DivisorExponent.mem_idealPow_vanishingIdeal_of_frequently`) gives `c' ∈ 𝓘_{A_j}^{a_j} = (u_j^{a_j})`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.MonomialPart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates Hironaka.HadamardBridge Hironaka.GiraudAlong Hironaka.DivisorExponent Hironaka.GermOrderProduct Hironaka.CodimOneCentre Hironaka.MemberPullback

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Powers of a principal ideal -/

section Principal

/-- **Powers of a principal ideal**: if every germ of `𝓘` at `y` is a multiple of `u`, every germ of `𝓘^a` at `y` is a
multiple of `u^a`. -/
theorem exists_eq_mul_pow_of_mem_idealPow {I : GermIdeal n M} {u : M → ℂ} {y : M}
    (hI : ∀ g, I.mem y g → IsInSpanAt (n := n) (· = u) y g) :
    ∀ {a : ℕ} {g : M → ℂ}, (idealPow I a).mem y g →
      ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * u z ^ a
  | 0, g, hg => ⟨g, hg, Eventually.of_forall fun z => by simp⟩
  | a + 1, g, hg => by
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_idealPow_succ_iff.mp hg
    choose p q hp hq hpq using hr
    choose d hd hpd using fun k => exists_eq_mul_pow_of_mem_idealPow hI (hp k)
    choose hqhol f hf hqf using fun k => isInSpanAt_eq_iff.mp (hI _ (hq k))
    refine ⟨fun z => ∑ k, c k z * (d k z * f k z),
      HolomorphicAt.sum _ fun k _ => (hc k).mul ((hd k).mul (hf k)), ?_⟩
    filter_upwards [hsum, eventually_all.mpr hpd, eventually_all.mpr hqf] with z hz h1 h2
    rw [hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpq k]
    simp only [Pi.mul_apply, h1 k, h2 k]
    ring

/-- Finite products of holomorphic germs are holomorphic. -/
theorem holomorphicAt_finset_prod {ι : Type*} (T : Finset ι) {F : ι → M → ℂ} {y : M}
    (h : ∀ i ∈ T, HolomorphicAt n (F i) y) : HolomorphicAt n (fun z => ∏ i ∈ T, F i z) y := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  | insert j T hj ih =>
    have := (h j (Finset.mem_insert_self j T)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.prod_insert hj] using this

/-- A germ is a multiple of every power of a germ that does not vanish at the point. -/
theorem exists_eq_mul_pow_of_ne_zero {u g : M → ℂ} {y : M} (hu : HolomorphicAt n u y) (huy : u y ≠ 0)
    (hg : HolomorphicAt n g y) (a : ℕ) : ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * u z ^ a := by
  refine ⟨fun z => g z * ((u z)⁻¹) ^ a,
    hg.mul (CompanionReduction.holomorphicAt_pow_of (BlowupFlatCoordinates.HolomorphicAt.inv hu huy) _), ?_⟩
  filter_upwards [hu.continuousAt.eventually (isOpen_ne.mem_nhds huy)] with z hz
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]

/-- A germ of `𝓘` has its powers in the powers of `𝓘`. -/
theorem pow_mem_idealPow {I : GermIdeal n M} {y : M} {u : M → ℂ} (hu : I.mem y u)
    (huh : HolomorphicAt n u y) : ∀ a : ℕ, (idealPow I a).mem y (fun z => u z ^ a)
  | 0 => by
    show HolomorphicAt n (fun z => u z ^ 0) y
    simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  | a + 1 => by
    have h := mul_mem_idealPow_succ (pow_mem_idealPow hu huh a) hu
      (by simpa [pow_succ] using (CompanionReduction.holomorphicAt_pow_of huh (a + 1)))
    simpa [pow_succ] using h

end Principal

/-! ### Points off coordinate hyperplanes -/

section Frequently

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

include hΦsrc in
/-- In flat coordinates, the points at which the coordinates with index in `T` are nonzero and the other coordinates
are those of `y` accumulate at every point `y` of the flat domain. -/
theorem frequently_flatMap_ne_zero {y : M} (hy : y ∈ flatDomain Φ) (T : Finset (Fin n)) :
    ∃ᶠ y' in 𝓝 y, y' ∈ flatDomain Φ ∧ (∀ l ∈ T, flatMap Φ y' l ≠ 0) ∧
      ∀ l, l ∉ T → flatMap Φ y' l = flatMap Φ y l := by
  set w₀ := flatMap Φ y
  set v : ComplexModel n := ∑ l ∈ T, EuclideanSpace.single l (1 : ℂ)
  have hv : ∀ l, v l = if l ∈ T then 1 else 0 := fun l => by simp [v]
  have hw₀T : w₀ ∈ Φ.target := flatMap_mem_target hy
  set γ : ℂ → ComplexModel n := fun t => w₀ + t • v
  have hγl : ∀ t l, γ t l = w₀ l + t * (if l ∈ T then 1 else 0) := fun t l => by
    simp [γ, hv l]
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγT : Tendsto γ (𝓝[≠] 0) (𝓝 w₀) := by
    have h := hγc.continuousAt (x := (0 : ℂ))
    simp only [ContinuousAt, γ, zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hφT : Tendsto (fun t => flatInv Φ (γ t)) (𝓝[≠] 0) (𝓝 y) := by
    have h1 := (continuousAt_flatInv hw₀T hΦsrc).tendsto
    rw [show flatInv Φ w₀ = y from flatInv_flatMap hy] at h1
    exact h1.comp hγT
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), γ t ∈ Φ.target ∧ ∀ l ∈ T, γ t l ≠ 0 := by
    refine (hγT.eventually (Φ.isOpen_target.mem_nhds hw₀T)).and ((eventually_all_finset T).mpr fun l hl => ?_)
    by_cases h0 : w₀ l = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hγl, h0, if_pos hl]
      simpa using ht
    · have hc : ContinuousAt (fun t : ℂ => w₀ l + t) 0 := (continuous_const.add continuous_id).continuousAt
      have : ∀ᶠ t in 𝓝 (0 : ℂ), w₀ l + t ≠ 0 :=
        hc.eventually (isOpen_ne.mem_nhds (by simpa using h0))
      filter_upwards [this.filter_mono nhdsWithin_le_nhds] with t ht
      rw [hγl, if_pos hl, mul_one]
      exact ht
  refine hφT.frequently (hev.frequently.mono fun t ⟨htT, htl⟩ => ?_)
  refine ⟨flatInv_mem_flatDomain htT hΦsrc, fun l hl => ?_, fun l hl => ?_⟩
  · rw [flatMap_flatInv htT hΦsrc]
    exact htl l hl
  · rw [flatMap_flatInv htT hΦsrc, hγl, if_neg hl, mul_zero, add_zero]

end Frequently

/-! ### Simultaneous divisibility by coordinate hyperplanes -/

section Factorization

variable {x : M} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
  {ι : Type*} [DecidableEq ι] {A : ι → Set M} {σ : ι → Fin n}

include hΦsrc in
/-- **Simultaneous divisibility** (`hir:monomial-factorization`): in a chart in which the sets `A i` are the coordinate
hyperplanes `{w_{σ i} = 0}` (submanifolds at their points), with `σ` injective on `T`, a germ at a point `y` of the chart
which is divisible by each `u_i^{a_i}` (`u_i = w_{σ i}`, `i ∈ T`) is divisible by `∏_{i ∈ T} u_i^{a_i}`. -/
theorem exists_eq_mul_prod_of_forall (a : ι → ℕ) {y : M} (hy : y ∈ flatDomain Φ) :
    ∀ (T : Finset ι),
      (∀ i ∈ T, ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ A i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i) = 0)) →
      (∀ i ∈ T, ∀ y ∈ A i, ∃ k, RegularAtDim (n := n) (A i) y k) →
      Set.InjOn σ T → ∀ {g : M → ℂ}, HolomorphicAt n g y →
      (∀ i ∈ T, ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * flatMap Φ z (σ i) ^ a i) →
      ∃ c, HolomorphicAt n c y ∧ g =ᶠ[𝓝 y] fun z => c z * ∏ i ∈ T, flatMap Φ z (σ i) ^ a i := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ _ g hg _
    exact ⟨g, hg, Eventually.of_forall fun z => by simp⟩
  | insert j T' hj ih =>
    intro hA' hreg' hσ g hg hdiv
    have hA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ A j ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ j) = 0) :=
      fun hy1 hy2 => hA' j (Finset.mem_insert_self j T') hy1 hy2
    have hreg := hreg' j (Finset.mem_insert_self j T')
    obtain ⟨c', hc', hgc'⟩ := ih (fun i hi _ hy1 hy2 => hA' i (Finset.mem_insert_of_mem hi) hy1 hy2)
      (fun i hi => hreg' i (Finset.mem_insert_of_mem hi)) (hσ.mono (by simp)) hg
      fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    obtain ⟨d, hd, hgd⟩ := hdiv j (Finset.mem_insert_self j T')
    set u : M → ℂ := fun z => flatMap Φ z (σ j) with hu_def
    set p : M → ℂ := fun z => ∏ i ∈ T', flatMap Φ z (σ i) ^ a i with hp_def
    have hcoord : ∀ l, ∀ z ∈ flatDomain Φ, HolomorphicAt n (fun z => flatMap Φ z l) z :=
      fun l z hz => holomorphicAt_flatCoord Φ l hz
    have hph : ∀ z ∈ flatDomain Φ, HolomorphicAt n p z := fun z hz =>
      holomorphicAt_finset_prod T' fun i _ => CompanionReduction.holomorphicAt_pow_of (hcoord (σ i) z hz) (a i)
    have huh : HolomorphicAt n u y := hcoord (σ j) y hy
    -- the cofactor `c'` is divisible by `u^{a_j}`
    obtain ⟨c'', hc'', hc'eq⟩ : ∃ c'', HolomorphicAt n c'' y ∧
        c' =ᶠ[𝓝 y] fun z => c'' z * u z ^ a j := by
      by_cases huy : u y = 0
      · have hyA : y ∈ A j := (hA hy.1 hy.2).mpr huy
        obtain ⟨k, hk⟩ := hreg y hyA
        have hσj : σ j ∉ T'.image σ := by
          intro h
          obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp h
          have := hσ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self j T') hij
          exact hj (this ▸ hi)
        -- near `y`: the two factorizations, holomorphy
        have key : ∀ᶠ z in 𝓝 y, z ∈ flatDomain Φ ∧ HolomorphicAt n d z ∧ HolomorphicAt n c' z ∧
            (∀ᶠ z' in 𝓝 z, g z' = c' z' * p z') ∧ (∀ᶠ z' in 𝓝 z, g z' = d z' * u z' ^ a j) := by
          filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy, hd.eventually_nhds, hc'.eventually_nhds,
            hgc'.eventually_nhds, hgd.eventually_nhds] with z h1 h2 h3 h4 h5
          exact ⟨h1, h2, h3, h4, h5⟩
        have hmem : (idealPow (vanishingIdeal (n := n) (A j)) (a j)).mem y c' := by
          refine mem_idealPow_vanishingIdeal_of_frequently hk hc' ?_
          refine ((frequently_flatMap_ne_zero hΦsrc hy (T'.image σ)).and_eventually
            key.eventually_nhds).mono ?_
          rintro y' ⟨⟨hy'D, hy'ne, hy'eq⟩, hy'key⟩
          have hy'A : y' ∈ A j := by
            refine (hA hy'D.1 hy'D.2).mpr ?_
            have := hy'eq (σ j) hσj
            change flatMap Φ y' (σ j) = 0
            rw [this]
            exact huy
          have hpy' : p y' ≠ 0 := by
            refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ ?_
            exact hy'ne (σ i) (Finset.mem_image_of_mem σ hi)
          have hpne : ∀ᶠ z in 𝓝 y', p z ≠ 0 :=
            (hph y' hy'D).continuousAt.eventually (isOpen_ne.mem_nhds hpy')
          refine ⟨hy'A, ?_⟩
          filter_upwards [hy'key, hpne.eventually_nhds] with z hzkey hzp hzA
          obtain ⟨hzD, hdz, -, hz1, hz2⟩ := hzkey
          have huz : u z = 0 := (hA hzD.1 hzD.2).mp hzA
          have hq : HolomorphicAt n (fun z' => d z' * (p z')⁻¹) z :=
            hdz.mul (BlowupFlatCoordinates.HolomorphicAt.inv (hph z hzD) hzp.self_of_nhds)
          have hupow : (idealPow (pointIdeal n z) (a j)).mem z (fun z' => u z' ^ a j) :=
            mem_idealPow_of_vanishesToOrderOn_univ
              (CodimOneCentre.vanishesToOrderOn_pow (mem_univ z) (hcoord (σ j) z hzD) huz (a j))
          refine mem_idealPow_congr (mul_mem_idealPow hq hupow) ?_
          filter_upwards [hz1, hz2, hzp] with z' h1 h2 h3
          have : c' z' = g z' / p z' := by rw [h1]; field_simp
          rw [this, h2]
          field_simp
        exact exists_eq_mul_pow_of_mem_idealPow
          (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ hA hy g).mp hg) hmem
      · refine ⟨fun z => c' z * ((u z)⁻¹) ^ a j,
          hc'.mul (CompanionReduction.holomorphicAt_pow_of
            (BlowupFlatCoordinates.HolomorphicAt.inv huh huy) _), ?_⟩
        filter_upwards [huh.continuousAt.eventually (isOpen_ne.mem_nhds huy)] with z hz
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    refine ⟨c'', hc'', ?_⟩
    filter_upwards [hgc', hc'eq] with z h1 h2
    rw [h1, h2, Finset.prod_insert hj]
    ring

end Factorization

/-! ### The monomial and nonmonomial parts -/

section Parts

open BoundaryCount NormalCrossings

variable {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- The members of a simple normal crossings divisor are closed submanifolds. -/
theorem isClosedSubmanifold_get (hn : 0 < n) (hE : IsSNCDivisor n E) (i : Fin E.length) :
    IsClosedSubmanifold n (E.get i) := by
  have h := isClosedSubmanifold_memberInter hn hE {i}
  have heq : memberInter E {i} = E.get i := by
    ext y
    simp [memberInter]
  rwa [heq] at h

/-- A germ of a coherent ideal stays in it under germ equality. -/
theorem mem_congr_of_isCoherent {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {y : M} {g g' : M → ℂ}
    (hg : 𝔟.mem y g) (hgg : g =ᶠ[𝓝 y] g') : 𝔟.mem y g' :=
  GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔟 (isInSpanAt_of_eq_mul hg
    ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg).congr hgg)
    (holomorphicAt_const 1) (hgg.symm.mono fun _ hz => by simp [hz]))

/-- **A germ that vanishes identically near no point is a non-zero-divisor**: if `f m = 0` near `y`, `m` holomorphic
at `y` and not vanishing near `y`, then `f = 0` near `y` (orders add, and a germ of infinite order vanishes). -/
theorem eventually_eq_zero_of_mul_eventually_eq_zero {f m : M → ℂ} {y : M} (hf : HolomorphicAt n f y)
    (hm : HolomorphicAt n m y) (hmne : ∃ᶠ z in 𝓝 y, m z ≠ 0)
    (h : (fun z => f z * m z) =ᶠ[𝓝 y] fun _ => 0) : f =ᶠ[𝓝 y] fun _ => 0 := by
  obtain ⟨b, hb⟩ := exists_notMem_idealPow_of_frequently hm hmne
  rcases b with _ | b
  · exact absurd hm hb
  refine eventually_eq_zero_of_forall_mem_idealPow hf fun q => ?_
  have hfm : (idealPow (pointIdeal n y) (q + b)).mem y (fun z => f z * m z) :=
    mem_idealPow_congr (zero_mem_idealPow _ y _) h.symm
  exact mem_idealPow_of_mul_mem hf hm hb hfm

end Parts

end

end Hironaka.MonomialPart

import Hironaka.Blowup.BlowupExistenceOriginGenerator

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The model blowup satisfies the universal property

`isBlowupAlong_originProj`: for `d ≥ 1` the projection
`originProj : OriginBlowup d → ℂᵈ` is the blowup of `ℂᵈ` along the origin, in the sense of
`Hironaka.BlowupSequences.IsBlowupAlong`.  This is the first time in the workspace that the
blowup of a manifold along a centre of codimension `≥ 2` is exhibited; before it, every blowup
hypothesis was conditional (`Hironaka.BlowupExistenceCodimOne` had settled only the range in
which the blowup is the identity).

The three steps, given a holomorphic `g : Z → ℂᵈ` whose pullback `g* 𝓘_0` is invertible:

* `exists_ne_zero_of_isOpen`: `g` vanishes on no nonempty open set.  If `u` generates
  `g* 𝓘_0` near `z₀` then `u` is itself a combination `∑ gᵢ cᵢ` of the components, so `u`
  vanishes wherever `g` does; and `u` vanishes on no nonempty open set by hypothesis.
* `lift_eqOn`: two lifts agree.  They agree wherever `g ≠ 0`, because a point of the blowup
  with nonzero image has its line determined by that image; and the set where two continuous
  maps into a Hausdorff space differ is open, so by the previous step it is empty.
* `exists_local_lift`: a lift exists near each point.  Writing `gᵢ = aᵢ u`, the `aᵢ` have no
  common zero -- for `g z₀ ≠ 0` this is immediate, and for `g z₀ = 0` it follows from
  `u = ∑ gᵢ cᵢ = u ∑ aᵢ cᵢ` together with the non-vanishing of `u`, which forces
  `∑ aᵢ cᵢ = 1` by continuity.  Picking `j` with `a_j (z₀) ≠ 0` gives the lift into the `j`-th
  chart.  The local lifts then glue, by the uniqueness step.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlowupExistenceOriginUniversal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupExistenceOriginModel BlowupExistenceOriginIdeal BlowupExistenceOriginGenerator

noncomputable section

variable {d m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-! ### A point of the blowup with nonzero image is determined by that image -/

theorem line_eq_span_point {p : OriginBlowup d} (hp : p.point ≠ 0) :
    p.line = Submodule.span ℂ {p.point} := by
  obtain ⟨w, hw, hline⟩ := p.isLine
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline ▸ p.point_mem)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hc]; simp)
  rw [hline, ← hc]
  exact (Submodule.span_singleton_smul_eq (by simpa using hc0) _).symm

theorem eq_of_originProj_eq {p q : OriginBlowup d} (hpq : originProj p = originProj q)
    (hp : originProj p ≠ 0) : p = q := by
  refine OriginBlowup.ext hpq ?_
  have hq : q.point ≠ 0 := fun h => hp (hpq.trans h)
  rw [line_eq_span_point (p := p) hp, line_eq_span_point hq]
  exact congrArg _ (congrArg _ hpq)

/-! ### The base map vanishes on no nonempty open set -/

variable {g : Z → ComplexModel d}

theorem exists_ne_zero_of_isOpen
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ g)
    (hinv : (GermIdeal.pullback (m := m) g
      (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).IsInvertible)
    {V : Set Z} (hV : IsOpen V) (hne : V.Nonempty) : ∃ y ∈ V, g y ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨U, hU, hzU, u, hu, hune, hmem⟩ := hinv z₀
  obtain ⟨y, hy, huy⟩ := hune (V ∩ U) (hV.inter hU) inter_subset_right ⟨z₀, hz₀, hzU⟩
  refine ⟨y, hy.1, fun hgy => huy ?_⟩
  have huhol : HolomorphicAt m u y := by
    filter_upwards [hU.mem_nhds hy.2] with y' hy'
    exact (hu y' hy').mdifferentiableAt (hU.mem_nhds hy')
  have huIdeal : (GermIdeal.pullback (m := m) g
      (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).mem y u :=
    (hmem y hy.2 u).mpr (isInSpanAt_eq_iff.mpr ⟨huhol, fun _ => 1, holomorphicAt_const 1,
      Eventually.of_forall fun _ => (one_mul _).symm⟩)
  obtain ⟨c, -, hceq⟩ := exists_eq_sum_compFun_of_mem_pullback hg hgy huIdeal
  have h := hceq.self_of_nhds
  rw [h]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : compFun g i y = 0 := by rw [compFun, hgy]; simp
  rw [this, zero_mul]

/-! ### Uniqueness of lifts -/

theorem lift_eqOn (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ g)
    (hinv : (GermIdeal.pullback (m := m) g
      (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).IsInvertible)
    {W : Set Z} (hW : IsOpen W) {h₁ h₂ : Z → OriginBlowup d}
    (hc₁ : ∀ y ∈ W, ContinuousAt h₁ y) (hc₂ : ∀ y ∈ W, ContinuousAt h₂ y)
    (he₁ : ∀ y ∈ W, originProj (h₁ y) = g y) (he₂ : ∀ y ∈ W, originProj (h₂ y) = g y) :
    EqOn h₁ h₂ W := by
  by_contra hcon
  obtain ⟨y₀, hy₀W, hy₀⟩ : ∃ y, y ∈ W ∧ h₁ y ≠ h₂ y := by
    by_contra hall
    exact hcon fun y hy => by
      by_contra hne
      exact hall ⟨y, hy, hne⟩
  have hSopen : IsOpen {y | y ∈ W ∧ h₁ y ≠ h₂ y} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyW, hy⟩
    obtain ⟨A, B, hA, hB, hyA, hyB, hAB⟩ := t2_separation hy
    filter_upwards [hW.mem_nhds hyW, (hc₁ y hyW).eventually (hA.mem_nhds hyA),
      (hc₂ y hyW).eventually (hB.mem_nhds hyB)] with y' h1 h2 h3
    exact ⟨h1, fun hEq => Set.disjoint_left.mp hAB h2 (by rw [← hEq] at h3; exact h3)⟩
  obtain ⟨y, hy, hgy⟩ := exists_ne_zero_of_isOpen hg hinv hSopen ⟨y₀, hy₀W, hy₀⟩
  exact hy.2 (eq_of_originProj_eq ((he₁ y hy.1).trans (he₂ y hy.1).symm)
    (by rw [he₁ y hy.1]; exact hgy))

/-! ### Local existence of lifts -/

theorem exists_local_lift (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ g)
    (hinv : (GermIdeal.pullback (m := m) g
      (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).IsInvertible) (z₀ : Z) :
    ∃ U : Set Z, IsOpen U ∧ z₀ ∈ U ∧ ∃ φ : Z → OriginBlowup d,
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ φ y) ∧
      ∀ y ∈ U, originProj (φ y) = g y := by
  classical
  obtain ⟨U₀, hU₀, hzU₀, u, hu, hune, hmem⟩ := hinv z₀
  have huhol : ∀ y ∈ U₀, HolomorphicAt m u y := fun y hy => by
    filter_upwards [hU₀.mem_nhds hy] with y' hy'
    exact (hu y' hy').mdifferentiableAt (hU₀.mem_nhds hy')
  -- every component of `g` is a multiple of the generator `u`
  have hcomp : ∀ i : Fin d, ∃ a : Z → ℂ, HolomorphicAt m a z₀ ∧
      compFun g i =ᶠ[𝓝 z₀] fun y => a y * u y := by
    intro i
    obtain ⟨-, a, ha, heq⟩ :=
      isInSpanAt_eq_iff.mp ((hmem z₀ hzU₀ _).mp (compFun_mem_pullback hg i z₀))
    exact ⟨a, ha, heq⟩
  choose a ha haeq using hcomp
  -- the multipliers have no common zero at `z₀`
  have hexists : ∃ j, a j z₀ ≠ 0 := by
    by_cases hg0 : g z₀ = 0
    · have huIdeal : (GermIdeal.pullback (m := m) g
          (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).mem z₀ u :=
        (hmem z₀ hzU₀ u).mpr (isInSpanAt_eq_iff.mpr ⟨huhol z₀ hzU₀, fun _ => 1,
          holomorphicAt_const 1, Eventually.of_forall fun _ => (one_mul _).symm⟩)
      obtain ⟨c, hc, hceq⟩ := exists_eq_sum_compFun_of_mem_pullback hg hg0 huIdeal
      have hcontF : ContinuousAt (fun y => 1 - ∑ i, a i y * c i y) z₀ :=
        continuousAt_const.sub
          (HolomorphicAt.sum _ fun i _ => (ha i).mul (hc i)).continuousAt
      have hzero : ∀ᶠ y in 𝓝 z₀, u y * (1 - ∑ i, a i y * c i y) = 0 := by
        have hall : ∀ᶠ y in 𝓝 z₀, ∀ i, compFun g i y = a i y * u y :=
          eventually_all.mpr haeq
        filter_upwards [hceq, hall] with y hy hy'
        have hS : (∑ i, compFun g i y * c i y) = u y * ∑ i, a i y * c i y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hy' i]; ring
        rw [mul_sub, mul_one, ← hS, ← hy]
        exact sub_self _
      have hFz : (1 : ℂ) - ∑ i, a i z₀ * c i z₀ = 0 := by
        by_contra hFne
        have hev : {y | (1 - ∑ i, a i y * c i y ≠ 0) ∧
            (u y * (1 - ∑ i, a i y * c i y) = 0) ∧ y ∈ U₀} ∈ 𝓝 z₀ :=
          (hcontF.eventually (isOpen_ne.mem_nhds hFne)).and
            (hzero.and (hU₀.mem_nhds hzU₀))
        obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hev
        obtain ⟨y, hyV, huy⟩ := hune V hVopen (fun y hy => (hVsub hy).2.2) ⟨z₀, hzV⟩
        obtain ⟨hF1, hF2, -⟩ := hVsub hyV
        rcases mul_eq_zero.mp hF2 with h | h
        · exact huy h
        · exact hF1 h
      have hsum : ∑ i, a i z₀ * c i z₀ = 1 := by linear_combination -hFz
      by_contra hall
      have : ∑ i, a i z₀ * c i z₀ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [not_exists] at hall
        rw [not_not.mp (hall i), zero_mul]
      rw [this] at hsum
      exact one_ne_zero hsum.symm
    · obtain ⟨j, hj⟩ := exists_coord_ne_zero hg0
      refine ⟨j, fun h => hj ?_⟩
      have heq := (haeq j).self_of_nhds
      change g z₀ j = a j z₀ * u z₀ at heq
      rw [heq, h, zero_mul]
  obtain ⟨j, hj⟩ := hexists
  -- the neighbourhood on which the lift is defined
  have hev : {y | a j y ≠ 0 ∧ (∀ i, compFun g i y = a i y * u y) ∧
      (∀ i, HolomorphicAt m (a i) y) ∧ HolomorphicAt m (compFun g j) y} ∈ 𝓝 z₀ :=
    ((ha j).continuousAt.eventually (isOpen_ne.mem_nhds hj)).and
      ((eventually_all.mpr haeq).and
        ((eventually_all.mpr fun i => (ha i).eventually).and
          (holomorphicAt_compFun hg j z₀).eventually))
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hUopen, hzU,
    fun y => originMk j (WithLp.toLp 2 fun i =>
      if i = j then compFun g j y else a i y * (a j y)⁻¹), ?_, ?_⟩
  · intro y hy
    obtain ⟨haj, -, hahol, hgjhol⟩ := hUsub hy
    refine (contMDiff_originMk j _).comp y (contMDiffAt_toLp fun i => ?_)
    by_cases hij : i = j
    · simpa [hij] using BlowupExistenceOriginIdeal.HolomorphicAt.contMDiffAt hgjhol
    · simp only [hij, if_false]
      exact BlowupExistenceOriginIdeal.HolomorphicAt.contMDiffAt
        ((hahol i).mul (BlowupFlatCoordinates.HolomorphicAt.inv (hahol j) haj))
  · intro y hy
    obtain ⟨haj, hcomp, -, -⟩ := hUsub hy
    set w : ComplexModel d :=
      WithLp.toLp 2 fun i => if i = j then compFun g j y else a i y * (a j y)⁻¹ with hw
    have hwj : w j = compFun g j y := by rw [hw]; simp
    have hwi : ∀ i, i ≠ j → w i = a i y * (a j y)⁻¹ := by
      intro i hi; rw [hw]; simp [hi]
    ext i
    show w j * gen j w i = compFun g i y
    rw [gen_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, mul_one, hwj]
    · rw [if_neg hij, hwj, hwi i hij, hcomp j, hcomp i]
      field_simp

/-! ### The universal property -/

theorem exists_lift (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ g)
    (hinv : (GermIdeal.pullback (m := m) g
      (vanishingIdeal (n := d) ({0} : Set (ComplexModel d)))).IsInvertible) :
    ∃! h : Z → OriginBlowup d,
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ h ∧ originProj ∘ h = g := by
  classical
  choose U hU hzU φ hφsmooth hφproj using exists_local_lift hg hinv
  set Φ : Z → OriginBlowup d := fun z => φ z z with hΦ
  have key : ∀ z, ∀ y ∈ U z, Φ y = φ z y := by
    intro z y hy
    have := lift_eqOn hg hinv ((hU y).inter (hU z))
      (fun y' hy' => (hφsmooth y y' hy'.1).continuousAt)
      (fun y' hy' => (hφsmooth z y' hy'.2).continuousAt)
      (fun y' hy' => hφproj y y' hy'.1) (fun y' hy' => hφproj z y' hy'.2)
    exact this ⟨hzU y, hy⟩
  have hproj : ∀ z, originProj (Φ z) = g z := fun z => hφproj z z (hzU z)
  have hsmooth : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ Φ := by
    intro z
    refine (hφsmooth z z (hzU z)).congr_of_eventuallyEq ?_
    filter_upwards [(hU z).mem_nhds (hzU z)] with y hy
    exact key z y hy
  refine ⟨Φ, ⟨hsmooth, funext hproj⟩, ?_⟩
  rintro h ⟨hhs, hhp⟩
  refine funext fun z => ?_
  exact lift_eqOn hg hinv isOpen_univ (fun y _ => (hhs y).continuousAt)
    (fun y _ => (hsmooth y).continuousAt)
    (fun y _ => congrFun hhp y) (fun y _ => hproj y) (mem_univ z)

/-- **The blowup of `ℂᵈ` at the origin exists.**  For `d ≥ 1` the incidence variety
`OriginBlowup d`, with its projection, satisfies the universal property of the blowup. -/
theorem isBlowupAlong_originProj {d : ℕ} (hd : 0 < d) :
    IsBlowupAlong d ({0} : Set (ComplexModel d)) (originProj (d := d)) :=
  ⟨isClosedSubmanifold_zero, interior_zero_eq_empty hd, contMDiff_originProj,
    isInvertible_pullback_originProj, fun _ _ _ _ _ _ hg hinv => exists_lift hg hinv⟩

end

end Hironaka.BlowupExistenceOriginUniversal

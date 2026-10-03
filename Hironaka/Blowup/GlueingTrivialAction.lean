/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Maps acting trivially modulo an ideal, and their lifts along a blowup

Source: Włodarczyk 2005, proof of `le:homo` (4): the coordinate change `φ` satisfies `φ^*(f) - f ∈ (h) ⊆ T(𝓘)` for
every `f`, and the same holds for its lift `φ₁` to a blowup with centre in `V(T(𝓘))`, modulo the transformed ideal
`T(𝓘)₁ = 𝓘(D)⁻¹ σ^*(T(𝓘))`; in particular `φ₁` fixes `V(T(𝓘)₁) ⊇ cosupp(𝓘₁, μ)` pointwise.

* `zeroSet J`, `TrivialAt f J y` (`f` fixes `y`, is holomorphic near `y`, and `g ∘ f - g ∈ J_y` for every germ `g`).
* `le_vanishingIdeal_of_subset_zeroSet`, `pullback_le_controlledTransform`,
  `mem_zeroSet_of_mem_zeroSet_controlledTransform`.
* `sub_mem_of_coord_sub_mem` (Hadamard, several variables): if the coordinates of `a` and `b` differ by germs of `J`,
  so do `G ∘ a` and `G ∘ b`; `trivialAt_of_coords`: trivial action can be checked on the coordinates of a chart;
  `eqOn_of_eqOn_diff`: continuous maps agreeing off a set with empty interior agree.
* `isLocalEquation_monomial`: in a monomial chart `W` of the blowup, `W_j` is a local equation of the exceptional
  divisor; `extendLifted`, `mdifferentiableAt_extendLifted`, `mdifferentiableAt_of_coords`, `eq_of_monomial_eq`.
* `trivialAt_lift_of_notMem` (away from the centre: `π` is a local biholomorphism), `trivialAt_lift_of_mem` (over
  the centre: in the monomial chart `j`, with `fᵢ ∘ f - fᵢ = W_j δᵢ` for the flat coordinates `fᵢ`, the coordinates of
  `f₁` are `W_i + W_j δᵢ` and `(W_i + δᵢ)/(1 + δⱼ)`; both lift `f ∘ π`, so they agree off the exceptional divisor, hence
  everywhere), and `trivialAt_lift`: **if `f` acts trivially modulo `J` (`C ⊆ V(J)`) and `π ∘ f₁ = f ∘ π`, then `f₁`
  acts trivially modulo `σ^c(J, 1)` at every point of `V(σ^c(J, 1))`**; in particular it fixes those points.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Nat

universe u

namespace Hironaka.GlueingTrivialAction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers BlowupControlledTransform BlowupExceptionalDivisor InvertibleIdealQuotient HolomorphicTaylorTail HomogenizedGlueing

noncomputable section

/-! ### Zero sets and trivial actions -/

section Basic

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The zero set of an ideal: the points at which all its germs vanish. -/
def zeroSet (J : GermIdeal n Y) : Set Y := {y | ∀ g, J.mem y g → g y = 0}

/-- **`f` acts trivially modulo `J` at `y`**: `f` fixes `y`, is holomorphic near `y`, and `g ∘ f - g ∈ J_y` for every
germ `g` holomorphic at `y`. -/
structure TrivialAt (f : Y → Y) (J : GermIdeal n Y) (y : Y) : Prop where
  apply_eq : f y = y
  mdifferentiableAt : ∀ᶠ p in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f p
  sub_mem : ∀ g : Y → ℂ, HolomorphicAt n g y → J.mem y (fun p => g (f p) - g p)

/-- A coherent ideal vanishing on `C` lies in the ideal of `C`. -/
theorem le_vanishingIdeal_of_subset_zeroSet {J : GermIdeal n Y} (hJ : J.IsCoherent) {C : Set Y}
    (hC : C ⊆ zeroSet J) : J.Le (vanishingIdeal (n := n) C) := by
  intro y g hg
  refine ⟨holomorphicAt_of_mem hJ hg, ?_⟩
  filter_upwards [eventually_mem hJ hg] with p hp hpC
  exact hC hpC g hp

/-- A germ of a coherent ideal times a holomorphic germ is a germ of the ideal. -/
theorem mul_mem {J : GermIdeal n Y} (hJ : J.IsCoherent) {y : Y} {c g : Y → ℂ} (hc : HolomorphicAt n c y)
    (hg : J.mem y g) : J.mem y (fun p => c p * g p) :=
  HomogenizedIdeal.mem_of_isInSpanAt hJ (RelativePrincipalizationSpan.IsInSpanAt.mul_left hc
    (InvertibleIdealQuotient.isInSpanAt_self hg (holomorphicAt_of_mem hJ hg)))

end Basic

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
include hπ

/-- `π^*J ⊆ σ^c(J, μ)` (coherent `J`). -/
theorem pullback_le_controlledTransform {J : GermIdeal n X} (hJ : J.IsCoherent) (μ : ℕ) :
    (GermIdeal.pullback (m := n) π J).Le (controlledTransform hπ J μ) := by
  have hcoh := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hJ
  intro y f hf
  exact ⟨holomorphicAt_of_mem hcoh hf, fun g hg =>
    mul_mem hcoh (BlowupFunctionTransform.holomorphicAt_of_mem_idealPow hg) hf⟩

/-- `g ∘ π ∈ (π^*J)_z` for `g ∈ J_{π z}`. -/
theorem comp_mem_pullback {J : GermIdeal n X} (hJ : J.IsCoherent) {z : Y} {g : X → ℂ} (hg : J.mem (π z) g) :
    (GermIdeal.pullback (m := n) π J).mem z (g ∘ π) :=
  RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (InvertibleIdealQuotient.isInSpanAt_self ⟨g, hg, rfl⟩
      ((holomorphicAt_of_mem hJ hg).comp_contMDiff (Eventually.of_forall fun q => hπ.contMDiff q)))

/-- Germs of `σ^c(J, μ)` can be replaced by eventually equal functions (coherent `J`). -/
theorem controlledTransform_mem_congr {J : GermIdeal n X} (hJ : J.IsCoherent) {μ : ℕ} {z : Y} {f f' : Y → ℂ}
    (hf : (controlledTransform hπ J μ).mem z f) (heq : f =ᶠ[𝓝 z] f') :
    (controlledTransform hπ J μ).mem z f' := by
  have hcoh := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hJ
  refine ⟨hf.1.congr heq, fun g hg => HomogenizedIdeal.mem_congr hcoh (hf.2 g hg) ?_⟩
  filter_upwards [heq] with y hy
  rw [hy]

/-- A point of the zero set of `σ^c(J, μ)` lies over the zero set of `J`. -/
theorem mem_zeroSet_of_mem_zeroSet_controlledTransform {J : GermIdeal n X} (hJ : J.IsCoherent) {μ : ℕ} {z : Y}
    (hz : z ∈ zeroSet (controlledTransform hπ J μ)) : π z ∈ zeroSet J := fun g hg =>
  hz (g ∘ π) (pullback_le_controlledTransform hπ hJ μ z _ (comp_mem_pullback hπ hJ hg))

end Blowup

/-! ### Hadamard's lemma in several variables -/

section Hadamard

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The projection onto the coordinates `< k`. -/
def lowProj (k : ℕ) : ComplexModel n →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 fun i => if i.1 < k then w i else 0
      map_add' := fun w w' => by ext i; simp only [PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun c w => by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
                                 split_ifs <;> simp }

theorem lowProj_apply (k : ℕ) (w : ComplexModel n) (i : Fin n) :
    lowProj k w i = if i.1 < k then w i else 0 := rfl

/-- `mixCoord a b k q` agrees with `a q` in the coordinates `< k` and with `b q` in the others. -/
def mixCoord (a b : Y → ComplexModel n) (k : ℕ) (q : Y) : ComplexModel n :=
  lowProj k (a q) + (b q - lowProj k (b q))

theorem mixCoord_apply (a b : Y → ComplexModel n) (k : ℕ) (q : Y) (i : Fin n) :
    mixCoord a b k q i = if i.1 < k then a q i else b q i := by
  simp only [mixCoord, PiLp.add_apply, PiLp.sub_apply, lowProj_apply]
  split_ifs <;> ring

theorem mixCoord_zero (a b : Y → ComplexModel n) : mixCoord a b 0 = b := by
  funext q; ext i; simp [mixCoord_apply]

theorem mixCoord_n (a b : Y → ComplexModel n) : mixCoord a b n = a := by
  funext q; ext i; simp [mixCoord_apply]

theorem mixCoord_succ (a b : Y → ComplexModel n) {k : ℕ} (hk : k < n) (q : Y) :
    mixCoord a b (k + 1) q =
      mixCoord a b k q + (a q ⟨k, hk⟩ - b q ⟨k, hk⟩) • EuclideanSpace.single (⟨k, hk⟩ : Fin n) (1 : ℂ) := by
  ext i
  simp only [mixCoord_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hik : i = ⟨k, hk⟩
  · subst hik; simp
  · have hne : i.1 ≠ k := fun h => hik (Fin.ext h)
    have h0 : (EuclideanSpace.single (⟨k, hk⟩ : Fin n) (1 : ℂ)) i = 0 := by simp [hik]
    rw [h0, mul_zero, add_zero]
    by_cases h1 : i.1 < k
    · simp [h1, Nat.lt_succ_of_lt h1]
    · have h2 : ¬ i.1 < k + 1 := by omega
      simp [h1, h2]

theorem mdifferentiableAt_mixCoord {a b : Y → ComplexModel n} {q : Y}
    (ha : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) a q)
    (hb : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b q) (k : ℕ) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (mixCoord a b k) q :=
  ((lowProj k).mdifferentiableAt.comp q ha).add (hb.sub ((lowProj k).mdifferentiableAt.comp q hb))

theorem mixCoord_self {a b : Y → ComplexModel n} {z : Y} (hab : a z = b z) (k : ℕ) :
    mixCoord a b k z = b z := by
  ext i; rw [mixCoord_apply]; split_ifs <;> simp [hab]

/-- **Hadamard's lemma in several variables, along maps**: if `a z = b z` and every coordinate of `a - b` is a germ of
the coherent ideal `J` at `z`, then so is `G ∘ a - G ∘ b` for every `G` holomorphic near `b z`. -/
theorem sub_mem_of_coord_sub_mem {J : GermIdeal n Y} (hJ : J.IsCoherent) {z : Y} {a b : Y → ComplexModel n}
    (ha : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) a q)
    (hb : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) b q)
    (hab : a z = b z) {G : ComplexModel n → ℂ} (hG : ∀ᶠ w in 𝓝 (b z), DifferentiableAt ℂ G w)
    (hmem : ∀ i, J.mem z (fun q => a q i - b q i)) :
    J.mem z (fun q => G (a q) - G (b q)) := by
  choose T hT hTeq using fun i : Fin n => exists_taylor_tail hG (EuclideanSpace.single i (1 : ℂ)) 1
  have hterm : ∀ k (hk : k < n),
      J.mem z (fun q => G (mixCoord a b (k + 1) q) - G (mixCoord a b k q)) := by
    intro k hk
    set i : Fin n := ⟨k, hk⟩ with hi
    set t : Y → ℂ := fun q => a q i - b q i with ht
    set γ : Y → ComplexModel n × ℂ := fun q => (mixCoord a b k q, t q) with hγ
    have hγd : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n × ℂ) γ q := by
      filter_upwards [ha, hb] with q hq1 hq2
      have hti : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) t q :=
        (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).mdifferentiableAt).comp q hq1).sub
          (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).mdifferentiableAt).comp q hq2)
      exact (mdifferentiableAt_mixCoord hq1 hq2 k).prodMk_space hti
    have hγz : γ z = (b z, 0) := by
      simp only [hγ, ht, mixCoord_self hab, hab, sub_self]
    have hγt : Tendsto γ (𝓝 z) (𝓝 (b z, (0 : ℂ))) := by
      rw [← hγz]; exact hγd.self_of_nhds.continuousAt
    have hTγ : HolomorphicAt n (fun q => T i (γ q)) z := by
      filter_upwards [hγd, hγt.eventually (hT i)] with q hq1 hq2
      exact hq2.mdifferentiableAt.comp q hq1
    have heq : (fun q => t q * T i (γ q)) =ᶠ[𝓝 z]
        fun q => G (mixCoord a b (k + 1) q) - G (mixCoord a b k q) := by
      filter_upwards [hγt.eventually (hTeq i)] with q hq
      rw [mixCoord_succ a b hk q]
      simp only [hγ, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
        one_mul, List.replicate_zero, iterDeriv_nil, pow_zero, mul_one, pow_one] at hq
      rw [hq]
      ring
    refine HomogenizedIdeal.mem_congr hJ ?_ heq
    have := mul_mem hJ hTγ (hmem i)
    refine HomogenizedIdeal.mem_congr hJ this (Eventually.of_forall fun q => ?_)
    simp only [ht]
    ring
  have hsum : J.mem z (fun q => ∑ k ∈ Finset.range n,
      (G (mixCoord a b (k + 1) q) - G (mixCoord a b k q))) := by
    refine HomogenizedIdeal.mem_of_isInSpanAt hJ (RelativePrincipalizationSpan.IsInSpanAt.sum _ fun k hk => ?_)
    have h := hterm k (Finset.mem_range.mp hk)
    exact InvertibleIdealQuotient.isInSpanAt_self h (holomorphicAt_of_mem hJ h)
  refine HomogenizedIdeal.mem_congr hJ hsum (Eventually.of_forall fun q => ?_)
  dsimp only
  rw [Finset.sum_range_sub (fun k => G (mixCoord a b k q)) n]
  simp only [mixCoord_n, mixCoord_zero]

end Hadamard

/-! ### A criterion in coordinates; agreement off a nowhere dense set -/

section Criterion

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Trivial action from coordinates**: let `W` be holomorphic near `z` with a holomorphic left inverse `ℓ` near `W z`
(`ℓ ∘ W = id` near `z`).  If `f` fixes `z`, is holomorphic near `z`, and every coordinate of `W ∘ f - W` is a germ of the
coherent ideal `J` at `z`, then `f` acts trivially modulo `J` at `z`. -/
theorem trivialAt_of_coords {J : GermIdeal n Y} (hJ : J.IsCoherent) {f : Y → Y} {z : Y} (hfz : f z = z)
    (hfd : ∀ᶠ p in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f p)
    {W : Y → ComplexModel n} (hW : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W q)
    {ℓ : ComplexModel n → Y}
    (hℓ : ∀ᶠ w in 𝓝 (W z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ℓ w)
    (hℓW : ∀ᶠ q in 𝓝 z, ℓ (W q) = q) (hcoord : ∀ i, J.mem z (fun q => W (f q) i - W q i)) :
    TrivialAt f J z := by
  refine ⟨hfz, hfd, fun g hg => ?_⟩
  have hfc : Tendsto f (𝓝 z) (𝓝 z) := by
    have := hfd.self_of_nhds.continuousAt
    rwa [ContinuousAt, hfz] at this
  have hWc : Tendsto W (𝓝 z) (𝓝 (W z)) := hW.self_of_nhds.continuousAt
  have hℓz : ℓ (W z) = z := hℓW.self_of_nhds
  have hℓc : Tendsto ℓ (𝓝 (W z)) (𝓝 z) := by
    have := hℓ.self_of_nhds.continuousAt
    rwa [ContinuousAt, hℓz] at this
  -- `G = g ∘ ℓ` is holomorphic near `W z`
  have hG : ∀ᶠ w in 𝓝 (W z), DifferentiableAt ℂ (g ∘ ℓ) w := by
    filter_upwards [hℓ, hℓc.eventually hg] with w hw1 hw2
    exact mdifferentiableAt_iff_differentiableAt.mp (hw2.comp w hw1)
  have hWf : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (W ∘ f) q := by
    filter_upwards [hfd, hfc.eventually hW] with q hq1 hq2
    exact hq2.comp q hq1
  have h := sub_mem_of_coord_sub_mem hJ hWf hW (by simp [hfz]) hG hcoord
  refine HomogenizedIdeal.mem_congr hJ h ?_
  filter_upwards [hℓW, hfc.eventually hℓW] with q hq1 hq2
  simp only [Function.comp_apply, hq1, hq2]

/-- **Agreement off a nowhere dense set**: continuous maps into a Hausdorff space that agree on `V \ S`, `V` open and
`S` with empty interior, agree on `V`. -/
theorem eqOn_of_eqOn_diff {Z : Type*} [TopologicalSpace Z] [T2Space Z] {g₁ g₂ : Y → Z} {V S : Set Y}
    (hV : IsOpen V) (hS : interior S = ∅) (h₁ : ContinuousOn g₁ V) (h₂ : ContinuousOn g₂ V)
    (heq : ∀ q ∈ V, q ∉ S → g₁ q = g₂ q) : EqOn g₁ g₂ V := by
  refine EqOn.of_subset_closure (s := V \ S) (fun q hq => heq q hq.1 hq.2) h₁ h₂ sdiff_subset ?_
  intro q hq
  rw [mem_closure_iff]
  intro N hN hqN
  by_contra hdisj
  rw [not_nonempty_iff_eq_empty] at hdisj
  have hsub : N ∩ V ⊆ S := fun p hp => by
    by_contra hpS
    have : p ∈ N ∩ (V \ S) := ⟨hp.1, hp.2, hpS⟩
    rw [hdisj] at this
    exact this
  have := interior_maximal hsub (hN.inter hV)
  rw [hS] at this
  exact this ⟨hqN, hq⟩

end Criterion

/-! ### The lift away from the centre -/

section OffCentre

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
include hπ

/-- **The lift of a trivially acting map acts trivially, away from the centre**: if `π ∘ f₁ = f ∘ π` near `z`,
`π z ∉ C` and `f` acts trivially modulo `J` at `π z`, then `f₁` acts trivially modulo `σ^c(J, 1)` at `z`. -/
theorem trivialAt_lift_of_notMem {J : GermIdeal n X} (hJ : J.IsCoherent) {f : X → X} {f₁ : Y → Y} {z : Y}
    (hz : π z ∉ C) (hf₁d : ∀ᶠ p in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁ p)
    (hcomm : ∀ᶠ p in 𝓝 z, π (f₁ p) = f (π p)) (htriv : TrivialAt f J (π z)) :
    TrivialAt f₁ (controlledTransform hπ J 1) z := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hf₁z : f₁ z = z := by
    have h1 : π (f₁ z) = π z := by rw [hcomm.self_of_nhds, htriv.apply_eq]
    have hz1 : π (f₁ z) ∈ Cᶜ := by rw [h1]; exact hz
    calc f₁ z = s ⟨π (f₁ z), hz1⟩ := (hsec (f₁ z) hz1).symm
      _ = s ⟨π z, hz⟩ := congrArg s (Subtype.ext h1)
      _ = z := hsec z hz
  refine ⟨hf₁z, hf₁d, fun g hg => ?_⟩
  -- `g = G ∘ π` near `z`, with `G = g ∘ s` holomorphic at `π z`
  set G : X → ℂ := extendOpens (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) (g ∘ s) with hGdef
  have hsz : s ⟨π z, hz⟩ = z := hsec z hz
  have hGh : HolomorphicAt n G (π z) := by
    have h1 : HolomorphicAt n (g ∘ s) (⟨π z, hz⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)) := by
      have : HolomorphicAt n g (s ⟨π z, hz⟩) := by rw [hsz]; exact hg
      exact this.comp_contMDiff (Eventually.of_forall fun q => hs q)
    exact (holomorphicAt_iff_extendOpens _).mp h1
  have hGπ : ∀ᶠ p in 𝓝 z, G (π p) = g p := by
    filter_upwards [(hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hz] with p hp
    rw [hGdef, show π p = ((⟨π p, hp⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)) : X) from rfl,
      extendOpens_val]
    exact congrArg g (hsec p hp)
  have hfc : Tendsto f₁ (𝓝 z) (𝓝 z) := by
    have := hf₁d.self_of_nhds.continuousAt
    rwa [ContinuousAt, hf₁z] at this
  have h1 := comp_mem_pullback hπ hJ (htriv.sub_mem G hGh)
  have h2 := pullback_le_controlledTransform hπ hJ 1 z _ h1
  refine controlledTransform_mem_congr hπ hJ h2 ?_
  filter_upwards [hGπ, hfc.eventually hGπ, hcomm] with p hp1 hp2 hp3
  simp only [Function.comp_apply]
  rw [← hp1, ← hp2, hp3]

end OffCentre

/-! ### Monomial charts -/

section Monomial

open BlowupFlatCoordinates BlowupMonomialCharts BlowupFunctionTransform

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
  {y₀ : X} {Φf : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}
  (hΦt : Φf.source ⊆ (chartAt (ComplexModel n) y₀).target)
  (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φf.source →
        (y ∈ C ↔ Φf.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))

include hπ hΦt hflat in
/-- **In a monomial chart, `W_j` is a local equation of the exceptional divisor.** -/
theorem isLocalEquation_monomial {j : Fin n} (hj : k ≤ j.1) {O : Set Y} (hO : IsOpen O)
    {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWeq : ∀ z' ∈ O, π z' ∈ flatDomain Φf ∧
      monomial k j (W z') = Φf.toFun (chartAt (ComplexModel n) y₀ (π z'))) :
    IsLocalEquation hπ O (fun p => W p j) := by
  classical
  have hπs := hπ.contMDiff
  have hWj : ∀ q ∈ O, W q j = flatCoord Φf j (π q) := fun q hq => by
    show W q j = Φf.toFun (chartAt (ComplexModel n) y₀ (π q)) j
    rw [← (hWeq q hq).2, monomial_apply]
    simp
  have hcoord : ∀ i : Fin n, ∀ q ∈ O, HolomorphicAt n (fun p => W p i) q := fun i q hq => by
    filter_upwards [hO.mem_nhds hq] with q' hq'
    exact (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
      q' (hWs q' hq')).mdifferentiableAt (by simp))
  refine ⟨hO, fun q hq => (hcoord j q hq).self_of_nhds.mdifferentiableWithinAt, fun V hVo hVO hV => ?_,
    fun p hp g => ?_⟩
  · by_contra hall
    push Not at hall
    have hsub : V ⊆ π ⁻¹' C := fun p hp => by
      have hpO := hVO hp
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hWeq p hpO
      refine (hflat hp1 hp2).mpr ?_
      rw [← hp3]
      intro i hi
      rw [monomial_apply, hall p hp]
      split_ifs with h
      · ring
      · have : i = j := by by_contra hne; exact h ⟨hi, hne⟩
        rw [this, hall p hp]
    have := interior_maximal hsub hVo
    rw [ExceptionalFibres.interior_preimage_eq_empty hπ] at this
    obtain ⟨p, hp⟩ := hV
    exact this hp
  · rw [exceptionalDivisor_ideal]
    constructor
    · intro hg
      refine IsInSpanAt.of_forall_eq_mul ?_ (show IsInSpanAt (n := n)
        (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π) p g from hg)
      rintro s ⟨a, ha, rfl⟩
      obtain ⟨bb, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φf hΦt hflat (hWeq p hp).1 ha
      refine ⟨fun q => ∑ i, bb i (π q) * (if i = j then 1 else W q i), ?_, ?_⟩
      · refine HolomorphicAt.sum _ fun i _ => ?_
        refine ((hbh i).comp_contMDiff (Eventually.of_forall fun q => hπs q)).mul ?_
        split_ifs
        · exact holomorphicAt_const 1
        · exact hcoord i p hp
      · filter_upwards [(hπs p).continuousAt.eventually hbeq, hO.mem_nhds hp] with q hq hqO
        simp only [Function.comp_apply, hq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfc : flatCoord Φf i (π q) = monomial k j (W q) i := by
          show Φf.toFun (chartAt (ComplexModel n) y₀ (π q)) i = _
          rw [← (hWeq q hqO).2]
        rw [hfc, monomial_apply]
        by_cases hki : k ≤ i.1
        · by_cases hij : i = j
          · subst hij; simp
          · simp [hki, hij]; ring
        · have : bb i = 0 := hb0 i (by omega)
          simp [this]
    · intro hg
      obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
      show IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧ s = a ∘ π)
        p g
      refine isInSpanAt_of_eq_mul ⟨flatCoord Φf j,
        flatCoord_mem_vanishingIdeal Φf hflat hj (hWeq p hp).1, rfl⟩ hgh hc ?_
      filter_upwards [hgc, hO.mem_nhds hp] with q hq hqO
      rw [hq, Function.comp_apply, hWj q hqO]

end Monomial

open scoped Classical in
/-- The map `w ↦ ℓ(w)` on the model space, from a map `ℓ` on a lifted open subset (extended by a constant). -/
def extendLifted {n : ℕ} {S : Opens (ComplexModel n)} {Z : Type*} (ℓ : LiftedOpen.{u} S → Z) {w₀ : ComplexModel n}
    (hw₀ : w₀ ∈ S) (w : ComplexModel n) : Z :=
  if h : w ∈ S then ℓ (LiftedOpen.mk S w h) else ℓ (LiftedOpen.mk S w₀ hw₀)

theorem extendLifted_of_mem {n : ℕ} {S : Opens (ComplexModel n)} {Z : Type*} (ℓ : LiftedOpen.{u} S → Z)
    {w₀ : ComplexModel n} (hw₀ : w₀ ∈ S) {w : ComplexModel n} (hw : w ∈ S) :
    extendLifted ℓ hw₀ w = ℓ (LiftedOpen.mk S w hw) := by
  classical
  simp only [extendLifted, dif_pos hw]

/-- `extendLifted ℓ` is holomorphic at the points of `S` when `ℓ` is. -/
theorem mdifferentiableAt_extendLifted {n : ℕ} {S : Opens (ComplexModel n)} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] {ℓ : LiftedOpen.{u} S → Z}
    (hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ) {w₀ : ComplexModel n} (hw₀ : w₀ ∈ S)
    {w : ComplexModel n} (hw : w ∈ S) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (extendLifted ℓ hw₀) w := by
  classical
  set mk' : ComplexModel n → LiftedOpen.{u} S :=
    fun v => if h : v ∈ S then LiftedOpen.mk S v h else LiftedOpen.mk S w₀ hw₀ with hmk'
  have hmkd : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ mk' w := by
    refine LiftedOpen.contMDiffAt_of_toModel S ?_
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [S.isOpen.mem_nhds hw] with v hv
    have hv' : v ∈ S := hv
    simp [hmk', hv']
  have heq : extendLifted ℓ hw₀ = ℓ ∘ mk' := by
    funext v
    by_cases hv : v ∈ S
    · rw [extendLifted_of_mem ℓ hw₀ hv, Function.comp_apply, hmk']
      dsimp only
      rw [dif_pos hv]
    · simp [extendLifted, hmk', hv]
  rw [heq]
  exact ((hℓ (mk' w)).comp w hmkd).mdifferentiableAt (by simp)

/-- A map into `ℂⁿ` is holomorphic at `q` when its coordinates are. -/
theorem mdifferentiableAt_of_coords {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {F : Y → ComplexModel n} {q : Y}
    (h : ∀ i, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fun p => F p i) q) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F q := by
  have hF : F = fun p => ∑ i, (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))) (F p i) := by
    funext p
    ext l
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.single]
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [hF]
  have : (fun p => ∑ i, (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))) (F p i)) = ∑ i, fun p => (ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℂ ℂ) (EuclideanSpace.single i (1 : ℂ))) (F p i) := by
    funext p; simp
  rw [this]
  exact MDifferentiableAt.sum fun i _ =>
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (EuclideanSpace.single i (1 : ℂ))).mdifferentiableAt.comp
      q (h i)

/-- The monomial map is injective on points with nonzero `j`-th coordinate. -/
theorem eq_of_monomial_eq {n k : ℕ} {j : Fin n} {a b : ComplexModel n}
    (h : BlowupMonomialCharts.monomial k j a = BlowupMonomialCharts.monomial k j b) (hb : b j ≠ 0) : a = b := by
  have hjj : a j = b j := by
    have := congrArg (fun w : ComplexModel n => w j) h
    simpa [BlowupMonomialCharts.monomial_apply] using this
  ext i
  have hi := congrArg (fun w : ComplexModel n => w i) h
  simp only [BlowupMonomialCharts.monomial_apply] at hi
  split_ifs at hi with hc
  · rw [hjj] at hi
    exact mul_right_cancel₀ hb hi
  · exact hi

/-! ### The lift over the centre -/

section Centre

open BlowupFlatCoordinates BlowupMonomialCharts BlowupFunctionTransform

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
include hπ

/-- **The lift of a trivially acting map acts trivially, over the centre** (Włodarczyk, proof of `le:homo` (4), the
computation in the monomial chart): let `J` be coherent with `C ⊆ V(J)`, `f` act trivially modulo `J` at `π z ∈ C`,
`f` preserve `X \ C` near `π z`, and `f₁` be holomorphic near `z` with `π ∘ f₁ = f ∘ π`.  If `z ∈ V(σ^c(J, 1))`, then
`f₁` acts trivially modulo `σ^c(J, 1)` at `z`. -/
theorem trivialAt_lift_of_mem {J : GermIdeal n X} (hJ : J.IsCoherent) (hCJ : C ⊆ zeroSet J)
    {f : X → X} {f₁ : Y → Y} {z : Y} (hz : π z ∈ C)
    (hzJ : z ∈ zeroSet (controlledTransform hπ J 1))
    (hf₁d : ∀ᶠ p in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁ p)
    (hcomm : ∀ᶠ p in 𝓝 z, π (f₁ p) = f (π p))
    (hfC : ∀ᶠ y in 𝓝 (π z), y ∉ C → f y ∉ C)
    (htriv : TrivialAt f J (π z)) :
    TrivialAt f₁ (controlledTransform hπ J 1) z := by
  classical
  have hπs := hπ.contMDiff
  obtain ⟨k, hk⟩ := hπ.1.2 (π z) hz
  obtain ⟨-, -, Φf, hΦt, -, hflat⟩ := hk
  have hy₀ : π z ∈ flatDomain Φf := ⟨mem_chart_source _ (π z), Φf.center_mem_source⟩
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓall, -⟩ :=
    BlowupLocalSurjectivity.exists_monomialLocalInverse hπ hΦt hflat hy₀
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ hΦt hflat hj
  have hh := isLocalEquation_monomial hπ hΦt hflat hj hO hWs hWeq
  have hJC : J.Le (vanishingIdeal (n := n) C) := le_vanishingIdeal_of_subset_zeroSet hJ hCJ
  have hJC1 : J.Le (idealPow (vanishingIdeal (n := n) C) 1) := fun y g hg =>
    BlowupDerivativeIdeal.mem_idealPow_one_of_mem (fun _ _ h => h.1) (hJC y g hg)
  have hJ1 : (controlledTransform hπ J 1).IsCoherent := isCoherent_controlledTransform hπ hJ hJC1
  -- the differences of the flat coordinates and their controlled transforms `δᵢ`
  have hΔ : ∀ i, J.mem (π z) (fun y => flatCoord Φf i (f y) - flatCoord Φf i y) := fun i =>
    htriv.sub_mem _ (holomorphicAt_flatCoord Φf i hy₀)
  have hδex : ∀ i, ∃ d : Y → ℂ, HolomorphicAt n d z ∧
      ((fun y => flatCoord Φf i (f y) - flatCoord Φf i y) ∘ π) =ᶠ[𝓝 z] (fun p => W p j ^ 1 * d p) :=
    fun i => exists_eq_pow_mul hh hzO (hJC1 _ _ (hΔ i))
  choose δ hδh hδeq using hδex
  have hδJ : ∀ i, (controlledTransform hπ J 1).mem z (δ i) := fun i =>
    mem_controlledTransform_of_eq_pow_mul hh hzO (hΔ i) (hδh i) (hδeq i)
  have hδz : ∀ i, δ i z = 0 := fun i => hzJ _ (hδJ i)
  -- the candidate coordinates of `f₁`
  set G : Y → ComplexModel n := fun q => WithLp.toLp 2 fun i =>
    if k ≤ i.1 ∧ i ≠ j then (W q i + δ i q) / (1 + δ j q) else W q i + W q j * δ i q with hGdef
  have hGi : ∀ q i, G q i =
      if k ≤ i.1 ∧ i ≠ j then (W q i + δ i q) / (1 + δ j q) else W q i + W q j * δ i q := fun q i => rfl
  have hGz : G z = W z := by
    ext i; rw [hGi]; split_ifs <;> simp [hδz]
  have hWhol : ∀ i, ∀ q ∈ O, HolomorphicAt n (fun p => W p i) q := fun i q hq => by
    filter_upwards [hO.mem_nhds hq] with q' hq'
    exact (((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).contMDiff.contMDiffAt.comp
      q' (hWs q' hq')).mdifferentiableAt (by simp))
  have hWd : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W q := by
    filter_upwards [hO.mem_nhds hzO] with q hq
    exact (hWs q hq).mdifferentiableAt (by simp)
  have hden : HolomorphicAt n (fun q => 1 + δ j q) z := (holomorphicAt_const 1).add (hδh j)
  have hden0 : (1 : ℂ) + δ j z ≠ 0 := by simp [hδz]
  have hinv : HolomorphicAt n (fun q => (1 + δ j q)⁻¹) z := BlowupFlatCoordinates.HolomorphicAt.inv hden hden0
  have hGhol : ∀ i, HolomorphicAt n (fun q => G q i) z := by
    intro i
    by_cases hc : k ≤ i.1 ∧ i ≠ j
    · have : (fun q => G q i) = fun q => (W q i + δ i q) * (1 + δ j q)⁻¹ := by
        funext q; rw [hGi, if_pos hc, div_eq_mul_inv]
      rw [this]
      exact ((hWhol i z hzO).add (hδh i)).mul hinv
    · have : (fun q => G q i) = fun q => W q i + W q j * δ i q := by
        funext q; rw [hGi, if_neg hc]
      rw [this]
      exact (hWhol i z hzO).add ((hWhol j z hzO).mul (hδh i))
  have hGd : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) G q := by
    filter_upwards [eventually_all.2 hGhol] with q hq
    exact mdifferentiableAt_of_coords hq
  -- `f` near `π z`
  have hfc : Tendsto f (𝓝 (π z)) (𝓝 (π z)) := by
    have := htriv.mdifferentiableAt.self_of_nhds.continuousAt
    rwa [ContinuousAt, htriv.apply_eq] at this
  have hπc : Tendsto π (𝓝 z) (𝓝 (π z)) := hπs.continuous.tendsto z
  have hfflat : ∀ᶠ q in 𝓝 z, f (π q) ∈ flatDomain Φf :=
    hπc.eventually (hfc.eventually ((isOpen_flatDomain Φf).mem_nhds hy₀))
  have hden_ne : ∀ᶠ q in 𝓝 z, (1 : ℂ) + δ j q ≠ 0 :=
    hden.self_of_nhds.continuousAt.eventually_ne hden0
  -- the key identity `σⱼ(G) = flat coordinates of f ∘ π`
  have hkey : ∀ᶠ q in 𝓝 z,
      monomial k j (G q) = Φf.toFun (chartAt (ComplexModel n) (π z) (f (π q))) := by
    filter_upwards [hO.mem_nhds hzO, eventually_all.2 fun i => hδeq i, hden_ne] with q hqO hqδ hqd
    ext i
    have h1 : Φf.toFun (chartAt (ComplexModel n) (π z) (f (π q))) i =
        monomial k j (W q) i + W q j * δ i q := by
      have h2 := hqδ i
      simp only [Function.comp_apply, pow_one] at h2
      have h3 : monomial k j (W q) i = flatCoord Φf i (π q) := by
        show monomial k j (W q) i = Φf.toFun (chartAt (ComplexModel n) (π z) (π q)) i
        rw [(hWeq q hqO).2]
      rw [h3]
      show flatCoord Φf i (f (π q)) = _
      linear_combination h2
    rw [h1, monomial_apply, monomial_apply, hGi, hGi q j, if_neg (fun h : k ≤ j.1 ∧ j ≠ j => h.2 rfl)]
    split_ifs with hc
    · field_simp
    · ring
  -- the lift through the monomial chart
  have hWmem : ∀ q ∈ O, W q ∈ monomialDomain Φf k j := fun q hq => by
    show monomial k j (W q) ∈ Φf.target
    rw [(hWeq q hq).2]; exact Φf.mapsTo_toFun (hWeq q hq).1.2
  set ℓ' : ComplexModel n → Y := extendLifted ℓ (hWmem z hzO) with hℓ'def
  have hℓ'W : ∀ q ∈ O, ℓ' (W q) = q := fun q hq => by
    rw [hℓ'def, extendLifted_of_mem ℓ _ (hWmem q hq)]
    exact hℓall ℓ hℓs hℓπ q hq (hWmem q hq)
  have hGmem : ∀ᶠ q in 𝓝 z, G q ∈ monomialDomain Φf k j := by
    filter_upwards [hkey, hfflat] with q hq1 hq2
    show monomial k j (G q) ∈ Φf.target
    rw [hq1]; exact Φf.mapsTo_toFun hq2.2
  have hπL : ∀ᶠ q in 𝓝 z, π (ℓ' (G q)) = f (π q) := by
    filter_upwards [hkey, hfflat, hGmem] with q hq1 hq2 hq3
    rw [hℓ'def, extendLifted_of_mem ℓ _ hq3]
    have h4 : π (ℓ (LiftedOpen.mk _ (G q) hq3)) = monomialChart Φf k j (LiftedOpen.mk _ (G q) hq3) :=
      congrFun hℓπ _
    rw [h4]
    simp only [monomialChart, LiftedOpen.toModel_mk]
    rw [hq1]
    exact flatInverse_flat Φf hq2
  have hLd : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (ℓ' ∘ G) q := by
    filter_upwards [hGd, hGmem] with q hq1 hq2
    exact (mdifferentiableAt_extendLifted hℓs (hWmem z hzO) hq2).comp q hq1
  -- `f₁ = ℓ' ∘ G` near `z`: both lift `f ∘ π`, and agree off the exceptional divisor
  have hinj := (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.injOn
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp (hf₁d.and (hLd.and (hcomm.and (hπL.and
    (hπc.eventually hfC)))))
  have hEq : EqOn f₁ (ℓ' ∘ G) V := by
    refine eqOn_of_eqOn_diff hVo (ExceptionalFibres.interior_preimage_eq_empty hπ)
      (fun q hq => (hVsub hq).1.continuousAt.continuousWithinAt)
      (fun q hq => (hVsub hq).2.1.continuousAt.continuousWithinAt) fun q hq hqC => ?_
    obtain ⟨-, -, h1, h2, h3⟩ := hVsub hq
    have hfq : f (π q) ∉ C := h3 hqC
    refine hinj ?_ ?_ (h1.trans h2.symm)
    · show π (f₁ q) ∈ Cᶜ; rw [h1]; exact hfq
    · show π (ℓ' (G q)) ∈ Cᶜ; rw [h2]; exact hfq
  have hf₁z : f₁ z = z := by
    rw [hEq hzV, Function.comp_apply, hGz]
    exact hℓ'W z hzO
  have hf₁c : Tendsto f₁ (𝓝 z) (𝓝 z) := by
    have := hf₁d.self_of_nhds.continuousAt
    rwa [ContinuousAt, hf₁z] at this
  -- `W ∘ f₁ = G` near `z`
  have hWf₁d : ∀ᶠ q in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (W ∘ f₁) q := by
    filter_upwards [hf₁d, hf₁c.eventually hWd] with q hq1 hq2
    exact hq2.comp q hq1
  obtain ⟨V₂, hV₂sub, hV₂o, hzV₂⟩ := mem_nhds_iff.mp (hWf₁d.and (hGd.and ((hf₁c.eventually
    (hO.mem_nhds hzO)).and (hkey.and (hcomm.and (hden_ne.and (hO.mem_nhds hzO)))))))
  have hEq₂ : EqOn (W ∘ f₁) G V₂ := by
    refine eqOn_of_eqOn_diff hV₂o (ExceptionalFibres.interior_preimage_eq_empty hπ)
      (fun q hq => (hV₂sub hq).1.continuousAt.continuousWithinAt)
      (fun q hq => (hV₂sub hq).2.1.continuousAt.continuousWithinAt) fun q hq hqC => ?_
    obtain ⟨-, -, hf₁O, hk1, hc1, hd1, hqO⟩ := hV₂sub hq
    -- `W q j ≠ 0` off the exceptional divisor
    have hWj : W q j ≠ 0 := by
      intro h0
      apply hqC
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hWeq q hqO
      refine (hflat hp1 hp2).mpr ?_
      change Φf.toFun (chartAt (ComplexModel n) (π z) (π q)) ∈ _
      rw [← hp3]
      intro i hi
      rw [monomial_apply]
      split_ifs with hc
      · rw [h0, mul_zero]
      · have : i = j := by by_contra hne; exact hc ⟨hi, hne⟩
        rw [this, h0]
    have hGj : G q j ≠ 0 := by
      rw [hGi, if_neg (fun h : k ≤ j.1 ∧ j ≠ j => h.2 rfl)]
      have : W q j + W q j * δ j q = W q j * (1 + δ j q) := by ring
      rw [this]
      exact mul_ne_zero hWj hd1
    refine eq_of_monomial_eq (k := k) ?_ hGj
    rw [Function.comp_apply, (hWeq _ hf₁O).2, hc1, hk1]
  -- the coordinates of `f₁` differ from those of the identity by germs of `σ^c(J, 1)`
  have hcoord : ∀ i, (controlledTransform hπ J 1).mem z (fun q => W (f₁ q) i - W q i) := by
    intro i
    have hev : (fun q => G q i - W q i) =ᶠ[𝓝 z] fun q => W (f₁ q) i - W q i := by
      filter_upwards [hV₂o.mem_nhds hzV₂] with q hq
      rw [show W (f₁ q) = G q from hEq₂ hq]
    refine HomogenizedIdeal.mem_congr hJ1 ?_ hev
    by_cases hc : k ≤ i.1 ∧ i ≠ j
    · have hev' : (fun q => (1 + δ j q)⁻¹ * δ i q + (-(W q i) * (1 + δ j q)⁻¹) * δ j q) =ᶠ[𝓝 z]
          fun q => G q i - W q i := by
        filter_upwards [hden_ne] with q hq
        rw [hGi, if_pos hc]
        field_simp
        ring
      refine HomogenizedIdeal.mem_congr hJ1 ?_ hev'
      refine HomogenizedIdeal.mem_of_isInSpanAt hJ1 (RelativePrincipalizationSpan.IsInSpanAt.add ?_ ?_)
      · exact RelativePrincipalizationSpan.IsInSpanAt.mul_left hinv
          (InvertibleIdealQuotient.isInSpanAt_self (hδJ i) (hδh i))
      · exact RelativePrincipalizationSpan.IsInSpanAt.mul_left
          (((holomorphicAt_const (-1)).mul (hWhol i z hzO)).mul hinv |>.congr
            (Eventually.of_forall fun q => by ring))
          (InvertibleIdealQuotient.isInSpanAt_self (hδJ j) (hδh j))
    · have hev' : (fun q => W q j * δ i q) = fun q => G q i - W q i := by
        funext q; rw [hGi, if_neg hc]; ring
      rw [← hev']
      exact mul_mem hJ1 (hWhol j z hzO) (hδJ i)
  -- conclusion
  have hℓd : ∀ᶠ w in 𝓝 (W z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ℓ' w := by
    filter_upwards [(monomialDomain Φf k j).isOpen.mem_nhds (hWmem z hzO)] with w hw
    exact mdifferentiableAt_extendLifted hℓs (hWmem z hzO) hw
  exact trivialAt_of_coords hJ1 hf₁z hf₁d hWd hℓd
    (Filter.mem_of_superset (hO.mem_nhds hzO) fun q hq => hℓ'W q hq) hcoord

/-- **Trivial action lifts to the blowup** (Włodarczyk, proof of `le:homo` (4)): let `J` be coherent with `C ⊆ V(J)`,
`f` act trivially modulo `J` at `π z` and preserve `X \ C` near `π z`, and `f₁` be holomorphic near `z` with
`π ∘ f₁ = f ∘ π`.  If `z ∈ V(σ^c(J, 1))`, then `f₁` acts trivially modulo `σ^c(J, 1)` at `z`; in particular it fixes
`z`. -/
theorem trivialAt_lift {J : GermIdeal n X} (hJ : J.IsCoherent) (hCJ : C ⊆ zeroSet J)
    {f : X → X} {f₁ : Y → Y} {z : Y} (hzJ : z ∈ zeroSet (controlledTransform hπ J 1))
    (hf₁d : ∀ᶠ p in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f₁ p)
    (hcomm : ∀ᶠ p in 𝓝 z, π (f₁ p) = f (π p))
    (hfC : ∀ᶠ y in 𝓝 (π z), y ∉ C → f y ∉ C)
    (htriv : TrivialAt f J (π z)) :
    TrivialAt f₁ (controlledTransform hπ J 1) z := by
  by_cases hz : π z ∈ C
  · exact trivialAt_lift_of_mem hπ hJ hCJ hz hzJ hf₁d hcomm hfC htriv
  · exact trivialAt_lift_of_notMem hπ hJ hz hf₁d hcomm htriv

end Centre

end

end Hironaka.GlueingTrivialAction

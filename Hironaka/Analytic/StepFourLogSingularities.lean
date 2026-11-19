import Hironaka.Analytic.ExcessIdealPrincipalization
import Hironaka.Analytic.CoherentIdealWeight
import Hironaka.Analytic.MeteredDivisorWeightBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 4: `φ'` has log singularities along `D|_W`

Source: Copy-4, `prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1869-1892`):

> `D := (1/M) G̃_M + ((C-1)/M) P^mov + (C/M) P^F + τ E_rel` [...] Since total transforms
> commute with restriction to strict transforms, `eq:GB-decomposition`, `eq:Pmov-restriction`
> and `eq:PF-restriction` give `D|_W = (1/ℓ) G_B + τ E_rel|_W` (`eq:DL-restriction`) [...]
> Since `φ_{K,ℓ}` has analytic singularities of type `(ℓ^{-1}, 𝔅)` and `𝔅 𝒪_W = 𝒪_W(-G_B)` is
> invertible, the function `φ' := (π|_W)^* φ_{K,ℓ} + τ ψ_{E_rel}|_W` has log singularities along
> `D|_W` with the restricted metric.

This is the field `hlog` of `PrincipalizationStepOneInterface.Copy4StepOneData`.

## Main results

* `sameSingularityTypeOn_stepFourWeights` — **`eq:DL-restriction` at the level of weights.**
  On the final model `π : Y → X`, with the ideal identities of the three stages
  (`G̃_M`'s ideal is `𝔥^q 𝔓`, and `Res_W(𝔅̃ 𝒪_Y) = Res_W(𝔥^r 𝔓 · 𝒪(-(P^F + P^F')))` from
  `ExcessIdealPrincipalization`), where `𝔥 = 𝒪(-(H^fix + H'))`, `𝔓 = 𝒪(-(P^mov + P'))` and the
  remainders `H'`, `P'`, `P^F'` are disjoint from `W`: for every weight `ψ_𝔅` of `𝔅̃` and all
  metrics of `G̃_M`, `P^mov`, `P^F`,
  `(C/M) ψ_𝔅 ∘ π = (1/M) ψ_{G̃_M} + ((C-1)/M) ψ_{P^mov} + (C/M) ψ_{P^F} + O(1)` on `W`,
  whenever `q = C r` (Copy-4: `q = M/m`, `r = ℓ/m`, `M = Cℓ`).  The coefficient identity is
  `eq:GB-decomposition`; it is checked on extended reals, `-∞` included.
* `logSingularitiesOfSameSingularityType` — two weights of the same singularity
  type, one of them `ψ_D`, give `HasLogSingularitiesAlong D` (the residual is constructed).
* `stepFourLogSingularities` — **the field `hlog`**: if `φ_K ∘ ι_V` has the singularity
  type of `(C/M) ψ_𝔅` on `V` (Copy-4: `φ_{K,ℓ}` of type `(ℓ^{-1}, 𝔅)`, `𝔅 = 𝔅̃|_V`), then
  `φ' = φ_K ∘ π|_W + τ ψ_E|_W` has log singularities along `D|_W`.

Sorry-free.  `φ_K` (the quasi-equisingular approximation) and `𝔅̃` are parameters.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFourLogSingularities

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  Hironaka.BlowupSequences RelativePrincipalizationSpan RestrictedIdealWeight
  IdealWeightPowers IdealWeightComparison GermIdealPullbackCalculus DivisorMetric
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction
  StepFiveAssemblyOfStepOneStepFour

noncomputable section

/-! ### Additive comparisons on extended reals -/

section Algebra

variable {Y : Type*}

/-- Two additive comparisons add. -/
theorem sameSingularityTypeOn_add {u₁ v₁ u₂ v₂ : Y → EReal} {S : Set Y}
    (h₁ : SameSingularityTypeOn u₁ v₁ S) (h₂ : SameSingularityTypeOn u₂ v₂ S) :
    SameSingularityTypeOn (fun y => u₁ y + u₂ y) (fun y => v₁ y + v₂ y) S := by
  have key : ∀ {u₁ v₁ u₂ v₂ : Y → EReal}, MoreSingularOn u₁ v₁ S → MoreSingularOn u₂ v₂ S →
      MoreSingularOn (fun y => u₁ y + u₂ y) (fun y => v₁ y + v₂ y) S := by
    intro u₁ v₁ u₂ v₂ ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩
    refine ⟨C₁ + C₂, fun y hy => ?_⟩
    calc u₁ y + u₂ y ≤ (v₁ y + (C₁ : EReal)) + (v₂ y + (C₂ : EReal)) :=
          add_le_add (hC₁ y hy) (hC₂ y hy)
      _ = (v₁ y + v₂ y) + ((C₁ + C₂ : ℝ) : EReal) := by
          rw [EReal.coe_add]
          abel
  exact ⟨key h₁.1 h₂.1, key h₁.2 h₂.2⟩

/-- An additive comparison survives multiplication by a nonnegative real. -/
theorem sameSingularityTypeOn_const_mul {u v : Y → EReal} {S : Set Y}
    (h : SameSingularityTypeOn u v S) {c : ℝ} (hc : 0 ≤ c) :
    SameSingularityTypeOn (fun y => (c : EReal) * u y) (fun y => (c : EReal) * v y) S := by
  have key : ∀ {u v : Y → EReal}, MoreSingularOn u v S →
      MoreSingularOn (fun y => (c : EReal) * u y) (fun y => (c : EReal) * v y) S := by
    intro u v ⟨C, hC⟩
    refine ⟨c * C, fun y hy => ?_⟩
    calc (c : EReal) * u y ≤ (c : EReal) * (v y + (C : EReal)) :=
          mul_le_mul_of_nonneg_left (hC y hy) (EReal.coe_nonneg.mpr hc)
      _ = (c : EReal) * v y + ((c * C : ℝ) : EReal) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc)
            (EReal.coe_ne_top _), ← EReal.coe_mul]
  exact ⟨key h.1, key h.2⟩

/-- `b` is bounded on `S` by a finite constant, two-sidedly. -/
def IsBoundedOn (b : Y → EReal) (S : Set Y) : Prop :=
  ∃ B : ℝ, ∀ y ∈ S, ((-B : ℝ) : EReal) ≤ b y ∧ b y ≤ (B : EReal)

theorem IsBoundedOn.add {b₁ b₂ : Y → EReal} {S : Set Y} (h₁ : IsBoundedOn b₁ S)
    (h₂ : IsBoundedOn b₂ S) : IsBoundedOn (fun y => b₁ y + b₂ y) S := by
  obtain ⟨B₁, hB₁⟩ := h₁
  obtain ⟨B₂, hB₂⟩ := h₂
  refine ⟨B₁ + B₂, fun y hy => ⟨?_, ?_⟩⟩
  · calc ((-(B₁ + B₂) : ℝ) : EReal) = ((-B₁ : ℝ) : EReal) + ((-B₂ : ℝ) : EReal) := by
          rw [← EReal.coe_add]; ring_nf
      _ ≤ b₁ y + b₂ y := add_le_add (hB₁ y hy).1 (hB₂ y hy).1
  · calc b₁ y + b₂ y ≤ (B₁ : EReal) + (B₂ : EReal) := add_le_add (hB₁ y hy).2 (hB₂ y hy).2
      _ = ((B₁ + B₂ : ℝ) : EReal) := (EReal.coe_add _ _).symm

theorem IsBoundedOn.nsmul {b : Y → EReal} {S : Set Y} (h : IsBoundedOn b S) :
    ∀ k : ℕ, IsBoundedOn (fun y => k • b y) S
  | 0 => ⟨0, fun y _ => by simp⟩
  | k + 1 => by
      simpa [succ_nsmul] using (IsBoundedOn.nsmul h k).add h

/-- **Adding a bounded term does not change the singularity type.** -/
theorem sameSingularityTypeOn_add_of_isBoundedOn (u : Y → EReal) {b : Y → EReal} {S : Set Y}
    (hb : IsBoundedOn b S) : SameSingularityTypeOn (fun y => u y + b y) u S := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨⟨B, fun y hy => add_le_add le_rfl (hB y hy).2⟩, ⟨B, fun y hy => ?_⟩⟩
  calc u y = u y + ((-B : ℝ) : EReal) + (B : EReal) := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
    _ ≤ u y + b y + (B : EReal) := add_le_add (add_le_add le_rfl (hB y hy).1) le_rfl

/-- Pointwise-equal functions have the same singularity type. -/
theorem sameSingularityTypeOn_of_eq {u v : Y → EReal} (S : Set Y) (h : ∀ y, u y = v y) :
    SameSingularityTypeOn u v S := by
  rw [show u = v from funext h]
  exact SameSingularityTypeOn.refl v S

/-- An extended real that is not `⊤` is `⊥` or real. -/
theorem eq_bot_or_exists_coe {x : EReal} (hx : x ≠ ⊤) : x = ⊥ ∨ ∃ t : ℝ, x = t := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | coe t => exact Or.inr ⟨t, rfl⟩
  | top => exact absurd rfl hx

/-- **`eq:GB-decomposition`, on extended reals.**  With `q = C r`, `C ≥ 1`, `r ≥ 1`, `M > 0`:
`(C/M)(r a + b + c) = (1/M)(q a + b) + ((C-1)/M) b + (C/M) c` for `a, b, c ≠ +∞` (each side
is `-∞` as soon as one of `a, b, c` is). -/
theorem gb_decomposition_ereal {a b c : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    {C M : ℝ} {r q : ℕ} (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r) (hq : (q : ℝ) = C * r) :
    ((C / M : ℝ) : EReal) * (r • a + b + c) =
      ((1 / M : ℝ) : EReal) * (q • a + b) + (((C - 1) / M : ℝ) : EReal) * b +
        ((C / M : ℝ) : EReal) * c := by
  have hCM : 0 < C / M := div_pos (by linarith) hM
  have h1M : 0 < 1 / M := div_pos one_pos hM
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by rw [hq]; positivity
  have hC1 : 0 ≤ (C - 1) / M := div_nonneg (by linarith) hM.le
  rw [EReal.nsmul_eq_mul, EReal.nsmul_eq_mul]
  have hrE : ((r : ℕ) : EReal) = ((r : ℝ) : EReal) := rfl
  have hqE : ((q : ℕ) : EReal) = ((q : ℝ) : EReal) := rfl
  rw [hrE, hqE]
  rcases eq_bot_or_exists_coe ha with rfl | ⟨x, rfl⟩
  · simp only [EReal.coe_mul_bot_of_pos hrR, EReal.coe_mul_bot_of_pos hqR, EReal.bot_add,
      EReal.coe_mul_bot_of_pos hCM, EReal.coe_mul_bot_of_pos h1M]
  rcases eq_bot_or_exists_coe hb with rfl | ⟨y, rfl⟩
  · simp only [EReal.add_bot, EReal.bot_add, EReal.coe_mul_bot_of_pos hCM,
      EReal.coe_mul_bot_of_pos h1M]
  rcases eq_bot_or_exists_coe hc with rfl | ⟨z, rfl⟩
  · simp only [EReal.add_bot, EReal.coe_mul_bot_of_pos hCM]
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  rw [hq]
  field_simp
  ring

end Algebra

/-! ### Log singularities from a singularity-type comparison -/

section LogSingularities

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Pointwise content of a two-sided additive comparison with a function that is never `+∞`:
at each point both are `-∞`, or both are real and differ by at most `|C₁| + |C₂|`. -/
theorem bot_or_coe_of_le_of_le {u v : EReal} {C₁ C₂ : ℝ} (hv : v ≠ ⊤)
    (h₁ : u ≤ v + (C₁ : EReal)) (h₂ : v ≤ u + (C₂ : EReal)) :
    (v = ⊥ ∧ u = ⊥) ∨ ∃ d f : ℝ, v = d ∧ u = f ∧ |f - d| ≤ |C₁| + |C₂| := by
  rcases eq_bot_or_exists_coe hv with rfl | ⟨d, rfl⟩
  · rw [EReal.bot_add] at h₁
    exact Or.inl ⟨rfl, le_bot_iff.mp h₁⟩
  have hutop : u ≠ ⊤ := by
    have : (d : EReal) + (C₁ : EReal) ≠ ⊤ := by
      rw [← EReal.coe_add]
      exact EReal.coe_ne_top _
    exact ne_top_of_le_ne_top this h₁
  rcases eq_bot_or_exists_coe hutop with rfl | ⟨f, rfl⟩
  · rw [EReal.bot_add] at h₂
    exact absurd (le_bot_iff.mp h₂) (EReal.coe_ne_bot _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h₁ h₂
  refine Or.inr ⟨d, f, rfl, rfl, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith [le_abs_self C₁, le_abs_self C₂, neg_abs_le C₁, neg_abs_le C₂]

/-- **Two weights of the same singularity type, one of them `ψ_D`, give log singularities along
`D`.**  The residual is `φ - ψ_D` where `ψ_D` is finite and `0` on `Supp D` (where `φ = -∞`
too). -/
def logSingularitiesOfSameSingularityType (D : MeteredEffectiveQDivisor n M)
    {φ : M → EReal} (hφ : SameSingularityTypeOn φ D.weight univ)
    (hne : ∀ x, D.weight x ≠ ⊤) : HasLogSingularitiesAlong D φ := by
  classical
  choose C₁ h₁ using hφ.1
  choose C₂ h₂ using hφ.2
  have key := fun x => bot_or_coe_of_le_of_le (hne x) (h₁ x (mem_univ x)) (h₂ x (mem_univ x))
  refine ⟨fun x => if D.weight x = ⊥ then 0 else (φ x).toReal - (D.weight x).toReal,
    |C₁| + |C₂|, fun x => ?_, fun x => ?_⟩
  · rcases key x with ⟨hx, -⟩ | ⟨d, f, hd, hf, hb⟩
    · simp only [hx, if_true, abs_zero]
      positivity
    · simp only [hd, hf, EReal.coe_ne_bot, if_false, EReal.toReal_coe]
      exact hb
  · rcases key x with ⟨hx, hφx⟩ | ⟨d, f, hd, hf, -⟩
    · simp [hx, hφx]
    · simp only [hd, hf, EReal.coe_ne_bot, if_false, EReal.toReal_coe, ← EReal.coe_add]
      congr 1
      ring

end LogSingularities

/-! ### `eq:DL-restriction` at the level of weights -/

section Weights

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A metric of an effective divisor is bounded on a compact set disjoint from the divisor. -/
theorem isBoundedOn_of_disjoint {D : EffectiveDivisor n Y} {E : MeteredEffectiveQDivisor n Y}
    (hsupp : E.support = D.support) {W : Set Y} (hW : IsCompact W)
    (hD : Disjoint D.support W) : IsBoundedOn E.weight W := by
  obtain ⟨B, hB⟩ := MeteredDivisorWeightBounds.exists_bound_of_isCompact_disjoint_support E hW
    (by rw [hsupp]; exact hD.symm)
  exact ⟨B, hB⟩

/-- A metered divisor's weight is never `+∞` on a compact manifold. -/
theorem weight_ne_top [CompactSpace Y] (E : MeteredEffectiveQDivisor n Y) (y : Y) :
    E.weight y ≠ ⊤ := by
  obtain ⟨K, hK⟩ := MeteredDivisorScaling.exists_forall_weight_le E
  exact ne_top_of_le_ne_top (EReal.coe_ne_top K) (hK y)

/-- **`eq:DL-restriction`, weight form** (Copy-4 Step 4, with `eq:GB-decomposition`,
`eq:Pmov-restriction`, `eq:PF-restriction`).  See the module docstring. -/
theorem sameSingularityTypeOn_stepFourWeights [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {W : Set Y}
    (hWc : IsCompact W) {𝔅 : GermIdeal n X} (h𝔅 : 𝔅.IsCoherent) {ψB : X → EReal}
    (hψB : HasAnalyticSingularitiesOfType (n := n) ψB 1 𝔅)
    {Hfix Hm Pmov PM PF PF' GM : EffectiveDivisor n Y}
    (hHm : Disjoint Hm.support W) (hPM : Disjoint PM.support W)
    (hPF' : Disjoint PF'.support W) {r q : ℕ}
    (hGM : GM.ideal = (idealPow (Hfix.ideal.mul Hm.ideal) q).mul (Pmov.ideal.mul PM.ideal))
    (h1 : RestrictLe W (GermIdeal.pullback (m := n) π 𝔅)
      (((idealPow (Hfix.ideal.mul Hm.ideal) r).mul (Pmov.ideal.mul PM.ideal)).mul
        (PF.ideal.mul PF'.ideal)))
    (h2 : RestrictLe W
      (((idealPow (Hfix.ideal.mul Hm.ideal) r).mul (Pmov.ideal.mul PM.ideal)).mul
        (PF.ideal.mul PF'.ideal)) (GermIdeal.pullback (m := n) π 𝔅))
    {EGM EPmov EPF : MeteredEffectiveQDivisor n Y} (hEGM : IsDivisorMetric GM EGM)
    (hEPmov : IsDivisorMetric Pmov EPmov) (hEPF : IsDivisorMetric PF EPF)
    {C M : ℝ} (hM : 0 < M) (hC : 1 ≤ C) (hr : 0 < r) (hq : (q : ℝ) = C * r) :
    SameSingularityTypeOn (fun y => ((C / M : ℝ) : EReal) * ψB (π y))
      (fun y => ((1 / M : ℝ) : EReal) * EGM.weight y +
        (((C - 1) / M : ℝ) : EReal) * EPmov.weight y + ((C / M : ℝ) : EReal) * EPF.weight y)
      W := by
  -- metrics of the remaining divisors
  obtain ⟨wHfix, -, hwHfix⟩ := exists_divisorMetric Hfix
  obtain ⟨wHm, hsHm, hwHm⟩ := exists_divisorMetric Hm
  obtain ⟨wPM, hsPM, hwPM⟩ := exists_divisorMetric PM
  obtain ⟨wPF', hsPF', hwPF'⟩ := exists_divisorMetric PF'
  have tHfix := hasAnalyticSingularitiesOfType_of_isDivisorMetric hwHfix
  have tHm := hasAnalyticSingularitiesOfType_of_isDivisorMetric hwHm
  have tPM := hasAnalyticSingularitiesOfType_of_isDivisorMetric hwPM
  have tPF' := hasAnalyticSingularitiesOfType_of_isDivisorMetric hwPF'
  have tPmov := hasAnalyticSingularitiesOfType_of_isDivisorMetric hEPmov
  have tPF := hasAnalyticSingularitiesOfType_of_isDivisorMetric hEPF
  have tGM := hasAnalyticSingularitiesOfType_of_isDivisorMetric hEGM
  -- the weight of `𝔅̃ 𝒪_Y`
  obtain ⟨ψBY, tBY⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent
    (isCoherent_pullback hπ h𝔅)
  have hcomp : SameSingularityTypeOn (fun y => ψB (π y)) ψBY W :=
    ⟨(sameSingularityTypeOn_univ_comp_pullback hπ hψB tBY).1.mono (subset_univ W),
     (sameSingularityTypeOn_univ_comp_pullback hπ hψB tBY).2.mono (subset_univ W)⟩
  -- the weight of the right-hand ideal, and the comparison on `W`
  have tL := hasAnalyticSingularitiesOfType_mul
    (hasAnalyticSingularitiesOfType_mul
      (hasAnalyticSingularitiesOfType_pow (hasAnalyticSingularitiesOfType_mul tHfix tHm) r)
      (hasAnalyticSingularitiesOfType_mul tPmov tPM))
    (hasAnalyticSingularitiesOfType_mul tPF tPF')
  have hL := sameSingularityTypeOn_of_restrictLe hWc tBY tL h1 h2
  -- drop the remainders, bounded on `W`
  have bHm := isBoundedOn_of_disjoint hsHm hWc hHm
  have bPM := isBoundedOn_of_disjoint hsPM hWc hPM
  have bPF' := isBoundedOn_of_disjoint hsPF' hWc hPF'
  have hdrop : SameSingularityTypeOn
      (fun y => r • (wHfix.weight y + wHm.weight y) + (EPmov.weight y + wPM.weight y) +
        (EPF.weight y + wPF'.weight y))
      (fun y => r • wHfix.weight y + EPmov.weight y + EPF.weight y) W := by
    have heq : ∀ y, r • (wHfix.weight y + wHm.weight y) + (EPmov.weight y + wPM.weight y) +
        (EPF.weight y + wPF'.weight y) =
        (r • wHfix.weight y + EPmov.weight y + EPF.weight y) +
          ((r • wHm.weight y + wPM.weight y) + wPF'.weight y) := by
      intro y
      rw [nsmul_add]
      abel
    exact (sameSingularityTypeOn_of_eq W heq).trans
      (sameSingularityTypeOn_add_of_isBoundedOn _ (((bHm.nsmul r).add bPM).add bPF'))
  have hB : SameSingularityTypeOn (fun y => ψB (π y))
      (fun y => r • wHfix.weight y + EPmov.weight y + EPF.weight y) W :=
    hcomp.trans (hL.trans hdrop)
  -- `G̃_M` on `W`
  have tGM' := hasAnalyticSingularitiesOfType_mul
    (hasAnalyticSingularitiesOfType_pow (hasAnalyticSingularitiesOfType_mul tHfix tHm) q)
    (hasAnalyticSingularitiesOfType_mul tPmov tPM)
  rw [← hGM] at tGM'
  have hGMW : SameSingularityTypeOn EGM.weight
      (fun y => q • wHfix.weight y + EPmov.weight y) W := by
    have h0 := sameSingularityTypeOn_univ_of_eq_type tGM tGM'
    have h0W : SameSingularityTypeOn EGM.weight
        (fun y => q • (wHfix.weight y + wHm.weight y) + (EPmov.weight y + wPM.weight y)) W :=
      ⟨h0.1.mono (subset_univ W), h0.2.mono (subset_univ W)⟩
    have heq : ∀ y, q • (wHfix.weight y + wHm.weight y) + (EPmov.weight y + wPM.weight y) =
        (q • wHfix.weight y + EPmov.weight y) + (q • wHm.weight y + wPM.weight y) := by
      intro y
      rw [nsmul_add]
      abel
    exact h0W.trans ((sameSingularityTypeOn_of_eq W heq).trans
      (sameSingularityTypeOn_add_of_isBoundedOn _ ((bHm.nsmul q).add bPM)))
  -- assemble with `eq:GB-decomposition`
  have hCM : (0 : ℝ) ≤ C / M := div_nonneg (by linarith) hM.le
  have h1M : (0 : ℝ) ≤ 1 / M := div_nonneg zero_le_one hM.le
  have hC1M : (0 : ℝ) ≤ (C - 1) / M := div_nonneg (by linarith) hM.le
  have hL' := sameSingularityTypeOn_const_mul hB hCM
  have hR := sameSingularityTypeOn_add (sameSingularityTypeOn_add
    (sameSingularityTypeOn_const_mul hGMW h1M) (SameSingularityTypeOn.refl
    (fun y => (((C - 1) / M : ℝ) : EReal) * EPmov.weight y) W))
    (SameSingularityTypeOn.refl (fun y => ((C / M : ℝ) : EReal) * EPF.weight y) W)
  refine hL'.trans ((sameSingularityTypeOn_of_eq W fun y => ?_).trans hR.symm)
  exact gb_decomposition_ereal (weight_ne_top wHfix y) (weight_ne_top EPmov y)
    (weight_ne_top EPF y) hM hC hr hq

end Weights

/-! ### The field `hlog` -/

section Hlog

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Copy-4 Step 4: `φ' = φ_K ∘ π|_W + τ ψ_E|_W` has log singularities along `D|_W`**, for
`D = copy4Divisor` (`eq:def-DLY`) restricted to the closed submanifold `W ⊆ π⁻¹ V`, given

* `hφK`: `φ_K` has the singularity type of `(C/M) ψ_𝔅` on `V` (Copy-4: `φ_{K,ℓ}` has analytic
  singularities of type `(ℓ^{-1}, 𝔅)` with `𝔅 = 𝔅̃|_V`, `ℓ^{-1} = C/M`);
* `hweights`: `eq:DL-restriction` in weight form (`sameSingularityTypeOn_stepFourWeights`). -/
def stepFourLogSingularities [CompactSpace Y] {π : Y → X} {V : Set X} {W : Set Y}
    (hW : IsClosedConnectedSubmanifold n W k) (hWV : ∀ y ∈ W, π y ∈ V)
    {φK : V → EReal} {ψB : X → EReal} {levQ CQ τQ : ℚ} (hlev : 0 < levQ) (hC : 1 ≤ CQ)
    (hτ : 0 ≤ τQ)
    (hφK : SameSingularityTypeOn φK (fun v => (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * ψB v.1)
      univ)
    (EGM EPmov EPF E : MeteredEffectiveQDivisor n Y)
    (hweights : SameSingularityTypeOn
      (fun y => (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * ψB (π y))
      (fun y => ((1 / (levQ : ℝ) : ℝ) : EReal) * EGM.weight y +
        ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * EPmov.weight y +
        (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * EPF.weight y) W) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ hnd : ∀ O : Set W, IsOpen O → O.Nonempty →
        ∃ p ∈ O, (copy4Divisor hlev hC hτ EGM EPmov EPF E).weight (p : Y) ≠ ⊥,
      HasLogSingularitiesAlong
        (restrictAlong k (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
          (copy4Divisor hlev hC hτ EGM EPmov EPF E) hnd)
        (fun w => φK ⟨π w.1, hWV w.1 w.2⟩ + ((τQ : ℝ) : EReal) * E.weight w.1) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  intro hnd
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  refine logSingularitiesOfSameSingularityType _ ?_
    (fun w => weight_ne_top (copy4Divisor hlev hC hτ EGM EPmov EPF E) w.1)
  -- transport the comparisons to the subtype `W`
  have hK : SameSingularityTypeOn (fun w : W => φK ⟨π w.1, hWV w.1 w.2⟩)
      (fun w : W => (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * ψB (π w.1)) univ := by
    obtain ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩ := hφK
    exact ⟨⟨C₁, fun w _ => h₁ ⟨π w.1, hWV w.1 w.2⟩ (mem_univ _)⟩,
      ⟨C₂, fun w _ => h₂ ⟨π w.1, hWV w.1 w.2⟩ (mem_univ _)⟩⟩
  have hD : SameSingularityTypeOn
      (fun w : W => (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * ψB (π w.1))
      (fun w : W => ((1 / (levQ : ℝ) : ℝ) : EReal) * EGM.weight w.1 +
        ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * EPmov.weight w.1 +
        (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * EPF.weight w.1) univ := by
    obtain ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩ := hweights
    exact ⟨⟨C₁, fun w _ => h₁ _ w.2⟩, ⟨C₂, fun w _ => h₂ _ w.2⟩⟩
  have htot := sameSingularityTypeOn_add (hK.trans hD)
    (SameSingularityTypeOn.refl (fun w : W => ((τQ : ℝ) : EReal) * E.weight w.1) univ)
  refine htot.trans (sameSingularityTypeOn_of_eq univ fun w => ?_)
  show _ = (copy4Divisor hlev hC hτ EGM EPmov EPF E).weight w.1
  simp only [copy4Divisor, MeteredDivisorScaling.weight_qcomb4]
  push_cast
  rfl

end Hlog

end

end Hironaka.StepFourLogSingularities

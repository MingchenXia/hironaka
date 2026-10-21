import TranscendentalNakamaye.Pending.MarkedIdealGeoTransform
import TranscendentalNakamaye.Pending.OrderMultiplicativity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sums and products of marked ideals under admissible blowups

Blueprint `hir:controlled-operations`, `hir:marked-operations-transform` (`blueprint/src/hironaka.tex`,
Hironaka phase H1/H2).  Source: Włodarczyk 2005 §2.9, the operations
`(𝓘, μ) + (𝓙, ν) = (𝓘^ν + 𝓙^μ, μν)` and `(𝓘, μ) · (𝓙, ν) = (𝓘𝓙, μ + ν)` and Lemma `le:operations`
(the transform half; the cosupport half is `IdealOrderArithmetic` / `OrderMultiplicativity`).

## Controlled transforms (`BlowupControlledTransform.controlledTransform`, `σ^c(𝔞, μ) = 𝓘_D^{-μ} π^*𝔞`)

For coherent `𝔞 ⊆ 𝓘_C^μ` and `𝔟 ⊆ 𝓘_C^ν`:
* `controlledTransform_mul`: `σ^c(𝔞𝔟, μ + ν) = σ^c(𝔞, μ) σ^c(𝔟, ν)`;
* `controlledTransform_idealPow`: `σ^c(𝔞^k, μk) = σ^c(𝔞, μ)^k`;
* `controlledTransform_sumIdeal`: `σ^c(𝔞 + 𝔟, μ) = σ^c(𝔞, μ) + σ^c(𝔟, μ)` (for `𝔟 ⊆ 𝓘_C^μ`);
* `controlledTransform_sumIdeal_idealPow`: `σ^c(𝔞^ν + 𝔟^μ, μν) = σ^c(𝔞, μ)^ν + σ^c(𝔟, ν)^μ`.
All by uniqueness of the controlled transform from `π^*`, products and sums: `pullback_sumIdeal`,
`mul_sumIdeal`, `idealPow_idealPow` (ideal algebra, coherent ideals).

## Marked ideals with `N = M` (corrected transform `MarkedIdeal.geoTransform`)

* `MarkedIdeal.add` (`(𝓘^ν + 𝓙^μ, μν)`) and `MarkedIdeal.mul` (`(𝓘𝓙, μ + ν)`), on `N`, `E` of the first;
* `isGeoTestTower_add_iff`: the multiple test blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous ones of `𝔪₁`
  and `𝔪₂`, and `geoTransformAlong_add`: along them `(𝔪₁ + 𝔪₂)_T = (𝔪₁)_T + (𝔪₂)_T`;
* `isGeoTestTower_mul` / `geoTransformAlong_mul`: a simultaneous multiple test blow-up of `𝔪₁` and `𝔪₂` is
  one of `𝔪₁ · 𝔪₂`, and `(𝔪₁ · 𝔪₂)_T = (𝔪₁)_T · (𝔪₂)_T`.
(Le:operations (1)--(2) of Włodarczyk for two summands / factors, `N = M`, same `E`, marks `≥ 1` for the sum.)

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.GermIdealOrder TranscendentalNakamaye.Pending.IdealWeightPowers
  TranscendentalNakamaye.Pending.RestrictedIdealExtension TranscendentalNakamaye.Pending.GermIdealTotalTransform
  TranscendentalNakamaye.Pending.GermIdealPullbackCalculus TranscendentalNakamaye.Pending.BlowupExceptionalDivisor
  TranscendentalNakamaye.Pending.BlowupControlledTransform TranscendentalNakamaye.Pending.IdealOrderArithmetic
  TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.MarkedIdeals

noncomputable section

/-! ### Ideal algebra -/

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Products are monotone. -/
theorem mul_le_mul' {𝔞 𝔞' 𝔟 𝔟' : GermIdeal n M} (h𝔞 : 𝔞.Le 𝔞') (h𝔟 : 𝔟.Le 𝔟') :
    (𝔞.mul 𝔟).Le (𝔞'.mul 𝔟') := fun x _ hg =>
  mem_mul_iff.mpr ((mem_mul_iff.mp hg).mono fun _ ⟨a, b, ha, hb, hs⟩ => ⟨a, b, h𝔞 x a ha, h𝔟 x b hb, hs⟩)

/-- Powers are monotone in the ideal. -/
theorem idealPow_mono {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    ∀ k : ℕ, (idealPow 𝔞 k).Le (idealPow 𝔟 k)
  | 0 => fun _ _ hg => hg
  | k + 1 => mul_le_mul' (idealPow_mono h k) h

/-- **`(𝔞^μ)^k = 𝔞^{μk}`** for a coherent ideal. -/
theorem idealPow_idealPow {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) :
    ∀ k : ℕ, idealPow (idealPow 𝔞 μ) k = idealPow 𝔞 (μ * k)
  | 0 => by rw [Nat.mul_zero, idealPow_zero, idealPow_zero]
  | k + 1 => by
      rw [idealPow_succ, idealPow_idealPow h𝔞 μ k, Nat.mul_succ,
        RestrictLeCalculus.idealPow_add h𝔞]

/-- **`𝔩(𝔞 + 𝔟) = 𝔩𝔞 + 𝔩𝔟`.** -/
theorem mul_sumIdeal {𝔩 𝔞 𝔟 : GermIdeal n M} (h𝔩 : ∀ x g, 𝔩.mem x g → HolomorphicAt n g x)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    𝔩.mul (sumIdeal 𝔞 𝔟) = sumIdeal (𝔩.mul 𝔞) (𝔩.mul 𝔟) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
    rintro s ⟨l, t, hl, ht, rfl⟩
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_sumIdeal_iff.mp ht
    have hlhol := h𝔩 x l hl
    have hrhol : ∀ k, HolomorphicAt n (r k) x := fun k => (hr k).elim (h𝔞 x _) (h𝔟 x _)
    have heq : (fun p => ∑ k, c k p * (l p * r k p)) =ᶠ[𝓝 x] l * t := by
      filter_upwards [hsum] with p hp
      simp only [Pi.mul_apply, hp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc k) ?_
    rcases hr k with hrk | hrk
    · exact InvertibleIdealQuotient.isInSpanAt_self
        (S := fun s => (𝔩.mul 𝔞).mem x s ∨ (𝔩.mul 𝔟).mem x s)
        (Or.inl (mul_mem_mul hl hrk (hlhol.mul (hrhol k)))) (hlhol.mul (hrhol k))
    · exact InvertibleIdealQuotient.isInSpanAt_self
        (S := fun s => (𝔩.mul 𝔞).mem x s ∨ (𝔩.mul 𝔟).mem x s)
        (Or.inr (mul_mem_mul hl hrk (hlhol.mul (hrhol k)))) (hlhol.mul (hrhol k))
  · refine mem_mul_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro s (hs | hs)
    · exact (mem_mul_iff.mp hs).mono fun _ ⟨l, a, hl, ha, h⟩ =>
        ⟨l, a, hl, le_sumIdeal_left' h𝔞 x a ha, h⟩
    · exact (mem_mul_iff.mp hs).mono fun _ ⟨l, b, hl, hb, h⟩ =>
        ⟨l, b, hl, le_sumIdeal_right' h𝔟 x b hb, h⟩

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **`f^*(𝔞 + 𝔟) = f^*𝔞 + f^*𝔟`** for ideals of holomorphic germs and a holomorphic map `f`. -/
theorem pullback_sumIdeal {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) f (sumIdeal 𝔞 𝔟) =
      sumIdeal (GermIdeal.pullback (m := n) f 𝔞) (GermIdeal.pullback (m := n) f 𝔟) := by
  have hfat : ∀ {y : Y}, ∀ᶠ y' in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y' :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
    rintro s ⟨a, ha, rfl⟩
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_sumIdeal_iff.mp ha
    have heq : (fun p => ∑ k, (c k ∘ f) p * (r k ∘ f) p) =ᶠ[𝓝 y] a ∘ f :=
      ((hf.continuous.tendsto y).eventually hsum).mono fun p hp => hp.symm
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine RelativePrincipalizationSpan.IsInSpanAt.mul_left ((hc k).comp_contMDiff hfat) ?_
    rcases hr k with hrk | hrk
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inl ?_)
        ((h𝔞 _ _ hrk).comp_contMDiff hfat)
      exact RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f)
          ⟨r k, hrk, rfl⟩ ((h𝔞 _ _ hrk).comp_contMDiff hfat))
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inr ?_)
        ((h𝔟 _ _ hrk).comp_contMDiff hfat)
      exact RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f y) a ∧ s = a ∘ f)
          ⟨r k, hrk, rfl⟩ ((h𝔟 _ _ hrk).comp_contMDiff hfat))
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro s (hs | hs)
    · exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
        fun _ ⟨a, ha, h⟩ => ⟨a, le_sumIdeal_left' h𝔞 _ a ha, h⟩
    · exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
        fun _ ⟨b, hb, h⟩ => ⟨b, le_sumIdeal_right' h𝔟 _ b hb, h⟩

end Algebra

/-! ### Controlled transforms of products, powers and sums -/

section Controlled

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {𝔞 𝔟 : GermIdeal n X} {μ ν : ℕ}

theorem isCoherent_D (hπ : IsBlowupAlong n C π) (μ : ℕ) :
    (idealPow (exceptionalDivisor hπ).ideal μ).IsCoherent :=
  isCoherent_idealPow (isCoherent_ideal _) μ

/-- **`σ^c(𝔞𝔟, μ + ν) = σ^c(𝔞, μ) σ^c(𝔟, ν)`**. -/
theorem controlledTransform_mul (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ))
    (hle𝔟 : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) ν)) :
    controlledTransform hπ (𝔞.mul 𝔟) (μ + ν) =
      (controlledTransform hπ 𝔞 μ).mul (controlledTransform hπ 𝔟 ν) := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  have hc𝔟 := isCoherent_controlledTransform hπ h𝔟 hle𝔟
  refine (eq_controlledTransform_of_eq_mul hπ (IdealWeightPowers.isCoherent_mul hc𝔞 hc𝔟) ?_).symm
  rw [pullback_mul hπ.contMDiff h𝔞 h𝔟, pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞,
    pullback_eq_mul_controlledTransform hπ h𝔟 hle𝔟,
    mul_mul_mul_comm (isCoherent_D hπ μ) hc𝔞 (isCoherent_D hπ ν) hc𝔟,
    ← RestrictLeCalculus.idealPow_add (isCoherent_ideal _)]

/-- **`σ^c(𝔞^k, μk) = σ^c(𝔞, μ)^k`**. -/
theorem controlledTransform_idealPow (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent)
    (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) (k : ℕ) :
    controlledTransform hπ (idealPow 𝔞 k) (μ * k) = idealPow (controlledTransform hπ 𝔞 μ) k := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_idealPow hc𝔞 k) ?_).symm
  rw [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff h𝔞,
    pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞, idealPow_mul (isCoherent_D hπ μ) hc𝔞,
    idealPow_idealPow (isCoherent_ideal _)]

/-- **`σ^c(𝔞 + 𝔟, μ) = σ^c(𝔞, μ) + σ^c(𝔟, μ)`**. -/
theorem controlledTransform_sumIdeal (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent)
    (h𝔟 : 𝔟.IsCoherent) (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ))
    (hle𝔟 : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    controlledTransform hπ (sumIdeal 𝔞 𝔟) μ =
      sumIdeal (controlledTransform hπ 𝔞 μ) (controlledTransform hπ 𝔟 μ) := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  have hc𝔟 := isCoherent_controlledTransform hπ h𝔟 hle𝔟
  have hol : ∀ {𝔠 : GermIdeal n Y}, 𝔠.IsCoherent → ∀ y g, 𝔠.mem y g → HolomorphicAt n g y :=
    fun h𝔠 _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg
  refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_sumIdeal hc𝔞 hc𝔟) ?_).symm
  rw [pullback_sumIdeal hπ.contMDiff (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg),
    pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞, pullback_eq_mul_controlledTransform hπ h𝔟 hle𝔟,
    mul_sumIdeal (hol (isCoherent_D hπ μ)) (hol hc𝔞) (hol hc𝔟)]

/-- **Włodarczyk's sum**: `σ^c(𝔞^ν + 𝔟^μ, μν) = σ^c(𝔞, μ)^ν + σ^c(𝔟, ν)^μ` for coherent `𝔞 ⊆ 𝓘_C^μ` and
`𝔟 ⊆ 𝓘_C^ν`. -/
theorem controlledTransform_sumIdeal_idealPow (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent)
    (h𝔟 : 𝔟.IsCoherent) (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ))
    (hle𝔟 : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) ν)) :
    controlledTransform hπ (sumIdeal (idealPow 𝔞 ν) (idealPow 𝔟 μ)) (μ * ν) =
      sumIdeal (idealPow (controlledTransform hπ 𝔞 μ) ν) (idealPow (controlledTransform hπ 𝔟 ν) μ) := by
  have hIC := isCoherent_vanishingIdeal_centre hπ
  have hle𝔞' : (idealPow 𝔞 ν).Le (idealPow (vanishingIdeal (n := n) C) (μ * ν)) := by
    rw [← idealPow_idealPow hIC]; exact idealPow_mono hle𝔞 ν
  have hle𝔟' : (idealPow 𝔟 μ).Le (idealPow (vanishingIdeal (n := n) C) (μ * ν)) := by
    rw [Nat.mul_comm, ← idealPow_idealPow hIC]; exact idealPow_mono hle𝔟 μ
  rw [controlledTransform_sumIdeal hπ (isCoherent_idealPow h𝔞 ν) (isCoherent_idealPow h𝔟 μ) hle𝔞' hle𝔟',
    controlledTransform_idealPow hπ h𝔞 hle𝔞 ν, Nat.mul_comm μ ν,
    controlledTransform_idealPow hπ h𝔟 hle𝔟 μ]

end Controlled

/-! ### Sums and products of marked ideals -/

namespace MarkedIdeal

open MarkedIdeals.MarkedIdeal

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The sum of marked ideals** (Włodarczyk §2.9): `(𝓘, μ) + (𝓙, ν) = (𝓘^ν + 𝓙^μ, μν)`, on `N` and `E` of the
first. -/
def add (𝔪₁ 𝔪₂ : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪₁.N
  E := 𝔪₁.E
  ideal := sumIdeal (idealPow 𝔪₁.ideal 𝔪₂.d) (idealPow 𝔪₂.ideal 𝔪₁.d)
  d := 𝔪₁.d * 𝔪₂.d

/-- **The product of marked ideals** (Włodarczyk §2.9): `(𝓘, μ) · (𝓙, ν) = (𝓘𝓙, μ + ν)`, on `N` and `E` of
the first. -/
def mul (𝔪₁ 𝔪₂ : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪₁.N
  E := 𝔪₁.E
  ideal := 𝔪₁.ideal.mul 𝔪₂.ideal
  d := 𝔪₁.d + 𝔪₂.d

variable [IsComplexManifold n M]

/-- The cosupport of a sum (`N = M`, marks `≥ 1`) is the intersection of the cosupports. -/
theorem cosupp_add {𝔪₁ 𝔪₂ : MarkedIdeal n M} (hN₁ : 𝔪₁.N = univ) (hN₂ : 𝔪₂.N = univ)
    (h₁ : 𝔪₁.ideal.IsCoherent) (h₂ : 𝔪₂.ideal.IsCoherent) (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) :
    (add 𝔪₁ 𝔪₂).cosupp = 𝔪₁.cosupp ∩ 𝔪₂.cosupp := by
  simp only [MarkedIdeals.MarkedIdeal.cosupp, add, hN₁, hN₂]
  exact OrderMultiplicativity.cosupport_sumIdeal_idealPow
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h₁ hg)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h₂ hg) hd₁ hd₂

/-- The cosupport of a product contains the intersection of the cosupports. -/
theorem inter_cosupp_subset_cosupp_mul {𝔪₁ 𝔪₂ : MarkedIdeal n M} (hN : 𝔪₁.N = 𝔪₂.N) :
    𝔪₁.cosupp ∩ 𝔪₂.cosupp ⊆ (mul 𝔪₁ 𝔪₂).cosupp := by
  simp only [MarkedIdeals.MarkedIdeal.cosupp, mul]
  rw [← hN] at *
  exact inter_cosupport_subset_cosupport_mul _ _

/-- Marked ideals with the same four fields are equal. -/
theorem ext_of {𝔪 𝔫 : MarkedIdeal n M} (hN : 𝔪.N = 𝔫.N) (hE : 𝔪.E = 𝔫.E) (hI : 𝔪.ideal = 𝔫.ideal)
    (hd : 𝔪.d = 𝔫.d) : 𝔪 = 𝔫 := by
  cases 𝔪; cases 𝔫; simp_all

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- Two marked ideals on `N = M` with the same `E`: data for the step lemmas. -/
structure IsAmbientPair (𝔪₁ 𝔪₂ : MarkedIdeal n M) : Prop where
  N₁ : 𝔪₁.N = univ
  N₂ : 𝔪₂.N = univ
  E : 𝔪₁.E = 𝔪₂.E
  coh₁ : 𝔪₁.ideal.IsCoherent
  coh₂ : 𝔪₂.ideal.IsCoherent

/-- **One step of le:operations (1)**: the transform of a sum is the sum of the transforms. -/
theorem geoTransform_add {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsAmbientPair 𝔪₁ 𝔪₂) {C : Set M} {π : M' → M}
    (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    (add 𝔪₁ 𝔪₂).geoTransform C π = add (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π) := by
  have hcohA : (add 𝔪₁ 𝔪₂).ideal.IsCoherent :=
    isCoherent_sumIdeal (isCoherent_idealPow h.coh₁ _) (isCoherent_idealPow h.coh₂ _)
  have h1 := geoTransform_ideal_eq_controlledTransform (𝔪 := add 𝔪₁ 𝔪₂) (C := C) h.N₁ hcohA hπ
  have h2 := geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪₁) (C := C) h.N₁ h.coh₁ hπ
  have h3 := geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪₂) (C := C) h.N₂ h.coh₂ hπ
  have hle₁ := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₁ h.coh₁ hC₁
  have hle₂ := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₂ h.coh₂ hC₂
  have hideal : ((add 𝔪₁ 𝔪₂).geoTransform C π).ideal =
      (add (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π)).ideal := by
    rw [h1]
    show controlledTransform hπ (sumIdeal (idealPow 𝔪₁.ideal 𝔪₂.d) (idealPow 𝔪₂.ideal 𝔪₁.d))
      (𝔪₁.d * 𝔪₂.d) = sumIdeal (idealPow (𝔪₁.geoTransform C π).ideal 𝔪₂.d)
        (idealPow (𝔪₂.geoTransform C π).ideal 𝔪₁.d)
    rw [h2, h3, controlledTransform_sumIdeal_idealPow hπ h.coh₁ h.coh₂ hle₁ hle₂]
  exact ext_of rfl rfl hideal rfl

/-- One admissible step keeps an ambient pair an ambient pair. -/
theorem IsAmbientPair.geoTransform {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsAmbientPair 𝔪₁ 𝔪₂) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C)
    (hC₂ : 𝔪₂.IsAdmissibleCentre C) : IsAmbientPair (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π) where
  N₁ := geoTransform_N_eq_univ h.N₁ hπ
  N₂ := geoTransform_N_eq_univ h.N₂ hπ
  E := by simp only [geoTransform_E, h.E]
  coh₁ := by
    rw [geoTransform_ideal_eq_controlledTransform h.N₁ h.coh₁ hπ]
    exact isCoherent_controlledTransform hπ h.coh₁
      (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₁ h.coh₁ hC₁)
  coh₂ := by
    rw [geoTransform_ideal_eq_controlledTransform h.N₂ h.coh₂ hπ]
    exact isCoherent_controlledTransform hπ h.coh₂
      (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₂ h.coh₂ hC₂)

/-- **A centre is admissible for a sum iff it is admissible for both summands** (`N = M`, marks `≥ 1`). -/
theorem isAdmissibleCentre_add_iff {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsAmbientPair 𝔪₁ 𝔪₂)
    (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) {C : Set M} :
    (add 𝔪₁ 𝔪₂).IsAdmissibleCentre C ↔ 𝔪₁.IsAdmissibleCentre C ∧ 𝔪₂.IsAdmissibleCentre C := by
  simp only [IsAdmissibleCentre, cosupp_add h.N₁ h.N₂ h.coh₁ h.coh₂ hd₁ hd₂, subset_inter_iff]
  show _ ∧ _ ∧ NormalCrossings.HasNormalCrossings n C 𝔪₁.E ↔ _
  rw [← h.E]
  tauto

/-- **A centre admissible for both factors is admissible for the product** (same `N`). -/
theorem IsAdmissibleCentre.mul {𝔪₁ 𝔪₂ : MarkedIdeal n M} (hN : 𝔪₁.N = 𝔪₂.N) {C : Set M}
    (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    (mul 𝔪₁ 𝔪₂).IsAdmissibleCentre C :=
  ⟨hC₁.1, (subset_inter hC₁.2.1 hC₂.2.1).trans (inter_cosupp_subset_cosupp_mul hN), hC₁.2.2⟩

/-- **One step of le:operations (2)**: the transform of a product is the product of the transforms. -/
theorem geoTransform_mul {𝔪₁ 𝔪₂ : MarkedIdeal n M} (h : IsAmbientPair 𝔪₁ 𝔪₂) {C : Set M} {π : M' → M}
    (hπ : IsBlowupAlong n C π) (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    (mul 𝔪₁ 𝔪₂).geoTransform C π = mul (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π) := by
  have hcohM : (mul 𝔪₁ 𝔪₂).ideal.IsCoherent := IdealWeightPowers.isCoherent_mul h.coh₁ h.coh₂
  have h1 := geoTransform_ideal_eq_controlledTransform (𝔪 := mul 𝔪₁ 𝔪₂) (C := C) h.N₁ hcohM hπ
  have h2 := geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪₁) (C := C) h.N₁ h.coh₁ hπ
  have h3 := geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪₂) (C := C) h.N₂ h.coh₂ hπ
  have hle₁ := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₁ h.coh₁ hC₁
  have hle₂ := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre h.N₂ h.coh₂ hC₂
  have hideal : ((mul 𝔪₁ 𝔪₂).geoTransform C π).ideal =
      (mul (𝔪₁.geoTransform C π) (𝔪₂.geoTransform C π)).ideal := by
    rw [h1]
    show controlledTransform hπ (𝔪₁.ideal.mul 𝔪₂.ideal) (𝔪₁.d + 𝔪₂.d) =
      (𝔪₁.geoTransform C π).ideal.mul (𝔪₂.geoTransform C π).ideal
    rw [h2, h3, controlledTransform_mul hπ h.coh₁ h.coh₂ hle₁ hle₂]
  exact ext_of rfl rfl hideal rfl

end MarkedIdeal

/-! ### Along towers -/

namespace MarkedIdeal

open MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk le:operations (1), transform half** (`N = M`, same `E`, marks `≥ 1`): the multiple test
blow-ups of `𝔪₁ + 𝔪₂` are exactly the simultaneous multiple test blow-ups of `𝔪₁` and `𝔪₂`, and along them
`(𝔪₁ + 𝔪₂)_T = (𝔪₁)_T + (𝔪₂)_T`. -/
theorem geoTransformAlong_add (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsAmbientPair 𝔪₁ 𝔪₂)
    (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (add 𝔪₁ 𝔪₂) T ↔ IsGeoTestTower 𝔪₁ T ∧ IsGeoTestTower 𝔪₂ T) ∧
      (IsGeoTestTower 𝔪₁ T → IsGeoTestTower 𝔪₂ T →
        geoTransformAlong (add 𝔪₁ 𝔪₂) T = add (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T) ∧
        IsAmbientPair (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T))
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ _ => ⟨rfl, h⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_add 𝔪₁ 𝔪₂ h hd₁ hd₂ T
      have hd₁T : 1 ≤ (geoTransformAlong 𝔪₁ T).d := by rw [d_geoTransformAlong]; exact hd₁
      have hd₂T : 1 ≤ (geoTransformAlong 𝔪₂ T).d := by rw [d_geoTransformAlong]; exact hd₂
      refine ⟨?_, fun h₁ h₂ => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          obtain ⟨hT₁, hT₂⟩ := ihT.mp hT
          obtain ⟨heq, hpair⟩ := ihE hT₁ hT₂
          rw [heq, isAdmissibleCentre_add_iff hpair hd₁T hd₂T] at hC
          exact ⟨⟨hT₁, hC.1⟩, hT₂, hC.2⟩
        · rintro ⟨⟨hT₁, hC₁⟩, hT₂, hC₂⟩
          obtain ⟨heq, hpair⟩ := ihE hT₁ hT₂
          refine ⟨ihT.mpr ⟨hT₁, hT₂⟩, ?_⟩
          rw [heq, isAdmissibleCentre_add_iff hpair hd₁T hd₂T]
          exact ⟨hC₁, hC₂⟩
      · obtain ⟨hT₁, hC₁⟩ := (isGeoTestTower_step_iff 𝔪₁ T C π hπ).mp h₁
        obtain ⟨hT₂, hC₂⟩ := (isGeoTestTower_step_iff 𝔪₂ T C π hπ).mp h₂
        obtain ⟨heq, hpair⟩ := ihE hT₁ hT₂
        refine ⟨?_, hpair.geoTransform hπ hC₁ hC₂⟩
        rw [geoTransformAlong_step, heq, geoTransform_add hpair hπ hC₁ hC₂]
        rfl

/-- **Resolutions of a sum** (`N = M`, same `E`, marks `≥ 1`): a tower resolves `𝔪₁ + 𝔪₂` iff it is a
simultaneous multiple test blow-up of `𝔪₁` and `𝔪₂` after which their cosupports are disjoint. -/
theorem isGeoResolution_add_iff (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsAmbientPair 𝔪₁ 𝔪₂)
    (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    IsGeoResolution (add 𝔪₁ 𝔪₂) T ↔ IsGeoTestTower 𝔪₁ T ∧ IsGeoTestTower 𝔪₂ T ∧
      (geoTransformAlong 𝔪₁ T).cosupp ∩ (geoTransformAlong 𝔪₂ T).cosupp = ∅ := by
  obtain ⟨hiff, heq⟩ := geoTransformAlong_add 𝔪₁ 𝔪₂ h hd₁ hd₂ T
  constructor
  · rintro ⟨hT, hc⟩
    obtain ⟨hT₁, hT₂⟩ := hiff.mp hT
    obtain ⟨he, hpair⟩ := heq hT₁ hT₂
    rw [he, cosupp_add hpair.N₁ hpair.N₂ hpair.coh₁ hpair.coh₂
      (by rw [d_geoTransformAlong]; exact hd₁) (by rw [d_geoTransformAlong]; exact hd₂)] at hc
    exact ⟨hT₁, hT₂, hc⟩
  · rintro ⟨hT₁, hT₂, hc⟩
    obtain ⟨he, hpair⟩ := heq hT₁ hT₂
    refine ⟨hiff.mpr ⟨hT₁, hT₂⟩, ?_⟩
    rw [he, cosupp_add hpair.N₁ hpair.N₂ hpair.coh₁ hpair.coh₂
      (by rw [d_geoTransformAlong]; exact hd₁) (by rw [d_geoTransformAlong]; exact hd₂)]
    exact hc

/-- **Włodarczyk le:operations (2), transform half** (`N = M`, same `E`): a simultaneous multiple test
blow-up of `𝔪₁` and `𝔪₂` is one of `𝔪₁ · 𝔪₂`, and along it `(𝔪₁ · 𝔪₂)_T = (𝔪₁)_T · (𝔪₂)_T`. -/
theorem geoTransformAlong_mul (𝔪₁ 𝔪₂ : MarkedIdeal n X) (h : IsAmbientPair 𝔪₁ 𝔪₂) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪₁ T → IsGeoTestTower 𝔪₂ T →
      IsGeoTestTower (mul 𝔪₁ 𝔪₂) T ∧
      geoTransformAlong (mul 𝔪₁ 𝔪₂) T = mul (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T) ∧
      IsAmbientPair (geoTransformAlong 𝔪₁ T) (geoTransformAlong 𝔪₂ T)
  | _, .refl, _, _ => ⟨trivial, rfl, h⟩
  | _, .step T C π hπ, h₁, h₂ => by
      obtain ⟨hT₁, hC₁⟩ := (isGeoTestTower_step_iff 𝔪₁ T C π hπ).mp h₁
      obtain ⟨hT₂, hC₂⟩ := (isGeoTestTower_step_iff 𝔪₂ T C π hπ).mp h₂
      obtain ⟨hT, heq, hpair⟩ := geoTransformAlong_mul 𝔪₁ 𝔪₂ h T hT₁ hT₂
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hT, ?_⟩, ?_, hpair.geoTransform hπ hC₁ hC₂⟩
      · rw [heq]
        exact IsAdmissibleCentre.mul (hpair.N₁.trans hpair.N₂.symm) hC₁ hC₂
      · rw [geoTransformAlong_step, heq, geoTransform_mul hpair hπ hC₁ hC₂]
        rfl

end MarkedIdeal

end

end TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform

import Hironaka.Resolution.HironakaG8LogTangentLift

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The controlled logarithmic inclusion under a blowup (G8 lane, run 0080; leaf G8-3H-C06)

Blueprint: `hironaka-g8-resume-log-controlled-inclusion.tex`.

Let `π : Y → X` be the blowup along a closed centre `C`, `N` a closed carrier with strict transform
`N' = closure (π⁻¹(N \ C))`, `E` a list of closed boundary members and `E' = strict E ++ [π⁻¹C]` the transformed
list, and assume the simultaneous normal crossings of `C`, `N`, `E` at the points of `C ∩ N`
(`BlowupSNCTransform.IsAdaptedAt`).  For an ideal `𝔞` of holomorphic germs with `𝔞|_N ⊆ 𝓘_C^{μ+1}|_N`
(`restrictLe_colonAlong_logDerivIdealAlong`):

  `(π^* 𝓓_{N,E}(𝔞) : (π^*𝓘_C)^μ)|_{N'} ⊆ 𝓓_{N',E'}((π^*𝔞 : (π^*𝓘_C)^{μ+1})|_{N'})|_{N'}`,

the colons taken along `N'` as in `MarkedIdeal.geoTransform`, and `𝓓_{N,E}` the whole logarithmic derivative ideal
`HironakaActualIntrinsicLogDerivativeFrame.logDerivIdealAlong` (the ideal, the carrier ideal and the derivatives along
fields tangent to `N` and to EVERY member of `E`).  This is the logarithmic form of Włodarczyk 2005, Lemma
`le:inclusions`, and Bierstone--Milman 2008, Lemmas 3.1--3.3 (for the log derivatives, BM08 §3.2), and of TN's
ordinary `DerivativeIdealAlongTransform.restrictLe_colonAlong_derivIdealAlong`; the only changed input is the
logarithmic lift `HironakaG8LogTangentLift.exists_log_tangent_lift` (`y · (ξ f) ∘ π = D'(f ∘ π)`, `D'(y) ∈ (y)`,
`D'` logarithmic for `(N', E')`).  No `C ⊆ N` hypothesis is needed.

Then the iterate (`restrictLe_colonAlong_logIter`): `𝔞|_N ⊆ 𝓘_C^{μ+r}|_N` implies
`(π^* 𝓓_{N,E}^r(𝔞) : (π^*𝓘_C)^μ)|_{N'} ⊆ 𝓓_{N',E'}^r((π^*𝔞 : (π^*𝓘_C)^{μ+r})|_{N'})|_{N'}`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogControlledInclusion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps BlowupTowers
  GermIdealOrder DerivativeIdeal IdealWeightPowers InvertibleIdealQuotient BlowupExceptionalDivisor
  BlowupControlledTransform BlowupDerivativeIdeal DerivativeIdealAlongTransform
open Hironaka.DerivativeIdealAlong Hironaka.DerivativeIdealAlongCoherent
  Hironaka.DerivativeIdealAlongEtale Hironaka.BlowupStrictSubmanifold
  Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient
  Hironaka.RestrictedIdealWeight Hironaka.RelativePrincipalizationSpan
  Hironaka.BlowupSNCTransform
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaG8LogDerivEtale
  Hironaka.HironakaG8LogTangentLift

noncomputable section

/-! ### The logarithmic operator on restricted inclusions -/

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Germs of the log operator are holomorphic. -/
theorem holomorphicAt_of_mem_logDerivIdealAlong {N : Set M} {E : List (Set M)} {A : GermIdeal n M} {x : M}
    {g : M → ℂ} (hg : (logDerivIdealAlong N E A).mem x g) : HolomorphicAt n g x :=
  hg.1

/-- Germs of the iterated log operator are holomorphic (for `r = 0`, given for `A`). -/
theorem holomorphicAt_of_mem_logIter {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) :
    ∀ r x g, ((logDerivIdealAlong N E)^[r] A).mem x g → HolomorphicAt n g x
  | 0, x, g, hg => hA x g hg
  | r + 1, x, g, hg => by
    rw [Function.iterate_succ_apply'] at hg
    exact hg.1

/-- **Log derivatives lower the restricted power of `𝓘_C` by one**: `𝔞|_N ⊆ 𝓘_C^{q+1}|_N` implies
`𝓓_{N,E}(𝔞)|_N ⊆ 𝓘_C^q|_N` (`f = ∑ aₖ hₖ + t` with `hₖ ∈ 𝓘_C^{q+1}` and `t ∈ 𝓘_N`; a field tangent to `N` keeps
`t` in `𝓘_N`). -/
theorem restrictLe_logDerivIdealAlong_idealPow {N C : Set M} {E : List (Set M)} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {q : ℕ}
    (hle : RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (q + 1))) :
    RestrictLe N (logDerivIdealAlong N E 𝔞) (idealPow (vanishingIdeal (n := n) C) q) := by
  have hC : ∀ y g, (vanishingIdeal (n := n) C).mem y g → HolomorphicAt n g y := fun _ _ h => h.1
  intro x hx u hu
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (mem_logDerivIdealAlong_iff.mp hu))
  rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact IsInSpanOnAt.mono (fun s hs => idealPow_succ_le hC q x s hs) (hle x hx σ hσ)
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    filter_upwards [hσ.2] with p hp hpN
    simp [hp hpN]
  · obtain ⟨K, h, a, hh, ha, hsum⟩ := hle x hx f hf
    have hhhol : ∀ k, HolomorphicAt n (h k) x := fun k => holomorphicAt_of_mem_idealPow (hh k)
    have htN : (vanishingIdeal (n := n) N).mem x (fun q => f q - ∑ k, a k q * h k q) :=
      ⟨GiraudAlong.holomorphicAt_sub (h𝔞 x f hf) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hhhol k)), by
        filter_upwards [hsum] with p hp hpN
        rw [hp hpN, sub_self]⟩
    have hmem : (idealPow (vanishingIdeal (n := n) C) q).mem x
        (fun p => ∑ k, (fieldDeriv e ξ (a k) p * h k p + a k p * fieldDeriv e ξ (h k) p)) := by
      refine mem_idealPow_of_isInSpanAt (IsInSpanAt.sum _ fun k _ => IsInSpanAt.add ?_ ?_)
      · exact IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt (ha k))
          (InvertibleIdealQuotient.isInSpanAt_self (idealPow_succ_le hC q x _ (hh k)) (hhhol k))
      · have h1 := fieldDeriv_mem_idealPow hC hξ.1.mem_source hξ.1.holomorphicAt (hh k)
        exact IsInSpanAt.mul_left (ha k) (InvertibleIdealQuotient.isInSpanAt_self h1
          (holomorphicAt_of_mem_idealPow h1))
    refine IsInSpanOnAt.congr_right (IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem
      (holomorphicAt_of_mem_idealPow hmem))) ?_
    filter_upwards [fieldDeriv_eventuallyEq_add_sum (ξ := ξ) hξ.1.mem_source ha hhhol (h𝔞 x f hf),
      (hξ.1.preserves _ htN).2] with p hp1 hp2 hpN
    rw [hp1, hp2 hpN, add_zero]

/-- Iterated: `𝔞|_N ⊆ 𝓘_C^{q+r}|_N` implies `𝓓_{N,E}^r(𝔞)|_N ⊆ 𝓘_C^q|_N`. -/
theorem restrictLe_logIter_idealPow {N C : Set M} {E : List (Set M)} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y) {q : ℕ} :
    ∀ r, RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (q + r)) →
      RestrictLe N ((logDerivIdealAlong N E)^[r] 𝔞) (idealPow (vanishingIdeal (n := n) C) q)
  | 0, hle => hle
  | r + 1, hle => by
    rw [Function.iterate_succ_apply']
    refine restrictLe_logDerivIdealAlong_idealPow (holomorphicAt_of_mem_logIter h𝔞 r)
      (restrictLe_logIter_idealPow h𝔞 r ?_)
    rwa [show q + 1 + r = q + (r + 1) by omega]

/-- **`𝓓_{W,E}` respects restricted inclusions**: `𝔟₁|_W ⊆ 𝔟₂|_W` implies
`𝓓_{W,E}(𝔟₁)|_W ⊆ 𝓓_{W,E}(𝔟₂)|_W` (for `f = ∑ aₖ gₖ + t` with `gₖ ∈ 𝔟₂` and `t ∈ 𝓘_W`, a log field gives
`ξ f = ∑ ξ(aₖ) gₖ + aₖ ξ(gₖ) + ξ(t)`, `ξ(t) ∈ 𝓘_W`). -/
theorem restrictLe_logDerivIdealAlong {W : Set M} {E : List (Set M)} {𝔟₁ 𝔟₂ : GermIdeal n M}
    (h₁ : ∀ y g, 𝔟₁.mem y g → HolomorphicAt n g y) (h₂ : ∀ y g, 𝔟₂.mem y g → HolomorphicAt n g y)
    (h : RestrictLe W 𝔟₁ 𝔟₂) : RestrictLe W (logDerivIdealAlong W E 𝔟₁) (logDerivIdealAlong W E 𝔟₂) := by
  intro x hx u hu
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (mem_logDerivIdealAlong_iff.mp hu))
  rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact IsInSpanOnAt.mono (fun s hs => mem_logDerivIdealAlong_of_mem hs (h₂ x s hs)) (h x hx σ hσ)
  · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self
      (mem_logDerivIdealAlong_of_vanishing hσ) hσ.1)
  · obtain ⟨K, g, a, hg, ha, hsum⟩ := h x hx f hf
    have hghol : ∀ k, HolomorphicAt n (g k) x := fun k => h₂ x _ (hg k)
    have htW : (vanishingIdeal (n := n) W).mem x (fun q => f q - ∑ k, a k q * g k q) :=
      ⟨GiraudAlong.holomorphicAt_sub (h₁ x f hf) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hghol k)), by
        filter_upwards [hsum] with p hp hpW
        rw [hp hpW, sub_self]⟩
    have hmem : IsInSpanAt (n := n) (LogGen W E 𝔟₂ x) x (fun p => ∑ k, (fieldDeriv e ξ (a k) p * g k p +
        a k p * fieldDeriv e ξ (g k) p) + fieldDeriv e ξ (fun q => f q - ∑ k, a k q * g k q) p) := by
      refine IsInSpanAt.add (IsInSpanAt.sum _ fun k _ => IsInSpanAt.add ?_ ?_) ?_
      · exact IsInSpanAt.mul_left (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt (ha k))
          (InvertibleIdealQuotient.isInSpanAt_self (Or.inl (hg k)) (hghol k))
      · exact IsInSpanAt.mul_left (ha k) (InvertibleIdealQuotient.isInSpanAt_self
          (Or.inr (Or.inr ⟨e, ξ, g k, hξ, hg k, rfl⟩))
          (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt (hghol k)))
      · exact InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inl (hξ.1.preserves _ htW)))
          (hξ.1.preserves _ htW).1
    have hξf : HolomorphicAt n (fieldDeriv e ξ f) x :=
      holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt (h₁ x f hf)
    have heq := fieldDeriv_eventuallyEq_add_sum (ξ := ξ) hξ.1.mem_source ha hghol (h₁ x f hf)
    have hmem' : (logDerivIdealAlong W E 𝔟₂).mem x (fieldDeriv e ξ f) :=
      mem_logDerivIdealAlong_iff.mpr (DerivativeIdeal.isInSpanAt_congr hmem heq.symm)
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem' hξf)

/-- Iterated monotonicity: `𝔟₁|_W ⊆ 𝔟₂|_W` implies `𝓓_{W,E}^r(𝔟₁)|_W ⊆ 𝓓_{W,E}^r(𝔟₂)|_W`. -/
theorem restrictLe_logIter {W : Set M} {E : List (Set M)} {𝔟₁ 𝔟₂ : GermIdeal n M}
    (h₁ : ∀ y g, 𝔟₁.mem y g → HolomorphicAt n g y) (h₂ : ∀ y g, 𝔟₂.mem y g → HolomorphicAt n g y)
    (h : RestrictLe W 𝔟₁ 𝔟₂) :
    ∀ r, RestrictLe W ((logDerivIdealAlong W E)^[r] 𝔟₁) ((logDerivIdealAlong W E)^[r] 𝔟₂)
  | 0 => h
  | r + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact restrictLe_logDerivIdealAlong (holomorphicAt_of_mem_logIter h₁ r)
      (holomorphicAt_of_mem_logIter h₂ r) (restrictLe_logIter h₁ h₂ h r)

end General

/-! ### The controlled inclusion -/

section Controlled

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} {π : Y → X}

/-- **The controlled logarithmic inclusion, one derivative** (Włodarczyk 2005, Lemma `le:inclusions`; BM08,
Lemmas 3.1--3.3 with logarithmic derivatives): let `N` be a closed carrier, `E` closed boundary members,
`C`, `N`, `E` simultaneously normal crossing at the points of `C ∩ N`, `N'` the strict transform and
`E' = strict E ++ [π⁻¹C]`, and `𝔞|_N ⊆ 𝓘_C^{μ+1}|_N`.  Then on `N'`
`(π^* 𝓓_{N,E}(𝔞) : 𝒪(-μD))|_{N'} ⊆ 𝓓_{N',E'}((π^*𝔞 : 𝒪(-(μ+1)D))|_{N'})|_{N'}`.
At `z ∈ N'` with `y` a generator of `𝒪(-D)`: every `s ∈ 𝔞_{π z}` is `s ∘ π = y^{μ+1} H + t ∘ π` with `H` in the
transform and `t ∈ 𝓘_N`; for a generator `ξ(f)` (`ξ` logarithmic for `(N, E)`) the logarithmic lift `D'` gives
`y (ξ f) ∘ π = D'(f ∘ π) = y^{μ+1}((μ+1) ρ H + D'(H))` on `N'`, and `D'(H)` is a generator of the target since `D'`
is logarithmic for `(N', E')`; then `y^{μ+1}` is cancelled on `N'`. -/
theorem restrictLe_colonAlong_logDerivIdealAlong (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N)
    {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) (hAd : ∀ x ∈ C, x ∈ N → IsAdaptedAt n C N E x)
    {𝔞 : GermIdeal n X} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ}
    (hle : RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (μ + 1))) :
    RestrictLe (geoStrictTransform π C N)
      (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E 𝔞))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) μ))
      (logDerivIdealAlong (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
        (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (μ + 1)))) := by
  classical
  intro z hzN g hg
  set N' := geoStrictTransform π C N with hN'
  set J := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with hJ
  set 𝔠 := colonAlong n N' (GermIdeal.pullback (m := n) π 𝔞) (idealPow J (μ + 1)) with h𝔠
  set ez := complexChartAt (n := n) z with hez
  have hπs := hπ.contMDiff
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have hcomp : ∀ {f : X → ℂ}, HolomorphicAt n f (π z) → HolomorphicAt n (fun p => f (π p)) z := fun hf =>
    hf.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  have hxN : π z ∈ N := geoStrictTransform_subset_preimage hπs.continuous hN hzN
  obtain ⟨U, y, hy⟩ := exists_isUniformDerivationGenerator hπ z
  have hzs : z ∈ ez.val.source := mem_complexChartAt_source z
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  have hpow : ∀ q, ∀ p ∈ U, ∀ g, (idealPow J q).mem p g ↔
      IsInSpanAt (n := n) (· = fun p => y p ^ q) p g :=
    idealPow_mem_iff_of_generator hy.holomorphicAt hy.generates
  have hpow_self : ∀ q, (idealPow J q).mem z (fun p => y p ^ q) := fun q =>
    (hpow q z hy.mem _).mpr (isInSpanAt_of_eq_mul rfl (holomorphicAt_pow hyz q) (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp))
  -- pullbacks of germs vanishing on `N` vanish on `N'`
  have hvan : ∀ t, (vanishingIdeal (n := n) N).mem (π z) t →
      ∀ᶠ p in 𝓝 z, p ∈ N' → t (π p) = 0 := fun t ht => by
    filter_upwards [hπc.eventually ht.2] with p hp hpN
    exact hp (geoStrictTransform_subset_preimage hπs.continuous hN hpN)
  -- Claim C: `s ∘ π = y^{μ+1} H + t ∘ π` with `H ∈ 𝔠` and `t ∈ 𝓘_N`
  have hC : ∀ s, 𝔞.mem (π z) s → ∃ H t, 𝔠.mem z H ∧ (vanishingIdeal (n := n) N).mem (π z) t ∧
      (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p + t (π p) := by
    intro s hs
    obtain ⟨K, h, a, hh, ha, hsum⟩ := hle (π z) hxN s hs
    have hhhol : ∀ k, HolomorphicAt n (h k) (π z) := fun k => holomorphicAt_of_mem_idealPow (hh k)
    set t : X → ℂ := fun q => s q - ∑ k, a k q * h k q with ht
    have hthol : HolomorphicAt n t (π z) :=
      GiraudAlong.holomorphicAt_sub (h𝔞 _ _ hs) (HolomorphicAt.sum _ fun k _ => (ha k).mul (hhhol k))
    have htN : (vanishingIdeal (n := n) N).mem (π z) t := ⟨hthol, by
      filter_upwards [hsum] with q hq hqN
      simp only [ht, hq hqN, sub_self]⟩
    have hHk : ∀ k, ∃ Hk : Y → ℂ, HolomorphicAt n Hk z ∧
        (fun p => h k (π p)) =ᶠ[𝓝 z] fun p => Hk p * y p ^ (μ + 1) := by
      intro k
      have h1 : (GermIdeal.pullback (m := n) π (idealPow (vanishingIdeal (n := n) C) (μ + 1))).mem z
          (fun p => h k (π p)) :=
        comp_mem_pullback (hh k) (hcomp (hhhol k)) (holomorphicAt_const 1)
          (Eventually.of_forall fun p => by simp)
      have h2 := pullback_le_idealPow_exceptionalDivisor hπ (fun _ _ h => h) z _ h1
      obtain ⟨-, Hk, hHk, hHkeq⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem _).mp h2)
      exact ⟨Hk, hHk, hHkeq⟩
    choose Hk hHk hHkeq using hHk
    set H : Y → ℂ := fun p => ∑ k, a k (π p) * Hk k p with hHdef
    have hHhol : HolomorphicAt n H z := HolomorphicAt.sum _ fun k _ => (hcomp (ha k)).mul (hHk k)
    have hsH : (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ (μ + 1) * H p + t (π p) := by
      filter_upwards [eventually_all.2 hHkeq] with p hp
      have e1 : ∑ k, a k (π p) * h k (π p) = y p ^ (μ + 1) * H p := by
        simp only [hHdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hp k]; ring
      simp only [ht, e1]
      ring
    have hsπ : (GermIdeal.pullback (m := n) π 𝔞).mem z (fun p => s (π p)) :=
      comp_mem_pullback hs (hcomp (h𝔞 _ _ hs)) (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp)
    refine ⟨H, t, ⟨hHhol, fun ℓ hℓ => ⟨(holomorphicAt_of_mem_idealPow hℓ).mul hHhol, ?_⟩⟩, htN, hsH⟩
    obtain ⟨-, d, hd, hℓd⟩ := isInSpanAt_eq_iff.mp ((hpow (μ + 1) z hy.mem ℓ).mp hℓ)
    refine IsInSpanOnAt.congr_right (g := fun p => d p * s (π p))
      (IsInSpanAt.restrict (isInSpanAt_of_eq_mul hsπ (hd.mul (hcomp (h𝔞 _ _ hs))) hd
        (Eventually.of_forall fun p => rfl))) ?_
    filter_upwards [hℓd, hsH, hvan t htN] with p hp1 hp2 hp3 hpN
    rw [hp1, hp2, hp3 hpN]
    ring
  -- the predicate carried through combinations
  let P : (Y → ℂ) → Prop := fun u => ∃ K : Y → ℂ, HolomorphicAt n K z ∧
    IsInSpanOnAt (n := n) N'
      ((logDerivIdealAlong N' (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) 𝔠).mem z) z K ∧
    ∀ᶠ p in 𝓝 z, p ∈ N' → y p * u p = y p ^ (μ + 1) * K p
  have hinD : ∀ H, 𝔠.mem z H → IsInSpanOnAt (n := n) N'
      ((logDerivIdealAlong N' (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) 𝔠).mem z) z H := fun H hH =>
    IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (mem_logDerivIdealAlong_of_mem hH hH.1) hH.1)
  -- Claim B: the generators of `𝓓_{N,E}(𝔞)` at `π z`
  have hB : ∀ σ, LogGen N E 𝔞 (π z) σ → P (fun p => σ (π p)) := by
    rintro σ (hσ | hσ | ⟨e, ξ, f, hξ, hf, rfl⟩)
    · obtain ⟨H, t, hH, ht, hsH⟩ := hC σ hσ
      refine ⟨fun p => y p * H p, hyz.mul hH.1, IsInSpanOnAt.mul_left hyz (hinD H hH), ?_⟩
      filter_upwards [hsH, hvan t ht] with p hp1 hp2 hpN
      rw [hp1, hp2 hpN]
      ring
    · refine ⟨fun _ => 0, holomorphicAt_const 0, IsInSpanAt.restrict BlowupStrictIdeal.isInSpanAt_zero, ?_⟩
      filter_upwards [hvan σ hσ] with p hp hpN
      rw [hp hpN]
      ring
    · obtain ⟨H, t, hH, ht, hsH⟩ := hC f hf
      obtain ⟨B, hBtan, hlift, ρ, hρ, hρeq⟩ := exists_log_tangent_lift hπ hN hEc hAd hzN hy hξ
      have hBhol := hBtan.1.holomorphicAt
      have hgen : (logDerivIdealAlong N' (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) 𝔠).mem z
          (fieldDeriv ez B H) :=
        mem_logDerivIdealAlong_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
          (Or.inr (Or.inr ⟨ez, B, H, hBtan, hH, rfl⟩)) (holomorphicAt_fieldDeriv hzs hBhol hH.1))
      refine ⟨fun p => ((μ : ℂ) + 1) * ρ p * H p + fieldDeriv ez B H p,
        (((holomorphicAt_const _).mul hρ).mul hH.1).add (holomorphicAt_fieldDeriv hzs hBhol hH.1),
        IsInSpanOnAt.add (IsInSpanOnAt.mul_left ((holomorphicAt_const _).mul hρ) (hinD H hH))
          (IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hgen
            (holomorphicAt_fieldDeriv hzs hBhol hH.1))), ?_⟩
      -- `D'(f ∘ π) = D'(y^{μ+1}) H + y^{μ+1} D'(H) + D'(1) (t ∘ π) + D'(t ∘ π)`
      have hsum2 := fieldDeriv_eventuallyEq_sum_mul (ξ := B) (K := 2)
        (a := ![fun p => y p ^ (μ + 1), fun _ => 1]) (s := ![H, fun p => t (π p)])
        (f := f ∘ π) hzs (fun i => by fin_cases i <;> simp [holomorphicAt_pow hyz, holomorphicAt_const])
        (fun i => by fin_cases i <;> simp [hH.1, hcomp ht.1])
        (by filter_upwards [hsH] with p hp; simp [Fin.sum_univ_two, hp])
      filter_upwards [hlift f (h𝔞 _ _ hf), hsum2, fieldDeriv_pow (ξ := B) hzs hyz μ, hρeq, hlift t ht.1,
        hvan t ht, hvan _ (hξ.1.preserves t ht)] with p hp1 hp2 hp3 hp4 hp5 hp6 hp7 hpN
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hp2
      have hp5' : fieldDeriv ez B (fun p => t (π p)) p = y p * fieldDeriv e ξ t (π p) := hp5.symm
      rw [hp1, hp2, hp3, hp4, fieldDeriv_const, hp5', hp7 hpN]
      ring
  -- Claim A: elements of `𝓓_{N,E}(𝔞)` at `π z`
  have hA : ∀ u, (logDerivIdealAlong N E 𝔞).mem (π z) u → P (fun p => u (π p)) := by
    intro u hu
    obtain ⟨-, K, σ, a, hσ, ha, hsum⟩ := mem_logDerivIdealAlong_iff.mp hu
    choose Kσ hKσ hKσspan hKσeq using fun i => hB (σ i) (hσ i)
    refine ⟨fun p => ∑ i, a i (π p) * Kσ i p, HolomorphicAt.sum _ fun i _ => (hcomp (ha i)).mul (hKσ i),
      IsInSpanOnAt.sum _ fun i _ => IsInSpanOnAt.mul_left (hcomp (ha i)) (hKσspan i), ?_⟩
    filter_upwards [hπc.eventually hsum, eventually_all.2 hKσeq] with p hp1 hp2 hpN
    rw [hp1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show y p * (a i (π p) * σ i (π p)) = a i (π p) * (y p * σ i (π p)) by ring, hp2 i hpN]
      ring
  -- Claim A': elements of `π^*𝓓_{N,E}(𝔞)` at `z`
  have hA' : ∀ v, (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E 𝔞)).mem z v → P v := by
    intro v hv
    obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hv
    choose u hu hsu using hs
    choose Ku hKu hKuspan hKueq using fun j => hA (u j) (hu j)
    refine ⟨fun p => ∑ j, c j p * Ku j p, HolomorphicAt.sum _ fun j _ => (hc j).mul (hKu j),
      IsInSpanOnAt.sum _ fun j _ => IsInSpanOnAt.mul_left (hc j) (hKuspan j), ?_⟩
    filter_upwards [hsum, eventually_all.2 hKueq] with p hp1 hp2 hpN
    rw [hp1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hsu j, show y p * (c j p * (u j ∘ π) p) = c j p * (y p * u j (π p)) by
        simp only [Function.comp_apply]; ring, hp2 j hpN]
      ring
  -- the main computation
  obtain ⟨hgh, hgall⟩ := hg
  obtain ⟨K, v, c, hv, hc, hsum⟩ := (hgall _ (hpow_self μ)).2
  choose Kv hKv hKvspan hKveq using fun j => hA' (v j) (hv j)
  have hKtot : HolomorphicAt n (fun p => ∑ j, c j p * Kv j p) z :=
    HolomorphicAt.sum _ fun j _ => (hc j).mul (hKv j)
  have hcanc := eventually_eq_on_of_pow_mul hπ hy (N := N) (μ + 1) (g := g)
    (G := fun p => ∑ j, c j p * Kv j p) (hgh.eventually.mono fun p hp => hp.continuousAt)
    (hKtot.eventually.mono fun p hp => hp.continuousAt) (by
      filter_upwards [hsum, eventually_all.2 hKveq] with p hp1 hp2 hpN
      rw [show y p ^ (μ + 1) * g p = y p * (y p ^ μ * g p) by ring, hp1 hpN, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show y p * (c j p * v j p) = c j p * (y p * v j p) by ring, hp2 j hpN]
        ring)
  exact IsInSpanOnAt.congr_right (IsInSpanOnAt.sum _ fun j _ => IsInSpanOnAt.mul_left (hc j) (hKvspan j))
    hcanc

/-- **The controlled logarithmic inclusion, iterated** (Włodarczyk 2005, Lemma `le:inclusions`; BM08 Lemmas
3.1--3.3, logarithmic): if `𝔞|_N ⊆ 𝓘_C^{μ+r}|_N`, then on `N'`
`(π^* 𝓓_{N,E}^r(𝔞) : 𝒪(-μD))|_{N'} ⊆ 𝓓_{N',E'}^r((π^*𝔞 : 𝒪(-(μ+r)D))|_{N'})|_{N'}`.  Induction on `r`: the
case `r = 1` (`restrictLe_colonAlong_logDerivIdealAlong`) applied to `𝓓_{N,E}^r(𝔞) ⊆ 𝓘_C^{μ+1}` on `N`
(`restrictLe_logIter_idealPow`), then `𝓓_{N',E'}` of the induction hypothesis (`restrictLe_logDerivIdealAlong`). -/
theorem restrictLe_colonAlong_logIter (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N)
    {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) (hAd : ∀ x ∈ C, x ∈ N → IsAdaptedAt n C N E x)
    {𝔞 : GermIdeal n X} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ r μ : ℕ, RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) (μ + r)) →
      RestrictLe (geoStrictTransform π C N)
        (colonAlong n (geoStrictTransform π C N)
          (GermIdeal.pullback (m := n) π ((logDerivIdealAlong N E)^[r] 𝔞))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) μ))
        ((logDerivIdealAlong (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]))^[r]
          (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
            (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (μ + r))))
  | 0, μ, _ => restrictLe_refl fun _ _ hg => hg.1
  | r + 1, μ, hle => by
    have hhol := holomorphicAt_of_mem_logIter (N := N) (E := E) h𝔞 r
    have h1 : RestrictLe N ((logDerivIdealAlong N E)^[r] 𝔞) (idealPow (vanishingIdeal (n := n) C) (μ + 1)) :=
      restrictLe_logIter_idealPow h𝔞 r (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    have h2 := restrictLe_colonAlong_logDerivIdealAlong hπ hN hEc hAd hhol h1
    have h3 := restrictLe_colonAlong_logIter hπ hN hEc hAd h𝔞 r (μ + 1)
      (by rwa [show μ + 1 + r = μ + (r + 1) by omega])
    rw [show μ + 1 + r = μ + (r + 1) by omega] at h3
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine restrictLe_trans h2 (restrictLe_logDerivIdealAlong ?_ ?_ h3)
    · exact fun _ _ hg => hg.1
    · refine holomorphicAt_of_mem_logIter ?_ r
      exact fun _ _ hg => hg.1

end Controlled

end

end Hironaka.HironakaG8LogControlledInclusion

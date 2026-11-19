import Hironaka.Analytic.MultiplierSubadditivityLocal
import Hironaka.Analytic.QuantitativeRegularizationChartGermTransfer
import Hironaka.Analytic.TraceInputSkoda

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Subadditivity of multiplier ideals on a complex manifold

Source: Demailly--Ein--Lazarsfeld, *A subadditivity property of multiplier ideals*, Michigan
Math. J. **48** (2000), Theorem 2.6, cited by Copy-4 as `eq:subadditivity`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex`,
`sec:positive-current`): for a `θ`-psh `φ`, `𝓘(qkφ) ⊆ 𝓘(qφ)^k`.

* `multiplierIdeal_add_le_mul` — **`𝓘((c₁ + c₂)φ) ⊆ 𝓘(c₁φ) 𝓘(c₂φ)`** for every `θ`-psh `φ` on a
  complex manifold of positive dimension and `c₁, c₂ > 0`.  In the chart at `x`,
  `Φ = φ ∘ e⁻¹ + ρ` is plurisubharmonic (`ThetaPlurisubharmonic`), the germs of `𝓘(cφ)_x` are the
  germs `L²` for `e^{-cΦ}` near `e(x)`
  (`QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_corrected_of_mem_multiplierIdeal`,
  `DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart`), and the local theorem
  `MultiplierSubadditivityLocal.inGermSpan_mul_of_multiplierIntegrableAt` applies to
  `P₁ = c₁Φ`, `P₂ = c₂Φ`.
* `multiplierIdeal_le_idealPow` — **`𝓘(kqφ) ⊆ 𝓘(qφ)^k`** by induction on `k` (`𝓘(0) = 0`).
* `multiplierIdeal_natMul_le_idealPow` — the clause of Copy-4 input (I2) in the form of
  `Copy4FixedDataFromInputs.TraceInput`: `∀ q k, 1 ≤ q → 𝓘((qk)φ) ⊆ 𝓘(qφ)^k`.
* `TraceInputAtPointNoSub`, `traceInputAtPoint_of_noSub` — `TraceInputSkoda.TraceInputAtPoint` with
  the subadditivity clause dropped, and the proof that it is no longer an input;
  `exists_copy4StepOneData_of_inputs_noSub` — the conclusion of `ct22Copy4_exists_stepOneData` from
  `hRP`, (I1), and (I2)+(I3) without the subadditivity clause.

Sorry-free.  No existing statement is changed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ENNReal

universe u

namespace Hironaka.MultiplierSubadditivity

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.PositiveClasses
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  IdealWeightPowers MultiplierIdealBergmanNadelIdeal MultiplierSubadditivityLocal
  QuantitativeRegularizationChartGermTransfer

/-! ### Scalars in the weight -/

/-- `c₁ a + c₂ a = (c₁ + c₂) a` in `EReal`, for `c₁, c₂ > 0` (including `a = ±∞`). -/
theorem coe_mul_add_coe_mul {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (a : EReal) :
    (c₁ : EReal) * a + (c₂ : EReal) * a = ((c₁ + c₂ : ℝ) : EReal) * a := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos hc₁, EReal.coe_mul_bot_of_pos hc₂,
        EReal.coe_mul_bot_of_pos (add_pos hc₁ hc₂), EReal.bot_add]
  | top =>
      rw [EReal.coe_mul_top_of_pos hc₁, EReal.coe_mul_top_of_pos hc₂,
        EReal.coe_mul_top_of_pos (add_pos hc₁ hc₂), EReal.top_add_top]
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, add_mul]

/-- Weighted integrability only depends on the weight `e^{-cφ}`. -/
theorem multiplierIntegrableAt_of_weight_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] {φ ψ : E → EReal} {c c' : ℝ} (hc' : 0 < c') {f : E → ℂ} {x : E}
    {μ : Measure E} (h : ∀ y, multiplierWeight c (φ y) = multiplierWeight c' (ψ y))
    (hf : MultiplierIntegrableAt φ c f x μ) : MultiplierIntegrableAt ψ c' f x μ := by
  obtain ⟨-, U, hU, hxU, hd, hm, hlt⟩ := hf
  have heq : multiplierDensity φ c f = multiplierDensity ψ c' f :=
    funext fun y => by simp only [multiplierDensity, h]
  exact ⟨hc', U, hU, hxU, hd, heq ▸ hm, heq ▸ hlt⟩

theorem multiplierWeight_one_mul (c : ℝ) (a : EReal) :
    multiplierWeight 1 ((c : EReal) * a) = multiplierWeight c a := by
  simp only [multiplierWeight, EReal.coe_one, one_mul]

/-! ### `𝓘((c₁ + c₂)φ) ⊆ 𝓘(c₁φ) 𝓘(c₂φ)` -/

section Manifold

variable {d' : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (d' + 1)) M]
  [IsComplexManifold (d' + 1) M]

/-- **Subadditivity of multiplier ideals** (Demailly--Ein--Lazarsfeld 2000, Theorem 2.6) on a
complex manifold of dimension `d' + 1`: `𝓘((c₁ + c₂)φ) ⊆ 𝓘(c₁φ) 𝓘(c₂φ)` for `θ`-psh `φ`. -/
theorem multiplierIdeal_add_le_mul_succ {θ : SmoothRealForm (d' + 1) M 2} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (multiplierIdeal (n := d' + 1) (c₁ + c₂) φ).Le
      ((multiplierIdeal (n := d' + 1) c₁ φ).mul (multiplierIdeal (n := d' + 1) c₂ φ)) := by
  intro x g hg
  set e : ComplexChart (d' + 1) M := complexChartAt (n := d' + 1) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel (d' + 1) := e.val x with hz₀
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hφ e z₀ (e.val.map_source hxs)
  obtain ⟨hWo, -, hρs, -⟩ := hρ
  set Φ : ComplexModel (d' + 1) → EReal := fun w => chartFunction φ e w + (ρ w : EReal) with hΦ
  have hgΦ : MultiplierIntegrableAt Φ (c₁ + c₂) (fun w => g (e.val.symm w)) z₀ volume :=
    multiplierIntegrableAt_corrected_of_mem_multiplierIdeal hφ e hWo hρs.continuousOn hpsh
      (add_pos hc₁ hc₂) hxs hz₀W hg
  set P₁ : ComplexModel (d' + 1) → EReal := fun w => (c₁ : EReal) * Φ w with hP₁
  set P₂ : ComplexModel (d' + 1) → EReal := fun w => (c₂ : EReal) * Φ w with hP₂
  have hf : MultiplierIntegrableAt (fun y => P₁ y + P₂ y) 1 (fun w => g (e.val.symm w)) z₀
      volume :=
    multiplierIntegrableAt_of_weight_eq one_pos (fun y => by
      show multiplierWeight (c₁ + c₂) (Φ y) =
        multiplierWeight 1 ((c₁ : EReal) * Φ y + (c₂ : EReal) * Φ y)
      rw [coe_mul_add_coe_mul hc₁ hc₂, multiplierWeight_one_mul]) hgΦ
  obtain ⟨N, sv, A, hsv, hA, hev⟩ := inGermSpan_mul_of_multiplierIntegrableAt hWo
    (hpsh.const_mul hc₁) (hpsh.const_mul hc₂) hz₀W hf
  choose aa bb haa hbb hsveq using hsv
  have haa' : ∀ i, (multiplierIdeal (n := d' + 1) c₁ φ).mem x (fun p => aa i (e.val p)) :=
    fun i => DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hφ hc₁ e hWo
      hρs.continuousOn hxs hz₀W
      (multiplierIntegrableAt_of_weight_eq hc₁ (fun y => multiplierWeight_one_mul c₁ (Φ y))
        (haa i))
  have hbb' : ∀ i, (multiplierIdeal (n := d' + 1) c₂ φ).mem x (fun p => bb i (e.val p)) :=
    fun i => DemaillyApproximationAnalyticType.mem_multiplierIdeal_of_chart hφ hc₂ e hWo
      hρs.continuousOn hxs hz₀W
      (multiplierIntegrableAt_of_weight_eq hc₂ (fun y => multiplierWeight_one_mul c₂ (Φ y))
        (hbb i))
  refine ⟨hg.1, N, fun i p => aa i (e.val p) * bb i (e.val p), fun i p => A i (e.val p),
    fun i => ⟨_, _, haa' i, hbb' i, rfl⟩,
    fun i => DemaillyApproximationAnalyticType.holomorphicAt_comp_atlas hxs (hA i), ?_⟩
  filter_upwards [e.val.open_source.mem_nhds hxs, (e.val.continuousAt hxs).eventually hev]
    with p hp hpev
  have h1 : g p = g (e.val.symm (e.val p)) := by rw [e.val.left_inv hp]
  rw [h1, hpev]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsveq i]

end Manifold

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Subadditivity of multiplier ideals** (Demailly--Ein--Lazarsfeld 2000, Theorem 2.6):
`𝓘((c₁ + c₂)φ) ⊆ 𝓘(c₁φ) 𝓘(c₂φ)` for every `θ`-psh `φ` on a complex manifold of positive
dimension and `c₁, c₂ > 0`. -/
theorem multiplierIdeal_add_le_mul (hn : 0 < n) {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (multiplierIdeal (n := n) (c₁ + c₂) φ).Le
      ((multiplierIdeal (n := n) c₁ φ).mul (multiplierIdeal (n := n) c₂ φ)) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact multiplierIdeal_add_le_mul_succ hφ hc₁ hc₂

/-- The product ideal is monotone in its first factor. -/
theorem mul_le_mul_left' {𝔞 𝔞' 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔞') :
    (𝔞.mul 𝔟).Le (𝔞'.mul 𝔟) := fun x _ hg => by
  obtain ⟨hgh, N, s, a, hs, ha, hsum⟩ := hg
  refine ⟨hgh, N, s, a, fun i => ?_, ha, hsum⟩
  obtain ⟨a', b', ha', hb', hs'⟩ := hs i
  exact ⟨a', b', h x a' ha', hb', hs'⟩

/-- `𝓘(0 · φ)` has no members: multiplier integrability requires a positive exponent. -/
theorem multiplierIdeal_zero_le (φ : M → EReal) (𝔟 : GermIdeal n M) :
    (multiplierIdeal (n := n) 0 φ).Le 𝔟 := fun _ _ hg => absurd hg.2.1 (lt_irrefl 0)

/-- `𝔞 ⊆ 𝒪 · 𝔞`. -/
theorem le_unitIdeal_mul (𝔞 : GermIdeal n M) (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    𝔞.Le ((unitIdeal n M).mul 𝔞) := fun x g hg => by
  show IsInSpanAt (n := n) (fun s => ∃ a b, (unitIdeal n M).mem x a ∧ 𝔞.mem x b ∧ s = a * b) x g
  refine isInSpanAt_of_eq_mul (s := g) (a := fun _ => (1 : ℂ))
    ⟨fun _ => 1, g, holomorphicAt_const 1, hg, ?_⟩ (h𝔞 x g hg) (holomorphicAt_const 1)
    (Eventually.of_forall fun y => by simp)
  funext y
  simp

/-- **`𝓘(kqφ) ⊆ 𝓘(qφ)^k`** (DEL00, by induction on `k`). -/
theorem multiplierIdeal_le_idealPow (hn : 0 < n) {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) {q : ℝ} (hq : 0 < q) :
    ∀ k : ℕ, (multiplierIdeal (n := n) ((k : ℝ) * q) φ).Le
      (idealPow (multiplierIdeal (n := n) q φ) k)
  | 0 => by
      rw [Nat.cast_zero, zero_mul]
      exact multiplierIdeal_zero_le φ _
  | 1 => by
      rw [Nat.cast_one, one_mul, idealPow_succ, idealPow_zero]
      exact le_unitIdeal_mul _ fun _ _ hg => hg.1
  | k + 2 => by
      have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * q := mul_pos (by positivity) hq
      have hsplit : (((k + 2 : ℕ) : ℝ) * q) = ((k + 1 : ℕ) : ℝ) * q + q := by push_cast; ring
      rw [hsplit, idealPow_succ]
      intro x g hg
      exact mul_le_mul_left' (multiplierIdeal_le_idealPow hn hφ hq (k + 1)) x g
        (multiplierIdeal_add_le_mul hn hφ hk hq x g hg)

/-- **The subadditivity clause of Copy-4 input (I2)**, in the form of
`Copy4FixedDataFromInputs.TraceInput`: `𝓘((qk)φ) ⊆ 𝓘(qφ)^k` for `q ≥ 1`. -/
theorem multiplierIdeal_natMul_le_idealPow (hn : 0 < n) {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : ThetaPlurisubharmonic θ φ) (q k : ℕ) (hq : 1 ≤ q) :
    (multiplierIdeal (n := n) ((q * k : ℕ) : ℝ) φ).Le
      (idealPow (multiplierIdeal (n := n) (q : ℝ) φ) k) := by
  have h := multiplierIdeal_le_idealPow hn hφ (q := (q : ℝ)) (by exact_mod_cast hq) k
  rwa [show ((k : ℝ) * (q : ℝ)) = ((q * k : ℕ) : ℝ) by push_cast; ring] at h

end General

/-! ### Copy-4 input (I2) without the subadditivity clause -/

section TraceInput

open PrincipalizationCopy4StepFiveCoreReduction SubmanifoldChartedSpace RestrictedIdealWeight
  PrincipalizationStepOneInterface Copy4FixedDataAssembly Copy4FixedDataFromInputs
  TraceInputSkoda

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **(I2) + (I3) with Copy-4's Skoda hypothesis and without the subadditivity clause**:
`TraceInputSkoda.TraceInputAtPoint` minus `∀ q k, 1 ≤ q → 𝓘((qk)φ) ⊆ 𝓘(qφ)^k`, which is now a
theorem (`multiplierIdeal_natMul_le_idealPow`). -/
def TraceInputAtPointNoSub [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  ∃ φ : X → EReal, IsThetaPshPotential θ.val φ ∧
    (∃ x ∈ V.carrier, lelongNumber (n := n) φ x = 0) ∧
    ∀ C : ℕ, 2 ≤ C → ∃ m : ℕ, 1 ≤ m ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 1 ≤ r ∧
        ∃ (idealB : GermIdeal n X) (ψB : X → EReal) (φK : V.carrier → EReal),
          idealB.IsCoherent ∧ ¬ V.carrier ⊆ idealB.zeroLocus ∧
          HasAnalyticSingularitiesOfType (n := n) ψB 1 idealB ∧
          RestrictLe V.carrier
            (idealB.mul (idealPow (multiplierIdeal (n := n) (m : ℝ) φ) ((C - 1) * r)))
            (multiplierIdeal (n := n) ((C * m * r : ℕ) : ℝ) φ) ∧
          IsLevelPotential omega θ V hV δ₀ φK ∧
          SameSingularityTypeOn φK
            (fun v => ((1 / ((m * r : ℕ) : ℝ) : ℝ) : EReal) * ψB v.1) univ

/-- **DEL00 supplies the subadditivity clause of (I2).** -/
theorem traceInputAtPoint_of_noSub [CompactSpace X] (hn : 0 < n) (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (h : TraceInputAtPointNoSub omega θ V hV) : TraceInputAtPoint omega θ V hV := by
  obtain ⟨φ, hφ, hpt, hqea⟩ := h
  exact ⟨φ, hφ, hpt, fun q k hq => multiplierIdeal_natMul_le_idealPow hn hφ.1 q k hq, hqea⟩

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `lem:relative-principalization`,
(I1) and (I2)+(I3) with Copy-4's Skoda hypothesis and no subadditivity hypothesis.** -/
theorem exists_copy4StepOneData_of_inputs_noSub (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n) (hI1 : AmbientFixedInput omega θ V)
    (hI2 : TraceInputAtPointNoSub omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) :=
  exists_copy4StepOneData_of_inputs_atPoint hRP omega θ V hV hdim_pos hdim_lt hI1
    (traceInputAtPoint_of_noSub (hdim_pos.trans hdim_lt) omega θ V hV hI2)

end TraceInput

end

end Hironaka.MultiplierSubadditivity

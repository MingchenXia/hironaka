import Hironaka.Analytic.Copy4FixedDataProducers

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `Copy4FixedData` from three source-shaped inputs, in Copy-4's order of constants

Source: Copy-4, `sec:setup` (Skoda at `x_*`, the restricted ambient ideals), `sec:fixed-data`
(`eq:def-R`, `eq:PhiR-lower`, `eq:constants`), `sec:positive-current` (`lem:positive-rooftop`,
`eq:def-K`, `eq:def-K-ell`, `lem:ideal-comparison`, `eq:subadditivity`) and `sec:ambient`
(`eq:def-TM`) (`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:
1383-1750`).

`Copy4FixedDataAssembly.exists_copy4StepOneData_of_fixedData` proves the conclusion of the named
input `ct22Copy4_exists_stepOneData` from `lem:relative-principalization` and a
`Copy4FixedData`.  This module produces a `Copy4FixedData` from three inputs that mention
neither a modification nor any of the derived objects (`U_M`, `Ψ_m`, `x₀`, the weights, the
constants):

* `AmbientFixedInput` (I1, `sec:fixed-data` on `X`): a Kähler current `R = θ + ddᶜΦ_R ≥ δ_R ω`
  (`eq:def-R`), a coherent `𝔧` with `V ⊄ Z(𝔧)` (Copy-4: `𝔧 = 𝓘_{Z'}`), and `eq:PhiR-lower` in
  the form `AmbientPhiRLowerSource` for weights of `𝓘_V` and `𝔧`;
* `TraceInput` (I2 + I3) for a `θ`-psh potential `φ` (Copy-4: `V_θ`):
  - (I2) `V ⊄ Z(𝓘(qφ))` for every `q ≥ 1` (Skoda at `x_*`, `sec:setup`) and
    `𝓘(qkφ) ⊆ 𝓘(qφ)^k` (`eq:subadditivity`, Demailly--Ein--Lazarsfeld);
  - (I3) `sec:positive-current` on `V`: for every `C ≥ 2` a level `m ≥ 1` and `δ₀ > 0` such that
    for arbitrarily large `r` (Copy-4: `ℓ = m r` dyadic) there are a coherent `𝔅̃` with
    `V ⊄ Z(𝔅̃)`, a weight `ψ_𝔅` of `𝔅̃`, `eq:ideal-comparison`
    `Res_V(𝔅̃ 𝓘(mφ)^{(C-1)r}) ⊆ Res_V 𝓘(Cmr φ)`, and `φ_{K,ℓ}` on `V` with
    `θ|_V - δ₀ ω|_V + ddᶜφ_{K,ℓ} ≥ 0` and the singularity type of `ℓ^{-1} ψ_𝔅` (Copy-4:
    analytic singularities of type `(ℓ^{-1}, 𝔅)`, `𝔅 = 𝔅̃|_V`).

* `nonempty_copy4FixedData` — **(I1) + (I2, I3) give `Copy4FixedData`**, following Copy-4's
  order: `c₀` (`lem:regularization`, only `(X, ω)`) → `L` (`L δ_R > c₀`) → `C`
  (`C - 1 ≥ L A_R`) → `m`, `δ₀` (I3) → `𝔅_m = 𝓘(mφ)` (Nadel), `Ψ_m`, `x₀` → `ℓ = m r` large
  (`M = Cℓ > L`, `M ≥ 2(C-1)c_Ψ/δ₀`) → `U_M` (`lem:regularization` at `M`, Nadel) → `τ`.
* `exists_copy4StepOneData_of_inputs` — with `hRP`: **the conclusion of
  `ct22Copy4_exists_stepOneData`**.

Sorry-free.  No existing statement is changed: this is the proved half of the split proposed in
I-0691, refined to inputs on `X` and `V`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.Copy4FixedDataFromInputs

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction SubmanifoldChartedSpace IdealWeightPowers
  RestrictedIdealWeight PrincipalizationStepOneInterface Copy4FixedDataAssembly
  Copy4FixedDataProducers

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **(I1) `sec:fixed-data` on `X`**: `eq:def-R` (`R = θ + ddᶜΦ_R ≥ δ_R ω`), a coherent `𝔧` with
`V ⊄ Z(𝔧)` (Copy-4: the ideal of the other components of `E_nK(α)`), weights of `𝓘_V` and `𝔧`,
and `eq:PhiR-lower` (`AmbientPhiRLowerSource`, constant `A_R ≥ 0`). -/
def AmbientFixedInput [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X) : Prop :=
  ∃ (PhiR : X → EReal) (δR : ℝ) (idealJ : GermIdeal n X) (psiIV psij : X → EReal) (A : ℝ),
    0 < δR ∧ IsThetaPshPotential (θ - δR • omega.form).val PhiR ∧
    HasAnalyticSingularitiesOfType (n := n) psiIV 1 (vanishingIdeal (n := n) V.carrier) ∧
    HasAnalyticSingularitiesOfType (n := n) psij 1 idealJ ∧
    ¬ V.carrier ⊆ idealJ.zeroLocus ∧ 0 ≤ A ∧
    Nonempty (AmbientPhiRLowerSource n X A PhiR psiIV psij)

/-- `φ_K` is a potential on `V` of `θ|_V - δ₀ ω|_V` (with `V`'s complex structure): Copy-4's
`K_ℓ = γ + ddᶜφ_{K,ℓ} ≥ δ₀ ω_V` (`eq:def-K-ell`). -/
def IsLevelPotential [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (δ₀ : ℝ) (φK : V.carrier → EReal) :
    Prop :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  IsThetaPshPotential
    (ClosedRealOneOneForm.pullback (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2)
      (θ - δ₀ • omega.form)).val φK

/-- **(I2) + (I3): the multiplier ideals of `φ = V_θ` and `sec:positive-current` on `V`.**  See
the module docstring. -/
def TraceInput [CompactSpace X] (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  ∃ φ : X → EReal, IsThetaPshPotential θ.val φ ∧
    (∀ q : ℕ, 1 ≤ q → ¬ V.carrier ⊆ (multiplierIdeal (n := n) (q : ℝ) φ).zeroLocus) ∧
    (∀ q k : ℕ, 1 ≤ q → (multiplierIdeal (n := n) ((q * k : ℕ) : ℝ) φ).Le
        (idealPow (multiplierIdeal (n := n) (q : ℝ) φ) k)) ∧
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

/-- **(I1) + (I2, I3) give `Copy4FixedData`**, the constants chosen in Copy-4's order. -/
theorem nonempty_copy4FixedData [CompactSpace X] [ConnectedSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hI1 : AmbientFixedInput omega θ V) (hI2 : TraceInput omega θ V hV) :
    Nonempty (Copy4FixedData omega θ V hV) := by
  classical
  -- `c₀` first: `lem:regularization` on `(X, ω)`
  obtain ⟨c₀, hc₀, hUMgen⟩ := exists_regularization_UM hn omega
  obtain ⟨PhiR, δR, idealJ, psiIV, psij, A, hδR, hPhiR, hIV, hj, hVJ, hA, ⟨src⟩⟩ := hI1
  obtain ⟨φ, hφ, hskoda, hsub, hqea⟩ := hI2
  -- `eq:constants`: `L`, then `C`
  set L : ℝ := c₀ / δR + 1 with hLdef
  have hL : 0 < L := by positivity
  have hconst : c₀ < L * δR := by
    rw [hLdef, add_mul, div_mul_cancel₀ _ hδR.ne']
    linarith
  set C : ℕ := ⌈L * A⌉₊ + 2 with hCdef
  have hC2 : 2 ≤ C := by omega
  have hC1 : 1 ≤ C := by omega
  have hCR : ((C : ℕ) : ℝ) = (⌈L * A⌉₊ : ℝ) + 2 := by rw [hCdef]; push_cast; ring
  -- the level `m` and `δ₀` (`sec:positive-current`)
  obtain ⟨m, hm, δ₀, hδ₀, hfam⟩ := hqea C hC2
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbcoh : (multiplierIdeal (n := n) (m : ℝ) φ).IsCoherent :=
    MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos hn hφ.1 hmR
  obtain ⟨psib, hb⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent hbcoh
  -- `Ψ_m` and `x₀`
  obtain ⟨x₀, hx₀V, Ψ, cΨ, hcΨ, hΨpsh, hΨtype, hΨx₀⟩ :=
    exists_idealFunction_of_not_subset omega V hj.2.1 hbcoh hVJ (hskoda m hm)
  -- `ℓ = m r` large
  obtain ⟨r, hNr, hr, idealB, ψB, φK, hBcoh, hVB, hψB, hcomp, hφK, hφKtype⟩ :=
    hfam (⌈L⌉₊ + ⌈2 * ((C : ℝ) - 1) * cΨ / δ₀⌉₊ + 1)
  have hM1 : 1 ≤ C * m * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrM : r ≤ C * m * r := by
    calc r = 1 * 1 * r := by ring
      _ ≤ C * m * r := Nat.mul_le_mul_right r (Nat.mul_le_mul hC1 hm)
  have hMR : (0 : ℝ) < ((C * m * r : ℕ) : ℝ) := by exact_mod_cast hM1
  have hNM : ((⌈L⌉₊ + ⌈2 * ((C : ℝ) - 1) * cΨ / δ₀⌉₊ + 1 : ℕ) : ℝ) ≤ ((C * m * r : ℕ) : ℝ) := by
    exact_mod_cast hNr.trans hrM
  push_cast at hNM
  have hceil1 := Nat.le_ceil L
  have hceil2 := Nat.le_ceil (2 * ((C : ℝ) - 1) * cΨ / δ₀)
  have hceil0 : (0 : ℝ) ≤ (⌈2 * ((C : ℝ) - 1) * cΨ / δ₀⌉₊ : ℝ) := Nat.cast_nonneg _
  have hceil0' : (0 : ℝ) ≤ (⌈L⌉₊ : ℝ) := Nat.cast_nonneg _
  have hLM : L < ((C * m * r : ℕ) : ℝ) := by push_cast; linarith
  have hκ : 2 * ((C : ℝ) - 1) * cΨ / δ₀ ≤ ((C * m * r : ℕ) : ℝ) := by push_cast; linarith
  -- `U_M` at the level `M = C m r`
  obtain ⟨psiBM, UM, hpsiBM, hUM, hUMlower⟩ := hUMgen θ φ hφ (C * m * r) hM1
  -- `τ`
  have hε : 0 < (L * δR - c₀) / ((C * m * r : ℕ) : ℝ) := div_pos (by linarith) hMR
  obtain ⟨τQ, hτpos, hτlt⟩ :=
    exists_rat_btwn (lt_min hε (half_pos hδ₀))
  have hτR : (0 : ℝ) < (τQ : ℝ) := by exact_mod_cast hτpos
  -- casts
  have hCQ : ((C : ℚ) : ℝ) = (C : ℝ) := Rat.cast_natCast C
  have hMQ : (((C * m * r : ℕ) : ℚ) : ℝ) = ((C * m * r : ℕ) : ℝ) := Rat.cast_natCast _
  have hcoef : ((C : ℚ) : ℝ) / (((C * m * r : ℕ) : ℚ) : ℝ) = 1 / ((m * r : ℕ) : ℝ) := by
    rw [hCQ, hMQ]
    have hC0 : (C : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hpow : C * m * r = m * (C * r) := by ring
  have hexp : r + (C - 1) * r = C * r := by
    calc r + (C - 1) * r = (C - 1 + 1) * r := by ring
      _ = C * r := by rw [Nat.sub_add_cancel hC1]
  refine ⟨
    { PhiR := PhiR
      δR := δR
      hPhiR := hPhiR
      psiIV := psiIV
      psij := psij
      idealJ := idealJ
      hIV := hIV
      hj := hj
      A := A
      hA := hA
      hPhiRsrc := src
      c₀ := c₀
      hc₀ := hc₀.le
      levQ := ((C * m * r : ℕ) : ℚ)
      UM := UM
      psiBM := psiBM
      idealBM := multiplierIdeal (n := n) ((C * m * r : ℕ) : ℝ) φ
      hpsiBM := hpsiBM
      hUM := hUM
      hUMlower := hUMlower
      hVBM := hskoda _ hM1
      Ψ := Ψ
      psib := psib
      idealb := multiplierIdeal (n := n) (m : ℝ) φ
      cΨ := cΨ
      δ := δ₀ / 2
      hΨpsh := hΨpsh
      hΨtype := hΨtype
      hb := hb
      hlev := by exact_mod_cast hM1
      L := L
      CQ := (C : ℚ)
      τQ := τQ
      hL := hL
      hLlev := by rw [hMQ]; exact hLM
      hconst := hconst
      hC := by exact_mod_cast hC2
      hCA := by
        rw [hCQ, hCR]
        linarith [Nat.le_ceil (L * A)]
      hκδ := by
        rw [hCQ, hMQ, div_mul_eq_mul_div, div_le_iff₀ hMR]
        have h2 := hκ
        rw [div_le_iff₀ hδ₀] at h2
        linarith [mul_comm δ₀ ((C * m * r : ℕ) : ℝ)]
      hτ := by exact_mod_cast hτpos
      hτε := by rw [hMQ]; exact (hτlt.trans_le (min_le_left _ _)).le
      x₀ := x₀
      hx₀V := hx₀V
      hΨx₀ := hΨx₀
      r := r
      p := (C - 1) * r
      hr := hr
      hrp := by
        rw [hexp, hCQ]
        push_cast
        ring
      hle := by
        rw [hexp, hpow]
        exact hsub m (C * r) hm
      idealB := idealB
      hBcoh := hBcoh
      hcomp := hcomp
      hVB := hVB
      ψB := ψB
      hψB := hψB
      δ₀ := δ₀
      hδτ := by linarith [(hτlt.trans_le (min_le_right _ _))]
      φK := φK
      hφK := hφK
      hφKtype := by rw [hcoef]; exact hφKtype }⟩

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `lem:relative-principalization`
and the inputs (I1)--(I3) on `X` and `V`.** -/
theorem exists_copy4StepOneData_of_inputs (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n) (hI1 : AmbientFixedInput omega θ V)
    (hI2 : TraceInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) := by
  obtain ⟨F⟩ := nonempty_copy4FixedData (hdim_pos.trans hdim_lt) omega θ V hV hI1 hI2
  exact exists_copy4StepOneData_of_fixedData hRP omega θ V hV hdim_lt F

end

end Hironaka.Copy4FixedDataFromInputs

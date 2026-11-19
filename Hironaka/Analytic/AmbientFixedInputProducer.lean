import Hironaka.Analytic.Copy4FixedDataFromInputs
import Hironaka.Analytic.NonKahlerLocusPoleSet
import Hironaka.Analytic.AmbientPhiRSourceOfAnalyticSingularities
import Hironaka.Analytic.KahlerDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `sec:fixed-data` on `X` from the ideal `𝔧` of the other components

Source: Copy-4, `sec:fixed-data`, `eq:def-R` and `eq:PhiR-lower`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1497-1527`):

> By `sec:nK`, there is a Kähler current with analytic singularities `R = θ + ddᶜΦ_R ∈ α`,
> `R ≥ δ_R ω`, with polar set `E_nK(α)` [...] Let `Z'` be the union of the irreducible
> components of `E_nK(α)` other than `V`, and put `𝔧 := 𝓘_{Z'}` [...] Rückert's
> Nullstellensatz and compactness therefore give a constant `A_R > 0` such that, locally on
> `X`, `Φ_R ≥ A_R(ψ_{𝓘_V} + ψ_𝔧) + O(1)`.

* `ambientFixedInput_of_cover` — the input (I1) of `Copy4FixedDataFromInputs`
  (`AmbientFixedInput`) from bigness of `α = {θ}`, a closed connected submanifold `V`, and a
  coherent `𝔧` with `E_nK(α) ⊆ V ∪ Z(𝔧)` and `V ⊄ Z(𝔧)` (Copy-4: `𝔧 = 𝓘_{Z'}`).  `Φ_R` comes from
  `NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus` (the route's existing
  Boucksom producer), normalized to the representative `θ`; `δ_R` from domination of `ω` by the
  Kähler form of the current; `A_R` from
  `AmbientPhiRSourceOfAnalyticSingularities.exists_ambientPhiRLowerSource_of_type`, i.e. from the
  named classical input `UniformNullstellensatzPower.demaillyII422_exists_idealPow_le_of_zeroLocus_subset`
  (Demailly CADG II.4.22).
* `exists_copy4StepOneData_of_cover` — with `hRP` and the input (I2)+(I3) (`TraceInput`): the
  conclusion of `ct22Copy4_exists_stepOneData`.

**Axiom status.**  Both theorems are sorry-free since TN23's discharge of Demailly 1992
(`df8d7063`, the Boucksom producer's root) and TN-CLASSICAL's proof of Demailly II.4.22
(`RueckertNullstellensatz`, run 0113): `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.  The coherence of `𝓘_{Z'}` (Cartan) remains the
hypothesis `h𝔧`, and `hRP` (Hironaka) and `TraceInput` remain hypotheses of
`exists_copy4StepOneData_of_cover` (on the route `hRP` is discharged by
`RelativePrincipalization.exists_factorizationData`, proved in place from the canonical resolution invariant).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AmbientFixedInputProducer

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  Copy4FixedDataFromInputs PrincipalizationStepOneInterface

noncomputable section

section Presentation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Subtracting a continuous real function keeps the analytic singularity type. -/
theorem hasAnalyticSingularitiesOfType_sub_continuous {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) {h : M → ℝ}
    (hh : Continuous h) :
    HasAnalyticSingularitiesOfType (n := n) (fun x => φ x - (h x : EReal)) c 𝔞 := by
  obtain ⟨hc, hcoh, hloc⟩ := hφ
  refine ⟨hc, hcoh, fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hgd, hgiff, R, C₀, hRb, heq⟩ := hloc x
  set U' : Set M := U ∩ {y | |h y - h x| < 1} with hU'
  have hU'o : IsOpen U' :=
    hU.inter (isOpen_lt ((hh.sub continuous_const).abs) continuous_const)
  refine ⟨U', hU'o, ⟨hxU, by simp⟩, N, g, fun i => (hgd i).mono inter_subset_left,
    fun y hy => hgiff y hy.1, fun y => R y - h y, C₀ + |h x| + 1, fun y hy => ?_,
    fun y hy => ?_⟩
  · have h1 := hRb y hy.1
    have h2 : |h y - h x| < 1 := hy.2
    have h3 : |h y| ≤ |h x| + 1 := by
      have := abs_sub_abs_le_abs_sub (h y) (h x)
      linarith
    calc |R y - h y| ≤ |R y| + |h y| := abs_sub _ _
      _ ≤ C₀ + (|h x| + 1) := add_le_add h1 h3
      _ = C₀ + |h x| + 1 := by ring
  · show φ y - (h y : EReal) = ((c : ℝ) : EReal) * generatorLog g y + ((R y - h y : ℝ) : EReal)
    rw [heq y hy.1, sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add, ← sub_eq_add_neg]

/-- A closed set lies in the zero locus of its vanishing ideal. -/
theorem subset_zeroLocus_vanishingIdeal (A : Set M) :
    A ⊆ (vanishingIdeal (n := n) A).zeroLocus :=
  fun _ hx _ hg => hg.2.self_of_nhds hx

end Presentation

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **(I1) from the ideal `𝔧` of the other components** (Copy-4 `sec:fixed-data`).  See the
module docstring; carries `sorryAx` through the Boucksom producer and Demailly II.4.22. -/
theorem ambientFixedInput_of_cover [CompactSpace X] (hn : 0 < n) (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) {𝔧 : GermIdeal n X}
    (h𝔧 : 𝔧.IsCoherent)
    (hcover : nonKahlerLocus (RealBottChern.ofRepresentative θ) ⊆ V.carrier ∪ 𝔧.zeroLocus)
    (hV𝔧 : ¬ V.carrier ⊆ 𝔧.zeroLocus) : AmbientFixedInput omega θ V := by
  classical
  -- `eq:def-R`: Boucksom's current, with polar set `E_nK(α)`
  obtain ⟨T, ⟨c, 𝔞R, hTtype⟩, -, hpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbig
  obtain ⟨h, hh, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  set φ : X → EReal := fun x => T.potential x - (h x : EReal) with hφdef
  have hφ' : IsThetaPshPotential (θ - T.lowerBound.form).val φ := by
    refine thetaPshPotential_sub_smooth
      (θ := (T.representative - T.lowerBound.form).val)
      (η := (θ - T.lowerBound.form).val) hh (fun e z hz => ?_) T.strictlyPsh
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, hrel e z hz]
    abel
  -- `δ_R`: `ω` is dominated by the Kähler form of the current
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omega.form)
  have hb : (T.lowerBound.form - A⁻¹ • omega.form).val.IsSemipositive := by
    have heq : T.lowerBound.form - A⁻¹ • omega.form =
        A⁻¹ • (-omega.form + A • T.lowerBound.form) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul hsemi (inv_nonneg.mpr hA.le)
  have hPhiR : IsThetaPshPotential (θ - A⁻¹ • omega.form).val φ := by
    have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ' hb
    have heq : θ - T.lowerBound.form + (T.lowerBound.form - A⁻¹ • omega.form) =
        θ - A⁻¹ • omega.form := by abel
    rwa [heq] at h1
  -- the weights of `𝓘_V` and `𝔧`
  obtain ⟨psiIV, hIV⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent
    (ExcessIdealPrincipalization.isCoherent_vanishingIdeal_of_isClosedConnectedSubmanifold hV)
  obtain ⟨psij, hj⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent h𝔧
  -- `Φ_R`'s presentation and the containment of zero loci
  have hhc : Continuous h := continuous_iff_continuousAt.mpr fun x =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn isOpen_univ
      (fun e => by simpa using hh e) (mem_univ x)
  have hφtype := hasAnalyticSingularitiesOfType_sub_continuous hTtype hhc
  have hz : 𝔞R.zeroLocus ⊆ ((vanishingIdeal (n := n) V.carrier).mul 𝔧).zeroLocus := by
    rw [← StepFourNoComponentContainsW.poleSet_eq_zeroLocus hTtype, hpole]
    intro x hx
    rcases hcover hx with hxV | hxJ
    · rw [RestrictLeCalculus.mul_comm']
      exact RestrictLeCalculus.zeroLocus_right_subset_mul _ _
        (subset_zeroLocus_vanishingIdeal V.carrier hxV)
    · exact RestrictLeCalculus.zeroLocus_right_subset_mul _ _ hxJ
  -- `eq:PhiR-lower` (Rückert's Nullstellensatz)
  obtain ⟨AR, hAR, hsrc⟩ :=
    AmbientPhiRSourceOfAnalyticSingularities.exists_ambientPhiRLowerSource_of_type hIV hj hφtype hz
  exact ⟨φ, A⁻¹, 𝔧, psiIV, psij, AR, inv_pos.mpr hA, hPhiR, hIV, hj, hV𝔧, hAR.le, hsrc⟩

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `hRP`, bigness, the ideal `𝔧` of the
other components, and (I2)+(I3).**  Carries `sorryAx` as `ambientFixedInput_of_cover` does. -/
theorem exists_copy4StepOneData_of_cover (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n) {𝔧 : GermIdeal n X} (h𝔧 : 𝔧.IsCoherent)
    (hcover : nonKahlerLocus (RealBottChern.ofRepresentative θ) ⊆ V.carrier ∪ 𝔧.zeroLocus)
    (hV𝔧 : ¬ V.carrier ⊆ 𝔧.zeroLocus) (hI2 : TraceInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) :=
  exists_copy4StepOneData_of_inputs hRP omega θ V hV hdim_pos hdim_lt
    (ambientFixedInput_of_cover (hdim_pos.trans hdim_lt) omega θ hbig V hV h𝔧 hcover hV𝔧) hI2

end

end Hironaka.AmbientFixedInputProducer

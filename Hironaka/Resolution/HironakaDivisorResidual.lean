/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDivisorPowers
import Hironaka.Analytic.ActualInvertibleIdealDifference
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Blowup.SmoothHypersurfaceIdeal
import Hironaka.Resolution.EmbeddedFromResolution
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

/-!
# Actual connected-component multiplicities and residual divisor ideals

The exponent is produced by local constancy of `divExp` and connectedness
of the genuine smooth carrier. The residual is the actual invertible
colon ideal, and its full stalkwise factorization is proved.

Mathematical source: Włodarczyk 2005, Step 2, monomial/nonmonomial
decomposition. This isolates a connected smooth hypersurface, rather
than assuming a global multiplicity on a disconnected SNC list member.
The same single-component argument appears in the SGPT project, but
this module uses only the Hironaka local algebra and geometry and
imports no SGPT module. Blueprint: `hironaka-divisor-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDivisorResidual

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.DivisorExponent
  Hironaka.IdealWeightPowers
  Hironaka.GermIdealTotalTransform
  Hironaka.HironakaDivisorPowers
  Hironaka.RelativePrincipalizationSpan
  Hironaka.InvertibleIdealQuotient

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Coherence and actual nonzero stalk members make the existing divisor
exponent locally constant on a genuine smooth carrier. -/
theorem isLocallyConstant_divExp_on_submanifold {W : Set M}
    (hW : IsClosedSubmanifold n W) {𝔞 : GermIdeal n M}
    (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAt 𝔞 x) :
    IsLocallyConstant (fun p : W => divExp n 𝔞 W (p : M)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨d, hd⟩ := hW.2 p p.property
  have hlocal := eventually_divExp_eq h𝔞 hd (Eventually.of_forall hne)
  have hincl : Tendsto (Subtype.val : W → M) (𝓝 p) (𝓝 (p : M)) :=
    continuous_subtype_val.continuousAt.tendsto
  filter_upwards [hincl.eventually hlocal] with q hq
  exact hq q.property

/-- A nonempty connected smooth carrier produces one actual finite
exponent and its divisibility characterization at every original point. -/
theorem exists_divExp_on_connected_submanifold {W : Set M} {d : ℕ}
    (hW : IsClosedConnectedSubmanifold n W d) {𝔞 : GermIdeal n M}
    (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAt 𝔞 x) :
    ∃ a : ℕ, ∀ x ∈ W, ∀ r : ℕ, IsDivNear n 𝔞 W r x ↔ r ≤ a := by
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  obtain ⟨p, hp⟩ := hW.2.1.nonempty
  have hloc := isLocallyConstant_divExp_on_submanifold
    ⟨hW.1, fun x hx => ⟨d, hW.2.2 x hx⟩⟩ h𝔞 hne
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine ⟨divExp n 𝔞 W p, fun x hx r => ?_⟩
  have hconst := hloc.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : W) (⟨p, hp⟩ : W)
  exact (isDivNear_iff_le_divExp hhol hx (hne x)).trans (by rw [hconst])

/-- A genuine smooth hypersurface has no ambient interior; this supplies
the nonvanishing clause for its actual vanishing ideal. -/
theorem interior_eq_empty_of_smooth_hypersurface {W : Set M} {d : ℕ}
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hd : d + 1 = n) :
    interior W = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hfull := EmbeddedFromResolution.regularAtDim_of_mem_nhds (n := n)
    (mem_interior_iff_mem_nhds.mp hx)
  have heq := RegularPointDimension.eq_of_regularAtDim (hW x (interior_subset hx)) hfull
  omega

/-- Remove the actual maximal multiplicity of one connected smooth
hypersurface from an effective divisor, with an invertible colon residual
and an equality of the complete original germ ideals. -/
theorem exists_residual_on_connected_hypersurface {W : Set M} {d : ℕ}
    (hW : IsClosedConnectedSubmanifold n W d) (hd : d + 1 = n)
    (D : EffectiveDivisor n M) :
    ∃ (a : ℕ) (R : EffectiveDivisor n M),
      (∀ x ∈ W, ∀ r : ℕ, IsDivNear n D.ideal W r x ↔ r ≤ a) ∧
      D.ideal = (idealPow (vanishingIdeal (n := n) W) a).mul R.ideal ∧
      R.ideal = colon D.ideal (idealPow (vanishingIdeal (n := n) W) a) ∧
      ¬ W ⊆ R.support := by
  have hDcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  obtain ⟨a, ha⟩ := exists_divExp_on_connected_submanifold hW hDcoh
    (fun x => isNonzeroAt_of_isInvertible D.isInvertible x)
  have hIW : (vanishingIdeal (n := n) W).IsInvertible :=
    BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne hW.1
      (interior_eq_empty_of_smooth_hypersurface hW.2.2 hd)
      (fun x hx => ⟨d, hW.2.2 x hx, hd⟩)
  have hL : (idealPow (vanishingIdeal (n := n) W) a).IsInvertible :=
    BlowupExceptionalDivisor.isInvertible_idealPow hIW a
  have hle : D.ideal.Le (idealPow (vanishingIdeal (n := n) W) a) :=
    HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hDcoh
      ⟨hW.1, fun x hx => ⟨d, hW.2.2 x hx⟩⟩
      (fun x hx => ((ha x hx a).mpr le_rfl).self_of_nhds hx)
  let R : EffectiveDivisor n M :=
    ⟨colon D.ideal (idealPow (vanishingIdeal (n := n) W) a),
      ActualInvertibleIdealDifference.isInvertible_colon D.isInvertible hL hle⟩
  have hDR : D.ideal = (idealPow (vanishingIdeal (n := n) W) a).mul R.ideal :=
    GermIdeal.ext (funext fun x => funext fun g => propext
      ⟨fun hg => le_mul_colon hDcoh hL hle x g hg,
        fun hg => mul_colon_le hDcoh x g hg⟩)
  refine ⟨a, R, ha, hDR, rfl, ?_⟩
  intro hcontains
  have hRcoh := DivisorMetric.isCoherent_of_isInvertible R.isInvertible
  have hRle : R.ideal.Le (vanishingIdeal (n := n) W) := by
    intro x g hg
    refine ⟨GermIdeal.IsCoherent.holomorphicAt_mem hRcoh hg, ?_⟩
    filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hRcoh hg] with y hy hyW
    exact hcontains hyW g hy
  have hsucc : D.ideal.Le (idealPow (vanishingIdeal (n := n) W) (a + 1)) := by
    rw [hDR]
    intro x g hg
    rw [idealPow_succ]
    exact mem_mul_iff.mpr ((mem_mul_iff.mp hg).mono
      (fun t ⟨p, q, hp, hq, heq⟩ => ⟨p, q, hp, hRle x q hq, heq⟩))
  obtain ⟨p, hp⟩ := hW.2.1.nonempty
  have hnear : IsDivNear n D.ideal W (a + 1) p :=
    (isDivNear_iff hDcoh (hW.2.2 p hp)).mpr (hsucc p)
  have := (ha p hp (a + 1)).mp hnear
  omega

/-- The actual connected-component producer supplies the factorization
of every genuine power of the original divisor ideal. -/
theorem exists_residual_power_on_connected_hypersurface {W : Set M} {d : ℕ}
    (hW : IsClosedConnectedSubmanifold n W d) (hd : d + 1 = n)
    (D : EffectiveDivisor n M) (k : ℕ) :
    ∃ (a : ℕ) (R : EffectiveDivisor n M),
      (∀ x ∈ W, ∀ r : ℕ, IsDivNear n D.ideal W r x ↔ r ≤ a) ∧
      D.ideal = (idealPow (vanishingIdeal (n := n) W) a).mul R.ideal ∧
      idealPow D.ideal k =
        (idealPow (vanishingIdeal (n := n) W) (a * k)).mul (idealPow R.ideal k) ∧
      ¬ W ⊆ R.support := by
  obtain ⟨a, R, ha, hD, -, hnot⟩ := exists_residual_on_connected_hypersurface hW hd D
  have hWcoh := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (⟨hW.1, fun x hx => ⟨d, hW.2.2 x hx⟩⟩ : IsClosedSubmanifold n W)
  refine ⟨a, R, ha, hD, ?_, hnot⟩
  rw [hD, BlowupControlledTransform.idealPow_mul
    (GermIdealPullbackCalculus.isCoherent_idealPow hWcoh a)
    (DivisorMetric.isCoherent_of_isInvertible R.isInvertible),
    MarkedIdealOperationsTransform.idealPow_idealPow hWcoh a k]

/-- The actual ordered product of the indicated powers of vanishing
ideals; the empty product is the holomorphic unit ideal. -/
def componentPowerProduct : List (Set M × ℕ) → GermIdeal n M
  | [] => unitIdeal n M
  | (W, a) :: A => (idealPow (vanishingIdeal (n := n) W) a).mul (componentPowerProduct A)

/-- Coherence is produced for the whole genuine finite product. -/
theorem isCoherent_componentPowerProduct (A : List (Set M × ℕ))
    (hA : ∀ p ∈ A, IsClosedSubmanifold n p.1) :
    (componentPowerProduct (n := n) A).IsCoherent := by
  induction A with
  | nil => exact isCoherent_unitIdeal
  | cons p A ih =>
    exact IdealWeightPowers.isCoherent_mul
      (GermIdealPullbackCalculus.isCoherent_idealPow
        (VanishingIdealCoherent.isCoherent_vanishingIdeal (hA p (by simp))) p.2)
      (ih fun q hq => hA q (List.mem_cons_of_mem p hq))

/-- Every finite list of genuine connected smooth hypersurfaces produces
an actual product factorization and a residual containing none of them.
An empty list and repetitions are allowed; no unit-residual conclusion
or disconnected-member multiplicity is assumed or asserted. -/
theorem exists_residual_on_finite_connected_hypersurfaces
    (E : List (Set M))
    (hE : ∀ W ∈ E, ∃ d, IsClosedConnectedSubmanifold n W d ∧ d + 1 = n)
    (D : EffectiveDivisor n M) :
    ∃ A : List (Set M × ℕ), A.map Prod.fst = E ∧
      ∃ R : EffectiveDivisor n M,
        D.ideal = (componentPowerProduct (n := n) A).mul R.ideal ∧
        (∀ W ∈ E, ¬ W ⊆ R.support) ∧ R.support ⊆ D.support := by
  induction E generalizing D with
  | nil =>
    refine ⟨[], rfl, D, ?_, by simp, Subset.rfl⟩
    exact (BlowupControlledTransform.unitIdeal_mul
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)).symm
  | cons W E ih =>
    obtain ⟨d, hW, hd⟩ := hE W (by simp)
    obtain ⟨a, D₁, -, hD, -, hWnot⟩ := exists_residual_on_connected_hypersurface hW hd D
    have hEt : ∀ V ∈ E, ∃ d, IsClosedConnectedSubmanifold n V d ∧ d + 1 = n :=
      fun V hV => hE V (List.mem_cons_of_mem W hV)
    obtain ⟨A, hAE, R, hD₁, hnot, hsupport⟩ := ih hEt D₁
    have hAcoh : (componentPowerProduct (n := n) A).IsCoherent := by
      apply isCoherent_componentPowerProduct
      intro p hp
      have hpmem : p.1 ∈ E := by
        rw [← hAE]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨j, hV, -⟩ := hEt p.1 hpmem
      exact ⟨hV.1, fun x hx => ⟨j, hV.2.2 x hx⟩⟩
    have hD₁support : D₁.support ⊆ D.support := by
      change D₁.ideal.zeroLocus ⊆ D.ideal.zeroLocus
      rw [hD]
      exact RestrictLeCalculus.zeroLocus_right_subset_mul _ _
    refine ⟨(W, a) :: A, ?_, R, ?_, ?_, hsupport.trans hD₁support⟩
    · simpa only [List.map_cons, Prod.fst] using congrArg (List.cons W) hAE
    · change D.ideal = ((idealPow (vanishingIdeal (n := n) W) a).mul
        (componentPowerProduct (n := n) A)).mul R.ideal
      rw [hD, hD₁, mul_assoc
        (GermIdealPullbackCalculus.isCoherent_idealPow
          (VanishingIdealCoherent.isCoherent_vanishingIdeal
            (⟨hW.1, fun x hx => ⟨d, hW.2.2 x hx⟩⟩ : IsClosedSubmanifold n W)) a)
        hAcoh (DivisorMetric.isCoherent_of_isInvertible R.isInvertible)]
    · intro V hV
      rcases List.mem_cons.mp hV with rfl | hV
      · exact fun h => hWnot (h.trans hsupport)
      · exact hnot V hV

end

end Hironaka.HironakaDivisorResidual

import Hironaka.Analytic.IEnvelopeOrder
import Hironaka.Analytic.TruncatedSingularityEnvelope

set_option autoImplicit false

/-!
# The P-envelope comparison from strong openness

`IncreasingStrongOpenness n` is the chart-level form of the strong openness
theorem for increasing sequences (Xia, Theorem 1.4.4, `xia-sgpt:page-0043`;
Guan--Zhou): for a locally uniformly bounded increasing sequence of PSH
functions on an open set, every weighted-L² holomorphic germ for the
regularized limit is already one for some member of the sequence.  The
regularized limit agrees with the pointwise limit Lebesgue-almost everywhere,
so this is the source statement.  It appears below as an explicit hypothesis; it is
proved in `Hironaka.StrongOpennessFromRegularOhsawaTakegoshi` from the regular case of the
Ohsawa--Takegoshi theorem, which is the one input not proved in this workspace.

Assuming it, `φ` and `P_θ[φ]` have the same multiplier germs at every positive
exponent (Xia, Proposition 3.2.9, `xia-sgpt:page-0142`): locally the
truncated envelopes `(φ + a₀ + j) ∧ V_θ` corrected by a smooth potential
form such a sequence, their regularized limit is `P_θ[φ]` corrected by the
same potential, and each of them has the singularity type of `φ`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Hironaka

noncomputable section


open Hironaka.IEnvelope
open Hironaka.QuasiEquisingularApproximation

/-- Strong openness for increasing sequences, in one complex chart model. -/
def IncreasingStrongOpenness (n : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (W : Set (ComplexModel n)) (v : ℕ → ComplexModel n → EReal),
    IsOpen W → (∀ j, PlurisubharmonicOn (v j) W) →
    (∀ y ∈ W, Monotone fun j => v j y) →
    LocallyUniformlyBoundedAbove (range v) W →
    ∀ z ∈ W, ∀ c : ℝ, 0 < c → ∀ f : ComplexModel n → ℂ, AnalyticAt ℂ f z →
      MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c f z volume →
      ∃ j, MultiplierIntegrableAt (v j) c f z volume

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Assuming strong openness, the regularized limit of an increasing sequence
of normalized theta-PSH potentials, each multiplier-ideal below `φ`, is again
multiplier-ideal below `φ`. -/
theorem iOrderOnManifold_uscRegularization_iSup_of_strongOpenness
    (hSO : IncreasingStrongOpenness n) {θ : SmoothRealForm n M 2}
    (hlocal : HasSmoothLocalPotentials θ) {φ : M → EReal}
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential θ (u j))
    (hu0 : ∀ j, u j ≤ 0) (hmono : Monotone u)
    (huφ : ∀ j, IOrderOnManifold (n := n) (u j) φ) :
    IOrderOnManifold (n := n) (uscRegularization (⨆ j, u j)) φ := by
  intro c hc e z hz f hf hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  set P := uscRegularization (⨆ j, u j) with hP
  have hPpot : IsThetaPshPotential θ P := by
    refine ⟨thetaPlurisubharmonic_uscRegularization_sSup hlocal (range_nonempty u)
      (by rintro _ ⟨j, rfl⟩; exact hu j) (by rintro _ ⟨j, rfl⟩; exact hu0 j), ?_⟩
    exact (hu 0).2.mono ((le_iSup u 0).trans (le_uscRegularization _))
  obtain ⟨W, ρ, hzW, hρ⟩ := hlocal e z hz
  let v : ℕ → ComplexModel n → EReal := fun j y => chartFunction (u j) e y + (ρ y : EReal)
  have hvpsh : ∀ j, PlurisubharmonicOn (v j) W := fun j =>
    chartCorrectedFamily_plurisubharmonicOn (F := {u j})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hu j) e hρ _
      ⟨u j, mem_singleton _, rfl⟩
  have hvmono : ∀ y ∈ W, Monotone fun j => v j y := fun y _ i j hij =>
    add_le_add (hmono hij _) le_rfl
  have hvbound : LocallyUniformlyBoundedAbove (range v) W := by
    refine (chartCorrectedFamily_locallyUniformlyBoundedAbove (F := range u)
      (by rintro _ ⟨j, rfl⟩; exact hu0 j) e hρ.1 hρ.2.2.1).mono_family ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨u j, ⟨j, rfl⟩, rfl⟩
  have hρc : ∀ y ∈ W, ContinuousAt ρ y := fun y hy =>
    ((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).continuousAt
  have hsup : (⨆ j, v j) = fun y => chartFunction (⨆ j, u j) e y + (ρ y : EReal) := by
    funext y
    simp only [iSup_apply, chartFunction, v]
    exact iSup_add_coe (fun j => u j (e.val.symm y)) (ρ y)
  have hVeq : ∀ y ∈ W, uscRegularization (⨆ j, v j) y =
      chartFunction P e y + (ρ y : EReal) := by
    intro y hy
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hρc y hy),
      uscRegularization_chartFunction_apply _ e (hρ.2.1 hy)]
  have hPpsh : PlurisubharmonicOn
      (fun y => chartFunction P e y + (ρ y : EReal)) W :=
    chartCorrectedFamily_plurisubharmonicOn (F := {P})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hPpot) e hρ _
      ⟨_, mem_singleton _, rfl⟩
  have hVqpsh : QuasiPlurisubharmonicAt (uscRegularization (⨆ j, v j)) z :=
    (hPpsh z hzW).quasiPlurisubharmonicAt.congr
      (eventually_of_mem (hρ.1.mem_nhds hzW) fun y hy => (hVeq y hy).symm)
  have hlow : ∀ᶠ y in 𝓝 z, ρ z - 1 < ρ y := hρc z hzW (Ioi_mem_nhds (by linarith))
  have hhigh : ∀ᶠ y in 𝓝 z, ρ y < ρ z + 1 := hρc z hzW (Iio_mem_nhds (by linarith))
  -- The chart germ of `P` is transported to the corrected regularized limit.
  have h2 : MultiplierIntegrableAt (uscRegularization (⨆ j, v j)) c f z volume := by
    refine multiplierIntegrableAt_of_moreSingularAt hVqpsh ⟨1 - ρ z, ?_⟩ hmem
    filter_upwards [hlow, hρ.1.mem_nhds hzW] with y hy hyW
    rw [hVeq y hyW, add_assoc, ← EReal.coe_add]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by linarith))
  obtain ⟨j, hj⟩ := hSO W v hρ.1 hvpsh hvmono hvbound z hzW c hc f hf h2
  have h4 : MultiplierIntegrableAt (chartFunction (u j) e) c f z volume := by
    refine multiplierIntegrableAt_of_moreSingularAt
      ((hu j).1.quasiPlurisubharmonic e z hz) ⟨ρ z + 1, ?_⟩ hj
    filter_upwards [hhigh] with y hy
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hy.le)
  exact huφ j c hc e z hz f hf h4

/-- Assuming strong openness, `I(c P_θ[φ]) ⊆ I(cφ)` for every positive
exponent. -/
theorem iOrderOnManifold_singularityEnvelope_self_of_strongOpenness
    [CompactSpace M] [Nonempty M] (hSO : IncreasingStrongOpenness n)
    {θ : SmoothRealForm n M 2} (hlocal : HasSmoothLocalPotentials θ)
    {φ : M → EReal} (hφ : IsThetaPshPotential θ φ) :
    IOrderOnManifold (n := n) (singularityEnvelope θ φ) φ := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_sub_const
  have hmemj : ∀ j : ℕ, (fun x => φ x - (C : EReal)) ∈
      truncatedSingularityCompetitors θ φ (-C + j) := by
    intro j
    refine ⟨hC, fun x => ?_⟩
    change φ x - (C : EReal) ≤ _
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith))
  rw [singularityEnvelope_eq_uscRegularization_iSup_truncated θ φ (-C)]
  refine iOrderOnManifold_uscRegularization_iSup_of_strongOpenness hSO hlocal
    (fun j => truncatedSingularityEnvelope_isThetaPshPotential hlocal ⟨_, hmemj j⟩)
    (fun j => truncatedSingularityEnvelope_le_zero θ φ _)
    (fun i j hij => truncatedSingularityEnvelope_mono θ φ (by
      have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
      linarith)) fun j => ?_
  exact iOrderOnManifold_of_le_add hφ.1.quasiPlurisubharmonic
    (truncatedSingularityEnvelope_le_add hφ.1.quasiPlurisubharmonic θ _)

/-- Xia, Proposition 3.2.9, assuming strong openness: a genuine theta-PSH
potential is I-equivalent to its ordinary P-envelope. -/
theorem iEquivalent_singularityEnvelope_of_strongOpenness
    [CompactSpace M] [Nonempty M] (hSO : IncreasingStrongOpenness n)
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal)
    (hφ : IsThetaPshPotential θ φ) :
    IEquivalentOnManifold (n := n) φ (singularityEnvelope θ φ) :=
  ⟨iOrderOnManifold_singularityEnvelope hclosed h11 hlocal hφ,
    iOrderOnManifold_singularityEnvelope_self_of_strongOpenness hSO hlocal hφ⟩

end

end Hironaka

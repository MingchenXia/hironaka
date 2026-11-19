import Hironaka.Analytic.ThetaPshEnvelopes
import Hironaka.Analytic.ERealChordUSC

set_option autoImplicit false

/-!
# Truncated singularity envelopes

For a real level `a`, the truncated envelope of `φ` is the regularized
supremum of normalized theta-PSH potentials lying below `φ + a` everywhere;
in Xia's notation this is `(φ + a) ∧ V_θ`.  It is a genuine theta-PSH
potential with the same singularity type as `φ` as soon as a normalized
translate of `φ` is a competitor.

The truncated envelopes increase with the level, and the ordinary
singularity envelope `P_θ[φ]` is the upper-semicontinuous regularization of
their supremum along any sequence of levels tending to `+∞`
(Xia, equation (3.4), `xia-sgpt:page-0142`).
-/

open Set

namespace Hironaka

noncomputable section



variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Normalized theta-PSH potentials lying below `φ + a` at every point. -/
def truncatedSingularityCompetitors (θ : SmoothRealForm n M 2) (φ : M → EReal)
    (a : ℝ) : Set (M → EReal) :=
  {u | u ∈ thetaPshCompetitors θ ∧ ∀ x, u x ≤ φ x + (a : EReal)}

/-- The truncated envelope `(φ + a) ∧ V_θ`. -/
def truncatedSingularityEnvelope (θ : SmoothRealForm n M 2) (φ : M → EReal)
    (a : ℝ) : M → EReal :=
  uscRegularization (sSup (truncatedSingularityCompetitors θ φ a))

theorem le_truncatedSingularityEnvelope {θ : SmoothRealForm n M 2}
    {φ u : M → EReal} {a : ℝ} (hu : IsThetaPshPotential θ u) (hu0 : u ≤ 0)
    (hua : ∀ x, u x ≤ φ x + (a : EReal)) :
    u ≤ truncatedSingularityEnvelope θ φ a :=
  (le_sSup (s := truncatedSingularityCompetitors θ φ a) ⟨⟨hu, hu0⟩, hua⟩).trans
    (le_uscRegularization _)

theorem truncatedSingularityEnvelope_le_zero (θ : SmoothRealForm n M 2)
    (φ : M → EReal) (a : ℝ) : truncatedSingularityEnvelope θ φ a ≤ 0 :=
  uscRegularization_le upperSemicontinuous_const
    (sSup_le fun _ hu => hu.1.2)

/-- The truncated envelope stays below the obstacle `φ + a`. -/
theorem truncatedSingularityEnvelope_le_add {φ : M → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (θ : SmoothRealForm n M 2)
    (a : ℝ) (x : M) :
    truncatedSingularityEnvelope θ φ a x ≤ φ x + (a : EReal) :=
  uscRegularization_le (g := fun x => φ x + (a : EReal))
    (upperSemicontinuous_add_coe_const hφ.upperSemicontinuous a)
    (sSup_le fun _ hu => hu.2) x

theorem truncatedSingularityEnvelope_mono (θ : SmoothRealForm n M 2)
    (φ : M → EReal) {a b : ℝ} (hab : a ≤ b) :
    truncatedSingularityEnvelope θ φ a ≤ truncatedSingularityEnvelope θ φ b := by
  apply uscRegularization_mono
  apply sSup_le_sSup
  intro u hu
  exact ⟨hu.1, fun x => (hu.2 x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hab))⟩

/-- A nonempty truncated envelope is a genuine theta-PSH potential. -/
theorem truncatedSingularityEnvelope_isThetaPshPotential
    {θ : SmoothRealForm n M 2} (hlocal : HasSmoothLocalPotentials θ)
    {φ : M → EReal} {a : ℝ}
    (hne : (truncatedSingularityCompetitors θ φ a).Nonempty) :
    IsThetaPshPotential θ (truncatedSingularityEnvelope θ φ a) := by
  refine ⟨thetaPlurisubharmonic_uscRegularization_sSup hlocal hne
    (fun _ hu => hu.1.1) (fun _ hu => hu.1.2), ?_⟩
  obtain ⟨u, hu, hua⟩ := hne
  exact hu.1.2.mono (le_truncatedSingularityEnvelope hu.1 hu.2 hua)

theorem truncatedSingularityEnvelope_le_singularityEnvelope
    (θ : SmoothRealForm n M 2) (φ : M → EReal) (a : ℝ) :
    truncatedSingularityEnvelope θ φ a ≤ singularityEnvelope θ φ :=
  uscRegularization_le (upperSemicontinuous_singularityEnvelope θ φ)
    (sSup_le fun _ hu => le_singularityEnvelope hu.1.1 hu.1.2
      ⟨a, fun x _ => hu.2 x⟩)

/-- Xia, equation (3.4): the singularity envelope is the regularized
supremum of the truncated envelopes at the levels `a₀ + j`. -/
theorem singularityEnvelope_eq_uscRegularization_iSup_truncated
    (θ : SmoothRealForm n M 2) (φ : M → EReal) (a₀ : ℝ) :
    singularityEnvelope θ φ =
      uscRegularization (⨆ j : ℕ, truncatedSingularityEnvelope θ φ (a₀ + j)) := by
  apply le_antisymm
  · apply uscRegularization_mono
    refine sSup_le fun u hu => ?_
    obtain ⟨⟨hu, hu0⟩, C, hC⟩ := hu
    obtain ⟨j, hj⟩ := exists_nat_ge (C - a₀)
    refine le_trans ?_ (le_iSup (fun j : ℕ => truncatedSingularityEnvelope θ φ (a₀ + j)) j)
    refine le_truncatedSingularityEnvelope hu hu0 fun x => (hC x (mem_univ x)).trans ?_
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
  · exact uscRegularization_le (upperSemicontinuous_singularityEnvelope θ φ)
      (iSup_le fun j => truncatedSingularityEnvelope_le_singularityEnvelope θ φ _)

end

end Hironaka

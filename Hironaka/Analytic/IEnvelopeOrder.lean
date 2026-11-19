import Hironaka.Analytic.IEnvelopeCompetitors
import Hironaka.Analytic.PotentialTheory.Envelopes
import Hironaka.Analytic.PotentialTheory.MultiplierIdeals

set_option autoImplicit false

/-!
# The elementary half of the envelope multiplier-ideal comparisons

A global additive comparison `φ ≤ ψ + C` with a quasi-PSH majorant `ψ` gives
the multiplier-ideal order `φ ≼_I ψ` at every positive exponent.  Since a
normalized translate of a genuine theta-PSH potential lies below both its
ordinary P-envelope and its I-envelope, this proves the inclusions
`I(cφ) ⊆ I(c P_θ[φ])` and `I(cφ) ⊆ I(c P_θ[φ]_I)`.

The reverse inclusions (Xia, Propositions 3.2.6 and 3.2.9) need the strong
openness theorem and are not asserted here.
-/

open Set Filter

namespace Hironaka

noncomputable section

open Hironaka
open Hironaka.IEnvelope
open Hironaka.QuasiEquisingularApproximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A global additive comparison with a quasi-PSH majorant gives the
multiplier-ideal order. -/
theorem iOrderOnManifold_of_le_add {φ ψ : M → EReal}
    (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {C : ℝ}
    (h : ∀ x, φ x ≤ ψ x + (C : EReal)) :
    IOrderOnManifold (n := n) φ ψ := by
  intro c _ e z hz f _ hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact multiplierIntegrableAt_of_moreSingularAt (hψ e z hz)
    ⟨C, Eventually.of_forall fun y => h _⟩ hmem

/-- A pointwise comparison with a quasi-PSH majorant gives the
multiplier-ideal order. -/
theorem iOrderOnManifold_of_le {φ ψ : M → EReal}
    (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) (h : φ ≤ ψ) :
    IOrderOnManifold (n := n) φ ψ :=
  iOrderOnManifold_of_le_add (C := 0) hψ fun x => by simpa using h x

/-- `I(cφ) ⊆ I(c P_θ[φ]_I)` for every positive exponent. -/
theorem iOrderOnManifold_iSingularityEnvelope
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2}
    (hlocal : HasSmoothLocalPotentials θ) {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) :
    IOrderOnManifold (n := n) φ (iSingularityEnvelope θ φ) := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_sub_const
  have hle : (fun x => φ x - (C : EReal)) ≤ iSingularityEnvelope θ φ :=
    le_iSingularityEnvelope hC.1 hC.2 (iEquivalentOnManifold_sub_const φ C)
  exact (iEquivalentOnManifold_sub_const φ C).2.trans
    (iOrderOnManifold_of_le
      (iSingularityEnvelope_isThetaPshPotential_of_potential hlocal hφ).1.quasiPlurisubharmonic
      hle)

/-- `I(cφ) ⊆ I(c P_θ[φ])` for every positive exponent. -/
theorem iOrderOnManifold_singularityEnvelope
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2}
    (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) :
    IOrderOnManifold (n := n) φ (singularityEnvelope θ φ) := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_singularityCompetitor
  have hle : (fun x => φ x - (C : EReal)) ≤ singularityEnvelope θ φ :=
    le_singularityEnvelope hC.1.1 hC.1.2 hC.2
  exact (iEquivalentOnManifold_sub_const φ C).2.trans
    (iOrderOnManifold_of_le
      (_root_.Hironaka.PotentialTheory.Envelopes.singularityEnvelope_isThetaPshPotential θ hclosed h11 hlocal φ hφ).1.quasiPlurisubharmonic
      hle)

end

end Hironaka

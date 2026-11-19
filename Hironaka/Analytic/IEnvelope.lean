import Hironaka.Analytic.PotentialTheory.EnvelopesBasic
import Hironaka.Analytic.QuasiEquisingularApproximation

set_option autoImplicit false

/-!
# Multiplier-ideal order and the I-envelope

This file encodes Hironaka, Definition 3.2.2, using the project's actual local
holomorphic-germ multiplier predicate.  The fixed-background I-envelope is
the upper-semicontinuous regularization of the supremum of normalized
theta-psh potentials with the same multiplier germs as the reference
potential at every positive exponent.

Only the definition and its order-theoretic laws are recorded here.  The
analytic facts that the envelope is theta-psh, that P-order implies I-order,
and that I-good potentials are dS-limits remain separate Pending theorems.
-/

open Set

namespace Hironaka.IEnvelope

noncomputable section

open QuasiEquisingularApproximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Multiplier-ideal order on a complex manifold: every positive-level
multiplier germ of `φ` is a multiplier germ of `ψ`. -/
def IOrderOnManifold (φ ψ : M → EReal) : Prop :=
  ∀ c : ℝ, 0 < c → MultiplierIdealIncluded (M := M) (n := n) φ c ψ c

/-- Equality of all positive-level local multiplier ideals. -/
def IEquivalentOnManifold (φ ψ : M → EReal) : Prop :=
  IOrderOnManifold (n := n) φ ψ ∧ IOrderOnManifold (n := n) ψ φ

theorem iOrderOnManifold_refl (φ : M → EReal) : IOrderOnManifold (n := n) φ φ := by
  intro c _
  exact fun _ _ _ _ _ hmem => hmem

theorem IOrderOnManifold.trans {φ ψ η : M → EReal}
    (hφψ : IOrderOnManifold (n := n) φ ψ)
    (hψη : IOrderOnManifold (n := n) ψ η) :
    IOrderOnManifold (n := n) φ η := by
  intro c hc
  exact fun e z hz f hf hmem =>
    hψη c hc e z hz f hf (hφψ c hc e z hz f hf hmem)

theorem IEquivalentOnManifold.refl (φ : M → EReal) :
    IEquivalentOnManifold (n := n) φ φ :=
  ⟨iOrderOnManifold_refl φ, iOrderOnManifold_refl φ⟩

theorem IEquivalentOnManifold.symm {φ ψ : M → EReal}
    (h : IEquivalentOnManifold (n := n) φ ψ) :
    IEquivalentOnManifold (n := n) ψ φ :=
  ⟨h.2, h.1⟩

theorem IEquivalentOnManifold.trans {φ ψ η : M → EReal}
    (hφψ : IEquivalentOnManifold (n := n) φ ψ)
    (hψη : IEquivalentOnManifold (n := n) ψ η) :
    IEquivalentOnManifold (n := n) φ η :=
  ⟨hφψ.1.trans hψη.1, hψη.2.trans hφψ.2⟩

variable [IsComplexManifold n M]

/-- The normalized theta-psh competitors in the I-envelope of `φ`. -/
def iSingularityCompetitors (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    Set (M → EReal) :=
  {u | u ∈ thetaPshCompetitors θ ∧ IEquivalentOnManifold (n := n) u φ}

theorem iSingularityCompetitors_eq_of_iEquivalent
    {θ : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (h : IEquivalentOnManifold (n := n) φ ψ) :
    iSingularityCompetitors θ φ = iSingularityCompetitors θ ψ := by
  ext u
  constructor
  · rintro ⟨hu, huφ⟩
    exact ⟨hu, huφ.trans h⟩
  · rintro ⟨hu, huψ⟩
    exact ⟨hu, huψ.trans h.symm⟩

/-- The pointwise supremum before upper-semicontinuous regularization. -/
def iSingularitySupremum (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    M → EReal :=
  sSup (iSingularityCompetitors θ φ)

theorem iSingularitySupremum_apply
    (θ : SmoothRealForm n M 2) (φ : M → EReal) (x : M) :
    iSingularitySupremum θ φ x =
      ⨆ u ∈ iSingularityCompetitors θ φ, u x := by
  simp only [iSingularitySupremum, sSup_apply, iSup_subtype]

/-- The fixed-background I-envelope `P_θ[φ]_I`. -/
def iSingularityEnvelope (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    M → EReal :=
  uscRegularization (iSingularitySupremum θ φ)

theorem iSingularitySupremum_le_envelope
    (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    iSingularitySupremum θ φ ≤ iSingularityEnvelope θ φ :=
  le_uscRegularization _

theorem le_iSingularityEnvelope {θ : SmoothRealForm n M 2}
    {φ u : M → EReal} (hu : IsThetaPshPotential θ u) (hu0 : u ≤ 0)
    (huφ : IEquivalentOnManifold (n := n) u φ) : u ≤ iSingularityEnvelope θ φ :=
  (le_sSup (s := iSingularityCompetitors θ φ) ⟨⟨hu, hu0⟩, huφ⟩).trans
    (iSingularitySupremum_le_envelope θ φ)

theorem upperSemicontinuous_iSingularityEnvelope
    (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    UpperSemicontinuous (iSingularityEnvelope θ φ) :=
  upperSemicontinuous_uscRegularization _

/-- The I-envelope is the least upper-semicontinuous majorant of all
normalized genuine theta-PSH potentials I-equivalent to the reference.  This
order-theoretic statement does not assert that the envelope is theta-PSH. -/
theorem iSingularityEnvelope_le_iff {θ : SmoothRealForm n M 2}
    {φ g : M → EReal} (hg : UpperSemicontinuous g) :
    iSingularityEnvelope θ φ ≤ g ↔
      ∀ u, IsThetaPshPotential θ u → u ≤ 0 →
        IEquivalentOnManifold (n := n) u φ → u ≤ g := by
  simpa only [iSingularityEnvelope, iSingularitySupremum,
    iSingularityCompetitors, thetaPshCompetitors, mem_ofPred_eq, and_imp] using
    (uscRegularization_sSup_le_iff (F := iSingularityCompetitors θ φ) hg)

theorem iSingularityEnvelope_le_zero
    (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    iSingularityEnvelope θ φ ≤ 0 := by
  apply uscRegularization_le upperSemicontinuous_const
  exact sSup_le fun _ hu => hu.1.2

theorem iSingularitySupremum_of_empty {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (h : iSingularityCompetitors θ φ = ∅) :
    iSingularitySupremum θ φ = ⊥ := by
  simp [iSingularitySupremum, h]

theorem iSingularityEnvelope_of_empty {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (h : iSingularityCompetitors θ φ = ∅) :
    iSingularityEnvelope θ φ = ⊥ := by
  unfold iSingularityEnvelope
  rw [iSingularitySupremum_of_empty h]
  exact uscRegularization_const ⊥

theorem iSingularityEnvelope_locallyNondegenerate
    {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hne : (iSingularityCompetitors θ φ).Nonempty) :
    LocallyNondegenerate (iSingularityEnvelope θ φ) := by
  obtain ⟨u, ⟨hu, hu0⟩, huφ⟩ := hne
  exact hu.2.mono (le_iSingularityEnvelope hu hu0 huφ)

/-- A genuine theta-PSH potential fixed by its multiplier-ideal envelope. -/
def IsIModelPotential (θ : SmoothRealForm n M 2) (φ : M → EReal) : Prop :=
  IsThetaPshPotential θ φ ∧ φ = iSingularityEnvelope θ φ

theorem IsIModelPotential.plurisubharmonic {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (h : IsIModelPotential θ φ) :
    IsThetaPshPotential θ φ :=
  h.1

theorem IsIModelPotential.envelope_eq {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (h : IsIModelPotential θ φ) :
    φ = iSingularityEnvelope θ φ :=
  h.2

theorem iSingularityEnvelope_eq_of_iEquivalent {θ : SmoothRealForm n M 2}
    {φ ψ : M → EReal} (h : IEquivalentOnManifold (n := n) φ ψ) :
    iSingularityEnvelope θ φ = iSingularityEnvelope θ ψ := by
  unfold iSingularityEnvelope iSingularitySupremum
  rw [iSingularityCompetitors_eq_of_iEquivalent h]

end

end Hironaka.IEnvelope

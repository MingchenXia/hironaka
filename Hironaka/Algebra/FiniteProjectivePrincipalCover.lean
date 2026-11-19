import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Actual principal localizations derive finite projectivity of the original module

No global finite-presentation, Noetherian or domain hypothesis is used in
the finite-local-projectivity theorem. The scalar action remains the
original one throughout.
-/

noncomputable section

namespace Hironaka.Algebra.FiniteProjectivePrincipalCover

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Native principal-local projectivity covers the original whole free locus. -/
theorem projective_of_principalCover [Module.FinitePresentation R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.Projective (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) : Module.Projective R M := by
  apply Module.freeLocus_eq_univ_iff.mp
  apply Set.eq_univ_of_forall
  intro p
  have hn : ¬ s ⊆ (p.asIdeal : Set R) := by
    intro hp
    have H : (⊤ : Ideal R) ≤ p.asIdeal := by
      rw [← hs]
      exact Ideal.span_le.mpr hp
    exact p.isPrime.ne_top (top_unique H)
  obtain ⟨g, hg, hgp⟩ := Set.not_subset.mp hn
  exact (Module.basicOpen_subset_freeLocus_iff.mpr (h ⟨g, hg⟩)) hgp

/-- Finite projectivity on actual principal localizations derives original finite presentation. -/
theorem finitePresentation_projective_of_principalCover
    (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.Finite (Localization.Away g.val)
      (LocalizedModule.Away g.val M) ∧
      Module.Projective (Localization.Away g.val) (LocalizedModule.Away g.val M)) :
    Module.FinitePresentation R M ∧ Module.Projective R M := by
  have hfp (g : s) : Module.FinitePresentation (Localization.Away g.val)
      (LocalizedModule.Away g.val M) := by
    let := (h g).1
    let := (h g).2
    exact Module.finitePresentation_of_projective _ _
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan s hs hfp
  exact ⟨inferInstance, projective_of_principalCover s hs fun g => (h g).2⟩

/-- Actual finite free local frames derive both properties of the SAME original module. -/
theorem finitePresentation_projective_of_principalFrames
    (s : Set R) (hs : Ideal.span s = ⊤) (n : s → ℕ)
    (e : ∀ g : s, LocalizedModule.Away g.val M ≃ₗ[Localization.Away g.val]
      (Fin (n g) → Localization.Away g.val)) :
    Module.FinitePresentation R M ∧ Module.Projective R M := by
  apply finitePresentation_projective_of_principalCover s hs
  intro g
  let : Module.Free (Localization.Away g.val) (LocalizedModule.Away g.val M) :=
    Module.Free.of_equiv (e g).symm
  let : Module.Finite (Localization.Away g.val) (LocalizedModule.Away g.val M) :=
    Module.Finite.equiv (e g).symm
  exact ⟨inferInstance, Module.Projective.of_free⟩

end Hironaka.Algebra.FiniteProjectivePrincipalCover

namespace Hironaka.Algebra.FiniteProjectivePrincipalCover

universe u v w z
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Actual local rings/modules/maps may be used instead of invented canonical localization actions.
The semilinear comparison uses the native method of
`Module.projective_of_localization_maximal'`, preserving the whole original map. -/
theorem finitePresentation_projective_of_localizationSpan
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Rₚ : s → Type w} [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)]
    [∀ g, IsLocalization.Away g.val (Rₚ g)]
    {Mₚ : s → Type z} [∀ g, AddCommGroup (Mₚ g)] [∀ g, Module R (Mₚ g)]
    [∀ g, Module (Rₚ g) (Mₚ g)] [∀ g, IsScalarTower R (Rₚ g) (Mₚ g)]
    (φ : ∀ g, M →ₗ[R] Mₚ g)
    [∀ g, IsLocalizedModule (Submonoid.powers g.val) (φ g)]
    (h : ∀ g, Module.Finite (Rₚ g) (Mₚ g) ∧ Module.Projective (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M ∧ Module.Projective R M := by
  have hfp (g : s) : Module.FinitePresentation (Rₚ g) (Mₚ g) := by
    let := (h g).1
    let := (h g).2
    exact Module.finitePresentation_of_projective _ _
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs φ hfp
  refine ⟨inferInstance, projective_of_principalCover s hs ?_⟩
  intro g
  let := (h g).2
  let e := (IsLocalization.algEquiv (Submonoid.powers g.val)
    (Rₚ g) (Localization.Away g.val)).toRingEquiv
  apply Module.Projective.of_equiv (M := Mₚ g) (R := Rₚ g) (σ := e)
  refine { __ := (IsLocalizedModule.linearEquiv (Submonoid.powers g.val) (φ g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g.val) M)), map_smul' := ?_ }
  intro a m
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers g.val) a
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers g.val) M) t)).1
  dsimp [e]
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self,
    algebraMap_smul, IsLocalization.map_id_mk']

end Hironaka.Algebra.FiniteProjectivePrincipalCover

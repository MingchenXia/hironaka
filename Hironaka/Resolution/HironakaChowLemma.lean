import Hironaka.Analytic.PrescribedBlowupDomination
import Hironaka.Analytic.AnalyticModelDomination

set_option autoImplicit false

/-!
# Hironaka's Chow lemma for complex manifolds: statements and reductions

Blueprint: `blueprint/src/hironaka-g10-chow.tex` (goal G10, milestone G10a; Hironaka
`thm:HironakaChow`, `def:modif`).

Main declarations:

* `HironakaChowLemmaManifold` — the goal G10a as a proposition: every proper analytic
  modification `f : Y → X` of a compact complex manifold is dominated by a finite
  composition of blowups with smooth centres (`IsBlowupSequence`).
* `IsDominatingIdeal n f 𝔞` — a coherent ideal with nowhere dense zero locus along which
  every holomorphic test map with invertible inverse-image ideal lifts through `f` (the
  manifold-test form of "the blowup of `𝔞` dominates `Y`").
* `HironakaDominatingIdealManifold` — the external input as a proposition (not an axiom):
  every proper modification of a compact complex manifold has a dominating ideal.  It is
  the consequence of Hironaka's flattening theorem recorded in the blueprint
  (`chow:dominating-ideal-existence`); it is **not** proved here.
* `hironakaChowLemmaManifold_of_dominatingIdeal` — the reduction of G10a to that input,
  through compact principalization (`HironakaAdmissibleSequence.exists_principalization_admissible`).
* `HasStableBlowupDomination` with its calculus: dominating ideals give it
  (`exists_domination_of_isDominatingIdeal`), it composes
  (`HasStableBlowupDomination.comp`), every blowup sequence has it
  (`hasStableBlowupDomination_of_isBlowupSequence`), and two blowup sequences of a
  compact manifold are dominated by a third (`exists_common_isBlowupSequence`).

Everything here is proved from the project's principalization; the only open input of
G10a is `HironakaDominatingIdealManifold`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaChowLemma

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaAdmissibleSequence AnalyticModificationLocalDiscrepancy

noncomputable section

section Calculus

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- The composite of two blowup sequences is a blowup sequence. -/
theorem isBlowupSequence_comp {f : Y → X} {g : Z → Y}
    (hf : IsBlowupSequence n X Y f) (hg : IsBlowupSequence n Y Z g) :
    IsBlowupSequence n X Z (f ∘ g) := by
  induction hg with
  | refl => exact hf
  | step g₀ C b _ hb ih => exact IsBlowupSequence.step (f ∘ g₀) C b ih hb

/-- The identity is a proper analytic modification. -/
theorem isAnalyticModification_id : IsAnalyticModification (n := n) (id : X → X) :=
  ⟨contMDiff_id, isProperMap_id, ∅, ∅, id, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty, contMDiff_id.contMDiffOn,
    (fun _ _ => rfl), (fun _ _ => rfl)⟩

/-- A blowup sequence is a proper analytic modification. -/
theorem isAnalyticModification_of_isBlowupSequence {f : Y → X}
    (hf : IsBlowupSequence n X Y f) : IsAnalyticModification (n := n) f := by
  induction hf with
  | refl => exact isAnalyticModification_id
  | step f C g _ hg ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hg)

end Calculus

section Definitions

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

variable (n) in
/-- `f : Y → X` is *dominated by a blowup sequence*: some blowup sequence `σ : X' → X`
factors holomorphically through `f`. -/
def HasBlowupDomination (f : Y → X) : Prop :=
  ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
    (_ : IsComplexManifold n X') (σ : X' → X) (g : X' → Y),
    IsBlowupSequence n X X' σ ∧
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g ∧ f ∘ g = σ

variable (n) in
/-- `f : Y → X` has *stable blowup domination*: for every proper analytic modification
`c : Z → X` there are a blowup sequence `σ : W → Z` and a holomorphic `ℓ : W → Y` with
`f ∘ ℓ = c ∘ σ`. -/
def HasStableBlowupDomination (f : Y → X) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (c : Z → X), IsAnalyticModification (n := n) c →
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → Z) (ℓ : W → Y),
      IsBlowupSequence n Z W σ ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ ∧ f ∘ ℓ = c ∘ σ

variable (n) in
/-- A coherent ideal `𝔞 ⊆ 𝒪_X` *dominates* `f : Y → X` if its zero locus has empty interior
and every holomorphic map `h : T → X` from a complex manifold of any dimension with
`h⁻¹𝔞 · 𝒪_T` invertible factors holomorphically through `f`.  This is the universal
property of the blowup of `X` along `𝔞` (as in `IsBlowupAlong`, without uniqueness)
composed with a morphism from that blowup to `Y`. -/
def IsDominatingIdeal (f : Y → X) (𝔞 : GermIdeal n X) : Prop :=
  𝔞.IsCoherent ∧ interior 𝔞.zeroLocus = ∅ ∧
    ∀ (m : ℕ) (T : Type u) [TopologicalSpace T] [ChartedSpace (ComplexModel m) T]
      [IsComplexManifold m T] (h : T → X),
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ h →
      (GermIdeal.pullback (m := m) h 𝔞).IsInvertible →
        ∃ g : T → Y, ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧ f ∘ g = h

end Definitions

/-- **Goal G10a (Hironaka's Chow lemma for manifolds)**, as a proposition: for every compact
complex manifold `X` and every proper analytic modification `f : Y → X` from a complex
manifold, there are a finite composition of blowups with smooth centres `σ : X' → X` and a
holomorphic `g : X' → Y` with `f ∘ g = σ`.  Not proved; see
`hironakaChowLemmaManifold_of_dominatingIdeal`. -/
def HironakaChowLemmaManifold : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X]
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (f : Y → X), IsAnalyticModification (n := n) f →
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (σ : X' → X) (g : X' → Y),
      IsBlowupSequence n X X' σ ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g ∧ f ∘ g = σ

/-- **External input of G10a**, as a proposition (not an axiom, not proved): every proper
analytic modification of a compact complex manifold has a dominating ideal.  This is
domination by a single blowup of a coherent ideal, a consequence of Hironaka's flattening
theorem (blueprint `chow:dominating-ideal-existence`). -/
def HironakaDominatingIdealManifold : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X]
    (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (f : Y → X), IsAnalyticModification (n := n) f →
    ∃ 𝔞 : GermIdeal n X, IsDominatingIdeal n f 𝔞

section Domination

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- The ideal of the centre dominates a blowup along a nowhere dense smooth centre. -/
theorem isDominatingIdeal_vanishingIdeal {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) : IsDominatingIdeal n π (vanishingIdeal (n := n) C) := by
  refine ⟨BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ, ?_, ?_⟩
  · rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := n) hπ.1.1]
    exact hπ.2.1
  · intro m T _ _ _ h hh hinv
    obtain ⟨g, ⟨hg, hgh⟩, _⟩ := hπ.2.2.2.2 m T h hh hinv
    exact ⟨g, hg, hgh⟩

omit [IsComplexManifold n Y] in
/-- A map with a holomorphic section is dominated by the unit ideal `𝓘_∅ = 𝒪_X`. -/
theorem isDominatingIdeal_of_section {f : Y → X} {φ : X → Y}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ) (hfφ : f ∘ φ = id) :
    IsDominatingIdeal n f (vanishingIdeal (n := n) (∅ : Set X)) := by
  refine ⟨VanishingIdealCoherent.isCoherent_vanishingIdeal
    ⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩, ?_, ?_⟩
  · rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := n) isClosed_empty]
    exact interior_empty
  · intro m T _ _ _ h hh _
    refine ⟨φ ∘ h, hφ.comp hh, ?_⟩
    rw [← Function.comp_assoc, hfφ]
    rfl

/-- **A dominating ideal gives stable domination.**  For a proper modification `f`
dominated by `𝔞` and any proper modification `c : Z → X` of the compact manifold `X`,
principalizing `c^*𝔞` on `Z` gives an admissible blowup sequence `σ : W → Z` and a
proper modification `ℓ : W → Y` with `f ∘ ℓ = c ∘ σ`. -/
theorem exists_domination_of_isDominatingIdeal [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) {𝔞 : GermIdeal n X}
    (h𝔞 : IsDominatingIdeal n f 𝔞) {c : Z → X} (hc : IsAnalyticModification (n := n) c) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → Z) (ℓ : W → Y)
      (D : EffectiveDivisor n W) (E : List (Set W)),
      IsAdmissibleBlowupSequence n Z [] (c ⁻¹' 𝔞.zeroLocus) W σ E ∧
      IsAnalyticModification (n := n) σ ∧ IsAnalyticModification (n := n) ℓ ∧
      f ∘ ℓ = c ∘ σ ∧
      GermIdeal.pullback (m := n) σ (GermIdeal.pullback (m := n) c 𝔞) = D.ideal ∧
      NormalCrossings.IsSNCDivisor n E ∧ D.support = σ ⁻¹' (c ⁻¹' 𝔞.zeroLocus) := by
  obtain ⟨hcoh, hthin, hlift⟩ := h𝔞
  let 𝔟 := GermIdeal.pullback (m := n) c 𝔞
  have hb : 𝔟.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hc.1 hcoh
  have hZ : 𝔟.zeroLocus = c ⁻¹' 𝔞.zeroLocus :=
    BlowupExceptionalDivisor.zeroLocus_pullback hc.1 hcoh
  have hbthin : interior 𝔟.zeroLocus = ∅ := by
    rw [hZ]
    exact AnalyticModelDomination.interior_preimage_eq_empty_of_isAnalyticModification hc hthin
  let := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  obtain ⟨W, tW, chW, mW, σ, D, E, hσ, hpb, hE, _hsuppE, hsupp, _hiso⟩ :=
    exists_principalization_admissible hb
      (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty hb hbthin)
  let := tW
  let := chW
  let := mW
  have hσa := AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    hb hσ D hsupp
  have hq := AnalyticModificationComposition.isAnalyticModification_comp hc hσa
  have hinv : (GermIdeal.pullback (m := n) (c ∘ σ) 𝔞).IsInvertible := by
    rw [GermIdealTotalTransform.pullback_comp hc.1 hσ.isBlowupSequence.contMDiff hcoh, hpb]
    exact D.isInvertible
  obtain ⟨ℓ, hℓ, hsquare⟩ := hlift n W (c ∘ σ) hq.1 hinv
  refine ⟨W, tW, chW, mW, σ, ℓ, D, E, ?_, hσa,
    AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hf hq hℓ hsquare,
    hsquare, hpb, hE, ?_⟩
  · rwa [hZ] at hσ
  · rwa [hZ] at hsupp

/-- A proper modification of a compact manifold with a dominating ideal has stable blowup
domination. -/
theorem hasStableBlowupDomination_of_isDominatingIdeal [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) {𝔞 : GermIdeal n X}
    (h𝔞 : IsDominatingIdeal n f 𝔞) : HasStableBlowupDomination n f := by
  intro Z _ _ _ c hc
  obtain ⟨W, tW, chW, mW, σ, ℓ, _D, _E, hσ, _hσa, hℓ, hsquare, _⟩ :=
    exists_domination_of_isDominatingIdeal hf h𝔞 hc
  exact ⟨W, tW, chW, mW, σ, ℓ, hσ.isBlowupSequence, hℓ.1, hsquare⟩

omit [IsComplexManifold n Y] in
/-- Stable blowup domination gives domination by a blowup sequence (take `c = id`). -/
theorem HasStableBlowupDomination.hasBlowupDomination {f : Y → X}
    (h : HasStableBlowupDomination n f) : HasBlowupDomination n f := by
  obtain ⟨W, tW, chW, mW, σ, ℓ, hσ, hℓ, hsquare⟩ := h X id isAnalyticModification_id
  exact ⟨W, tW, chW, mW, σ, ℓ, hσ, hℓ, hsquare⟩

/-- A proper modification of a compact manifold with a dominating ideal is dominated by a
blowup sequence. -/
theorem hasBlowupDomination_of_isDominatingIdeal [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) {𝔞 : GermIdeal n X}
    (h𝔞 : IsDominatingIdeal n f 𝔞) : HasBlowupDomination n f :=
  (hasStableBlowupDomination_of_isDominatingIdeal hf h𝔞).hasBlowupDomination

omit [IsComplexManifold n Y] in
/-- A map with a holomorphic section has stable blowup domination. -/
theorem hasStableBlowupDomination_of_section {f : Y → X} {φ : X → Y}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ) (hfφ : f ∘ φ = id) :
    HasStableBlowupDomination n f := by
  intro Z _ _ _ c hc
  refine ⟨Z, inferInstance, inferInstance, inferInstance, id, φ ∘ c, IsBlowupSequence.refl,
    hφ.comp hc.1, ?_⟩
  rw [← Function.comp_assoc, hfφ]
  rfl

omit [IsComplexManifold n Z] in
/-- **Stable domination composes.**  If `f₁ : Y → X` is a proper modification and `f₁`,
`f₂ : Z → Y` have stable blowup domination, so has `f₁ ∘ f₂`. -/
theorem HasStableBlowupDomination.comp {f₁ : Y → X} {f₂ : Z → Y}
    (hf₁ : IsAnalyticModification (n := n) f₁)
    (h₁ : HasStableBlowupDomination n f₁) (h₂ : HasStableBlowupDomination n f₂) :
    HasStableBlowupDomination n (f₁ ∘ f₂) := by
  intro V _ _ _ c hc
  obtain ⟨W₁, t₁, ch₁, m₁, σ₁, ℓ₁, hσ₁, hℓ₁, hsq₁⟩ := h₁ V c hc
  let := t₁
  let := ch₁
  let := m₁
  have hq := AnalyticModificationComposition.isAnalyticModification_comp hc
    (isAnalyticModification_of_isBlowupSequence hσ₁)
  have hℓ₁a := AnalyticModelDomination.isAnalyticModification_of_holomorphic_over hf₁ hq hℓ₁ hsq₁
  obtain ⟨W₂, t₂, ch₂, m₂, σ₂, ℓ₂, hσ₂, hℓ₂, hsq₂⟩ := h₂ W₁ ℓ₁ hℓ₁a
  let := t₂
  let := ch₂
  let := m₂
  refine ⟨W₂, t₂, ch₂, m₂, σ₁ ∘ σ₂, ℓ₂, isBlowupSequence_comp hσ₁ hσ₂, hℓ₂, ?_⟩
  calc (f₁ ∘ f₂) ∘ ℓ₂ = f₁ ∘ (f₂ ∘ ℓ₂) := rfl
    _ = f₁ ∘ (ℓ₁ ∘ σ₂) := by rw [hsq₂]
    _ = (f₁ ∘ ℓ₁) ∘ σ₂ := rfl
    _ = (c ∘ σ₁) ∘ σ₂ := by rw [hsq₁]
    _ = c ∘ (σ₁ ∘ σ₂) := rfl

/-- A blowup along a nowhere dense smooth centre of a compact manifold has stable blowup
domination. -/
theorem hasStableBlowupDomination_of_isBlowupAlong [CompactSpace X] {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) : HasStableBlowupDomination n π :=
  hasStableBlowupDomination_of_isDominatingIdeal
    (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ)
    (isDominatingIdeal_vanishingIdeal hπ)

/-- **Every blowup sequence of a compact manifold has stable blowup domination.** -/
theorem hasStableBlowupDomination_of_isBlowupSequence [CompactSpace X] {f : Y → X}
    (hf : IsBlowupSequence n X Y f) : HasStableBlowupDomination n f := by
  induction hf with
  | refl => exact hasStableBlowupDomination_of_section contMDiff_id rfl
  | step f₀ C b hf₀ hb ih =>
      let := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf₀).1
      exact HasStableBlowupDomination.comp (isAnalyticModification_of_isBlowupSequence hf₀) ih
        (hasStableBlowupDomination_of_isBlowupAlong hb)

/-- **Blowup sequences of a compact manifold form a directed system**: two blowup
sequences are dominated by a third. -/
theorem exists_common_isBlowupSequence [CompactSpace X] {f₁ : Y → X} {f₂ : Z → X}
    (h₁ : IsBlowupSequence n X Y f₁) (h₂ : IsBlowupSequence n X Z f₂) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → X) (g₁ : W → Y) (g₂ : W → Z),
      IsBlowupSequence n X W σ ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₂ ∧
      f₁ ∘ g₁ = σ ∧ f₂ ∘ g₂ = σ := by
  obtain ⟨W, tW, chW, mW, τ, ℓ, hτ, hℓ, hsq⟩ :=
    hasStableBlowupDomination_of_isBlowupSequence h₂ Y f₁
      (isAnalyticModification_of_isBlowupSequence h₁)
  let := tW
  let := chW
  let := mW
  exact ⟨W, tW, chW, mW, f₁ ∘ τ, τ, ℓ, isBlowupSequence_comp h₁ hτ, hτ.contMDiff, hℓ, rfl,
    hsq⟩

end Domination

/-- **Reduction of G10a to the dominating-ideal input.**  If every proper modification of a
compact complex manifold has a dominating ideal, Hironaka's Chow lemma holds for compact
complex manifolds.  The hypothesis is the external input `HironakaDominatingIdealManifold`
(a consequence of Hironaka's flattening theorem); it is not proved in this project. -/
theorem hironakaChowLemmaManifold_of_dominatingIdeal
    (H : HironakaDominatingIdealManifold.{u}) : HironakaChowLemmaManifold.{u} := by
  intro n X _ _ _ _ Y _ _ _ f hf
  obtain ⟨𝔞, h𝔞⟩ := H n X Y f hf
  exact hasBlowupDomination_of_isDominatingIdeal hf h𝔞

end

end Hironaka.HironakaChowLemma

import DeJongAlterations.StableModificationBridge.SubschemeScalarVanishing
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! Actual reduced two-section geometry internally supplies the whole native nilradical lifting engine. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalCoverEngine

open CategoryTheory AlgebraicGeometry
open StableModification StableModification.Projectivity StableModification.CurvesField
open StableModification.CurvesField.Positive StableModification.CurvesField.Ample
open StableModification.CurvesField.Ample.LineBundleData
open Projectivity.LineBundleData TwoSectionScalarVanishing SubschemeScalarVanishing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The SAME actual nilradical closed subscheme covers every original point. -/
theorem reduction_surjective (X : Scheme.{u}) : Function.Surjective X.nilradical.subschemeι := by
  intro x
  have hx : x ∈ ((X.nilradical.support : Set X)) := by
    rw [Scheme.support_nilradical]
    trivial
  rw [← X.nilradical.range_subschemeι] at hx
  exact hx

section Ratios

variable {Y : Scheme.{u}} {M : LineBundleData Y} {N : ℤ}
  (s₀ s₁ : M.Sections N ⊤)

/-- The SAME actual opposite section ratio is inverse to the native two-section transition. -/
theorem ratio_inverse_transition :
    resL s₀.nonvanishingLocus s₁.nonvanishingLocus
        (ratio s₁ (leftFrame_nonvanishing s₀)) *
      (transition s₀ s₁ : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)) = 1 := by
  let τ := leftFrame s₀
  let σ := rightFrame s₁
  let r := ratio s₁ (leftFrame_nonvanishing s₀)
  have hr : σ.restrict (inf_le_right : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤
      s₁.nonvanishingLocus) = resL s₀.nonvanishingLocus s₁.nonvanishingLocus r •
      τ.restrict (inf_le_left : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤
        s₀.nonvanishingLocus) := by
    have h := congrArg
      (Sections.restrict (inf_le_left : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤
        s₀.nonvanishingLocus)) (restrict_eq_ratio_smul s₁ (leftFrame_nonvanishing s₀))
    simpa only [σ, τ, r, rightFrame, leftFrame, Sections.restrict_restrict,
      Sections.restrict_smul] using h
  have ht : τ.restrict (inf_le_left : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤
      s₀.nonvanishingLocus) =
      (transition s₀ s₁ : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)) •
        σ.restrict (inf_le_right : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤
          s₁.nonvanishingLocus) := by
    simpa only [τ, σ, transition, coe_transUnit] using
      (restrict_eq_transFun_smul (leftFrame s₀) (rightFrame_nonvanishing s₁))
  have hσ := nonvanishingLocus_restrict_of_eq (rightFrame_nonvanishing s₁)
    (inf_le_right : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus ≤ s₁.nonvanishingLocus)
  apply (mulSec_bijective (unitModule Y) hσ).1
  simp only [mulSec_unit, mul_smul, one_smul]
  rw [← ht, ← hr]

end Ratios

variable {X : Scheme.{u}} {U V : X.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))


variable {M : LineBundleData (X.nilradical.subscheme)} {N : ℤ} (s₀ s₁ : M.Sections N ⊤)
  (h₀ : s₀.nonvanishingLocus = (X.nilradical.subschemeι) ⁻¹ᵁ U) (h₁ : s₁.nonvanishingLocus = (X.nilradical.subschemeι) ⁻¹ᵁ V)

include h₀ h₁ in
private theorem overlap_eq : s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus = (X.nilradical.subschemeι) ⁻¹ᵁ (U ⊓ V) := by
  rw [h₀, h₁]
  rfl

variable (g : Γ(X, U ⊓ V)ˣ)
  (hg : coverMap X.nilradical (U ⊓ V) _ (overlap_eq s₀ s₁ h₀ h₁) g =
    (transition s₀ s₁ : Γ((X.nilradical.subscheme), s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)))

include hU hUV hg in
/-- Native reduced geometry INTERNALLY supplies the actual localization element and inverse congruence. -/
theorem exists_localization_element :
    ∃ h : Γ(X, U), X.basicOpen h = U ⊓ V ∧
      resL U V h * (g : Γ(X, U ⊓ V)) - 1 ∈ X.nilradical.ideal ⟨_, hUV⟩ := by
  obtain ⟨h, hh⟩ := coverMap_surjective X.nilradical U hU _ h₀
    (ratio s₁ (leftFrame_nonvanishing s₀))
  have hpre : (X.nilradical.subschemeι) ⁻¹ᵁ X.basicOpen h = (X.nilradical.subschemeι) ⁻¹ᵁ (U ⊓ V) := by
    rw [← coverMap_basicOpen X.nilradical U _ h₀ h, hh, basicOpen_ratio, h₀, h₁]
    rfl
  have hbasic : X.basicOpen h = U ⊓ V := by
    ext x
    obtain ⟨z, rfl⟩ := reduction_surjective X x
    change z ∈ (X.nilradical.subschemeι) ⁻¹ᵁ X.basicOpen h ↔ z ∈ (X.nilradical.subschemeι) ⁻¹ᵁ (U ⊓ V)
    rw [hpre]
  refine ⟨h, hbasic, ?_⟩
  rw [← coverMap_kernel X.nilradical (U ⊓ V) hUV _ (overlap_eq s₀ s₁ h₀ h₁)]
  change coverMap X.nilradical (U ⊓ V) _ (overlap_eq s₀ s₁ h₀ h₁)
    (resL U V h * (g : Γ(X, U ⊓ V)) - 1) = 0
  rw [map_sub, map_mul, map_one,
    coverMap_restrict X.nilradical inf_le_left h₀ (overlap_eq s₀ s₁ h₀ h₁), hh, hg,
    ratio_inverse_transition, sub_self]

variable [IsLocallyNoetherian X] [CompactSpace (X.nilradical.subscheme)]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (X.nilradical.subscheme)))]
  {K : Type u} [Field K] (p : (X.nilradical.subscheme) ⟶ Spec (.of K)) (hp : IsProjectiveOver p)

include hp hU hV hUV hg in
/-- Every native nilradical layer and its eventual exact coboundary are produced INTERNALLY. -/
theorem exists_nilradical_coboundaries
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (haff₀ : IsAffineOpen s₀.nonvanishingLocus) (haff₁ : IsAffineOpen s₁.nonvanishingLocus) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ w ∈ X.nilradical.ideal ⟨_, hUV⟩,
      IsCobdy (resL U V) (resR U V) g (X.nilradical.ideal ⟨_, hU⟩)
        (X.nilradical.ideal ⟨_, hV⟩) ⊥ k w := by
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : IsNoetherianRing Γ(X, U ⊓ V) :=
    IsLocallyNoetherian.component_noetherian ⟨U ⊓ V, hUV⟩
  obtain ⟨h, hh, hgh⟩ := exists_localization_element hU hUV s₀ s₁ h₀ h₁ g hg
  have hO := exists_modulo_scalar_coboundaries X.nilradical hU hV hUV s₀ s₁ h₀ h₁
    p hp hcov haff₀ haff₁ g hg
  have hnil : IsNilpotent (X.nilradical.ideal ⟨U ⊓ V, hUV⟩) :=
    IsNoetherianRing.isNilpotent_nilradical Γ(X, U ⊓ V)
  obtain ⟨e, he⟩ := hnil
  let IA : ℕ → Ideal Γ(X, U) := fun j => (X.nilradical ^ (j + 1)).ideal ⟨_, hU⟩
  let IB : ℕ → Ideal Γ(X, V) := fun j => (X.nilradical ^ (j + 1)).ideal ⟨_, hV⟩
  let IC : ℕ → Ideal Γ(X, U ⊓ V) := fun j => (X.nilradical ^ (j + 1)).ideal ⟨_, hUV⟩
  have hstep (j : ℕ) : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ w ∈ IC j,
      IsCobdy (resL U V) (resR U V) g (IA j) (IB j) (IC (j + 1)) k w := by
    apply exists_cobdy_idealSheaf hU hV hUV g hh X.nilradical
      (X.nilradical ^ (j + 1)) (X.nilradical ^ (j + 1 + 1)) hgh ?_ hO
    intro W
    change X.nilradical.ideal W * X.nilradical.ideal W ^ (j + 1) ≤
      X.nilradical.ideal W ^ (j + 1 + 1)
    exact le_of_eq (pow_succ' (X.nilradical.ideal W) (j + 1)).symm
  have hA (j : ℕ) : IA (j + 1) ≤ IA j :=
    Ideal.pow_le_pow_right (by omega)
  have hB (j : ℕ) : IB (j + 1) ≤ IB j :=
    Ideal.pow_le_pow_right (by omega)
  have hlast : IC e = ⊥ := by
    change X.nilradical.ideal ⟨U ⊓ V, hUV⟩ ^ (e + 1) = 0
    rw [pow_succ, he, zero_mul]
  simpa only [IA, IB, IC, Nat.zero_add, pow_one] using
    exists_forall_mem_of_filtration (ρU := resL U V) (ρV := resR U V) (g := g)
      IA IB IC hA hB e hlast
      (fun j _ => hstep j)

include hp hU hV hUV hg in
/-- Every actual reduced-compatible coefficient pair lifts with its whole original residues retained. -/
theorem exists_pair_lifts
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (haff₀ : IsAffineOpen s₀.nonvanishingLocus) (haff₁ : IsAffineOpen s₁.nonvanishingLocus) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ α : Γ(X, U), ∀ β : Γ(X, V),
      resR U V β - (g : Γ(X, U ⊓ V)) ^ k * resL U V α ∈ X.nilradical.ideal ⟨_, hUV⟩ →
      ∃ a : Γ(X, U), ∃ b : Γ(X, V), resR U V b = (g : Γ(X, U ⊓ V)) ^ k * resL U V a ∧
        a - α ∈ X.nilradical.ideal ⟨_, hU⟩ ∧ b - β ∈ X.nilradical.ideal ⟨_, hV⟩ := by
  obtain ⟨k₀, hk₀⟩ := exists_nilradical_coboundaries hU hV hUV s₀ s₁ h₀ h₁ g hg
    p hp hcov haff₀ haff₁
  exact ⟨k₀, fun k hk α β hαβ => exists_lift_of_cobdy (hk₀ k hk) α β hαβ⟩

end DeJongAlterations.StableModificationBridge.NilradicalCoverEngine

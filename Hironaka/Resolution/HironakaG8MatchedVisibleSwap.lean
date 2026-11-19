import Hironaka.Resolution.HironakaG8VisibleSwapRestriction
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MatchedVisibleSwap

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail HironakaG8VisibleSwapRestriction
  HironakaLocalPrincipalization

variable {n : ℕ} {X₁ X₂ Y₁ Y₂ Z₁ Z₂ B₁ B₂ Q₁ Q₂ : CMfd.{0} n}

private abbrev twice {X Y Z : CMfd.{0} n} {C : Set X} {D : Set Y}
    {π : Y → X} {q : Z → Y} (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q) :
    BlowupTower X Z := .step (.step .refl C π hπ) D q hq

private theorem centers_of_match
    {C₁ D₁ : Set X₁} {C₂ D₂ : Set X₂}
    {π₁ : Y₁ → X₁} {π₂ : Y₂ → X₂} {q₁ : Z₁ → Y₁} {q₂ : Z₂ → Y₂}
    {hπ₁ : IsBlowupAlong n C₁ π₁} {hπ₂ : IsBlowupAlong n C₂ π₂}
    {hq₁ : IsBlowupAlong n (π₁ ⁻¹' D₁) q₁} {hq₂ : IsBlowupAlong n (π₂ ⁻¹' D₂) q₂}
    {φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {ψ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (h : IsTowerIso φ (twice hπ₁ hq₁) (twice hπ₂ hq₂) ψ) :
    φ ⁻¹' C₂ = C₁ ∧ φ ⁻¹' D₂ = D₁ := by
  cases h with
  | step hp _ _ _ _ hDC =>
    cases hp with
    | step hBase _ _ α hComm hC =>
      cases hBase
      refine ⟨hC,?_⟩
      ext x
      obtain ⟨y,rfl⟩ := surjective_of_isBlowupAlong hπ₁ x
      change φ (π₁ y) ∈ D₂ ↔ π₁ y ∈ D₁
      rw [← hComm]
      exact Set.ext_iff.mp hDC y

/-- A strict comparison of two original disjoint pairs also compares the
actual swapped pairs. The terminal map is the conjugate of the original
one by the two genuine swap comparisons. -/
theorem matched_pairs_after_disjoint_swap
    {C₁ D₁ : Set X₁} {C₂ D₂ : Set X₂}
    {π₁ : Y₁ → X₁} {π₂ : Y₂ → X₂} {q₁ : Z₁ → Y₁} {q₂ : Z₂ → Y₂}
    (hπ₁ : IsBlowupAlong n C₁ π₁) (hπ₂ : IsBlowupAlong n C₂ π₂)
    (hq₁ : IsBlowupAlong n (π₁ ⁻¹' D₁) q₁) (hq₂ : IsBlowupAlong n (π₂ ⁻¹' D₂) q₂)
    {φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {ψ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (h : IsTowerIso φ (twice hπ₁ hq₁) (twice hπ₂ hq₂) ψ)
    {ρ₁ : B₁ → X₁} {ρ₂ : B₂ → X₂} {r₁ : Q₁ → B₁} {r₂ : Q₂ → B₂}
    (hρ₁ : IsBlowupAlong n D₁ ρ₁) (hρ₂ : IsBlowupAlong n D₂ ρ₂)
    (hr₁ : IsBlowupAlong n (ρ₁ ⁻¹' C₁) r₁) (hr₂ : IsBlowupAlong n (ρ₂ ⁻¹' C₂) r₂)
    (hDisj : Disjoint D₁ C₁)
    (e₁ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₁)
    (e₂ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂)
    (he₁ : (ρ₁ ∘ r₁) ∘ e₁ = π₁ ∘ q₁) (he₂ : (ρ₂ ∘ r₂) ∘ e₂ = π₂ ∘ q₂) :
    IsTowerIso φ (twice hρ₁ hr₁) (twice hρ₂ hr₂) ((e₁.symm.trans ψ).trans e₂) := by
  obtain ⟨hC,hD⟩ := centers_of_match h
  let ρ₂' : B₂ → X₁ := φ.symm ∘ ρ₂
  have hρ₂' : IsBlowupAlong n D₁ ρ₂' := by
    rw [← hD]
    exact MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
      φ.contMDiff φ.symm.contMDiff φ.apply_symm_apply φ.symm_apply_apply hρ₂
  have hds : (ρ₂' ⁻¹' C₁) = ρ₂ ⁻¹' C₂ := by
    ext x
    change φ.symm (ρ₂ x) ∈ C₁ ↔ ρ₂ x ∈ C₂
    rw [← hC]
    change φ (φ.symm (ρ₂ x)) ∈ C₂ ↔ _
    rw [φ.apply_symm_apply]
  have hr₂' : IsBlowupAlong n (ρ₂' ⁻¹' C₁) r₂ := hds.symm ▸ hr₂
  obtain ⟨χ,hχ,_,hUnique⟩ := same_disjoint_pair_strict hρ₁ hr₁ hρ₂' hr₂'
    hπ₁.1 hπ₁.2.1 hDisj
  let f := (e₁.symm.trans ψ).trans e₂
  have hf : (ρ₂' ∘ r₂) ∘ f = ρ₁ ∘ r₁ := by
    funext z
    apply φ.injective
    change φ (φ.symm (ρ₂ (r₂ (e₂ (ψ (e₁.symm z)))))) = φ (ρ₁ (r₁ z))
    rw [φ.apply_symm_apply]
    have h₂ := congrFun he₂ (ψ (e₁.symm z))
    have h₁ := congrFun he₁ (e₁.symm z)
    have hm := h.proj_comm (e₁.symm z)
    change ρ₂ (r₂ (e₂ (ψ (e₁.symm z)))) = π₂ (q₂ (ψ (e₁.symm z))) at h₂
    change ρ₁ (r₁ (e₁ (e₁.symm z))) = π₁ (q₁ (e₁.symm z)) at h₁
    change φ (π₁ (q₁ (e₁.symm z))) = π₂ (q₂ (ψ (e₁.symm z))) at hm
    rw [e₁.apply_symm_apply] at h₁
    rw [h₂,← hm,← h₁]
  have hfχ := hUnique f hf
  have hChange : IsTowerIso φ (twice hρ₂' hr₂') (twice hρ₂ hr₂)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Q₂ ∞) := by
    refine .step (.step .refl hρ₂' hρ₂ (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B₂ ∞)
      (fun x => (φ.apply_symm_apply (ρ₂ x)).symm) hD) hr₂' hr₂ _ (fun _ => rfl) hds.symm
  have hFinal := hχ.trans hChange
  have hb : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X₁ ∞).trans φ = φ := by ext x; rfl
  have hEnd : χ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Q₂ ∞) = f := by
    rw [hfχ]
    ext z
    rfl
  rwa [hb,hEnd] at hFinal

open HironakaSharpActualCurveComparisonRestriction BlowupRestrictOpen

/-- Compare an actual swap on the smaller chart with the literal
restriction of the larger swap, keeping its original base map. -/
theorem nested_pairs_after_disjoint_swap
    {C₁ D₁ : Set X₁} {C₂ D₂ : Set X₂}
    {π₁ : Y₁ → X₁} {π₂ : Y₂ → X₂} {q₁ : Z₁ → Y₁} {q₂ : Z₂ → Y₂}
    (hπ₁ : IsBlowupAlong n C₁ π₁) (hπ₂ : IsBlowupAlong n C₂ π₂)
    (hq₁ : IsBlowupAlong n (π₁ ⁻¹' D₁) q₁) (hq₂ : IsBlowupAlong n (π₂ ⁻¹' D₂) q₂)
    (U : Opens X₂)
    (φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ψ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (twice hπ₂ hq₂) U))
    (h : IsTowerIso φ (twice hπ₁ hq₁) (restrict U (twice hπ₂ hq₂)) ψ)
    {ρ₁ : B₁ → X₁} {ρ₂ : B₂ → X₂} {r₁ : Q₁ → B₁} {r₂ : Q₂ → B₂}
    (hρ₁ : IsBlowupAlong n D₁ ρ₁) (hρ₂ : IsBlowupAlong n D₂ ρ₂)
    (hr₁ : IsBlowupAlong n (ρ₁ ⁻¹' C₁) r₁) (hr₂ : IsBlowupAlong n (ρ₂ ⁻¹' C₂) r₂)
    (hDisj : Disjoint D₁ C₁)
    (e₁ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₁)
    (e₂ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂)
    (he₁ : (ρ₁ ∘ r₁) ∘ e₁ = π₁ ∘ q₁) (he₂ : (ρ₂ ∘ r₂) ∘ e₂ = π₂ ∘ q₂) :
    ∃ χ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (twice hρ₂ hr₂) U),
      IsTowerIso φ (twice hρ₁ hr₁) (restrict U (twice hρ₂ hr₂)) χ ∧
      ∀ z, (χ z).val = e₂ (ψ (e₁.symm z)).val := by
  let C : Set U := Subtype.val ⁻¹' C₂
  let D : Set U := Subtype.val ⁻¹' D₂
  let P : BlowupTower X₂ Y₂ := .step .refl C₂ π₂ hπ₂
  let P' : BlowupTower X₂ B₂ := .step .refl D₂ ρ₂ hρ₂
  let L := twice hπ₂ hq₂
  let R := twice hρ₂ hr₂
  let π : openPreimage P U → U := fun y => ⟨π₂ y.val,y.property⟩
  let ρ : openPreimage P' U → U := fun y => ⟨ρ₂ y.val,y.property⟩
  let q : openPreimage L U → openPreimage P U := fun y => ⟨q₂ y.val,y.property⟩
  let r : openPreimage R U → openPreimage P' U := fun y => ⟨r₂ y.val,y.property⟩
  let hπ : IsBlowupAlong n C π := isBlowupAlong_restrict hπ₂ U _
  let hρ : IsBlowupAlong n D ρ := isBlowupAlong_restrict hρ₂ U _
  let hq : IsBlowupAlong n (π ⁻¹' D) q := isBlowupAlong_restrict hq₂ (openPreimage P U) _
  let hr : IsBlowupAlong n (ρ ⁻¹' C) r := isBlowupAlong_restrict hr₂ (openPreimage P' U) _
  have hOpen : (openPreimage L U : Set Z₂) = e₂ ⁻¹' (openPreimage R U : Set Q₂) := by
    ext z
    change π₂ (q₂ z) ∈ U ↔ ρ₂ (r₂ (e₂ z)) ∈ U
    rw [show ρ₂ (r₂ (e₂ z)) = π₂ (q₂ z) from congrFun he₂ z]
  let e := openRestriction e₂ (openPreimage L U) (openPreimage R U) hOpen
  have he : (ρ ∘ r) ∘ e = π ∘ q := by
    funext z
    apply Subtype.ext
    exact congrFun he₂ z.val
  exact ⟨(e₁.symm.trans ψ).trans e,
    matched_pairs_after_disjoint_swap (X₂ := CMfd.of (n := n) U) (C₂ := C) (D₂ := D)
      hπ₁ hπ hq₁ hq h hρ₁ hρ hr₁ hr hDisj e₁ e he₁ he,fun _ => rfl⟩

/-- The conjugated comparison extends through both genuinely transported
suffixes, also allowing the swapped pairs to have matched prefixes. -/
theorem append_matched_carried_suffix
    {F₁ F₂ G₁ G₂ : CMfd.{0} n}
    {φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {ψ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    {e₁ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₁}
    {e₂ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂}
    {P₁ : BlowupTower X₁ Q₁} {P₂ : BlowupTower X₂ Q₂}
    (hPair : IsTowerIso φ P₁ P₂ ((e₁.symm.trans ψ).trans e₂))
    {S₁ : BlowupTower Z₁ F₁} {S₂ : BlowupTower Z₂ F₂}
    {T₁ : BlowupTower Q₁ G₁} {T₂ : BlowupTower Q₂ G₂}
    {ζ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₂}
    {f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₁}
    {f₂ : F₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₂}
    (hS : IsTowerIso ψ S₁ S₂ ζ)
    (h₁ : IsTowerIso e₁ S₁ T₁ f₁) (h₂ : IsTowerIso e₂ S₂ T₂ f₂) :
    IsTowerIso φ (P₁.append T₁) (P₂.append T₂) ((f₁.symm.trans ζ).trans f₂) :=
  hPair.append ((h₁.symm.trans hS).trans h₂)

end Hironaka.HironakaG8MatchedVisibleSwap

#print axioms Hironaka.HironakaG8MatchedVisibleSwap.matched_pairs_after_disjoint_swap

#print axioms Hironaka.HironakaG8MatchedVisibleSwap.nested_pairs_after_disjoint_swap
#print axioms Hironaka.HironakaG8MatchedVisibleSwap.append_matched_carried_suffix

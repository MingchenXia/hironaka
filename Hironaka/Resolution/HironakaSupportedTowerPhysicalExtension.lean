import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
import Hironaka.Resolution.HironakaG34CanonicalLocalEquivariance
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSupportedTowerPhysicalExtension

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  G3UniverseEmptyAwareCore HironakaSharpActualCurveComparisonRestriction
  HironakaOriginalTerminalProjectionUniqueness HironakaG34CanonicalLocalEquivariance RestrictEmptyTower

variable {n : ℕ} {X : CMfd.{u} n}

private theorem comparison_agrees_on_corresponding_windows
    {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    (U₁ : Opens X₁) (U₂ : Opens X₂) (hU : (U₁ : Set X₁) = Φ ⁻¹' (U₂ : Set X₂))
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂)
    (hGlobal : ∀ z, T₂.proj (Ψ z) = Φ (T₁.proj z))
    (ψ : CMfd.of (n := n) (openPreimage T₁ U₁)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ U₂))
    (hLocal : ∀ z : openPreimage T₁ U₁, T₂.proj (ψ z).val = Φ (T₁.proj z.val)) :
    ∀ z : openPreimage T₁ U₁, Ψ z.val = (ψ z).val := by
  have hOpen : (openPreimage T₁ U₁ : Set Y₁) = Ψ ⁻¹' (openPreimage T₂ U₂ : Set Y₂) := by
    ext z
    change (T₁.proj z ∈ U₁) ↔ (T₂.proj (Ψ z) ∈ U₂)
    rw [hGlobal, show (T₁.proj z ∈ U₁) ↔ (Φ (T₁.proj z) ∈ U₂) by
      change T₁.proj z ∈ (U₁ : Set X₁) ↔ T₁.proj z ∈ Φ ⁻¹' (U₂ : Set X₂)
      rw [hU]]
  let ΨU := openRestriction Ψ (openPreimage T₁ U₁) (openPreimage T₂ U₂) hOpen
  have hEq : ΨU = ψ := by
    apply biholomorphisms_eq_of_actual_proj_eq (restrict U₂ T₂)
    intro z
    apply Subtype.ext
    rw [proj_restrict,proj_restrict]
    exact (hGlobal z.val).trans (hLocal z).symm
  intro z
  exact congrArg (fun e => (e z).val) hEq

private theorem centres_match_of_corresponding_traces
    {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    (U₁ : Opens X₁) (U₂ : Opens X₂) (hU : (U₁ : Set X₁) = Φ ⁻¹' (U₂ : Set X₂))
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂) {C₁ : Set Y₁} {C₂ : Set Y₂}
    (hC₁ : C₁ ⊆ (openPreimage T₁ U₁ : Set Y₁)) (hC₂ : C₂ ⊆ (openPreimage T₂ U₂ : Set Y₂))
    (Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂)
    (hGlobal : ∀ z, T₂.proj (Ψ z) = Φ (T₁.proj z))
    (ψ : CMfd.of (n := n) (openPreimage T₁ U₁)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ U₂))
    (hLocal : ∀ z : openPreimage T₁ U₁, T₂.proj (ψ z).val = Φ (T₁.proj z.val))
    (hTrace : ψ ⁻¹' ((Subtype.val : openPreimage T₂ U₂ → Y₂) ⁻¹' C₂) =
      (Subtype.val : openPreimage T₁ U₁ → Y₁) ⁻¹' C₁) : Ψ ⁻¹' C₂ = C₁ := by
  have hRead (z : Y₁) (hz : z ∈ openPreimage T₁ U₁) : Ψ z ∈ C₂ ↔ z ∈ C₁ := by
    let p : openPreimage T₁ U₁ := ⟨z,hz⟩
    have he := comparison_agrees_on_corresponding_windows Φ U₁ U₂ hU T₁ T₂ Ψ hGlobal ψ hLocal p
    have hh := Set.ext_iff.mp hTrace p
    change (ψ p).val ∈ C₂ ↔ z ∈ C₁ at hh
    change Ψ z = (ψ p).val at he
    exact he.symm ▸ hh
  ext z
  change Ψ z ∈ C₂ ↔ z ∈ C₁
  constructor
  · intro hz
    have hV : T₂.proj (Ψ z) ∈ U₂ := hC₂ hz
    rw [hGlobal] at hV
    apply (hRead z ?_).mp hz
    change T₁.proj z ∈ (U₁ : Set X₁)
    rw [hU]
    exact hV
  · intro hz
    exact (hRead z (hC₁ hz)).mpr hz

private theorem window_projection_comm
    {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    (U₁ : Opens X₁) (U₂ : Opens X₂) (hU : (U₁ : Set X₁) = Φ ⁻¹' (U₂ : Set X₂))
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : CMfd.of (n := n) (openPreimage T₁ U₁)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ U₂)}
    (hψ : EmptyAwareTowerIso (openRestriction Φ U₁ U₂ hU) (restrict U₁ T₁) (restrict U₂ T₂) ψ)
    (z : openPreimage T₁ U₁) : T₂.proj (ψ z).val = Φ (T₁.proj z.val) := by
  have h := congrArg Subtype.val (emptyAware_proj_comm hψ z)
  change ((restrict U₂ T₂).proj (ψ z)).val =
    (openRestriction Φ U₁ U₂ hU ((restrict U₁ T₁).proj z)).val at h
  rw [openRestriction_val,proj_restrict,proj_restrict] at h
  exact h

private theorem global_map_agrees_on_window {Y₁ Y₂ : CMfd.{u} n} (U : Opens X)
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    {Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (hΨ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ Ψ)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U))}
    (hψ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U T₁) (restrict U T₂) ψ) :
    ∀ z : openPreimage T₁ U, Ψ z.val = (ψ z).val := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hU : (U : Set X) = Φ ⁻¹' (U : Set X) := rfl
  have hBase : openRestriction Φ U U hU = Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ :=
    Diffeomorph.ext (fun _ => rfl)
  exact comparison_agrees_on_corresponding_windows Φ U U hU T₁ T₂ Ψ (emptyAware_proj_comm hΨ) ψ
    (window_projection_comm Φ U U hU (hBase.symm ▸ hψ))

private theorem centre_empty_of_trace_empty {Y : CMfd.{u} n} (U : Opens X) (T : BlowupTower X Y)
    {C : Set Y} (hOver : C ⊆ (openPreimage T U : Set Y))
    (hTrace : (Subtype.val : openPreimage T U → Y) ⁻¹' C = ∅) : C = ∅ :=
  subset_empty_iff.mp (fun _ hz => Set.disjoint_left.mp
    ((preimage_val_eq_empty_iff (openPreimage T U) C).mp hTrace) hz (hOver hz))

private theorem centres_match_of_supported_traces {Y₁ Y₂ : CMfd.{u} n} (U : Opens X)
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂) {C₁ : Set Y₁} {C₂ : Set Y₂}
    (hC₁ : C₁ ⊆ (openPreimage T₁ U : Set Y₁)) (hC₂ : C₂ ⊆ (openPreimage T₂ U : Set Y₂))
    {Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (hΨ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ Ψ)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U))}
    (hψ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U T₁) (restrict U T₂) ψ)
    (hTrace : ψ ⁻¹' ((Subtype.val : openPreimage T₂ U → Y₂) ⁻¹' C₂) =
      (Subtype.val : openPreimage T₁ U → Y₁) ⁻¹' C₁) : Ψ ⁻¹' C₂ = C₁ := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hU : (U : Set X) = Φ ⁻¹' (U : Set X) := rfl
  have hBase : openRestriction Φ U U hU = Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ :=
    Diffeomorph.ext (fun _ => rfl)
  exact centres_match_of_corresponding_traces Φ U U hU T₁ T₂ hC₁ hC₂ Ψ
    (emptyAware_proj_comm hΨ) ψ (window_projection_comm Φ U U hU (hBase.symm ▸ hψ)) hTrace

private theorem step_step_emptyAware_cases {A B Y Z : CMfd.{u} n}
    {T₁ : BlowupTower X A} {T₂ : BlowupTower X B} {C₁ : Set A} {C₂ : Set B}
    {π₁ : Y → A} {π₂ : Z → B} {hπ₁ : IsBlowupAlong n C₁ π₁} {hπ₂ : IsBlowupAlong n C₂ π₂}
    {Φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (h : EmptyAwareTowerIso Φ (.step T₁ C₁ π₁ hπ₁) (.step T₂ C₂ π₂ hπ₂) χ) :
    (∃ β : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B,
      EmptyAwareTowerIso Φ T₁ T₂ β ∧ β ⁻¹' C₂ = C₁) ∨
    (C₁ = ∅ ∧ ∃ β : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso Φ T₁ (.step T₂ C₂ π₂ hπ₂) β) ∨
    (C₂ = ∅ ∧ ∃ β : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B,
      EmptyAwareTowerIso Φ (.step T₁ C₁ π₁ hπ₁) T₂ β) := by
  cases h with
  | step h _ _ _ _ hC => exact Or.inl ⟨_,h,hC⟩
  | leftEmpty h _ _ _ => exact Or.inr (Or.inl ⟨rfl,_,h⟩)
  | rightEmpty h _ _ _ => exact Or.inr (Or.inr ⟨rfl,_,h⟩)

private theorem step_refl_emptyAware_cases {A Y : CMfd.{u} n}
    {T : BlowupTower X A} {C : Set A} {π : Y → A} {hπ : IsBlowupAlong n C π}
    {Φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (h : EmptyAwareTowerIso Φ (.step T C π hπ) (.refl : BlowupTower X X) χ) :
    C = ∅ ∧ ∃ β : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      EmptyAwareTowerIso Φ T (.refl : BlowupTower X X) β := by
  cases h with
  | leftEmpty h _ _ _ => exact ⟨rfl,_,h⟩

private theorem refl_step_emptyAware_cases {A Y : CMfd.{u} n}
    {T : BlowupTower X A} {C : Set A} {π : Y → A} {hπ : IsBlowupAlong n C π}
    {Φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : EmptyAwareTowerIso Φ (.refl : BlowupTower X X) (.step T C π hπ) χ) :
    C = ∅ ∧ ∃ β : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A,
      EmptyAwareTowerIso Φ (.refl : BlowupTower X X) T β := by
  cases h with
  | rightEmpty h _ _ _ => exact ⟨rfl,_,h⟩

private theorem exists_global_emptyAware {K : Set X} (U : Opens X) (hKU : K ⊆ U)
    {Y₁ Y₂ : CMfd.{u} n} (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (h₁ : CentresOver K T₁) (h₂ : CentresOver K T₂)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U))}
    (hψ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U T₁) (restrict U T₂) ψ) :
    ∃ Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ Ψ := by
  generalize hs : T₁.length + T₂.length = size
  induction size using Nat.strong_induction_on generalizing Y₁ Y₂ with
  | h size ih =>
    cases T₁ with
    | refl =>
      cases T₂ with
      | refl => exact ⟨_,.refl⟩
      | step P₂ C₂ π₂ hπ₂ =>
        obtain ⟨hTrace,β,hβ⟩ := refl_step_emptyAware_cases hψ
        have hEmpty : C₂ = ∅ := centre_empty_of_trace_empty U P₂ (fun _ h => hKU (h₂.2 h)) hTrace
        subst C₂
        have hShort : (BlowupTower.refl : BlowupTower X X).length + P₂.length < size := by
          rw [BlowupTower.length_step] at hs
          omega
        obtain ⟨η,hη⟩ := ih _ hShort .refl P₂ h₁ h₂.1 hβ rfl
        obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ₂
        exact ⟨η.trans φ.symm,.rightEmpty hη hπ₂ φ hφ⟩
    | step P₁ C₁ π₁ hπ₁ =>
      cases T₂ with
      | refl =>
        obtain ⟨hTrace,β,hβ⟩ := step_refl_emptyAware_cases hψ
        have hEmpty : C₁ = ∅ := centre_empty_of_trace_empty U P₁ (fun _ h => hKU (h₁.2 h)) hTrace
        subst C₁
        have hShort : P₁.length + (BlowupTower.refl : BlowupTower X X).length < size := by
          rw [BlowupTower.length_step] at hs
          omega
        obtain ⟨η,hη⟩ := ih _ hShort P₁ .refl h₁.1 h₂ hβ rfl
        obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ₁
        exact ⟨φ.trans η,.leftEmpty hη hπ₁ φ hφ⟩
      | step P₂ C₂ π₂ hπ₂ =>
        rcases step_step_emptyAware_cases hψ with ⟨β,hβ,hTrace⟩ | ⟨hTrace,β,hβ⟩ | ⟨hTrace,β,hβ⟩
        · have hShort : P₁.length + P₂.length < size := by
            rw [BlowupTower.length_step,BlowupTower.length_step] at hs
            omega
          obtain ⟨η,hη⟩ := ih _ hShort P₁ P₂ h₁.1 h₂.1 hβ rfl
          have hC := centres_match_of_supported_traces U P₁ P₂
            (fun _ h => hKU (h₁.2 h)) (fun _ h => hKU (h₂.2 h)) hη hβ hTrace
          obtain ⟨θ,hθ⟩ := exists_isTowerIso_step (IsTowerIso.refl (Φ := η)) hπ₁ hπ₂ hC
          exact ⟨θ,.step hη hπ₁ hπ₂ θ (fun p => (hθ.proj_comm p).symm) hC⟩
        · have hEmpty : C₁ = ∅ := centre_empty_of_trace_empty U P₁ (fun _ h => hKU (h₁.2 h)) hTrace
          subst C₁
          have hShort : P₁.length + (P₂.step C₂ π₂ hπ₂).length < size := by
            rw [BlowupTower.length_step] at hs
            omega
          obtain ⟨η,hη⟩ := ih _ hShort P₁ (.step P₂ C₂ π₂ hπ₂) h₁.1 h₂ hβ rfl
          obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ₁
          exact ⟨φ.trans η,.leftEmpty hη hπ₁ φ hφ⟩
        · have hEmpty : C₂ = ∅ := centre_empty_of_trace_empty U P₂ (fun _ h => hKU (h₂.2 h)) hTrace
          subst C₂
          have hShort : (P₁.step C₁ π₁ hπ₁).length + P₂.length < size := by
            rw [BlowupTower.length_step,BlowupTower.length_step] at hs
            rw [BlowupTower.length_step]
            omega
          obtain ⟨η,hη⟩ := ih _ hShort (.step P₁ C₁ π₁ hπ₁) P₂ h₁ h₂.1 hβ rfl
          obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ₂
          exact ⟨η.trans φ.symm,.rightEmpty hη hπ₂ φ hφ⟩

/-- A comparison on an open containing the centre footprint extends to the same ambient towers. -/
theorem emptyAware_extends_of_centresOver {K : Set X} (U : Opens X) (hKU : K ⊆ U)
    {Y₁ Y₂ : CMfd.{u} n} (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (h₁ : CentresOver K T₁) (h₂ : CentresOver K T₂)
    {ψ : (CMfd.of (n := n) (openPreimage T₁ U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U))}
    (hψ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U T₁) (restrict U T₂) ψ) :
    ∃ Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ Ψ ∧
        ∀ z : openPreimage T₁ U, Ψ z.val = (ψ z).val := by
  obtain ⟨Ψ,hΨ⟩ := exists_global_emptyAware U hKU T₁ T₂ h₁ h₂ hψ
  exact ⟨Ψ,hΨ,global_map_agrees_on_window U T₁ T₂ hΨ hψ⟩

/-- If every centre lies over a comparison window, a strict comparison
of the restricted towers extends with all stage and slot positions. -/
theorem isTowerIso_extends_of_supported_windows {X₁ X₂ : CMfd.{u} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    (U₁ : Opens X₁) (U₂ : Opens X₂) (hU : (U₁ : Set X₁) = Φ ⁻¹' (U₂ : Set X₂))
    {Y₁ Y₂ : CMfd.{u} n} (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (h₁ : CentresOver (U₁ : Set X₁) T₁) (h₂ : CentresOver (U₂ : Set X₂) T₂)
    {ψ : CMfd.of (n := n) (openPreimage T₁ U₁)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ U₂)}
    (hψ : IsTowerIso (openRestriction Φ U₁ U₂ hU) (restrict U₁ T₁) (restrict U₂ T₂) ψ) :
    ∃ Ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂, IsTowerIso Φ T₁ T₂ Ψ := by
  induction T₁ generalizing Y₂ with
  | refl =>
    cases T₂ with
    | refl => exact ⟨Φ,.refl⟩
    | step P C π hπ =>
      have hLen := hψ.length_eq
      simp only [length_restrict,BlowupTower.length_step,BlowupTower.length_refl] at hLen
      omega
  | step P₁ C₁ π₁ hπ₁ ih =>
    cases T₂ with
    | refl =>
      have hLen := hψ.length_eq
      simp only [length_restrict,BlowupTower.length_step,BlowupTower.length_refl] at hLen
      omega
    | step P₂ C₂ π₂ hπ₂ =>
      obtain ⟨β,hβ,_,hTrace⟩ := hψ.step_inv
      obtain ⟨η,hη⟩ := ih P₂ h₁.1 h₂.1 hβ
      have hC := centres_match_of_corresponding_traces Φ U₁ U₂ hU P₁ P₂
        h₁.2 h₂.2 η (fun z => (hη.proj_comm z).symm) β
          (window_projection_comm Φ U₁ U₂ hU (emptyAware_of_isTowerIso hβ)) hTrace
      exact exists_isTowerIso_step hη hπ₁ hπ₂ hC

end
end Hironaka.HironakaSupportedTowerPhysicalExtension

import Hironaka.Resolution.HironakaG3MixedComponentOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport

/-! Comparison on the strict contact for two lifts of the SAME lower history.
This is not an ambient overlap or a global gluing theorem. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ContactComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport

/-- Two actual coupled lifts of the same intrinsic tower have a common
strict-contact biholomorphism over the original base. It preserves the
ordered retained boundary trace and all strict transforms of lower subsets. -/
theorem exists_contact_comparison_of_same_lower_history
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d}
    {Y₁ Y₂ : CMfd.{0} (d+t)} {N : Set X} {B : List (Set X)}
    {J : GermIdeal (d+t) X} {ι : P → X} {M : MarkedIdeal d P}
    {T : BlowupTower P Q} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
    {η₁ : Q → Y₁} {η₂ : Q → Y₂}
    (h₁ : CoupledHistory N B J ι M T U₁ η₁)
    (h₂ : CoupledHistory N B J ι M T U₂ η₂) :
    ∃ (hr₁ : ∀ y ∈ contactAlong N U₁, RegularAtDim (n := d+t) (contactAlong N U₁) y d)
      (hr₂ : ∀ y ∈ contactAlong N U₂, RegularAtDim (n := d+t) (contactAlong N U₂) y d),
      letI := chartedSpace (Nat.le_add_right d t) hr₁
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₁
      letI := chartedSpace (Nat.le_add_right d t) hr₂
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₂
      ∃ e : (contactAlong N U₁) ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
          (contactAlong N U₂),
        (∀ z, U₂.proj (e z).val = U₁.proj z.val) ∧
        ((geoTransformAlong (fullMarked B J) U₂).E.map
          (fun H => (fun z => (e z).val) ⁻¹' H) =
         (geoTransformAlong (fullMarked B J) U₁).E.map
          (fun H => (Subtype.val : contactAlong N U₁ → Y₁) ⁻¹' H)) ∧
        ∀ (V : Set P) (z : contactAlong N U₁),
          (e z).val ∈ strictAlong U₂ (ι '' V) ↔
            z.val ∈ strictAlong U₁ (ι '' V) := by
  obtain ⟨_hc₁, hr₁, _hI₁, _hN₁, _hSNC₁, _hTr₁, F₁, hF₁, hSq₁, _hIdeal₁, hB₁⟩ :=
    endpoint_of_coupledHistory h₁
  obtain ⟨_hc₂, hr₂, _hI₂, _hN₂, _hSNC₂, _hTr₂, F₂, hF₂, hSq₂, _hIdeal₂, hB₂⟩ :=
    endpoint_of_coupledHistory h₂
  let := chartedSpace (Nat.le_add_right d t) hr₁
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₁
  let := chartedSpace (Nat.le_add_right d t) hr₂
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₂
  let e := F₁.symm.trans F₂
  refine ⟨hr₁, hr₂, e, ?_, ?_, ?_⟩
  · intro z
    have hq₁ := congrFun hSq₁ (F₁.symm z)
    have hq₂ := congrFun hSq₂ (F₁.symm z)
    change U₂.proj (F₂ (F₁.symm z)).val = U₁.proj z.val
    change U₂.proj (η₂ (F₁.symm z)) = ι (T.proj (F₁.symm z)) at hq₂
    change U₁.proj (η₁ (F₁.symm z)) = ι (T.proj (F₁.symm z)) at hq₁
    rw [← congrFun hF₂ (F₁.symm z)] at hq₂
    rw [← congrFun hF₁ (F₁.symm z), F₁.apply_symm_apply] at hq₁
    exact hq₂.trans hq₁.symm
  · have hTrace₁ : (geoTransformAlong M T).E.map (fun H => F₁.symm ⁻¹' H) =
        (geoTransformAlong (fullMarked B J) U₁).E.map
          (fun H => (Subtype.val : contactAlong N U₁ → Y₁) ⁻¹' H) := by
      rw [← hB₁, List.map_map]
      apply List.map_congr_left
      intro H _
      ext z
      change η₁ (F₁.symm z) ∈ H ↔ z.val ∈ H
      rw [← congrFun hF₁ (F₁.symm z), F₁.apply_symm_apply]
    have hTrace₂ : (geoTransformAlong M T).E.map (fun H => F₁.symm ⁻¹' H) =
        (geoTransformAlong (fullMarked B J) U₂).E.map
          (fun H => (fun z => (e z).val) ⁻¹' H) := by
      rw [← hB₂, List.map_map]
      apply List.map_congr_left
      intro H _
      ext z
      change η₂ (F₁.symm z) ∈ H ↔ (F₂ (F₁.symm z)).val ∈ H
      rw [← congrFun hF₂ (F₁.symm z)]
    exact hTrace₂.symm.trans hTrace₁
  · intro V z
    have hS₁ := strictAlong_image_of_coupledHistory h₁ V
    have hS₂ := strictAlong_image_of_coupledHistory h₂ V
    rw [← hS₁, ← hS₂]
    change ((F₂ (F₁.symm z)).val ∈ η₂ '' strictAlong T V) ↔
      z.val ∈ η₁ '' strictAlong T V
    constructor
    · rintro ⟨q, hq, hqeq⟩
      have hval : (F₂ q).val = (F₂ (F₁.symm z)).val :=
        (congrFun hF₂ q).trans hqeq
      have heq : q = F₁.symm z := F₂.injective (Subtype.ext hval)
      subst q
      refine ⟨F₁.symm z, hq, ?_⟩
      rw [← congrFun hF₁ (F₁.symm z), F₁.apply_symm_apply]
    · rintro ⟨q, hq, hqeq⟩
      have hval : (F₁ q).val = z.val := (congrFun hF₁ q).trans hqeq
      have heq : q = F₁.symm z :=
        F₁.injective ((Subtype.ext hval).trans (F₁.apply_symm_apply z).symm)
      subst q
      refine ⟨F₁.symm z, hq, ?_⟩
      exact (congrFun hF₂ (F₁.symm z)).symm

end
end Hironaka.HironakaG3ContactComparison

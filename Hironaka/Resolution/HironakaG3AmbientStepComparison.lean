import Hironaka.Resolution.HironakaG3ContactComparison
import Hironaka.Blowup.BlowupTowerIsomorphism

/-! The next ambient blowups over the same intrinsic step are compared by the
universal properties, including the actual lower embedding. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AmbientStepComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport
  HironakaActualClosedContactBlowupRestriction MarkedIdealBiholomorphism

/-- Once the previous ambient map carries the same actual lower embedding,
uniqueness of blowups gives the next ambient comparison, and uniqueness of
the intrinsic-to-ambient lift forces it to carry the next embedding. -/
theorem exists_comparison_of_same_lower_step
    {d t : ℕ} {Q R : CMfd.{0} d} {Y₁ Y₂ Z₁ Z₂ : CMfd.{0} (d+t)}
    {S : Set Y₁} (hr : ∀ y ∈ S, RegularAtDim (n := d+t) S y d) :
    letI := chartedSpace (Nat.le_add_right d t) hr
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
    ∀ (F : Q ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S)
      (β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂)
      (C : Set Q) (ρ : R → Q) (_hρ : IsBlowupAlong d C ρ)
      (π₁ : Z₁ → Y₁) (π₂ : Z₂ → Y₂)
      (_hπ₁ : IsBlowupAlong (d+t) ((fun q => (F q).val) '' C) π₁)
      (_hπ₂ : IsBlowupAlong (d+t) ((fun q => β (F q).val) '' C) π₂)
      (κ₁ : R → Z₁) (κ₂ : R → Z₂)
      (_hκ₁ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ κ₁)
      (_hκ₂ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ κ₂)
      (_hSq₁ : π₁ ∘ κ₁ = (fun q => (F q).val) ∘ ρ)
      (_hSq₂ : π₂ ∘ κ₂ = (fun q => β (F q).val) ∘ ρ),
      ∃ χ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Z₂,
        (∀ z, π₂ (χ z) = β (π₁ z)) ∧ (∀ z, χ (κ₁ z) = κ₂ z) := by
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  intro F β C ρ hρ π₁ π₂ hπ₁ hπ₂ κ₁ κ₂ hκ₁ hκ₂ hSq₁ hSq₂
  let D : Set S := F '' C
  have hCentre : (Subtype.val : S → Y₁) '' D = (fun q => (F q).val) '' C := by
    simp only [D, image_image]
  have hB : β ⁻¹' ((fun q => β (F q).val) '' C) = (fun q => (F q).val) '' C := by
    ext y
    constructor
    · rintro ⟨q,hq,hqeq⟩
      exact ⟨q,hq,β.injective hqeq⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q,hq,rfl⟩
  have hπ₂' := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply hπ₂
  rw [hB] at hπ₂'
  obtain ⟨a,b,ha,hb,hπa,_hπb,hba,hab⟩ := BlowupUniqueness.exists_biholomorphism_over hπ₁ hπ₂'
  let χ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Z₂ :=
    ⟨⟨a,b,congrFun hba,congrFun hab⟩,ha,hb⟩
  have hχ : ∀ z, π₂ (χ z) = β (π₁ z) := by
    intro z
    have h := congrFun hπa z
    change β.symm (π₂ (χ z)) = π₁ z at h
    rw [← h, β.apply_symm_apply]
  have hρS : IsBlowupAlong d D (F ∘ ρ) := by
    have h := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
      F.symm.contMDiff F.contMDiff F.symm_apply_apply F.apply_symm_apply hρ
    have hPre : F.symm ⁻¹' C = D := by
      ext z
      constructor
      · intro hz
        exact ⟨F.symm z, hz, F.apply_symm_apply z⟩
      · rintro ⟨q, hq, rfl⟩
        change F.symm (F q) ∈ C
        rw [F.symm_apply_apply]
        exact hq
    rw [hPre] at h
    exact h
  have hπ₁S : IsBlowupAlong (d+t) ((Subtype.val : S → Y₁) '' D) π₁ := by
    rw [hCentre]
    exact hπ₁
  obtain ⟨k,_hk,hUnique⟩ := HironakaActualClosedContactBlowupRestriction.exists_unique_lift
    (Nat.le_add_right d t) hr hπ₁S hρS
  have hComp : π₁ ∘ (χ.symm ∘ κ₂) = (Subtype.val : S → Y₁) ∘ (F ∘ ρ) := by
    funext z
    have hχz := hχ (χ.symm (κ₂ z))
    rw [χ.apply_symm_apply] at hχz
    have h2 := congrFun hSq₂ z
    change π₂ (κ₂ z) = β (F (ρ z)).val at h2
    apply β.injective
    exact hχz.symm.trans h2
  have hSq₁' : π₁ ∘ κ₁ = (Subtype.val : S → Y₁) ∘ (F ∘ ρ) := by
    simpa only [Function.comp_def] using hSq₁
  have hEq : χ.symm ∘ κ₂ = κ₁ :=
    (hUnique (χ.symm ∘ κ₂) ⟨χ.symm.contMDiff.comp hκ₂,hComp⟩).trans
      (hUnique κ₁ ⟨hκ₁,hSq₁'⟩).symm
  refine ⟨χ,hχ,?_⟩
  intro z
  have h := congrFun hEq z
  change χ.symm (κ₂ z) = κ₁ z at h
  rw [← h, χ.apply_symm_apply]

end
end Hironaka.HironakaG3AmbientStepComparison

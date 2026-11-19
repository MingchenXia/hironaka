import Hironaka.Resolution.HironakaG3EmptyAwareOldSlots
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG3EmptyAwareBornSlots
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupStrictSubmanifold
  HomogenizedGlueingTower BlowupTowerIsomorphism HironakaG3EmptyAwareHistory MemberInterTowerAlong
  HironakaNormalCrossingsSeparationChoiceComparison

def bornAlong {d : ℕ} {X : CMfd.{u} d} : {Y : CMfd.{u} d} → BlowupTower X Y → List (Set Y)
  | _, .refl => []
  | _, .step T C π _ => (bornAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C]

theorem born_closed {d : ℕ} {X Y : CMfd.{u} d} (T : BlowupTower X Y) :
    ∀ H ∈ bornAlong T, IsClosed H := by
  induction T with
  | refl => simp [bornAlong]
  | @step Y Z T C π hπ ih =>
    intro H hH
    change H ∈ (bornAlong T).map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨B,_,rfl⟩ := List.mem_map.mp hH
      exact isClosed_closure
    · rw [List.mem_singleton.mp hH]
      exact hπ.1.1.preimage hπ.contMDiff.continuous

private theorem filter_map_skip_empty {P Q : Type*} (f : Set P → Set Q)
    (hf : f ∅ = ∅) (L : List (Set P)) :
    (L.map f).filter (fun H => decide H.Nonempty) =
      ((L.filter (fun H => decide H.Nonempty)).map f).filter (fun H => decide H.Nonempty) := by
  induction L with
  | nil => rfl
  | cons H L ih =>
    by_cases hH : H.Nonempty
    · by_cases hfH : (f H).Nonempty <;> simp [hH,hfH,ih]
    · have : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
      subst H
      simp [hf,ih]

theorem filter_map_bijection {P Q : Type*} (f : P → Q) (hf : Surjective f) (L : List (Set Q)) :
    (L.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (L.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction L with
  | nil => rfl
  | cons H L ih =>
    have h : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun hh => hh.preimage hf⟩
    by_cases hH : H.Nonempty <;> simp [h,hH,ih]

/-- Chronological exceptional births agree after deleting literal empty slots. -/
theorem emptyAware_born_boundary {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    (bornAlong T₁).filter (fun H => decide H.Nonempty) =
      ((bornAlong T₂).filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
  induction h with
  | refl => rfl
  | @step Y₁ Y₂ Z₁ Z₂ T₁ T₂ ψ h C₁ π₁ hπ₁ C₂ π₂ hπ₂ χ hcomm hC ih =>
    have hf₁ : geoStrictTransform π₁ C₁ ∅ = ∅ := by simp [geoStrictTransform]
    have hf₂ : geoStrictTransform π₂ C₂ ∅ = ∅ := by simp [geoStrictTransform]
    have hmid : ((bornAlong T₁).map (geoStrictTransform π₁ C₁)).filter (fun H => decide H.Nonempty) =
        (((bornAlong T₂).map (geoStrictTransform π₂ C₂)).filter (fun H => decide H.Nonempty)).map (χ ⁻¹' ·) := by
      rw [filter_map_skip_empty _ hf₁, ih]
      have hmap : (((bornAlong T₂).filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·)).map
          (geoStrictTransform π₁ C₁) = (((bornAlong T₂).filter (fun H => decide H.Nonempty)).map
          (geoStrictTransform π₂ C₂)).map (χ ⁻¹' ·) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro H hH
        rw [← hC]
        exact geoStrictTransform_preimage_of_square ψ χ π₁ π₂ C₂ H hcomm
      rw [hmap,filter_map_bijection χ χ.surjective,← filter_map_skip_empty _ hf₂]
    have hexc : π₁ ⁻¹' C₁ = χ ⁻¹' (π₂ ⁻¹' C₂) := by
      rw [←hC]
      ext z
      change ψ (π₁ z) ∈ C₂ ↔ π₂ (χ z) ∈ C₂
      rw [hcomm]
    simp only [bornAlong,List.filter_append,List.map_append] at ⊢
    rw [hmid,hexc]
    congr 1
    simpa only [List.map_cons,List.map_nil] using filter_map_bijection χ χ.surjective [π₂ ⁻¹' C₂]
  | @leftEmpty Y₁ Y₂ Z₁ T₁ T₂ ψ h π hπ χ hχ ih =>
    have hmap : (bornAlong T₁).map (geoStrictTransform π ∅) = (bornAlong T₁).map (χ ⁻¹' ·) := by
      apply List.map_congr_left
      intro H hH
      rw [ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous (born_closed T₁ H hH)]
      ext z
      change π z ∈ H ↔ χ z ∈ H
      rw [hχ]
    simp only [bornAlong,preimage_empty,List.filter_append,List.filter_cons,Set.not_nonempty_empty,
      decide_false,Bool.false_eq_true,reduceIte,List.filter_nil,List.append_nil]
    rw [hmap,filter_map_bijection χ χ.surjective,ih,List.map_map]
    rfl
  | @rightEmpty Y₁ Y₂ Z₂ T₁ T₂ ψ h π hπ χ hχ ih =>
    have hmap : (bornAlong T₂).map (geoStrictTransform π ∅) = (bornAlong T₂).map (χ ⁻¹' ·) := by
      apply List.map_congr_left
      intro H hH
      rw [ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous (born_closed T₂ H hH)]
      ext z
      change π z ∈ H ↔ χ z ∈ H
      rw [hχ]
    simp only [bornAlong,preimage_empty,List.filter_append,List.filter_cons,Set.not_nonempty_empty,
      decide_false,Bool.false_eq_true,reduceIte,List.filter_nil,List.append_nil]
    rw [hmap,filter_map_bijection χ χ.surjective,ih,List.map_map]
    congr 1
    funext H
    ext z
    change ψ z ∈ H ↔ χ (χ.symm (ψ z)) ∈ H
    rw [χ.apply_symm_apply]

end
end Hironaka.HironakaG3EmptyAwareBornSlots

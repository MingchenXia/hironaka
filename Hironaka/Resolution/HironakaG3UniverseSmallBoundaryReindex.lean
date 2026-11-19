import Hironaka.Resolution.HironakaG3UniverseSmallBoundary
import Hironaka.Blowup.NormalCrossingsInvariance
set_option autoImplicit false
open Set Function
universe u v
namespace Hironaka.HironakaG3UniverseSmallBoundaryReindex
noncomputable section
open BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3UniverseSmallBoundary NormalCrossingsInvariance

/-- A locally finite indexed SNC boundary has a base-universe nonempty reindexing with the same support. -/
theorem exists_small_boundary_reindex_with_labels {n : ℕ} (X : CMfd.{u} n) {ι : Type v}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (κ : Type) (f : κ → ι),
      Injective f ∧ (∀ i, (D i).Nonempty → i ∈ range f) ∧
      IsLocallyFiniteSNCDivisor n (fun j => D (f j)) ∧
      (∀ j, (D (f j)).Nonempty) ∧ (⋃ j, D (f j)) = ⋃ i, D i := by
  classical
  let I := {i : ι // (D i).Nonempty}
  let : Small.{0} I := nonempty_index_small X D hD
  let f : Shrink.{0} I → ι := fun j => ((equivShrink I).symm j).val
  have hf : Injective f := by
    intro j k h
    apply (equivShrink I).symm.injective
    exact Subtype.ext h
  have hRange : ∀ i, (D i).Nonempty → i ∈ range f := by
    intro i hi
    exact ⟨equivShrink I ⟨i,hi⟩, by simp [f]⟩
  refine ⟨Shrink.{0} I, f, hf, hRange,
    ⟨hD.1.comp_injective hf, fun j => hD.2.1 (f j), ?_⟩,
    (fun j => ((equivShrink I).symm j).property), ?_⟩
  · intro x
    obtain ⟨S,hA,hcard,hinj⟩ := hD.2.2 x
    exact ⟨fun j => S (f j), IsCoordinateFamilyAt.reindex hA f (fun _ => rfl) (fun _ => rfl),
      fun j hj => hcard (f j) hj, fun j hj k hk hEq => hf (hinj hj hk hEq)⟩
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨f j,hj⟩
    · rintro ⟨i,hi⟩
      refine ⟨equivShrink I ⟨i,⟨x,hi⟩⟩, ?_⟩
      simpa only [f, Equiv.symm_apply_apply] using hi

theorem exists_small_boundary_reindex {n : ℕ} (X : CMfd.{u} n) {ι : Type v}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (κ : Type) (B : κ → Set X), IsLocallyFiniteSNCDivisor n B ∧
      (∀ j, (B j).Nonempty) ∧ (⋃ j, B j) = ⋃ i, D i := by
  obtain ⟨κ,f,_hf,_hRange,hB,hBne,hUnion⟩ := exists_small_boundary_reindex_with_labels X D hD
  exact ⟨κ,fun j => D (f j),hB,hBne,hUnion⟩

end
end Hironaka.HironakaG3UniverseSmallBoundaryReindex

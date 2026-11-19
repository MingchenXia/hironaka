import Hironaka.Resolution.HironakaG3IndexedTopContact
import Hironaka.Resolution.HironakaG3RBoundaryTop
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3IndexedTopContactEndpoint
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3IndexedContainingBoundary HironakaG3IndexedTopContact

/-- Remove empty labels without changing the support or relative normal crossings. -/
theorem nonempty_boundary_reindex {n : ℕ} {X : CMfd.{v} n} {ι : Type u}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) {C : Set X}
    (hNC : HasNormalCrossingsWithBoundary C D) :
    ∃ (κ : Type u) (F : κ → Set X), IsLocallyFiniteSNCDivisor n F ∧
      (∀ i, (F i).Nonempty) ∧ (⋃ i, F i) = ⋃ i, D i ∧ HasNormalCrossingsWithBoundary C F := by
  let κ := {i : ι // (D i).Nonempty}
  let e : κ → ι := Subtype.val
  have he : Injective e := Subtype.val_injective
  refine ⟨κ, fun i => D (e i), ⟨hD.1.comp_injective he, fun i => hD.2.1 (e i), fun x => ?_⟩,
    fun i => i.2, ?_, ?_⟩
  · obtain ⟨S,hA,hcard,hinj⟩ := hD.2.2 x
    exact ⟨fun i => S (e i), NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hA e (fun _ => rfl) (fun _ => rfl),
      fun i hi => hcard (e i) hi, fun i hi j hj hij => he (hinj hi hj hij)⟩
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨⟨i,⟨x,hi⟩⟩,hi⟩
  · intro x hx
    obtain ⟨S₀,S,hA,hcard⟩ := hNC x hx
    refine ⟨S₀, fun i => S (e i), NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hA (Option.map e) ?_ ?_, fun i hi => hcard (e i) hi⟩
    · rintro (_ | i) <;> rfl
    · rintro (_ | i) <;> rfl

/-- Equal contact dimension needs no blowup: the identity is an endpoint. -/
theorem indexed_top_contact_identity_endpoint {n r : ℕ} {X : CMfd.{0} n} {ι : Type u}
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hD : IsLocallyFiniteSNCDivisor n D)
    (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (htop : n - (containingLabels C D hC.nonempty hD.1).card ≤ r) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : X → X) ∧
    IsProperMap (id : X → X) ∧ Surjective (id : X → X) ∧
    IsIsomorphismOver n (id : X → X) univ ∧
    IsClosedSubmanifold n (strictTransform n (id : X → X) C) ∧
    (∀ x ∈ strictTransform n (id : X → X) C,
      RegularAtDim (n := n) (strictTransform n (id : X → X) C) x r) ∧
    ∃ (κ : Type u) (F : κ → Set X), IsLocallyFiniteSNCDivisor n F ∧
      (∀ i, (F i).Nonempty) ∧
      (⋃ i, F i) = (id : X → X) ⁻¹' (⋃ i, D i) ∪ exceptionalLocus n (id : X → X) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (id : X → X) C) F := by
  obtain ⟨_,_,hsm,hreg,hNC⟩ := indexed_top_contact_already_normal C D hC hD hpure htop
  have hst : strictTransform n (id : X → X) C = C := by
    simp [strictTransform, exceptionalLocus_id, hC.analytic.isClosed.closure_eq]
  obtain ⟨κ,F,hF,hne,hU,hFNC⟩ := nonempty_boundary_reindex D hD hNC
  refine ⟨contMDiff_id,isProperMap_id,surjective_id,⟨bijOn_id _,by rw [exceptionalLocus_id]; exact disjoint_empty _⟩,?_,?_,κ,F,hF,hne,?_,?_⟩
  · simpa only [hst] using hsm
  · simpa only [hst] using hreg
  · simpa only [exceptionalLocus_id, union_empty, preimage_id] using hU
  · simpa only [hst] using hFNC
end
end Hironaka.HironakaG3IndexedTopContactEndpoint

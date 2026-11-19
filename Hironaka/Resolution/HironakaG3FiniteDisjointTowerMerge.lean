import Hironaka.Resolution.HironakaG3EmptyAwareNestedRestriction
import Hironaka.Resolution.HironakaG3RestrictEndpointComparison
import Hironaka.Resolution.HironakaG3TwoDisjointTowerMerge
import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3FiniteDisjointTowerMerge
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  HironakaG3EmptyAwareHistory HironakaG3TwoDisjointTowerMerge
  HironakaG3RestrictEndpointComparison HironakaG3EmptyAwareNestedRestriction HironakaG3EmptyAwareComposition HironakaActualProcessedAllMasksDrop

def finiteSupport {n : ℕ} {X : CMfd.{0} n} {ι : Type u} (F : ι → Set X) (s : Finset ι) : Set X :=
  ⋃ i ∈ s, F i

theorem finite_disjoint_towers_physical_comparisons {n : ℕ} {X : CMfd.{0} n} {ι : Type u}
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (W : ι → Opens X)
    (hFW : ∀ i, F i ⊆ W i)
    (hW : ∀ i j, i ≠ j → Disjoint (W i : Set X) (F j))
    (Y : ι → CMfd.{0} n) (T : ∀ i, BlowupTower X (Y i))
    (hT : ∀ i, CentresOver (F i) (T i)) (s : Finset ι) :
    ∃ (Z : CMfd.{0} n) (M : BlowupTower X Z), CentresOver (finiteSupport F s) M ∧
      ∀ i ∈ s, ∃ φ : (CMfd.of (n := n) (openPreimage M (W i))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (T i) (W i))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (W i)) ∞)
          (restrict (W i) M) (restrict (W i) (T i)) φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨X,.refl,trivial,?_⟩
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
    obtain ⟨Z,M,hM,hCompare⟩ := ih
    have hClosed : IsClosed (finiteSupport F s) := by
      exact s.finite_toSet.isClosed_biUnion (fun j _ => hF j)
    have hDis : Disjoint (finiteSupport F s) (F i) := by
      apply Set.disjoint_left.mpr
      intro x hx hiF
      obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hx
      have hji : j ≠ i := by intro h; subst j; exact hi hj
      exact Set.disjoint_left.mp (hW j i hji) (hFW j hxj) hiF
    obtain ⟨Z',Q,hQ,hFirst,ψR,hSecond⟩ := two_disjoint_towers_with_actual_comparisons
      (finiteSupport F s) (F i) hClosed (hF i) hDis M hM (T i) (hT i)
    have hUnion : finiteSupport F (insert i s) = finiteSupport F s ∪ F i := by
      ext x
      simp only [finiteSupport, Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
      aesop
    refine ⟨Z',M.append Q,?_,?_⟩
    · rw [hUnion]
      apply (centresOver_append_iff (finiteSupport F s ∪ F i) M Q).mpr
      exact ⟨centresOver_mono_local Set.subset_union_left M hM,
        centresOver_mono_local (Set.preimage_mono Set.subset_union_right) Q hQ⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        let R : Opens X := ⟨(finiteSupport F s)ᶜ,hClosed.isOpen_compl⟩
        have hWiR : W i ≤ R := by
          intro x hxW hxS
          obtain ⟨j,hj,hxF⟩ := Set.mem_iUnion₂.mp hxS
          have hij : i ≠ j := by intro h; subst j; exact hi hj
          exact Set.disjoint_left.mp (hW i j hij) hxW hxF
        exact emptyAware_nested_restriction (M.append Q) (T i) hWiR ψR hSecond
      · have hji : j ≠ i := by intro h; subst j; exact hi hj
        obtain ⟨φ,hφ⟩ := hCompare j hj
        obtain ⟨ψ,hψ⟩ := hFirst (W j) (hW j i hji)
        refine ⟨ψ.trans φ,?_⟩
        simpa only [Diffeomorph.refl_trans] using HironakaG3EmptyAwareComposition.trans hψ hφ

theorem finite_disjoint_towers_endpoint_comparisons {n : ℕ} {X : CMfd.{0} n} {ι : Type u}
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (W : ι → Opens X)
    (hFW : ∀ i, F i ⊆ W i)
    (hW : ∀ i j, i ≠ j → Disjoint (W i : Set X) (F j))
    (Y : ι → CMfd.{0} n) (T : ∀ i, BlowupTower X (Y i))
    (hT : ∀ i, CentresOver (F i) (T i)) (s : Finset ι) :
    ∃ (Z : CMfd.{0} n) (M : BlowupTower X Z), CentresOver (finiteSupport F s) M ∧
      ∀ i ∈ s, ∃ φ : (CMfd.of (n := n) (openPreimage M (W i))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (T i) (W i))),
        ∀ z, (T i).proj (φ z).val = M.proj z.val := by
  obtain ⟨Z,M,hM,hCompare⟩ := finite_disjoint_towers_physical_comparisons F hF W hFW hW Y T hT s
  refine ⟨Z,M,hM,?_⟩
  intro i hi
  obtain ⟨φ,hφ⟩ := hCompare i hi
  refine ⟨φ,?_⟩
  intro z
  have h := congrArg Subtype.val (emptyAware_proj_comm hφ z)
  simpa only [Diffeomorph.coe_refl, id_eq, proj_restrict] using h
end
end Hironaka.HironakaG3FiniteDisjointTowerMerge

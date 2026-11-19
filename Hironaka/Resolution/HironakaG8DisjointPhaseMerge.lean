import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
import Hironaka.Resolution.HironakaG3ClosedFootprintTransportedTower

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG8DisjointPhaseMerge

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  MarkedIdealTowerTransport BlowupTowerIsomorphism RestrictEmptyTower
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition HironakaG3FiniteDisjointTowerMerge
  HironakaG3ClosedFootprintTransportedTower HironakaG3CentresOverGenericFactor

/-- Physical empty-aware comparisons of respective prefixes and tails concatenate. -/
theorem emptyAware_append {n : ℕ} {X₁ X₂ A₁ A₂ Y₁ Y₂ : CMfd.{u} n}
    {α : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {β : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A₂}
    {χ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    {P₁ : BlowupTower X₁ A₁} {P₂ : BlowupTower X₂ A₂}
    {R₁ : BlowupTower A₁ Y₁} {R₂ : BlowupTower A₂ Y₂}
    (hP : EmptyAwareTowerIso α P₁ P₂ β) (hR : EmptyAwareTowerIso β R₁ R₂ χ) :
    EmptyAwareTowerIso α (P₁.append R₁) (P₂.append R₂) χ := by
  induction hR with
  | refl => exact hP
  | step _ hπ₁ hπ₂ ψ hComm hC ih => exact .step ih hπ₁ hπ₂ ψ hComm hC
  | leftEmpty _ hπ ψ hψ ih => exact .leftEmpty ih hπ ψ hψ
  | rightEmpty _ hπ ψ hψ ih => exact .rightEmpty ih hπ ψ hψ

/-- Comparisons on the two restricted phases identify the full restricted histories. -/
theorem emptyAware_append_restricted {n : ℕ} {X A₁ A₂ Y₁ Y₂ : CMfd.{0} n}
    (U : Opens X) (P₁ : BlowupTower X A₁) (P₂ : BlowupTower X A₂)
    (R₁ : BlowupTower A₁ Y₁) (R₂ : BlowupTower A₂ Y₂)
    {β : (CMfd.of (n := n) (openPreimage P₁ U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage P₂ U))}
    (hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U P₁) (restrict U P₂) β)
    {χ : (CMfd.of (n := n) (openPreimage R₁ (openPreimage P₁ U)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage R₂ (openPreimage P₂ U)))}
    (hR : EmptyAwareTowerIso β (restrict (openPreimage P₁ U) R₁) (restrict (openPreimage P₂ U) R₂) χ) :
    ∃ φ : (CMfd.of (n := n) (openPreimage (P₁.append R₁) U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (P₂.append R₂) U)),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
        (restrict U (P₁.append R₁)) (restrict U (P₂.append R₂)) φ := by
  have hL := isTowerIso_restrict_append U P₁ R₁
  have hRight := (isTowerIso_restrict_append U P₂ R₂).symm
  let eL := opensCongr (n := n) (openPreimage_append P₁ R₁ U).symm
  let eR := opensCongr (n := n) (openPreimage_append P₂ R₂ U).symm
  refine ⟨(eL.trans χ).trans eR.symm,?_⟩
  simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans] using
    trans (trans (emptyAware_of_isTowerIso hL) (emptyAware_append hP hR)) (emptyAware_of_isTowerIso hRight)

/-- Perform every first phase before any second phase, with both actual comparisons on each isolated window. -/
theorem finite_disjoint_split_towers_merge {n : ℕ} {X : CMfd.{0} n} {ι : Type u} [Fintype ι]
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (U : ι → Opens X) (hFU : ∀ i, F i ⊆ U i)
    (hU : ∀ i j, i ≠ j → Disjoint (U i : Set X) (F j))
    (Y Z : ι → CMfd.{0} n) (P : ∀ i, BlowupTower X (Y i)) (R : ∀ i, BlowupTower (Y i) (Z i))
    (hP : ∀ i, CentresOver (F i) (P i)) (hR : ∀ i, CentresOver ((P i).proj ⁻¹' F i) (R i)) :
    ∃ (K : CMfd.{0} n) (T : BlowupTower X K) (L : CMfd.{0} n) (Q : BlowupTower K L),
      CentresOver (⋃ i, F i) T ∧ CentresOver (T.proj ⁻¹' (⋃ i, F i)) Q ∧
      ∀ i, ∃ β : (CMfd.of (n := n) (openPreimage T (U i)))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (P i) (U i))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (U i) ∞)
          (restrict (U i) T) (restrict (U i) (P i)) β ∧
        ∃ χ : (CMfd.of (n := n) (openPreimage Q (openPreimage T (U i))))
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          (CMfd.of (n := n) (openPreimage (R i) (openPreimage (P i) (U i)))),
          EmptyAwareTowerIso β (restrict (openPreimage T (U i)) Q) (restrict (openPreimage (P i) (U i)) (R i)) χ := by
  classical
  obtain ⟨K,T,hT,hCompare⟩ := finite_disjoint_towers_physical_comparisons F hF U hFU hU Y P hP Finset.univ
  choose β hβ using fun i => hCompare i (Finset.mem_univ i)
  let A (i : ι) : Opens K := openPreimage T (U i)
  let A' (i : ι) : Opens (Y i) := openPreimage (P i) (U i)
  let G (i : ι) : Set K := T.proj ⁻¹' F i
  have hG (i : ι) : IsClosed (G i) := (hF i).preimage T.contMDiff_proj.continuous
  have hGA (i : ι) : G i ⊆ A i := fun _ hx => hFU i hx
  have hSep (i j : ι) (hij : i ≠ j) : Disjoint (A i : Set K) (G j) := by
    apply Set.disjoint_left.mpr
    intro x hx hxG
    exact Set.disjoint_left.mp (hU i j hij) hx hxG
  have hExt (i : ι) : ∃ (L' : CMfd.{0} n) (Q' : BlowupTower K L'),
      CentresOver (G i) Q' ∧
      ∃ e : (transport (β i) (restrict (A' i) (R i))).target
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage Q' (A i))),
        IsTowerIso (β i) (restrict (A i) Q') (restrict (A' i) (R i))
          (e.symm.trans (transport (β i) (restrict (A' i) (R i))).back) := by
    have hEq : (β i).symm ⁻¹' ((Subtype.val : A i → K) ⁻¹' G i) =
        (Subtype.val : A' i → Y i) ⁻¹' ((P i).proj ⁻¹' F i) := by
      ext z
      have hp := emptyAware_proj_comm (hβ i) ((β i).symm z)
      rw [(β i).apply_symm_apply] at hp
      have hp' := congrArg Subtype.val hp
      change (((restrict (U i) (P i)).proj z : U i) : X) =
        (((restrict (U i) T).proj ((β i).symm z) : U i) : X) at hp'
      rw [proj_restrict,proj_restrict] at hp'
      change T.proj ((β i).symm z).val ∈ F i ↔ (P i).proj z.val ∈ F i
      rw [← hp']
    apply extend_transported_closed_footprint_tower (A i) (G i) (hG i) (hGA i) (β i) (restrict (A' i) (R i))
    rw [hEq]
    exact centresOver_restrict (A' i) _ (R i) (hR i)
  choose L' Q' hQ' hPhysical using hExt
  obtain ⟨L,Q,hQ,hCompQ⟩ := finite_disjoint_towers_physical_comparisons G hG A hGA hSep L' Q' hQ' Finset.univ
  have hUnion : finiteSupport (X := K) G (Finset.univ : Finset ι) = T.proj ⁻¹' (⋃ i, F i) := by
    simp [finiteSupport,G,preimage_iUnion]
  rw [hUnion] at hQ
  refine ⟨K,T,L,Q,by simpa [finiteSupport] using hT,hQ,?_⟩
  intro i
  refine ⟨β i,hβ i,?_⟩
  obtain ⟨φ,hφ⟩ := hCompQ i (Finset.mem_univ i)
  obtain ⟨e,he⟩ := hPhysical i
  refine ⟨φ.trans (e.symm.trans (transport (β i) (restrict (A' i) (R i))).back),?_⟩
  simpa only [Diffeomorph.refl_trans] using trans hφ (emptyAware_of_isTowerIso he)

end
end Hironaka.HironakaG8DisjointPhaseMerge

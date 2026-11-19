import Hironaka.Resolution.HironakaActualIntrinsicIsoCommonGraphSquare
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicHS
import Hironaka.Resolution.HironakaActualReferenceHSSingularCentre
import Hironaka.Analytic.FibreDimensionLowerBound

/-! Transport of the ambient HS cut along the two actual graph projections. -/
set_option autoImplicit false

open Set TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CommonGraphHSCut

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualAnalyticSubspace HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaHolomorphicPointJets
  HironakaActualAnalyticSubspaceIntrinsicHS HironakaActualReferenceHSSingularCentre
  HironakaActualIntrinsicIsoCommonGraphSquare HironakaActualLocalCommonGraphModel
  HironakaReducedComplexAnalyticSpaces HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualIntrinsicIsoPairedWindows

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [ChartedSpace (ComplexModel m) N]
  [IsComplexManifold n M] [IsComplexManifold m N]

private theorem off_carrier_zero {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    {x : M} (hx : x ∉ W) (q : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n) W) x q = 0 := by
  let A := vanishingIdeal (n := n) W
  have hz : A.zeroLocus = W := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed
  have htop : wholeChartStalkIdeal A x x (mem_chart_source _ x) = ⊤ := by
    by_contra h
    exact hx (hz ▸ (wholeChartStalk_le_maximal_iff_support A
      (CartanIrreducible.cartanCoherence W hW) x).mp (IsLocalRing.le_maximalIdeal h))
  change hilbertSamuelValue (wholeChartStalkIdeal A x x (mem_chart_source _ x)) q = 0
  rw [htop, hilbertSamuelValue, top_sup_eq]
  exact Module.finrank_zero_of_subsingleton

/-- An actual intrinsic isomorphism from an original embedding to the common
graph carries its entire ambient positive HS cut and all ambient upper bounds. -/
theorem ambient_cut_and_bound_of_intrinsic_iso {W : Set M} {D : Set N}
    (hD : IsComplexAnalyticSubset (n := m) D)
    (e : actualSubspaceLocallyRingedSpace (n := n) W ≅
      actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) W)
    (H : ℕ → ℕ) (hH : 0 < H 0) :
    {y | ∀ q, hilbertSamuelAt (vanishingIdeal (n := m) D) y q = H q} =
      (fun x : W => (e.hom.base x).val) ''
        {x : W | ∀ q, hilbertSamuelAt (vanishingIdeal (n := n) W) x.val q = H q} ∧
    ((∀ x q, hilbertSamuelAt (vanishingIdeal (n := n) W) x q ≤ H q) →
      ∀ y q, hilbertSamuelAt (vanishingIdeal (n := m) D) y q ≤ H q) := by
  have hit (y : D) : ∃ x : W, e.hom.base x = y := by
    refine ⟨e.inv.base y, ?_⟩
    exact congrArg (fun a => a.base y) e.inv_hom_id
  constructor
  · ext y
    constructor
    · intro hy
      have hyD : y ∈ D := by
        by_contra hn
        exact (Nat.ne_of_gt hH) ((hy 0).symm.trans (off_carrier_zero hD hn 0))
      obtain ⟨x, hx⟩ := hit ⟨y, hyD⟩
      refine ⟨x, ?_, congrArg Subtype.val hx⟩
      intro q
      rw [hilbertSamuelAt_vanishing_intrinsic_iso e he x q, hx]
      exact hy q
    · rintro ⟨x, hx, rfl⟩ q
      exact (hilbertSamuelAt_vanishing_intrinsic_iso e he x q).symm.trans (hx q)
  · intro hUpper y q
    by_cases hy : y ∈ D
    · obtain ⟨x, hx⟩ := hit ⟨y, hy⟩
      have h := (hilbertSamuelAt_vanishing_intrinsic_iso e he x q).symm
      rw [hx] at h
      exact h.le.trans (hUpper x.val q)
    · rw [off_carrier_zero hD hy q]
      exact Nat.zero_le _

/-- The common graph is itself an analytic subset of its literal common
ambient, by pulling back the base carrier and imposing the graph equations. -/
theorem commonGraphSubset_analytic {a b : ℕ}
    (U : Opens (ComplexModel a)) (V : Opens (ComplexModel b))
    (F : ComplexModel a → ComplexModel b) (hF : ContDiffOn ℂ ∞ F U)
    {W : Set (ComplexModel a)}
    (hW : IsComplexAnalyticSubset (n := a) ((Subtype.val : U → ComplexModel a) ⁻¹' W)) :
    IsComplexAnalyticSubset (n := a+b) (commonGraphSubset U V F W) := by
  let P := commonDomain U V
  let p : P → U := fun z => ⟨tangentProjection a b z.val, z.property.1⟩
  have hp : ContMDiff 𝓘(ℂ,ComplexModel (a+b)) 𝓘(ℂ,ComplexModel a) ∞ p := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (tangentProjection a b).contMDiff.comp contMDiff_subtype_val
  have hFU : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ (fun u : U => F u.val) := by
    intro u
    exact contMDiffAt_subtype_iff.mpr
      ((hF.contDiffAt (U.isOpen.mem_nhds u.property)).contMDiffAt)
  have hz : ContMDiff 𝓘(ℂ,ComplexModel (a+b)) 𝓘(ℂ,ComplexModel b) ∞
      (fun z : P => actualJointNormalProjection a b z.val - F (p z).val) :=
    ((actualJointNormalProjection a b).contMDiff.comp contMDiff_subtype_val).sub (hFU.comp hp)
  have hbase := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hp hW
  have hnormal := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hz
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel b))
  convert hbase.inter hnormal using 1
  ext z
  exact and_congr_right (fun _ => sub_eq_zero.symm)

/-- Independent intrinsic originals yield one actual closed analytic graph
and carry their whole positive cuts and upper bounds onto that graph. -/
theorem exists_commonGraph_ambient_cuts
    {a b : ℕ} {U : Opens (ComplexModel a)} {V : Opens (ComplexModel b)}
    {C : Set U} {D : Set V}
    (e : actualSubspaceLocallyRingedSpace (n := a) C ≅
      actualSubspaceLocallyRingedSpace (n := b) D)
    (he : e.hom ≫ subspacePointMap (n := b) D = subspacePointMap (n := a) C)
    (hC : IsComplexAnalyticSubset (n := a) C) (hD : IsComplexAnalyticSubset (n := b) D)
    (c : C) (H : ℕ → ℕ) (hH : 0 < H 0) :
    ∃ (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b))
      (F : ComplexModel a → ComplexModel b),
      A ≤ U ∧ B ≤ V ∧ c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      let W := coordinateWindowSubset C A
      let T := coordinateWindowSubset D B
      let S := commonGraphSubset A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a)))
      IsComplexAnalyticSubset (n := a+b) S ∧
      ∃ (eW : actualSubspaceLocallyRingedSpace (n := a) W ≅
          actualSubspaceLocallyRingedSpace (n := a+b) S)
        (eT : actualSubspaceLocallyRingedSpace (n := b) T ≅
          actualSubspaceLocallyRingedSpace (n := a+b) S),
        {z | ∀ q, hilbertSamuelAt (vanishingIdeal (n := a+b) S) z q = H q} =
          (fun x : W => (eW.hom.base x).val) ''
            {x : W | ∀ q, hilbertSamuelAt (vanishingIdeal (n := a) W) x.val q = H q} ∧
        {z | ∀ q, hilbertSamuelAt (vanishingIdeal (n := a+b) S) z q = H q} =
          (fun y : T => (eT.hom.base y).val) ''
            {y : T | ∀ q, hilbertSamuelAt (vanishingIdeal (n := b) T) y.val q = H q} ∧
        ((∀ x q, hilbertSamuelAt (vanishingIdeal (n := a) W) x q ≤ H q) →
          ∀ z q, hilbertSamuelAt (vanishingIdeal (n := a+b) S) z q ≤ H q) ∧
        ((∀ y q, hilbertSamuelAt (vanishingIdeal (n := b) T) y q ≤ H q) →
          ∀ z q, hilbertSamuelAt (vanishingIdeal (n := a+b) S) z q ≤ H q) := by
  obtain ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,hW,_hT,hFT,hGW,hGF,hFG,_hFval,_hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  obtain ⟨eW,eT,heW,heT,_hw,_ht⟩ :=
    actualCommonGraphModelIsos_with_coordinates A B (coordinateCarrier C ∩ A)
      (coordinateCarrier D ∩ B) inter_subset_right inter_subset_right F G hF hG hFT hGW hGF hFG
  have hS := commonGraphSubset_analytic A B F hF hW
  obtain ⟨hCutW,hUpperW⟩ := ambient_cut_and_bound_of_intrinsic_iso hS eW heW H hH
  obtain ⟨hCutT,hUpperT⟩ := ambient_cut_and_bound_of_intrinsic_iso hS eT heT H hH
  exact ⟨A,B,F,hAU,hBV,hcA,hdB,hS,eW,eT,hCutW,hCutT,hUpperW,hUpperT⟩

#print axioms exists_commonGraph_ambient_cuts

end
end Hironaka.HironakaG1CommonGraphHSCut

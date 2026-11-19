import Hironaka.Analytic.Unibranch.HironakaG11PresReduction
import Hironaka.Analytic.Unibranch.HironakaG11StrictTransformTowers

/-! Whole native HS readouts on the SAME arbitrary original canonical prefix,
from ordinary INITIAL native records and their computed positive powers.
Blueprint FIRST: original-native-current-hs-readout.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11HSPhaseInduction HironakaG11PresWindows HironakaG11PresReduction
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualPowerBoundaryExponents ResolutionInvariantSeq
open ResolutionInvariantSpec (IsInvDomain)

variable {Base : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}
  (w : ι→DimEmbedding Base N) (raw : ∀ i,MarkedIdeal N (Amb w i)) (e : ι→ℕ)

/-- COMPUTED whole positive powers, keeping their TRUE marks and boundary. -/
def chosenRecord (i : ι) : MarkedIdeal N (Amb w i) := powerMarked (raw i) (e i)

variable {H : ℕ→ℕ} (hRaw : ∀ i,IsNativeWindowRecord (w i) (raw i) H)
  (he : ∀ i,1≤e i)
include hRaw he

theorem chosen_isHSWindowRecord (i : ι) :
    IsHSWindowRecord (w i) (chosenRecord w raw e i) H :=
  (hRaw i).isHSWindowRecord.powerMarked (he i)

variable {Λ : Type*} [LinearOrder Λ] (R : ResolutionInvariant.{0} N N Λ)

theorem chosen_presentation (i : ι) :
    HSPresentation R (w i) (chosenRecord w raw e i) H :=
  (chosen_isHSWindowRecord w raw e hRaw he i).hsPresentation R

variable {m : ℕ} (s : GStage R (chosenRecord w raw e) (mapAdm w) m)
  (xs : XStage w s.T)

/-- Derived from the SAME initial presentation and SAME current original history. -/
theorem current_native_data (i : ι) (c : xs.carrier i) :
    originalStalkHS xs.Y ((xs.map i).hom.left.base c)≤H ∧
    (c.val∈rcos (chosenRecord w raw e) s.T i ↔
      originalStalkHS xs.Y ((xs.map i).hom.left.base c)=H) ∧
    (c.val∈rcos (chosenRecord w raw e) s.T i →
      (xs.map i).hom.left.base c∈intrinsicSingularLocus xs.Y.obj) := by
  have hLocal:=(chosen_presentation w raw e hRaw he R i (s.T i).2 (s.canonical i)).2
  rw [← xs.carrier_eq i] at hLocal
  have hData:=hLocal (xs.analytic i) c
  have hHS:=originalStalkHS_openImmersion (xs.map i) (xs.isOpenImmersion i) c
  refine ⟨fun l=>(congrFun hHS l).trans_le (hData.1 l),?_,?_⟩
  · exact ⟨fun hc=>hHS.trans (hData.2.1.mp hc),
      fun h=>(hData.2.1).mpr (hHS.symm.trans h)⟩
  · intro hc
    exact (Set.ext_iff.mp
      (HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
        (xs.map i) (xs.isOpenImmersion i)) c).mpr (hData.2.2 hc)

theorem current_centre_profile (K : ∀ i,Set (w i).ambient) (i : ι) (c : xs.carrier i)
    (hc : c.val∈gcentre R (chosenRecord w raw e) K s.T i) :
    originalStalkHS xs.Y ((xs.map i).hom.left.base c)=H :=
  (current_native_data w raw e hRaw he R s xs i c).2.1.mp hc.1

/-- SAME accepted current family; its local profiles are DERIVED, not an input packet. -/
theorem current_global_centre_profile (K : ∀ i,Set (w i).ambient)
    (hCover : ∀ i (c : (w i).carrier), c.val∈(chosenRecord w raw e i).cosupp →
      ∃ j,∃ c' : (w j).carrier,c'.val∈K j ∧
        (w j).toLocalEmbedding.toPoint c'=(w i).toLocalEmbedding.toPoint c)
    (hTr : RecordsTransport R (chosenRecord w raw e) (mapAdm w)) :
    let hD := fun i=>(chosen_isHSWindowRecord w raw e hRaw he i).1
    let hcos := HSPresentation.cosupp_subset (fun i=>chosen_presentation w raw e hRaw he R i)
    let hsub := (HSPresentation.cosuppInStrictSing
      (fun i=>chosen_presentation w raw e hRaw he R i)).gcentre_subset (K := K) s xs
    ∀ y, y∈(xs.centres hD hcos hCover hTr s hsub).support → originalStalkHS xs.Y y=H := by
  intro hD hcos hsub y hy
  obtain ⟨i,c,hc,hcy⟩:=(xs.centres hD hcos hCover hTr s hsub).mem_support.mp hy
  exact hcy ▸ current_centre_profile w raw e hRaw he R s xs K i c hc

end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout

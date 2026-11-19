import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Coherence.VanishingIdealCoherent

/-! The existing general source-biholomorphism blowup theorem is physically
located in a thin module. Its original qualified name and proof are retained.
Blueprint: `hir:sharp-actual-blowup-source-biholomorphism`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveSuccessorLocalBlowup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
variable {n : ℕ} {X : CMfd.{u} n}

/-- The full original universal property survives a genuine source biholomorphism. -/
theorem isBlowupAlong_comp_diffeomorph {Y Y' : CMfd.{u} n}
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsBlowupAlong n C (π ∘ e) := by
  refine ⟨hπ.1,hπ.2.1,hπ.contMDiff.comp e.contMDiff,?_,?_⟩
  · rw [GermIdealTotalTransform.pullback_comp hπ.contMDiff e.contMDiff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1)]
    apply GermIdealTotalTransform.isInvertible_pullback e.contMDiff _ hπ.2.2.2.1
    have he : exceptionalLocus n e=∅ :=
      eq_empty_iff_forall_notMem.mpr (MarkedIdealTowerTransport.notMem_exceptionalLocus e)
    rw [he,interior_empty]
  · intro m Z _ _ _ g hg hginv
    obtain ⟨h,⟨hh,hπh⟩,huniq⟩ := hπ.2.2.2.2 m Z g hg hginv
    refine ⟨e.symm ∘ h,⟨e.symm.contMDiff.comp hh,?_⟩,?_⟩
    · funext z
      change π (e (e.symm (h z)))=g z
      exact (congrArg π (e.apply_symm_apply (h z))).trans (congrFun hπh z)
    · rintro h' ⟨hh',hComp⟩
      have heq : e ∘ h'=h := huniq (e ∘ h') ⟨e.contMDiff.comp hh',hComp⟩
      funext z
      exact e.injective ((congrFun heq z).trans (e.apply_symm_apply (h z)).symm)

end
end Hironaka.HironakaSharpActualCurveSuccessorLocalBlowup

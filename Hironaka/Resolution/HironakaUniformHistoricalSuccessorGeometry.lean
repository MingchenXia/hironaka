import Hironaka.Resolution.HironakaUniformHistoricalSuccessorQuotients
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! The SAME actual normal chart, its entire differential strict set and
intrinsic all-order HS function are recentered at EVERY exceptional point.
No strict-set, origin-ideal or target profile dictionary is supplied. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaUniformHistoricalSuccessorGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaUniformHistoricalSuccessorQuotients HironakaActualAnalyticBlowupTaylor
  HironakaBaseChange HironakaActualVanishingIntrinsicHSTransport
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance

variable {n : ℕ}

/-- The literal global translation, with its genuine holomorphic inverse. -/
def modelTranslation (p : ComplexModel n) :
    ComplexModel n ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ ComplexModel n where
  toFun w:=w+p
  invFun w:=w-p
  left_inv w:=add_sub_cancel_right w p
  right_inv w:=sub_add_cancel w p
  contMDiff_toFun:=by
    have h : ContDiff ℂ ∞ (fun w : ComplexModel n=>w+p):=contDiff_id.add contDiff_const
    exact h.contMDiff
  contMDiff_invFun:=by
    have h : ContDiff ℂ ∞ (fun w : ComplexModel n=>w-p):=contDiff_id.sub contDiff_const
    exact h.contMDiff

private def modelTranslationUniv (p : ComplexModel n) :
    ComplexModel n ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      (⊤ : Opens (ComplexModel n)) where
  toFun w:=⟨w+p,mem_univ _⟩
  invFun w:=w.val-p
  left_inv w:=add_sub_cancel_right w p
  right_inv w:=Subtype.ext (sub_add_cancel w.val p)
  contMDiff_toFun:=by
    apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens (ComplexModel n)) _).mp
    exact (modelTranslation p).contMDiff
  contMDiff_invFun:=(modelTranslation p).symm.contMDiff.comp contMDiff_subtype_val

private theorem modelTranslation_open_embedding (p : ComplexModel n) :
    IsOpenHoloEmbedding n (fun w : ComplexModel n=>w+p):=
  ⟨⊤,modelTranslationUniv p,fun _=>rfl⟩

private theorem actualBlowupMap_contMDiff (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n=>z i):=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i):=by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul (contDiff_const.add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

/-- The WHOLE differential strict set in the SAME normal chart at EVERY
exceptional point, retaining the original normal set, pivot and full W. -/
theorem actual_chart_strict_translate
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (z : ComplexModel n) (hz : z e=0) :
    strictTransform n (actualAnalyticBlowupMap A e (fun i=>b i+z i))
      ((fun w : ComplexModel n=>w+actualAnalyticBlowupMap A e b z) ⁻¹' W)=
      (fun w : ComplexModel n=>w+z) ⁻¹' strictTransform n (actualAnalyticBlowupMap A e b) W := by
  exact strictTransform_preimage_eq (actualBlowupMap_contMDiff A e b)
    (actualBlowupMap_contMDiff A e (fun i=>b i+z i))
    (modelTranslation_open_embedding (actualAnalyticBlowupMap A e b z))
    (modelTranslation_open_embedding z)
    (actualBlowupMap_translate_at_zero_pivot A e b z hz) W

/-- The intrinsic WHOLE HS function under the literal coordinate translation,
for ANY set, without an ideal-map or finite-profile certificate. -/
theorem hilbertSamuelAt_vanishing_translate
    (W : Set (ComplexModel n)) (p : ComplexModel n) (ell : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n:=n) ((fun w : ComplexModel n=>w+p) ⁻¹' W)) 0 ell=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) p ell := by
  have h:=hilbertSamuelAt_vanishing_actual_biholomorphic_any (modelTranslation p) W 0 ell
  change hilbertSamuelAt (vanishingIdeal (n:=n) ((fun w : ComplexModel n=>w+p) ⁻¹' W)) 0 ell=
    hilbertSamuelAt (vanishingIdeal (n:=n) W) (0+p) ell at h
  simpa only [zero_add] using h

/-- Actual chart-point geometric persistence is exactly the whole profile
condition in the recentered SAME normal chart, at EVERY exceptional point. -/
theorem actual_chart_geometric_persistence_translate_iff
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (z : ComplexModel n) (hz : z e=0) :
    (∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e (fun i=>b i+z i))
      ((fun w : ComplexModel n=>w+actualAnalyticBlowupMap A e b z) ⁻¹' W))) 0 ell=
        hilbertSamuelAt (vanishingIdeal (n:=n)
          ((fun w : ComplexModel n=>w+actualAnalyticBlowupMap A e b z) ⁻¹' W)) 0 ell) ↔
    ∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W)) z ell=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (actualAnalyticBlowupMap A e b z) ell := by
  rw [actual_chart_strict_translate A e b W z hz]
  simp only [hilbertSamuelAt_vanishing_translate]

end
end Hironaka.HironakaUniformHistoricalSuccessorGeometry

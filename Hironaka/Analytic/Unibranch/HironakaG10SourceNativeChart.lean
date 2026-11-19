import Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
import Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

/-! # Native centered chart for the actual source entry germ -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart
open Hironaka Hironaka
  HolGerm OkaRelationSheaf OkaGermBridge HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaG10ArtinianParameterPullback
  HironakaG10HirChartFlattener HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10SourceTensorGerm
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

noncomputable def normalFirstSwap (t d : ℕ) : ComplexModel (t+d) ≃L[ℂ] ComplexModel (d+t) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (finAddFlip : Fin (t+d) ≃ Fin (d+t))).toContinuousLinearEquiv

theorem normalFirstSwap_first (t d : ℕ) (w : ComplexModel (t+d)) (i : Fin d) :
    normalFirstSwap t d w (i.castAdd t) = w (i.natAdd t) := by
  change w ((finAddFlip : Fin (t+d) ≃ Fin (d+t)).symm (i.castAdd t)) = _
  rw [(finAddFlip : Fin (t+d) ≃ Fin (d+t)).symm_apply_eq.mpr
    (finAddFlip_apply_natAdd i t).symm]

theorem normalFirstSwap_second (t d : ℕ) (w : ComplexModel (t+d)) (i : Fin t) :
    normalFirstSwap t d w (i.natAdd d) = w (i.castAdd d) := by
  change w ((finAddFlip : Fin (t+d) ≃ Fin (d+t)).symm (i.natAdd d)) = _
  rw [(finAddFlip : Fin (t+d) ≃ Fin (d+t)).symm_apply_eq.mpr
    (finAddFlip_apply_castAdd i d).symm]

/-- The actual coordinate swap turns fibre-first projections into the native
parameter-first product coordinates. -/
theorem splitModel_normalFirstSwap (t d : ℕ) (w : ComplexModel (t+d)) :
    splitModel d t (normalFirstSwap t d w) =
      (actualJointNormalProjection t d w, tangentProjection t d w) := by
  apply Prod.ext
  · ext i
    change normalFirstSwap t d w (i.castAdd t) = w (i.natAdd t)
    exact normalFirstSwap_first t d w i
  · ext i
    change normalFirstSwap t d w (i.natAdd d) = w (i.castAdd d)
    exact normalFirstSwap_second t d w i

/-- The original source germ in the fibre-first construction is exactly the
native base-first centered chart germ, with the actual block interchange. -/
theorem swapParameterFibre_native_centered (t d : ℕ) (x : ComplexModel t)
    (F : ComplexModel d × ComplexModel t → ℂ) (hF : HolAt F (0,x))
    (hG : HolAt (sourceJointFibreFirst t d x F) 0) :
    swapParameterFibre d t (germAt 0 (F ∘ centredChart d t (0,x))) =
      HolGerm.mk (sourceJointFibreFirst t d x F) hG := by
  have hcenter : HolAt (F ∘ centredChart d t (0,x)) 0 := by
    have h : HolAt F (centredChart d t (0,x) 0) := by rw [centredChart_zero]; exact hF
    exact h.comp (centredChart d t (0,x)).continuous (differentiable_centredChart d t (0,x))
  rw [germAt_of_holAt hcenter]
  change HolGerm.comapEquiv (normalFirstSwap t d) (HolGerm.mk _ _) = _
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  apply Eventually.of_forall
  intro w
  simp [sourceJointFibreFirst, centredChart, splitModel_normalFirstSwap]

/-- Native whole-stalk flatness is exactly flatness of the quotient by the
same recentered original entry germs used by source tensor substitution. -/
theorem source_native_stalk_flat_quotient {n : ℕ} (t d : ℕ) (x : ComplexModel t)
    (F : Fin 1 → Fin n → ComplexModel d × ComplexModel t → ℂ)
    (hF : ∀ i j, HolAt (F i j) (0,x))
    (hG : ∀ j, HolAt (sourceJointFibreFirst t d x (F 0 j)) 0)
    (hflat : StalkFlatAt d t F (0,x)) :
    letI := tangentAlgebra d t
    Module.Flat (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.span (Set.range fun j =>
        (swapParameterFibre d t).symm
          (HolGerm.mk (sourceJointFibreFirst t d x (F 0 j)) (hG j)))) := by
  let : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    tangentAlgebra d t
  have hentry : (fun j => (swapParameterFibre d t).symm
      (HolGerm.mk (sourceJointFibreFirst t d x (F 0 j)) (hG j))) =
      (fun j => germAt 0 (centredMatrix d t F (0,x) 0 j)) := by
    funext j
    apply (swapParameterFibre d t).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (swapParameterFibre_native_centered t d x (F 0 j) (hF 0 j) (hG j)).symm
  rw [hentry]
  have hchart := (native_flat_iff_stalkFlatAt d t F (0,x) hF).mpr hflat
  apply RingHom.flat_algebraMap_iff.mp
  change (chartMap d t (entryIdeal d t (centredMatrix d t F (0,x)))).Flat
  exact hchart

end Hironaka.Analytic.Unibranch.HironakaG10SourceNativeChart

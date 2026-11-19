import Hironaka.Analytic.Unibranch.HironakaG10SquareZeroCurveFlat

/-! Reassociation of finite smooth models preserves every coordinate. -/
set_option autoImplicit false
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualAnalyticBaseChangeCoefficients HironakaG10LinearCurveMatrixPullback
namespace Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity
noncomputable section

def assocModel (d t a : ℕ) : ComplexModel ((d+t)+a) ≃L[ℂ] ComplexModel (d+(t+a)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (Nat.add_assoc d t a))).toContinuousLinearEquiv

theorem assocModel_apply (d t a : ℕ) (w : ComplexModel ((d+t)+a)) (i : Fin (d+(t+a))) :
    assocModel d t a w i = w (Fin.cast (Nat.add_assoc d t a).symm i) := by
  rfl

/-- Reassociation commutes with the actual nested linear-curve map. -/
theorem assocModel_linearCurve (d t a : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (w : ComplexModel ((1+t)+a)) :
    assocModel d t a (jointBaseMap (d+t) (1+t) a (linearJointMap d t L) w) =
      jointBaseMap d 1 (t+a) L (assocModel 1 t a w) := by
  have hproj : tangentProjection 1 t (tangentProjection (1+t) a w) =
      tangentProjection 1 (t+a) (assocModel 1 t a w) := by
    ext i
    simp only [tangentProjection_apply,assocModel_apply]
    have hi : (i.castAdd t).castAdd a =
        Fin.cast (Nat.add_assoc 1 t a).symm (i.castAdd (t+a)) := by apply Fin.ext; simp
    rw [hi]
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    have hc : Fin.cast (Nat.add_assoc d t a).symm (i.castAdd (t+a)) =
        (i.castAdd t).castAdd a := by apply Fin.ext; simp
    rw [assocModel_apply,hc]
    simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_tangent,
      actualJointNormalInclusion_tangent,add_zero,linearJointMap_apply]
    rw [hproj]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro j
      have hc : Fin.cast (Nat.add_assoc d t a).symm ((j.castAdd a).natAdd d) =
          (j.natAdd d).castAdd a := by apply Fin.ext; simp
      have hc' : Fin.cast (Nat.add_assoc 1 t a).symm ((j.castAdd a).natAdd 1) =
          (j.natAdd 1).castAdd a := by apply Fin.ext; simp
      rw [assocModel_apply,hc]
      simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_tangent,
        actualJointNormalInclusion_tangent,add_zero,linearJointMap_apply,
        tangentInclusion_normal,actualJointNormalInclusion_normal,zero_add,
        actualJointNormalProjection_apply,tangentProjection_apply,assocModel_apply,hc']
    · intro j
      have hc : Fin.cast (Nat.add_assoc d t a).symm ((j.natAdd t).natAdd d) =
          j.natAdd (d+t) := by apply Fin.ext; simp; omega
      have hc' : Fin.cast (Nat.add_assoc 1 t a).symm ((j.natAdd t).natAdd 1) =
          j.natAdd (1+t) := by apply Fin.ext; simp; omega
      rw [assocModel_apply,hc]
      simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_normal,
        actualJointNormalInclusion_normal,zero_add,actualJointNormalProjection_apply,
        assocModel_apply,hc']
end
end Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity

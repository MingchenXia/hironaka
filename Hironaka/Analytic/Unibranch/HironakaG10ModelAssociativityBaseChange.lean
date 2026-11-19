import Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm

/-! Reassociation of arbitrary holomorphic base changes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualAnalyticBaseChangeCoefficients HironakaHolomorphicJetChartInvariance
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
namespace Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityBaseChange
noncomputable section

/-- Reassociation commutes with the actual nested analytic base-change map. -/
theorem assocModel_baseChange (d e t a : ℕ) (φ : ComplexModel e → ComplexModel d)
    (w : ComplexModel ((e+t)+a)) :
    assocModel d t a (jointBaseMap (d+t) (e+t) a (jointBaseMap d e t φ) w) =
      jointBaseMap d e (t+a) φ (assocModel e t a w) := by
  have hproj : tangentProjection e t (tangentProjection (e+t) a w) =
      tangentProjection e (t+a) (assocModel e t a w) := by
    ext i
    simp only [tangentProjection_apply,assocModel_apply]
    have hi : (i.castAdd t).castAdd a =
        Fin.cast (Nat.add_assoc e t a).symm (i.castAdd (t+a)) := by apply Fin.ext; simp
    rw [hi]
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    have hc : Fin.cast (Nat.add_assoc d t a).symm (i.castAdd (t+a)) =
        (i.castAdd t).castAdd a := by apply Fin.ext; simp
    rw [assocModel_apply,hc]
    simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_tangent,
      actualJointNormalInclusion_tangent,add_zero,jointBaseMap]
    rw [hproj]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro j
      have hc : Fin.cast (Nat.add_assoc d t a).symm ((j.castAdd a).natAdd d) =
          (j.natAdd d).castAdd a := by apply Fin.ext; simp
      have hc' : Fin.cast (Nat.add_assoc e t a).symm ((j.castAdd a).natAdd e) =
          (j.natAdd e).castAdd a := by apply Fin.ext; simp
      rw [assocModel_apply,hc]
      simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_tangent,
        actualJointNormalInclusion_tangent,add_zero,jointBaseMap,
        tangentInclusion_normal,actualJointNormalInclusion_normal,zero_add,
        actualJointNormalProjection_apply,tangentProjection_apply,assocModel_apply,hc']
    · intro j
      have hc : Fin.cast (Nat.add_assoc d t a).symm ((j.natAdd t).natAdd d) =
          j.natAdd (d+t) := by apply Fin.ext; simp; omega
      have hc' : Fin.cast (Nat.add_assoc e t a).symm ((j.natAdd t).natAdd e) =
          j.natAdd (e+t) := by apply Fin.ext; simp; omega
      rw [assocModel_apply,hc]
      simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_normal,
        actualJointNormalInclusion_normal,zero_add,actualJointNormalProjection_apply,
        assocModel_apply,hc']

/-- The nested base map is holomorphic near the origin. -/
theorem jointBaseMap_holomorphic (d e t : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel (e+t)), DifferentiableAt ℂ (jointBaseMap d e t φ) w := by
  have hp : Tendsto (tangentProjection e t) (𝓝 (0 : ComplexModel (e+t)))
      (𝓝 (0 : ComplexModel e)) := by
    simpa only [map_zero] using (tangentProjection e t).continuous.tendsto 0
  filter_upwards [hp.eventually hφ] with w hw
  exact ((tangentInclusion d t).differentiableAt.comp w
    (hw.comp w (tangentProjection e t).differentiableAt)).add
      ((actualJointNormalInclusion d t).differentiableAt.comp w
        (actualJointNormalProjection e t).differentiableAt)

theorem jointBaseMap_origin (d e t : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ0 : φ 0 = 0) : jointBaseMap d e t φ 0 = 0 := by
  simp only [jointBaseMap, map_zero, hφ0, zero_add]

/-- Reassociation preserves pullback of each whole holomorphic germ for any
holomorphic origin-preserving base map and any two base dimensions. -/
theorem assocGermEquiv_baseChange (d e t a : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (g : HolGerm (ComplexModel ((d+t)+a))) :
    jointBasePullback d e (t+a) φ hφ hφ0 (assocGermEquiv d t a g) =
      assocGermEquiv e t a (jointBasePullback (d+t) (e+t) a (jointBaseMap d e t φ)
        (jointBaseMap_holomorphic d e t φ hφ) (jointBaseMap_origin d e t φ hφ0) g) := by
  have hpoint (w : ComplexModel (e+(t+a))) :
      (assocModel d t a).symm (jointBaseMap d e (t+a) φ w) =
        jointBaseMap (d+t) (e+t) a (jointBaseMap d e t φ) ((assocModel e t a).symm w) := by
    apply (assocModel d t a).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    simpa using (assocModel_baseChange d e t a φ ((assocModel e t a).symm w)).symm
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold assocGermEquiv jointBasePullback
    rw [HolGerm.comapEquiv_mk,compAlgHom_mk,compAlgHom_mk,HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (hpoint w)

end
end Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityBaseChange

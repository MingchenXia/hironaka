/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.SharpGeometryExact
import Hironaka.Resolution.HironakaActualPlaneContactBlowup
import Hironaka.Analytic.SubmanifoldIdealRestriction
import Hironaka.Analytic.SubmanifoldCodRestrict

/-!
# The actual strict contact-plane map is the genuine lower-dimensional blowup

Actual intrinsic stratum charts and whole exceptional ideal restriction give
its original centre invertibility. Two genuine universal comparisons then
construct inverse holomorphic maps, proving the whole restriction property.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPlaneContactBlowupRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualHolomorphicGraphIdeal
  HironakaActualGraphFunctionalIdeal HironakaActualGraphContactCoefficient HironakaActualPlaneContactBlowup
  HironakaSmoothSubmersionOrderedChoiceImageTrace BlowupStrictSubmanifold
  SubmanifoldChartedSpace
variable {d : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+1)) Y]
  [IsComplexManifold (d+1) Y] {D : Set (ComplexModel d)} {π : Y → ComplexModel (d+1)}

private theorem contactPlane_closed (d : ℕ) : IsClosed (contactPlane d) := by
  change IsClosed {z : ComplexModel (d+1) | tangentProjection d 1 z∈univ ∧ actualJointNormalProjection d 1 z=0}
  simpa only [mem_univ,true_and] using isClosed_eq (actualJointNormalProjection d 1).continuous continuous_const

private theorem contactPlane_eq_zeroSet (d : ℕ) :
    contactPlane d={z : ComplexModel (d+1) | graphFunction (fun _ : ComplexModel d => (0 : ComplexModel 1)) 0 z=0} := by
  ext z
  change (tangentProjection d 1 z∈univ ∧ actualJointNormalProjection d 1 z=0) ↔ z (Fin.natAdd d 0)-0=0
  simp only [mem_univ,true_and,sub_zero]
  constructor
  · intro h
    exact congrArg (fun v : ComplexModel 1 => v 0) h
  · intro h
    ext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact h

private theorem contactPlane_regular (d : ℕ) (z : ComplexModel (d+1)) (hz : z∈contactPlane d) :
    RegularAtDim (n := d+1) (contactPlane d) z d := by
  have hzero : graphFunction (fun _ : ComplexModel d => (0 : ComplexModel 1)) 0 z=0 :=
    (congrArg (fun A : Set (ComplexModel (d+1)) => z∈A) (contactPlane_eq_zeroSet d)).mp hz
  have hr := graphNormalContact_regularAtDim (fun _ : ComplexModel d => (0 : ComplexModel 1))
    ⊤ contDiff_const.contDiffOn 0 (z := z) (by simp) hzero
  rw [contactPlane_eq_zeroSet]
  simpa only [Opens.coe_top,preimage_univ,inter_univ,Nat.add_sub_cancel] using hr

private theorem strictPlane_regular (hπ : IsBlowupAlong (d+1) (planeCentre D) π)
    (z : Y) (hz : z∈geoStrictTransform π (planeCentre D) (contactPlane d)) :
    RegularAtDim (n := d+1) (geoStrictTransform π (planeCentre D) (contactPlane d)) z d :=
  regularAtDim_geoStrictTransform hπ (contactPlane_closed d) (contactPlane_regular d)
    (fun _ hx => ⟨mem_univ _,hx.2⟩) hz

/-- The SAME actual strict contact subtype has its GENUINELY constructed intrinsic flattening atlas. -/
@[instance_reducible] def strictPlaneChartedSpace (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    ChartedSpace (ComplexModel d) (geoStrictTransform π (planeCentre D) (contactPlane d)) :=
  chartedSpace (Nat.le_succ d) (strictPlane_regular hπ)

theorem strictPlane_isComplexManifold (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    letI := strictPlaneChartedSpace hπ
    IsComplexManifold d (geoStrictTransform π (planeCentre D) (contactPlane d)) :=
  isComplexManifold_chartedSpace (Nat.le_succ d) (strictPlane_regular hπ)

/-- The literal intrinsic strict-plane projection, before any comparison isomorphism. -/
def restrictedPlaneProjection (π : Y → ComplexModel (d+1)) (D : Set (ComplexModel d)) :
    geoStrictTransform π (planeCentre D) (contactPlane d) → ComplexModel d :=
  fun s => tangentProjection d 1 (π s.val)

/-- The actual restricted projection is genuinely holomorphic for its internally constructed stratum atlas. -/
theorem restrictedPlaneProjection_contMDiff (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    letI := strictPlaneChartedSpace hπ
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ (restrictedPlaneProjection π D) := by
  let := strictPlaneChartedSpace hπ
  exact (tangentProjection d 1).contMDiff.comp
    (hπ.contMDiff.comp (contMDiff_val (Nat.le_succ d) (strictPlane_regular hπ)))

private theorem planeSection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞ (planeSection d) := by
  change ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+1)) ∞
    (fun x => tangentInclusion d 1 x+actualJointNormalInclusion d 1 0)
  exact (tangentInclusion d 1).contMDiff.add contMDiff_const

private theorem planeSection_projection {z : ComplexModel (d+1)} (hz : z∈contactPlane d) :
    planeSection d (tangentProjection d 1 z)=z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [planeSection,graphSection]
  · have he := congrArg (fun v : ComplexModel 1 => v j) hz.2
    simpa [planeSection,graphSection] using he.symm

omit [IsComplexManifold (d+1) Y] in
private theorem restrictedPlaneProjection_factor (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    π∘(Subtype.val : geoStrictTransform π (planeCentre D) (contactPlane d) → Y)=
      planeSection d∘restrictedPlaneProjection π D := by
  funext s
  exact (planeSection_projection (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
    (contactPlane_closed d) s.property)).symm

private theorem planeCentre_pullback (D : Set (ComplexModel d)) :
    GermIdeal.pullback (m := d) (planeSection d) (vanishingIdeal (n := d+1) (planeCentre D))=
      vanishingIdeal (n := d) D := by
  apply GermIdeal.ext
  funext x F
  exact propext (graphSection_pullback_mem_iff (fun _ => 0) x
    (Eventually.of_forall fun _ => differentiableAt_const _) D F)

/-- The actual restricted strict-plane map has GENUINELY invertible whole original centre pullback. -/
theorem restrictedPlaneProjection_invertible (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    letI := strictPlaneChartedSpace hπ
    letI := strictPlane_isComplexManifold hπ
    (GermIdeal.pullback (m := d) (restrictedPlaneProjection π D) (vanishingIdeal (n := d) D)).IsInvertible := by
  let := strictPlaneChartedSpace hπ
  have := strictPlane_isComplexManifold hπ
  let S := geoStrictTransform π (planeCentre D) (contactPlane d)
  have hval := contMDiff_val (Nat.le_succ d) (strictPlane_regular hπ)
  have halong : RestrictedIdealQuotient.IsInvertibleAlong (d+1) S
      (GermIdeal.pullback (m := d+1) π (vanishingIdeal (n := d+1) (planeCentre D))) := by
    have h := MarkedIdeals.MarkedIdeal.isInvertibleAlong_geoStrictTransform hπ (contactPlane d) 1
    change RestrictedIdealQuotient.IsInvertibleAlong (d+1) S
      (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1) at h
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at h
    exact h
  have hres := SubmanifoldIdealRestriction.isInvertible_restrictIdeal hval halong
  change (GermIdeal.pullback (m := d) (Subtype.val : S → Y)
    (GermIdeal.pullback (m := d+1) π (vanishingIdeal (n := d+1) (planeCentre D)))).IsInvertible at hres
  rw [← whole_pullback_comp hπ.contMDiff hval (vanishingIdeal (n := d+1) (planeCentre D))
    (fun _ _ h => h.1)] at hres
  rw [restrictedPlaneProjection_factor hπ,
    whole_pullback_comp planeSection_contMDiff (restrictedPlaneProjection_contMDiff hπ)
      (vanishingIdeal (n := d+1) (planeCentre D)) (fun _ _ h => h.1),planeCentre_pullback] at hres
  exact hres

/-- Two GENUINE universal comparisons internally construct an actual biholomorphism onto the strict contact subtype. -/
theorem exists_strictPlane_diffeomorph {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] {ρ : Z → ComplexModel d}
    (hπ : IsBlowupAlong (d+1) (planeCentre D) π) (hρ : IsBlowupAlong d D ρ) :
    letI := strictPlaneChartedSpace hπ
    letI := strictPlane_isComplexManifold hπ
    ∃ E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
        geoStrictTransform π (planeCentre D) (contactPlane d),
      restrictedPlaneProjection π D∘E=ρ := by
  let := strictPlaneChartedSpace hπ
  have := strictPlane_isComplexManifold hπ
  let S := geoStrictTransform π (planeCentre D) (contactPlane d)
  let σ := restrictedPlaneProjection π D
  have hσ := restrictedPlaneProjection_contMDiff hπ
  have hinv := restrictedPlaneProjection_invertible hπ
  obtain ⟨κ,⟨hκ,hcomm⟩,_hunique⟩ := exists_unique_plane_blowup_lift hπ hρ
  obtain ⟨_hp,hrange⟩ := plane_blowup_lift_proper_and_range hπ hρ κ hκ hcomm
  have hκS : ∀ z,κ z∈S := by
    intro z
    change κ z∈geoStrictTransform π (planeCentre D) (contactPlane d)
    rw [← hrange]
    exact ⟨z,rfl⟩
  let α : Z → S := fun z => ⟨κ z,hκS z⟩
  have hα : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ α :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_succ d) (strictPlane_regular hπ) hκ hκS
  have hσα : σ∘α=ρ := by
    funext z
    change tangentProjection d 1 (π (κ z))=ρ z
    have he : π (κ z)=planeSection d (ρ z) := congrFun hcomm z
    rw [he]
    exact projection_graphSection _ _
  obtain ⟨β,⟨hβ,hρβ⟩,_hβunique⟩ := hρ.2.2.2.2 d S σ hσ hinv
  have hβα : β∘α=id := by
    apply BlowupUniqueness.eq_id_of_comp_eq hρ (hβ.comp hα)
    calc
      ρ∘(β∘α)=(ρ∘β)∘α := rfl
      _=σ∘α := congrArg (fun a => a∘α) hρβ
      _=ρ := hσα
  have hval := contMDiff_val (Nat.le_succ d) (strictPlane_regular hπ)
  have hgInv : (GermIdeal.pullback (m := d) (π∘(Subtype.val : S → Y))
      (vanishingIdeal (n := d+1) (planeCentre D))).IsInvertible := by
    rw [restrictedPlaneProjection_factor hπ,
      whole_pullback_comp planeSection_contMDiff hσ (vanishingIdeal (n := d+1) (planeCentre D))
        (fun _ _ h => h.1),planeCentre_pullback]
    exact hinv
  obtain ⟨k₀,_hk₀,huniq⟩ := hπ.2.2.2.2 d S (π∘(Subtype.val : S → Y))
    (hπ.contMDiff.comp hval) hgInv
  have hκβ : κ∘β=(Subtype.val : S → Y) := by
    have hπκβ : π∘(κ∘β)=π∘(Subtype.val : S → Y) := by
      calc
        π∘(κ∘β)=(π∘κ)∘β := rfl
        _=(planeSection d∘ρ)∘β := congrArg (fun a => a∘β) hcomm
        _=planeSection d∘(ρ∘β) := rfl
        _=planeSection d∘σ := congrArg (fun a => planeSection d∘a) hρβ
        _=π∘(Subtype.val : S → Y) := (restrictedPlaneProjection_factor hπ).symm
    exact (huniq (κ∘β) ⟨hκ.comp hβ,hπκβ⟩).trans
      (huniq (Subtype.val : S → Y) ⟨hval,rfl⟩).symm
  have hαβ : α∘β=id := by
    funext s
    apply Subtype.ext
    exact congrFun hκβ s
  let E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S :=
    { toFun := α
      invFun := β
      left_inv := congrFun hβα
      right_inv := congrFun hαβ
      contMDiff_toFun := hα
      contMDiff_invFun := hβ }
  exact ⟨E,hσα⟩

/-- ORIGINAL centre data prove the entire actual lower-dimensional blowup universal property for the SAME strict contact map. -/
theorem restrictedPlaneProjection_isBlowupAlong (D : Set (ComplexModel d))
    (hD : IsClosedSubmanifold d D) (hDint : interior D=∅)
    (hπ : IsBlowupAlong (d+1) (planeCentre D) π) :
    letI := strictPlaneChartedSpace hπ
    letI := strictPlane_isComplexManifold hπ
    IsBlowupAlong d D (restrictedPlaneProjection π D) := by
  let := strictPlaneChartedSpace hπ
  have := strictPlane_isComplexManifold hπ
  let S := geoStrictTransform π (planeCentre D) (contactPlane d)
  let σ := restrictedPlaneProjection π D
  obtain ⟨Z,tZ,cZ,mZ,ρ,hρ⟩ := BlowupExistence.exists_isBlowupAlong D hD hDint
  obtain ⟨E,hE⟩ := exists_strictPlane_diffeomorph hπ hρ
  have hρinv : ρ∘E.symm=σ := by
    funext s
    have he := congrFun hE (E.symm s)
    simpa only [Function.comp_apply,E.apply_symm_apply] using he.symm
  refine ⟨hD,hDint,restrictedPlaneProjection_contMDiff hπ,restrictedPlaneProjection_invertible hπ,?_⟩
  intro m T _tT _cT _mT g hg hginv
  obtain ⟨h,⟨hh,hρh⟩,hunique⟩ := hρ.2.2.2.2 m T g hg hginv
  refine ⟨E∘h,⟨E.contMDiff.comp hh,?_⟩,?_⟩
  · calc
      σ∘(E∘h)=(σ∘E)∘h := rfl
      _=ρ∘h := congrArg (fun a => a∘h) hE
      _=g := hρh
  · intro h' hh'
    have hcomp : ρ∘(E.symm∘h')=g := by
      calc
        ρ∘(E.symm∘h')=(ρ∘E.symm)∘h' := rfl
        _=σ∘h' := congrArg (fun a => a∘h') hρinv
        _=g := hh'.2
    have he := hunique (E.symm∘h') ⟨E.symm.contMDiff.comp hh'.1,hcomp⟩
    funext t
    have hc := congrArg E (congrFun he t)
    simpa only [Function.comp_apply,E.apply_symm_apply] using hc

end
end Hironaka.HironakaActualPlaneContactBlowupRestriction

/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalParts

/-! # The actual middle tangent-displacement-zero quotient

The genuine linear inclusion E(c,x)=(c;0,x) induces a surjective whole
holomorphic germ map. An actual coordinate block permutation transports the
existing coordinate-plane Hadamard kernel theorem to the exact middle v
coordinates. The SAME original joint ideal and displacement ideal map to the
original ideal and normal ideal, including every finite power/truncation.
The quotient preserves the ORIGINAL tangent germ scalar action. No supplied
kernel, coordinate-quotient, flatness or normal-flatness certificate is used.
Blueprint: `hironaka-tangent-displacement-zero-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTangentDisplacementZeroQuotient
noncomputable section
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HolGerm HolomorphicTaylorTail
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualCentrePrincipalParts

private def coordinateMap {m n : ℕ} (r : Fin m → Fin n) :
    ComplexModel n →L[ℂ] ComplexModel m :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin m => EuclideanSpace.proj (r i))

private theorem coordinateMap_apply {m n : ℕ} (r : Fin m → Fin n)
    (z : ComplexModel n) (i : Fin m) : coordinateMap r z i=z (r i) := rfl

private def coordinatePullback {m n : ℕ} (r : Fin m → Fin n) :
    HolGerm (ComplexModel m) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (coordinateMap r)
    (Eventually.of_forall fun _ => (coordinateMap r).differentiableAt) (map_zero _)

private theorem coordinatePullback_coordinate {m n : ℕ} (r : Fin m → Fin n) (i : Fin m) :
    coordinatePullback r (coordinateGerm i)=coordinateGerm (r i) := by
  unfold coordinatePullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

private theorem coordinatePullback_inverse {m n : ℕ} (e : Fin m ≃ Fin n)
    (g : HolGerm (ComplexModel m)) :
    coordinatePullback e.symm (coordinatePullback e g)=g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold coordinatePullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    change F (coordinateMap e (coordinateMap e.symm z))=F z
    congr 1
    ext i
    simp only [coordinateMap_apply,Equiv.symm_apply_apply]

/-- The genuine block permutation of indices sends (c;v,x) to (c,x;v). -/
private def middleBlockEquiv (d t : ℕ) : Fin (d+(d+t)) ≃ Fin ((d+t)+d) :=
  (finSumFinEquiv.symm.trans
    ((Equiv.refl (Fin d)).sumCongr finSumFinEquiv.symm)).trans
    (((Equiv.refl (Fin d)).sumCongr (Equiv.sumComm (Fin d) (Fin t))).trans
      ((Equiv.sumAssoc (Fin d) (Fin t) (Fin d)).symm.trans
        ((finSumFinEquiv.sumCongr (Equiv.refl (Fin d))).trans finSumFinEquiv)))

private theorem middleBlockEquiv_c (d t : ℕ) (i : Fin d) :
    middleBlockEquiv d t (i.castAdd (d+t))=(i.castAdd t).castAdd d := by
  simp [middleBlockEquiv]

private theorem middleBlockEquiv_v (d t : ℕ) (i : Fin d) :
    middleBlockEquiv d t ((i.castAdd t).natAdd d)=i.natAdd (d+t) := by
  simp [middleBlockEquiv]

private theorem middleBlockEquiv_x (d t : ℕ) (i : Fin t) :
    middleBlockEquiv d t ((i.natAdd d).natAdd d)=(i.natAdd d).castAdd d := by
  simp [middleBlockEquiv]

/-- The actual continuous linear inclusion E(c,x)=(c;0,x), retaining the original base. -/
def actualTangentDisplacementZeroInclusion (d t : ℕ) :
    ComplexModel (d+t) →L[ℂ] ComplexModel (d+(d+t)) :=
  (coordinateMap (middleBlockEquiv d t)).comp (tangentInclusion (d+t) d)

theorem actualTangentDisplacementZeroInclusion_c (d t : ℕ)
    (z : ComplexModel (d+t)) (i : Fin d) :
    actualTangentDisplacementZeroInclusion d t z (i.castAdd (d+t))=z (i.castAdd t) := by
  simp only [actualTangentDisplacementZeroInclusion,ContinuousLinearMap.comp_apply,
    coordinateMap_apply,middleBlockEquiv_c,tangentInclusion_tangent]

theorem actualTangentDisplacementZeroInclusion_v (d t : ℕ)
    (z : ComplexModel (d+t)) (i : Fin d) :
    actualTangentDisplacementZeroInclusion d t z ((i.castAdd t).natAdd d)=0 := by
  simp only [actualTangentDisplacementZeroInclusion,ContinuousLinearMap.comp_apply,
    coordinateMap_apply,middleBlockEquiv_v,tangentInclusion_normal]

theorem actualTangentDisplacementZeroInclusion_x (d t : ℕ)
    (z : ComplexModel (d+t)) (i : Fin t) :
    actualTangentDisplacementZeroInclusion d t z ((i.natAdd d).natAdd d)=z (i.natAdd d) := by
  simp only [actualTangentDisplacementZeroInclusion,ContinuousLinearMap.comp_apply,
    coordinateMap_apply,middleBlockEquiv_x,tangentInclusion_tangent]

/-- Literal whole holomorphic germ pullback by E(c,x)=(c;0,x). -/
def actualTangentDisplacementZeroTrace (d t : ℕ) :
    HolGerm (ComplexModel (d+(d+t))) →ₐ[ℂ] HolGerm (ComplexModel (d+t)) :=
  compAlgHom (actualTangentDisplacementZeroInclusion d t)
    (Eventually.of_forall fun _ => (actualTangentDisplacementZeroInclusion d t).differentiableAt)
    (map_zero _)

/-- The span of the actual middle tangent-displacement coordinates, with no x coordinates. -/
def tangentDisplacementIdeal (d t : ℕ) : Ideal (HolGerm (ComplexModel (d+(d+t)))) :=
  Ideal.span (range fun i : Fin d => coordinateGerm ((i.castAdd t).natAdd d))

private theorem jointMap_zeroDisplacement (d t : ℕ) (z : ComplexModel (d+t)) :
    actualCentreJointMap d t (actualTangentDisplacementZeroInclusion d t z)=z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [actualCentreJointMap,add_apply,ContinuousLinearMap.comp_apply,PiLp.add_apply,
      actualJointNormalProjection_apply,actualTangentDisplacementZeroInclusion_v,
      tangentInclusion_tangent,tangentProjection_apply,actualTangentDisplacementZeroInclusion_c,
      zero_add]
  · simp only [actualCentreJointMap,add_apply,ContinuousLinearMap.comp_apply,PiLp.add_apply,
      actualJointNormalProjection_apply,actualTangentDisplacementZeroInclusion_x,
      tangentInclusion_normal,add_zero]

/-- Every entire original germ is recovered after actual joint translation and v=0. -/
theorem actualTangentDisplacementZeroTrace_jointPullback (d t : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualTangentDisplacementZeroTrace d t (actualCentreJointPullback d t g)=g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold actualTangentDisplacementZeroTrace actualCentreJointPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (jointMap_zeroDisplacement d t z)

/-- The original whole tangent germ scalar pullbacks commute with the actual v=0 map. -/
theorem actualTangentDisplacementZeroTrace_tangentPullback (d t : ℕ)
    (b : HolGerm (ComplexModel d)) :
    actualTangentDisplacementZeroTrace d t (tangentPullback d (d+t) b)=
      tangentPullback d t b := by
  induction b using HolGerm.induction_on with
  | h F hF =>
    unfold actualTangentDisplacementZeroTrace tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    change F (tangentProjection d (d+t) (actualTangentDisplacementZeroInclusion d t z))=
      F (tangentProjection d t z)
    apply congrArg F
    ext i
    exact actualTangentDisplacementZeroInclusion_c d t z i

theorem actualTangentDisplacementZeroTrace_surjective (d t : ℕ) :
    Function.Surjective (actualTangentDisplacementZeroTrace d t) :=
  fun g => ⟨actualCentreJointPullback d t g,actualTangentDisplacementZeroTrace_jointPullback d t g⟩

private theorem zeroTrace_eq_permuted_planeTrace (d t : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    actualTangentDisplacementZeroTrace d t g=
      planeTrace (d+t) d (coordinatePullback (middleBlockEquiv d t) g) := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold actualTangentDisplacementZeroTrace planeTrace coordinatePullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun _ => rfl

private theorem map_displacementIdeal (d t : ℕ) :
    Ideal.map (coordinatePullback (middleBlockEquiv d t)).toRingHom
      (tangentDisplacementIdeal d t)=normalIdeal (d+t) d := by
  unfold tangentDisplacementIdeal normalIdeal
  rw [Ideal.map_span,← Set.range_comp]
  apply congrArg (fun f : Fin d → HolGerm (ComplexModel ((d+t)+d)) => Ideal.span (range f))
  funext i
  exact (coordinatePullback_coordinate (middleBlockEquiv d t) _).trans
    (congrArg coordinateGerm (middleBlockEquiv_v d t i))

/-- The ENTIRE true v=0 kernel equals the span of the actual middle v coordinates. -/
theorem tangentDisplacementIdeal_eq_ker (d t : ℕ) :
    tangentDisplacementIdeal d t=RingHom.ker (actualTangentDisplacementZeroTrace d t).toRingHom := by
  let r := coordinatePullback (middleBlockEquiv d t)
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      have he := congrArg (coordinatePullback (middleBlockEquiv d t).symm) hab
      simpa only [r,coordinatePullback_inverse] using he
    · intro b
      refine ⟨coordinatePullback (middleBlockEquiv d t).symm b,?_⟩
      exact coordinatePullback_inverse (middleBlockEquiv d t).symm b
  calc
    _ = Ideal.comap r.toRingHom (Ideal.map r.toRingHom (tangentDisplacementIdeal d t)) :=
      (Ideal.comap_map_of_bijective r.toRingHom hr).symm
    _ = Ideal.comap r.toRingHom (normalIdeal (d+t) d) := by rw [map_displacementIdeal]
    _ = _ := by
      rw [normalIdeal_eq_ker_planeTrace]
      ext g
      change planeTrace (d+t) d (r g)=0 ↔ actualTangentDisplacementZeroTrace d t g=0
      rw [zeroTrace_eq_permuted_planeTrace]

/-- All elements of every whole original ideal are recovered, not only a generator family. -/
theorem map_jointIdeal_eq_original (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (Ideal.map (actualCentreJointPullback d t).toRingHom I)=I := by
  rw [Ideal.map_map]
  have he : (actualTangentDisplacementZeroTrace d t).toRingHom.comp
      (actualCentreJointPullback d t).toRingHom=RingHom.id _ := by
    apply RingHom.ext
    intro g
    exact actualTangentDisplacementZeroTrace_jointPullback d t g
  rw [he,Ideal.map_id]

/-- The EXISTING original joint ideal maps literally to its original holomorphic generator ideal. -/
theorem map_actualCentreJointIdeal_eq_original (d t : ℕ) {ι : Type*}
    (H : ι → ComplexModel (d+t) → ℂ) (hH0 : ∀ i,HolAt (H i) 0) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (actualCentreJointIdeal d t H hH0)=Ideal.span (range fun i => HolGerm.mk (H i) (hH0 i)) := by
  unfold actualCentreJointIdeal
  rw [Ideal.map_span,← Set.range_comp]
  apply congrArg (fun f : ι → HolGerm (ComplexModel (d+t)) => Ideal.span (range f))
  funext i
  exact actualTangentDisplacementZeroTrace_jointPullback d t _

theorem actualTangentDisplacementZeroTrace_v (d t : ℕ) (i : Fin d) :
    actualTangentDisplacementZeroTrace d t (coordinateGerm ((i.castAdd t).natAdd d))=0 := by
  unfold actualTangentDisplacementZeroTrace coordinateGerm
  rw [compAlgHom_mk,← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualTangentDisplacementZeroInclusion_v d t z i

theorem actualTangentDisplacementZeroTrace_x (d t : ℕ) (i : Fin t) :
    actualTangentDisplacementZeroTrace d t (coordinateGerm ((i.natAdd d).natAdd d))=
      normalCoordinate d t i := by
  unfold actualTangentDisplacementZeroTrace normalCoordinate coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualTangentDisplacementZeroInclusion_x d t z i

/-- The SAME genuine joint displacement ideal (v,x) maps to the ORIGINAL normal ideal (x). -/
theorem map_jointNormalIdeal_eq_normal (d t : ℕ) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (normalIdeal d (d+t))=normalIdeal d t := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    change actualTangentDisplacementZeroTrace d t (normalCoordinate d (d+t) i) ∈ normalIdeal d t
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change actualTangentDisplacementZeroTrace d t (coordinateGerm ((j.castAdd t).natAdd d)) ∈ _
      rw [actualTangentDisplacementZeroTrace_v]
      exact Ideal.zero_mem _
    · change actualTangentDisplacementZeroTrace d t (coordinateGerm ((j.natAdd d).natAdd d)) ∈ _
      rw [actualTangentDisplacementZeroTrace_x]
      exact Ideal.subset_span ⟨j,rfl⟩
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    rw [← actualTangentDisplacementZeroTrace_x]
    apply Ideal.mem_map_of_mem
    exact Ideal.subset_span ⟨i.natAdd d,rfl⟩

theorem map_jointNormalIdeal_pow_eq_normal (d t a : ℕ) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (normalIdeal d (d+t)^a)=normalIdeal d t^a := by
  rw [Ideal.map_pow,map_jointNormalIdeal_eq_normal]

/-- Every SAME finite joint truncation ideal has the literal original normal-truncation image. -/
theorem map_jointTruncation_eq_original (d t a : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (actualTangentDisplacementZeroTrace d t).toRingHom
      (Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ normalIdeal d (d+t)^a)=
      I ⊔ normalIdeal d t^a := by
  rw [Ideal.map_sup,map_jointIdeal_eq_original,map_jointNormalIdeal_pow_eq_normal]

/-- The actual v=0 map preserves the ORIGINAL B tangent scalar actions. -/
def actualTangentDisplacementZeroBaseAlgHom (d t : ℕ) :
    letI := tangentAlgebra d (d+t)
    letI := tangentAlgebra d t
    HolGerm (ComplexModel (d+(d+t))) →ₐ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)) :=
  letI := tangentAlgebra d (d+t)
  letI := tangentAlgebra d t
  { (actualTangentDisplacementZeroTrace d t).toRingHom with
    commutes' := actualTangentDisplacementZeroTrace_tangentPullback d t }

/-- The genuine middle-coordinate quotient is an isomorphism over the ORIGINAL tangent germ ring. -/
def tangentDisplacementQuotientAlgEquiv (d t : ℕ) :
    letI := tangentAlgebra d (d+t)
    letI := tangentAlgebra d t
    (HolGerm (ComplexModel (d+(d+t))) ⧸ tangentDisplacementIdeal d t) ≃ₐ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (d+t)) := by
  letI := tangentAlgebra d (d+t)
  letI := tangentAlgebra d t
  rw [tangentDisplacementIdeal_eq_ker]
  exact Ideal.quotientKerAlgEquivOfSurjective (f := actualTangentDisplacementZeroBaseAlgHom d t)
    (actualTangentDisplacementZeroTrace_surjective d t)

private theorem quotientKerAlgEquivOfEq_mk {B R S : Type*} [CommRing B] [CommRing R]
    [CommRing S] [Algebra B R] [Algebra B S] (V : Ideal R) (q : R →ₐ[B] S)
    (hV : V=RingHom.ker q.toRingHom) (hq : Function.Surjective q) (g : R) :
    (show (R ⧸ V) ≃ₐ[B] S from by rw [hV];exact Ideal.quotientKerAlgEquivOfSurjective hq)
      (Ideal.Quotient.mk V g)=q g := by
  subst V
  rfl

/-- Every original class maps to its actual v=0 trace, retaining its genuine numerator. -/
theorem tangentDisplacementQuotientAlgEquiv_mk (d t : ℕ)
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    letI := tangentAlgebra d (d+t)
    letI := tangentAlgebra d t
    tangentDisplacementQuotientAlgEquiv d t (Ideal.Quotient.mk (tangentDisplacementIdeal d t) g)=
      actualTangentDisplacementZeroTrace d t g := by
  let := tangentAlgebra d (d+t)
  let := tangentAlgebra d t
  exact quotientKerAlgEquivOfEq_mk (tangentDisplacementIdeal d t)
    (actualTangentDisplacementZeroBaseAlgHom d t) (tangentDisplacementIdeal_eq_ker d t)
    (actualTangentDisplacementZeroTrace_surjective d t) g

end
end Hironaka.HironakaActualTangentDisplacementZeroQuotient

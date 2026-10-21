/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPrincipalPartsResidueSymbols
import Hironaka.Resolution.HironakaStrictFilteredGradedQuotient

/-!
# The actual zero-base joint fibre, whole layers and symbols

Actual pullback along z ↦ (0,z) has the entire original base maximal ideal as
its whole kernel, by a literal two-block permutation and coordinate Hadamard
division. For any whole joint ideal K this identifies all actual fibre
truncations and layers with those of its genuine original ambient image.
The layer dictionary commutes with literal actual multiplication. In particular
the existing original joint pullback ideal maps to the original ideal itself.

No analytic kernel, quotient dictionary or flatness is assumed. This does not
yet transport all tangent cuts to the original centre-normal filtration or
prove general higher Hilbert--Samuel transformation / G8.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualJointBaseFibre
noncomputable section
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HolGerm
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal
  HironakaRelativeNormalFibreHilbertSamuel
  HironakaActualCentreJointJets HironakaActualCentrePrincipalParts

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

/-- Actual trace on the zero-base slice (0,z), retaining every original germ. -/
def jointBaseZeroTrace (d n : ℕ) :
    HolGerm (ComplexModel (d+n)) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (actualJointNormalInclusion d n)
    (Eventually.of_forall fun _ => (actualJointNormalInclusion d n).differentiableAt) (map_zero _)

/-- The actual normal-coordinate projection supplies the genuine whole-germ retraction. -/
def jointNormalPullback (d n : ℕ) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel (d+n)) :=
  compAlgHom (actualJointNormalProjection d n)
    (Eventually.of_forall fun _ => (actualJointNormalProjection d n).differentiableAt) (map_zero _)

theorem jointBaseZeroTrace_normalPullback (d n : ℕ) (g : HolGerm (ComplexModel n)) :
    jointBaseZeroTrace d n (jointNormalPullback d n g)=g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold jointBaseZeroTrace jointNormalPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (actualJointNormalProjection_inclusion d n z)

theorem jointBaseZeroTrace_surjective (d n : ℕ) :
    Function.Surjective (jointBaseZeroTrace d n) :=
  fun g => ⟨jointNormalPullback d n g,jointBaseZeroTrace_normalPullback d n g⟩

private def blockSwap (d n : ℕ) : Fin (d+n) ≃ Fin (n+d) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin d) (Fin n)).trans finSumFinEquiv)

private theorem blockSwap_tangent (d n : ℕ) (i : Fin d) :
    blockSwap d n (i.castAdd n)=i.natAdd n := by simp [blockSwap]

private theorem blockSwap_normal (d n : ℕ) (i : Fin n) :
    blockSwap d n (i.natAdd d)=i.castAdd d := by simp [blockSwap]

private theorem maximalIdeal_eq_coordinate_span (n : ℕ) :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))=
      Ideal.span (range (coordinateGerm : Fin n → HolGerm (ComplexModel n))) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨h,he⟩ := exists_coordinate_decomposition g
    have hz : HolGerm.eval g=0 := (HolGerm.mem_maximalIdeal_iff g).mp hg
    rw [hz,map_zero,zero_add] at he
    rw [he]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rfl

private theorem tangentPullback_coordinate (d n : ℕ) (i : Fin d) :
    tangentPullback d n (coordinateGerm i)=coordinateGerm (i.castAdd n) := by
  unfold tangentPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

theorem baseMaximalIdeal_eq_tangent_span (d n : ℕ) :
    originalBaseMaximalIdeal d n=
      Ideal.span (range fun i : Fin d => coordinateGerm (i.castAdd n)) := by
  unfold originalBaseMaximalIdeal
  rw [maximalIdeal_eq_coordinate_span,Ideal.map_span,← Set.range_comp]
  apply congrArg (fun f : Fin d → HolGerm (ComplexModel (d+n)) => Ideal.span (range f))
  funext i
  exact tangentPullback_coordinate d n i

private theorem zeroTrace_eq_permuted_planeTrace (d n : ℕ)
    (g : HolGerm (ComplexModel (d+n))) :
    jointBaseZeroTrace d n g=planeTrace n d (coordinatePullback (blockSwap d n) g) := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold jointBaseZeroTrace planeTrace coordinatePullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    change F (actualJointNormalInclusion d n z)=
      F (coordinateMap (blockSwap d n) (tangentInclusion n d z))
    apply congrArg F
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [actualJointNormalInclusion_tangent,coordinateMap_apply,
        blockSwap_tangent,tangentInclusion_normal]
    · simp only [actualJointNormalInclusion_normal,coordinateMap_apply,
        blockSwap_normal,tangentInclusion_tangent]

private theorem map_baseMaximalIdeal_blockSwap (d n : ℕ) :
    Ideal.map (coordinatePullback (blockSwap d n)).toRingHom
      (originalBaseMaximalIdeal d n)=normalIdeal n d := by
  rw [baseMaximalIdeal_eq_tangent_span]
  unfold normalIdeal
  rw [Ideal.map_span,← Set.range_comp]
  apply congrArg (fun f : Fin d → HolGerm (ComplexModel (n+d)) => Ideal.span (range f))
  funext i
  exact (coordinatePullback_coordinate (blockSwap d n) _).trans
    (congrArg coordinateGerm (blockSwap_tangent d n i))

/-- The entire actual zero-base kernel is exactly the WHOLE original base maximal image. -/
theorem baseMaximalIdeal_eq_ker_jointBaseZeroTrace (d n : ℕ) :
    originalBaseMaximalIdeal d n=RingHom.ker (jointBaseZeroTrace d n).toRingHom := by
  let r := coordinatePullback (blockSwap d n)
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      have he := congrArg (coordinatePullback (blockSwap d n).symm) hab
      simpa only [r,coordinatePullback_inverse] using he
    · intro b
      refine ⟨coordinatePullback (blockSwap d n).symm b,?_⟩
      exact coordinatePullback_inverse (blockSwap d n).symm b
  calc
    _ = Ideal.comap r.toRingHom (Ideal.map r.toRingHom (originalBaseMaximalIdeal d n)) :=
      (Ideal.comap_map_of_bijective r.toRingHom hr).symm
    _ = Ideal.comap r.toRingHom (normalIdeal n d) := by rw [map_baseMaximalIdeal_blockSwap]
    _ = _ := by
      rw [normalIdeal_eq_ker_planeTrace]
      ext g
      change planeTrace n d (r g)=0 ↔ jointBaseZeroTrace d n g=0
      rw [zeroTrace_eq_permuted_planeTrace]

theorem jointBaseZeroTrace_jointPullback (d t : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    jointBaseZeroTrace d (d+t) (actualCentreJointPullback d t g)=g := by
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold jointBaseZeroTrace actualCentreJointPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg F
    simpa only [map_zero,add_zero] using actualCentreJointMap_fibre d t 0 z

theorem map_jointIdeal_eq_original (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (jointBaseZeroTrace d (d+t)).toRingHom
      (Ideal.map (actualCentreJointPullback d t).toRingHom I)=I := by
  rw [Ideal.map_map]
  have he : (jointBaseZeroTrace d (d+t)).toRingHom.comp
      (actualCentreJointPullback d t).toRingHom=RingHom.id _ := by
    apply RingHom.ext
    intro g
    exact jointBaseZeroTrace_jointPullback d t g
  rw [he,Ideal.map_id]

theorem jointBaseZeroTrace_normalCoordinate (d n : ℕ) (i : Fin n) :
    jointBaseZeroTrace d n (normalCoordinate d n i)=coordinateGerm i := by
  unfold jointBaseZeroTrace normalCoordinate coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualJointNormalInclusion_normal d n z i

theorem map_jointNormalIdeal_eq_maximalIdeal (d n : ℕ) :
    Ideal.map (jointBaseZeroTrace d n).toRingHom (normalIdeal d n)=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  rw [maximalIdeal_eq_coordinate_span,normalIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg (fun f : Fin n → HolGerm (ComplexModel n) => Ideal.span (range f))
  funext i
  exact jointBaseZeroTrace_normalCoordinate d n i

theorem map_jointFibreTruncation_eq_original (d t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (jointBaseZeroTrace d (d+t)).toRingHom
      ((Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ originalBaseMaximalIdeal d (d+t)) ⊔
        normalIdeal d (d+t)^s)=
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^s := by
  have hM : Ideal.map (jointBaseZeroTrace d (d+t)).toRingHom
      (originalBaseMaximalIdeal d (d+t))=⊥ := by
    rw [baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl
  rw [Ideal.map_sup,Ideal.map_sup,map_jointIdeal_eq_original,hM,sup_bot_eq,
    Ideal.map_pow,map_jointNormalIdeal_eq_maximalIdeal]

/-- The actual zero-base trace identifies every whole original joint fibre truncation with the original ambient one. -/
def jointBaseFibreTruncationAlgEquiv (d t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (HolGerm (ComplexModel (d+(d+t))) ⧸
      ((Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ originalBaseMaximalIdeal d (d+t)) ⊔
        normalIdeal d (d+t)^s)) ≃ₐ[ℂ]
    (HolGerm (ComplexModel (d+t)) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^s)) := by
  let D := (Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ originalBaseMaximalIdeal d (d+t)) ⊔
    normalIdeal d (d+t)^s
  let F := I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^s
  have hpre : Ideal.comap (jointBaseZeroTrace d (d+t)).toRingHom F=D := by
    dsimp only [F]
    rw [← map_jointFibreTruncation_eq_original d t s I,
      Ideal.comap_map_of_surjective (jointBaseZeroTrace d (d+t)).toRingHom (jointBaseZeroTrace_surjective d (d+t))]
    change D ⊔ RingHom.ker (jointBaseZeroTrace d (d+t)).toRingHom = D
    rw [← baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
    exact sup_eq_left.mpr (le_sup_right.trans le_sup_left)
  let f := Ideal.quotientMapₐ F (jointBaseZeroTrace d (d+t)) hpre.ge
  refine AlgEquiv.ofBijective f ⟨?_,?_⟩
  · intro a b hab
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    change g-h ∈ D
    rw [← hpre]
    change jointBaseZeroTrace d (d+t) (g-h) ∈ F
    rw [map_sub]
    change Ideal.Quotient.mk F (jointBaseZeroTrace d (d+t) g)=
      Ideal.Quotient.mk F (jointBaseZeroTrace d (d+t) h) at hab
    exact Ideal.Quotient.eq.mp hab
  · intro a
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,hh⟩ := jointBaseZeroTrace_surjective d (d+t) g
    refine ⟨Ideal.Quotient.mk D h,?_⟩
    change Ideal.Quotient.mk F (jointBaseZeroTrace d (d+t) h)=Ideal.Quotient.mk F g
    rw [hh]

theorem jointBaseFibreTruncationAlgEquiv_mk (d t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : HolGerm (ComplexModel (d+(d+t)))) :
    jointBaseFibreTruncationAlgEquiv d t s I
      (Ideal.Quotient.mk
        ((Ideal.map (actualCentreJointPullback d t).toRingHom I ⊔ originalBaseMaximalIdeal d (d+t)) ⊔
          normalIdeal d (d+t)^s) g)=
    Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^s)
      (jointBaseZeroTrace d (d+t) g) := rfl

/-- Every whole joint ideal has its actual ambient zero-base fibre, including all normal powers. -/
theorem map_baseFibreTruncation (d n s : ℕ) (K : Ideal (HolGerm (ComplexModel (d+n)))) :
    Ideal.map (jointBaseZeroTrace d n).toRingHom
      ((K ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^s)=
      Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^s := by
  have hM : Ideal.map (jointBaseZeroTrace d n).toRingHom
      (originalBaseMaximalIdeal d n)=⊥ := by
    rw [baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl
  rw [Ideal.map_sup,Ideal.map_sup,hM,sup_bot_eq,Ideal.map_pow,map_jointNormalIdeal_eq_maximalIdeal]

/-- The canonical full fibre quotient for any joint ideal; this applies unchanged after every tangent cut. -/
def baseFibreTruncationAlgEquiv (d n s : ℕ)
    (K : Ideal (HolGerm (ComplexModel (d+n)))) :
    (HolGerm (ComplexModel (d+n)) ⧸
      ((K ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^s)) ≃ₐ[ℂ]
    (HolGerm (ComplexModel n) ⧸
      (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^s)) := by
  let D := (K ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^s
  let F := Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^s
  have hpre : Ideal.comap (jointBaseZeroTrace d n).toRingHom F=D := by
    dsimp only [F]
    rw [← map_baseFibreTruncation d n s K,
      Ideal.comap_map_of_surjective (jointBaseZeroTrace d n).toRingHom (jointBaseZeroTrace_surjective d n)]
    change D ⊔ RingHom.ker (jointBaseZeroTrace d n).toRingHom = D
    rw [← baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
    exact sup_eq_left.mpr (le_sup_right.trans le_sup_left)
  let f := Ideal.quotientMapₐ F (jointBaseZeroTrace d n) hpre.ge
  refine AlgEquiv.ofBijective f ⟨?_,?_⟩
  · intro a b hab
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    change g-h ∈ D
    rw [← hpre]
    change jointBaseZeroTrace d n (g-h) ∈ F
    rw [map_sub]
    change Ideal.Quotient.mk F (jointBaseZeroTrace d n g)=
      Ideal.Quotient.mk F (jointBaseZeroTrace d n h) at hab
    exact Ideal.Quotient.eq.mp hab
  · intro a
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨h,hh⟩ := jointBaseZeroTrace_surjective d n g
    refine ⟨Ideal.Quotient.mk D h,?_⟩
    change Ideal.Quotient.mk F (jointBaseZeroTrace d n h)=Ideal.Quotient.mk F g
    rw [hh]

theorem baseFibreTruncationAlgEquiv_mk (d n s : ℕ)
    (K : Ideal (HolGerm (ComplexModel (d+n)))) (g : HolGerm (ComplexModel (d+n))) :
    baseFibreTruncationAlgEquiv d n s K
      (Ideal.Quotient.mk ((K ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^s) g)=
    Ideal.Quotient.mk
      (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^s)
      (jointBaseZeroTrace d n g) := rfl

section Layers
set_option maxHeartbeats 1000000
open HironakaRelativeNormalAssociatedGraded HironakaStrictFilteredGradedQuotient
  HironakaActualPrincipalPartsResidueSymbols
variable (d n : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  tangentAlgebra d n
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  IsScalarTower.of_algHom (tangentPullback d n)

/-- The actual zero-base map on the entire fibre layer, with the original ambient adic layer as target. -/
def jointBaseFibreLayerMap (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    originalNormalGradedPiece d n
      (K ⊔ originalBaseMaximalIdeal d n) q →ₗ[ℂ]
    adicLayer (Ideal.map (jointBaseZeroTrace d n).toRingHom K) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) q := by
  let e := (baseFibreTruncationAlgEquiv d n (q+1) K).toLinearMap
  refine (e.comp ((originalNormalGradedPiece d n
    (K ⊔ originalBaseMaximalIdeal d n) q).restrictScalars ℂ).subtype).codRestrict
      ((adicLayer (Ideal.map (jointBaseZeroTrace d n).toRingHom K) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) q).restrictScalars ℂ) ?_
  intro z
  obtain ⟨g,hg,he⟩ := z.property
  change g ∈ normalIdeal d n^q at hg
  have hv : z.val=Ideal.Quotient.mk
      ((K ⊔ originalBaseMaximalIdeal d n) ⊔
        normalIdeal d n^(q+1)) g := he.symm
  change baseFibreTruncationAlgEquiv d n (q+1) K z.val ∈ _
  rw [hv,baseFibreTruncationAlgEquiv_mk]
  refine ⟨jointBaseZeroTrace d n g,?_,rfl⟩
  change jointBaseZeroTrace d n g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q
  rw [← map_jointNormalIdeal_eq_maximalIdeal d n,← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hg

theorem jointBaseFibreLayerMap_mk (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ)
    (g : HolGerm (ComplexModel (d+n))) (hg : g ∈ normalIdeal d n^q) :
    (jointBaseFibreLayerMap d n K q
      ⟨Ideal.Quotient.mk
        ((K ⊔ originalBaseMaximalIdeal d n) ⊔
          normalIdeal d n^(q+1)) g,⟨g,hg,rfl⟩⟩).val =
    Ideal.Quotient.mk (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+1))
      (jointBaseZeroTrace d n g) := rfl

theorem jointBaseFibreLayerMap_injective (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    Function.Injective (jointBaseFibreLayerMap d n K q) := by
  intro a b hab
  apply Subtype.ext
  exact (baseFibreTruncationAlgEquiv d n (q+1) K).injective (congrArg Subtype.val hab)

theorem jointBaseFibreLayerMap_surjective (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    Function.Surjective (jointBaseFibreLayerMap d n K q) := by
  rintro ⟨x,hx⟩
  obtain ⟨h,hh,he⟩ := hx
  change h ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q at hh
  rw [← map_jointNormalIdeal_eq_maximalIdeal d n,← Ideal.map_pow] at hh
  obtain ⟨g,hg,hg'⟩ :=
    (Ideal.mem_map_iff_of_surjective (jointBaseZeroTrace d n).toRingHom
      (jointBaseZeroTrace_surjective d n)).mp hh
  refine ⟨⟨Ideal.Quotient.mk
    ((K ⊔ originalBaseMaximalIdeal d n) ⊔
      normalIdeal d n^(q+1)) g,⟨g,hg,rfl⟩⟩,?_⟩
  apply Subtype.ext
  have hhg : jointBaseZeroTrace d n g=h := hg'
  have hclass := congrArg (Ideal.Quotient.mk
    (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+1))) hhg
  exact (jointBaseFibreLayerMap_mk d n K q g hg).trans (hclass.trans he)

def jointBaseFibreLayerEquiv (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    originalNormalGradedPiece d n
      (K ⊔ originalBaseMaximalIdeal d n) q ≃ₗ[ℂ]
    adicLayer (Ideal.map (jointBaseZeroTrace d n).toRingHom K) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) q :=
  LinearEquiv.ofBijective (jointBaseFibreLayerMap d n K q)
    ⟨jointBaseFibreLayerMap_injective d n K q,jointBaseFibreLayerMap_surjective d n K q⟩

/-- Actual normal-ideal members have actual ambient maximal-ideal traces. -/
theorem jointBaseZeroTrace_mem_maximalIdeal (v : HolGerm (ComplexModel (d+n)))
    (hv : v ∈ normalIdeal d n) :
    jointBaseZeroTrace d n v ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  rw [← map_jointNormalIdeal_eq_maximalIdeal d n]
  exact Ideal.mem_map_of_mem _ hv

/-- The entire layer dictionary commutes with literal actual multiplication. -/
theorem jointBaseFibreLayerMap_symbol (K : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ)
    (z : originalNormalGradedPiece d n
      (K ⊔ originalBaseMaximalIdeal d n) q) :
    jointBaseFibreLayerMap d n K (q+1)
      (originalLayerSymbolMul d n
        (K ⊔ originalBaseMaximalIdeal d n) v hv q z)=
    adicSymbolMul (Ideal.map (jointBaseZeroTrace d n).toRingHom K) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
      (jointBaseZeroTrace d n v) (jointBaseZeroTrace_mem_maximalIdeal d n v hv) q
        (jointBaseFibreLayerMap d n K q z) := by
  rcases z with ⟨x,hx⟩
  obtain ⟨g,hg,rfl⟩ := hx
  change g ∈ normalIdeal d n^q at hg
  apply Subtype.ext
  change baseFibreTruncationAlgEquiv d n (q+2) K
    (Ideal.Quotient.mk
      ((K ⊔ originalBaseMaximalIdeal d n) ⊔
        normalIdeal d n^(q+2)) (v*g)) =
    Ideal.Quotient.mk (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+2))
      (jointBaseZeroTrace d n v * jointBaseZeroTrace d n g)
  rw [baseFibreTruncationAlgEquiv_mk,map_mul]

end Layers

end
end Hironaka.HironakaActualJointBaseFibre

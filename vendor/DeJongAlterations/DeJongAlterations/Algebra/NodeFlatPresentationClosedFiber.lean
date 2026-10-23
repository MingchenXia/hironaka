import DeJongAlterations.Algebra.NodeFlatPresentationEvaluation
import DeJongAlterations.Algebra.NodeFlatPresentationUniqueness
import DeJongAlterations.Algebra.NodeFlatPresentationCompleteness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Noetherian.Basic

/-! # Original split nodal closed-fibre coordinates and their actual complete evaluation -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open MvPowerSeries IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

abbrev splitNodeIdeal (K : Type*) [CommRing K] : Ideal (MvPowerSeries (Fin 2) K) :=
  Ideal.span {X (0 : Fin 2) * X 1}

abbrev SplitNode (K : Type*) [CommRing K] := MvPowerSeries (Fin 2) K ⧸ splitNodeIdeal K

/-- The original constant coefficient descends through the actual nodal relation. -/
def splitNodeConstant (K : Type*) [CommRing K] : SplitNode K →+* K :=
  Ideal.Quotient.lift (splitNodeIdeal K) constantCoeff (by
    have h : splitNodeIdeal K ≤ RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) K →+* K) := by
      rw [Ideal.span_singleton_le_iff_mem]
      simp
    exact fun a ha => h ha)

@[simp]
theorem splitNodeConstant_coordinate (K : Type*) [CommRing K] (i : Fin 2) :
    splitNodeConstant K (Ideal.Quotient.mk (splitNodeIdeal K) (X i)) = 0 := by
  simp [splitNodeConstant]

/-- Each actual coordinate class of the split node is a nonunit. -/
theorem splitNode_coordinate_nonunit (K : Type*) [CommRing K] [Nontrivial K] (i : Fin 2) :
    ¬ IsUnit (Ideal.Quotient.mk (splitNodeIdeal K) (X i)) := by
  intro h
  have := h.map (splitNodeConstant K)
  rw [splitNodeConstant_coordinate] at this
  exact not_isUnit_zero this

variable (A : Type u) [CommRing A] [IsLocalRing A]
  (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

abbrev CoefficientResidue := A ⧸ maximalIdeal A
abbrev closedFiberIdeal : Ideal B := (maximalIdeal A).map (algebraMap A B)
abbrev ClosedFiber := B ⧸ closedFiberIdeal A B

instance closedFiberAlgebra : Algebra (CoefficientResidue A) (ClosedFiber A B) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

instance closedFiber_nontrivial : Nontrivial (ClosedFiber A B) :=
  Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt (map_maximalIdeal_lt_top (algebraMap A B)))

instance closedFiber_isLocalRing : IsLocalRing (ClosedFiber A B) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective

/-- The actual closed-fibre map specified by the split nodal fibre isomorphism. -/
def closedFiberMap (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A →+* ClosedFiber A B :=
  e.toRingHom.comp ((Ideal.Quotient.mk (splitNodeIdeal (CoefficientResidue A))).comp
    (MvPowerSeries.map (Ideal.Quotient.mk (maximalIdeal A))))

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem closedFiberMap_C
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    closedFiberMap A B e (C a) = Ideal.Quotient.mk (closedFiberIdeal A B) (algebraMap A B a) := by
  change e (Ideal.Quotient.mk _ (MvPowerSeries.map _ (C a))) = _
  rw [MvPowerSeries.map_C]
  change e (algebraMap (CoefficientResidue A) (SplitNode (CoefficientResidue A))
    (Ideal.Quotient.mk (maximalIdeal A) a)) = _
  rw [e.commutes]
  rfl

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
theorem closedFiberMap_surjective
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    Function.Surjective (closedFiberMap A B e) :=
  e.surjective.comp (Ideal.Quotient.mk_surjective.comp
    (map_surjective _ Ideal.Quotient.mk_surjective))

/-- Chosen actual lifts through the original target quotient, not a supplied presentation. -/
def coordinateLifts
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) : B :=
  Classical.choose (Ideal.Quotient.mk_surjective (closedFiberMap A B e (X i)))

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem coordinateLifts_reduction
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    Ideal.Quotient.mk (closedFiberIdeal A B) (coordinateLifts A B e i) =
      closedFiberMap A B e (X i) :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (closedFiberMap A B e (X i)))

omit [IsLocalHom (algebraMap A B)] in
theorem coordinateLifts_mem
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    coordinateLifts A B e i ∈ maximalIdeal B := by
  intro hu
  have hq := hu.map (Ideal.Quotient.mk (closedFiberIdeal A B))
  rw [coordinateLifts_reduction] at hq
  have hn := hq.map e.symm.toRingHom
  have hx : e.symm (closedFiberMap A B e (X i)) =
      Ideal.Quotient.mk (splitNodeIdeal (CoefficientResidue A)) (X i) := by
    simp [closedFiberMap]
  change IsUnit (e.symm (closedFiberMap A B e (X i))) at hn
  rw [hx] at hn
  exact splitNode_coordinate_nonunit (CoefficientResidue A) i hn

variable [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]

/-- The original evaluation constructed from the original closed-fibre isomorphism. -/
def presentationMap
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A →ₐ[A] B :=
  evaluation (maximalIdeal B) (coordinateLifts A B e) (coordinateLifts_mem A B e)

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem presentationMap_C
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    presentationMap A B e (C a) = algebraMap A B a := evaluation_C _ _ _ _

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem presentationMap_X
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    presentationMap A B e (X i) = coordinateLifts A B e i := evaluation_X _ _ _ _

/-- Agreement on original coefficients and coordinates forces the entire specified fibre map. -/
theorem presentationMap_closedFiber
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    (Ideal.Quotient.mk (closedFiberIdeal A B)).comp (presentationMap A B e).toRingHom =
      closedFiberMap A B e := by
  let : IsNoetherianRing (ClosedFiber A B) := isNoetherianRing_of_surjective B _
    (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective
  apply formal_hom_ext (maximalIdeal (ClosedFiber A B))
  · intro a
    change Ideal.Quotient.mk _ (presentationMap A B e (C a)) = closedFiberMap A B e (C a)
    rw [presentationMap_C, closedFiberMap_C]
  · intro i
    change Ideal.Quotient.mk _ (presentationMap A B e (X i)) = closedFiberMap A B e (X i)
    rw [presentationMap_X, coordinateLifts_reduction]
  · intro i
    change Ideal.Quotient.mk _ (presentationMap A B e (X i)) ∈ _
    rw [presentationMap_X]
    let := IsLocalHom.of_surjective (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective
    exact map_nonunit _ _ (coordinateLifts_mem A B e i)

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
/-- The actual original coefficient ideal has exactly its original image under evaluation. -/
theorem presentationMap_image_coefficientIdeal
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    ((maximalIdeal A).map (C : A →+* MvPowerSeries (Fin 2) A)).map
      (presentationMap A B e).toRingHom = closedFiberIdeal A B := by
  rw [Ideal.map_map]
  apply congrArg (fun f : A →+* B => (maximalIdeal A).map f)
  ext a
  exact presentationMap_C A B e a

/-- Completeness of the original coefficient ring upgrades the actual fibre surjection. -/
theorem presentationMap_surjective [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    Function.Surjective (presentationMap A B e) := by
  let M : Ideal (MvPowerSeries (Fin 2) A) := (maximalIdeal A).map C
  let : IsPrecomplete M (MvPowerSeries (Fin 2) A) :=
    isPrecomplete_extended (maximalIdeal A) (IsNoetherian.noetherian _)
  have hm : M.map (presentationMap A B e).toRingHom = closedFiberIdeal A B :=
    presentationMap_image_coefficientIdeal A B e
  let : IsHausdorff (M.map (presentationMap A B e).toRingHom) B :=
    IsHausdorff.of_le_jacobson _ _ (by
      rw [hm]
      exact (map_maximalIdeal_le (algebraMap A B)).trans (maximalIdeal_le_jacobson _))
  apply surjective_of_mk_map_comp_surjective (I := M) (presentationMap A B e).toRingHom
  rw [hm, presentationMap_closedFiber]
  exact closedFiberMap_surjective A B e

omit [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
  [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
/-- The specified closed-fibre model has its literal original nodal kernel. -/
theorem closedFiberMap_eq_zero_iff
    (e : SplitNode (CoefficientResidue A) ≃ₐ[CoefficientResidue A] ClosedFiber A B)
    (f : MvPowerSeries (Fin 2) A) :
    closedFiberMap A B e f = 0 ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maximalIdeal A)) f ∈ splitNodeIdeal (CoefficientResidue A) := by
  change e (Ideal.Quotient.mk _ (MvPowerSeries.map _ f)) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]

end DeJongAlterations.Algebra.NodeFlatPresentation

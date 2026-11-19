import Hironaka.Algebra.NodeNonsplitComplete
import Hironaka.Algebra.NodeFlatPresentationClosedFiber

/-! # The original quadratic node fibre constructs actual complete-local coordinates -/

noncomputable section

namespace Hironaka.Algebra.NodeNonsplit

open MvPowerSeries IsLocalRing NodeFormalMorse NodeFlatPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

abbrev quadraticNodeIdeal {R : Type*} [CommRing R] (Q : Quadratic R) : Ideal (Series R) :=
  Ideal.span {Q.series}

abbrev QuadraticNode {R : Type*} [CommRing R] (Q : Quadratic R) := Series R ⧸ quadraticNodeIdeal Q

/-- The actual constant coefficient kills the original homogeneous quadratic relation. -/
def quadraticNodeConstant {R : Type*} [CommRing R] (Q : Quadratic R) : QuadraticNode Q →+* R :=
  Ideal.Quotient.lift (quadraticNodeIdeal Q) constantCoeff (by
    have h : quadraticNodeIdeal Q ≤ RingHom.ker (constantCoeff : Series R →+* R) := by
      rw [Ideal.span_singleton_le_iff_mem]
      simp [Quadratic.series, Quadratic.value, Quadratic.map]
    exact fun f hf => h hf)

@[simp]
theorem quadraticNodeConstant_coordinate {R : Type*} [CommRing R] (Q : Quadratic R) (i : Fin 2) :
    quadraticNodeConstant Q (Ideal.Quotient.mk (quadraticNodeIdeal Q) (X i)) = 0 := by
  simp [quadraticNodeConstant]

theorem quadraticNode_coordinate_nonunit {R : Type*} [CommRing R] [Nontrivial R]
    (Q : Quadratic R) (i : Fin 2) :
    ¬ IsUnit (Ideal.Quotient.mk (quadraticNodeIdeal Q) (X i)) := by
  intro h
  have hu := h.map (quadraticNodeConstant Q)
  rw [quadraticNodeConstant_coordinate] at hu
  exact not_isUnit_zero hu

variable (A : Type u) [CommRing A] [IsLocalRing A]
  (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  (Q : Quadratic A)

/-- The actual closed-fibre map specified by the original quadratic nodal fibre isomorphism. -/
def closedFiberMap (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A →+* ClosedFiber A B :=
  e.toRingHom.comp ((Ideal.Quotient.mk (quadraticNodeIdeal (Q.map (Ideal.Quotient.mk (maximalIdeal A))))).comp
    (MvPowerSeries.map (Ideal.Quotient.mk (maximalIdeal A))))

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem closedFiberMap_C
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    closedFiberMap A B Q e (C a) = Ideal.Quotient.mk (closedFiberIdeal A B) (algebraMap A B a) := by
  change e (Ideal.Quotient.mk _ (MvPowerSeries.map _ (C a))) = _
  rw [MvPowerSeries.map_C]
  change e (algebraMap (CoefficientResidue A) (QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))))
    (Ideal.Quotient.mk (maximalIdeal A) a)) = _
  rw [e.commutes]
  rfl

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
theorem closedFiberMap_surjective
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    Function.Surjective (closedFiberMap A B Q e) :=
  e.surjective.comp (Ideal.Quotient.mk_surjective.comp
    (map_surjective _ Ideal.Quotient.mk_surjective))

/-- Chosen actual lifts through the original target quotient, not a supplied presentation. -/
def coordinateLifts
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) : B :=
  Classical.choose (Ideal.Quotient.mk_surjective (closedFiberMap A B Q e (X i)))

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem coordinateLifts_reduction
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    Ideal.Quotient.mk (closedFiberIdeal A B) (coordinateLifts A B Q e i) =
      closedFiberMap A B Q e (X i) :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (closedFiberMap A B Q e (X i)))

omit [IsLocalHom (algebraMap A B)] in
theorem coordinateLifts_mem
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    coordinateLifts A B Q e i ∈ maximalIdeal B := by
  intro hu
  have hq := hu.map (Ideal.Quotient.mk (closedFiberIdeal A B))
  rw [coordinateLifts_reduction] at hq
  have hn := hq.map e.symm.toRingHom
  have hx : e.symm (closedFiberMap A B Q e (X i)) =
      Ideal.Quotient.mk (quadraticNodeIdeal (Q.map (Ideal.Quotient.mk (maximalIdeal A)))) (X i) := by
    simp [closedFiberMap]
  change IsUnit (e.symm (closedFiberMap A B Q e (X i))) at hn
  rw [hx] at hn
  exact quadraticNode_coordinate_nonunit (Q.map (Ideal.Quotient.mk (maximalIdeal A))) i hn

variable [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]

/-- The original evaluation constructed from the original closed-fibre isomorphism. -/
def presentationMap
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    MvPowerSeries (Fin 2) A →ₐ[A] B :=
  evaluation (maximalIdeal B) (coordinateLifts A B Q e) (coordinateLifts_mem A B Q e)

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem presentationMap_C
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (a : A) :
    presentationMap A B Q e (C a) = algebraMap A B a := evaluation_C _ _ _ _

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
@[simp]
theorem presentationMap_X
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) (i : Fin 2) :
    presentationMap A B Q e (X i) = coordinateLifts A B Q e i := evaluation_X _ _ _ _

/-- Agreement on original coefficients and coordinates forces the entire specified fibre map. -/
theorem presentationMap_closedFiber
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    (Ideal.Quotient.mk (closedFiberIdeal A B)).comp (presentationMap A B Q e).toRingHom =
      closedFiberMap A B Q e := by
  let : IsNoetherianRing (ClosedFiber A B) := isNoetherianRing_of_surjective B _
    (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective
  apply formal_hom_ext (maximalIdeal (ClosedFiber A B))
  · intro a
    change Ideal.Quotient.mk _ (presentationMap A B Q e (C a)) = closedFiberMap A B Q e (C a)
    rw [presentationMap_C, closedFiberMap_C]
  · intro i
    change Ideal.Quotient.mk _ (presentationMap A B Q e (X i)) = closedFiberMap A B Q e (X i)
    rw [presentationMap_X, coordinateLifts_reduction]
  · intro i
    change Ideal.Quotient.mk _ (presentationMap A B Q e (X i)) ∈ _
    rw [presentationMap_X]
    let := IsLocalHom.of_surjective (Ideal.Quotient.mk (closedFiberIdeal A B)) Ideal.Quotient.mk_surjective
    exact map_nonunit _ _ (coordinateLifts_mem A B Q e i)

omit [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] in
/-- The actual original coefficient ideal has exactly its original image under evaluation. -/
theorem presentationMap_image_coefficientIdeal
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    ((maximalIdeal A).map (C : A →+* MvPowerSeries (Fin 2) A)).map
      (presentationMap A B Q e).toRingHom = closedFiberIdeal A B := by
  rw [Ideal.map_map]
  apply congrArg (fun f : A →+* B => (maximalIdeal A).map f)
  ext a
  exact presentationMap_C A B Q e a

/-- Completeness of the original coefficient ring upgrades the actual fibre surjection. -/
theorem presentationMap_surjective [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B) :
    Function.Surjective (presentationMap A B Q e) := by
  let M : Ideal (MvPowerSeries (Fin 2) A) := (maximalIdeal A).map C
  let : IsPrecomplete M (MvPowerSeries (Fin 2) A) :=
    isPrecomplete_extended (maximalIdeal A) (IsNoetherian.noetherian _)
  have hm : M.map (presentationMap A B Q e).toRingHom = closedFiberIdeal A B :=
    presentationMap_image_coefficientIdeal A B Q e
  let : IsHausdorff (M.map (presentationMap A B Q e).toRingHom) B :=
    IsHausdorff.of_le_jacobson _ _ (by
      rw [hm]
      exact (map_maximalIdeal_le (algebraMap A B)).trans (maximalIdeal_le_jacobson _))
  apply surjective_of_mk_map_comp_surjective (I := M) (presentationMap A B Q e).toRingHom
  rw [hm, presentationMap_closedFiber]
  exact closedFiberMap_surjective A B Q e

omit [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
  [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
/-- The specified closed-fibre model has its literal original nodal kernel. -/
theorem closedFiberMap_eq_zero_iff
    (e : QuadraticNode (Q.map (Ideal.Quotient.mk (maximalIdeal A))) ≃ₐ[CoefficientResidue A] ClosedFiber A B)
    (f : MvPowerSeries (Fin 2) A) :
    closedFiberMap A B Q e f = 0 ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maximalIdeal A)) f ∈ quadraticNodeIdeal (Q.map (Ideal.Quotient.mk (maximalIdeal A))) := by
  change e (Ideal.Quotient.mk _ (MvPowerSeries.map _ f)) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]

end Hironaka.Algebra.NodeNonsplit

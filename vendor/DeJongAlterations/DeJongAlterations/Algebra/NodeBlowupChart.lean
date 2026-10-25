import DeJongAlterations.Algebra.NodeDomain
import DeJongAlterations.Geometry.AffineBlowupChart

/-!
# Genuine fraction-algebra charts of the node blowup

The quotient presentations are identified with the actual fraction subalgebras, using
the proved node-domain kernel and injectivity, rather than an unsaturated relation ideal.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeBlowupChart

open Polynomial CategoryTheory

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The literal node quotient used by the polynomial chart identities. -/
abbrev Node (A : Type*) [CommRing A] (c : A) :=
  MvPolynomial (Fin 2) A ⧸ NodeChart.uChartIdeal A c

/-- The two coordinates of the literal quotient. -/
def coordinate (c : A) (i : Fin 2) : Node A c :=
  Ideal.Quotient.mk (NodeChart.uChartIdeal A c) (MvPolynomial.X i)

/-- Orient the nested polynomial model so the first literal coordinate is the coefficient variable. -/
def coordinateEquiv : MvPolynomial (Fin 2) A ≃ₐ[A] A[X][X] :=
  (MvPolynomial.renameEquiv A (Equiv.swap (0 : Fin 2) 1)).trans NodeDomain.polynomialEquiv

omit [IsDomain A] in
theorem coordinateEquiv_equation (c : A) :
    coordinateEquiv (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c) =
      NodeDomain.nestedEquation c := by
  change NodeDomain.polynomialEquiv
    ((MvPolynomial.renameEquiv A (Equiv.swap (0 : Fin 2) 1))
      (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c)) = _
  have h : (MvPolynomial.renameEquiv A (Equiv.swap (0 : Fin 2) 1))
      (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c) =
        MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c := by
    simp [MvPolynomial.renameEquiv_apply, mul_comm]
  rw [h]
  exact NodeDomain.polynomialEquiv_equation c

omit [IsDomain A] in
theorem coordinateEquiv_X0 : coordinateEquiv (MvPolynomial.X 0 : MvPolynomial (Fin 2) A) =
    C (X : A[X]) := by
  have hX1 : (MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X 1) =
      C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := A) (j := (0 : Fin 1))
  simp [coordinateEquiv, NodeDomain.polynomialEquiv, MvPolynomial.renameEquiv_apply,
    hX1, Polynomial.mapAlgEquiv, MvPolynomial.uniqueAlgEquiv_apply]

omit [IsDomain A] in
theorem coordinateEquiv_X1 : coordinateEquiv (MvPolynomial.X 1 : MvPolynomial (Fin 2) A) =
    (X : A[X][X]) := by
  simp [coordinateEquiv, NodeDomain.polynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_X_zero, Polynomial.mapAlgEquiv]

omit [IsDomain A] in
theorem coordinateEquiv_C (a : A) : coordinateEquiv (MvPolynomial.C a) = C (C a) :=
  coordinateEquiv.commutes a

/-- The actual node quotient is canonically equivalent to this oriented nested model. -/
def orientedQuotientEquiv (c : A) :
    Node A c ≃ₐ[A] (A[X][X] ⧸ NodeDomain.nestedIdeal c) :=
  Ideal.quotientEquivAlg _ _ coordinateEquiv (by
    rw [NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
    change NodeDomain.nestedIdeal c = Ideal.span {coordinateEquiv
      (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C c)}
    rw [coordinateEquiv_equation]
    rfl)

/-- The actual quotient embedding sends the first coordinate to the Laurent variable. -/
def nodeLocalizationEmbedding (c : A) (hc : c ≠ 0) :
    Node A c →+* NodeDomain.CoefficientLocalization A :=
  (NodeDomain.nestedQuotientEmbedding c hc).comp (orientedQuotientEquiv c).toRingHom

theorem nodeLocalizationEmbedding_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (nodeLocalizationEmbedding c hc) :=
  (NodeDomain.nestedQuotientEmbedding_injective c hc).comp (orientedQuotientEquiv c).injective

@[simp]
theorem nodeLocalizationEmbedding_mk (c : A) (hc : c ≠ 0) (P : MvPolynomial (Fin 2) A) :
    nodeLocalizationEmbedding c hc (Ideal.Quotient.mk _ P) =
      NodeDomain.nestedEvaluation c (coordinateEquiv P) := rfl

@[simp]
theorem nodeLocalizationEmbedding_coordinate0 (c : A) (hc : c ≠ 0) :
    nodeLocalizationEmbedding c hc (coordinate c 0) =
      algebraMap A[X] (NodeDomain.CoefficientLocalization A) X := by
  change NodeDomain.nestedEvaluation c (coordinateEquiv (MvPolynomial.X 0)) = _
  rw [coordinateEquiv_X0]
  simp [NodeDomain.nestedEvaluation]

@[simp]
theorem nodeLocalizationEmbedding_coordinate1 (c : A) (hc : c ≠ 0) :
    nodeLocalizationEmbedding c hc (coordinate c 1) = NodeDomain.evaluationPoint c := by
  change NodeDomain.nestedEvaluation c (coordinateEquiv (MvPolynomial.X 1)) = _
  rw [coordinateEquiv_X1]
  simp [NodeDomain.nestedEvaluation]

@[simp]
theorem nodeLocalizationEmbedding_C (c : A) (hc : c ≠ 0) (a : A) :
    nodeLocalizationEmbedding c hc (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      algebraMap A[X] (NodeDomain.CoefficientLocalization A) (C a) := by
  rw [nodeLocalizationEmbedding_mk, coordinateEquiv_C]
  simp [NodeDomain.nestedEvaluation]

/-- Laurent evaluation induced by a nonzero field element. -/
def coordinateLocalizationLift {F : Type*} [Field F] [Algebra A F]
    (x : F) (hx : x ≠ 0) : NodeDomain.CoefficientLocalization A →+* F :=
  IsLocalization.Away.lift (X : A[X]) (g := (Polynomial.aeval x).toRingHom)
    (by simpa using (isUnit_iff_ne_zero.mpr hx))

omit [IsDomain A] in
@[simp]
theorem coordinateLocalizationLift_algebraMap {F : Type*} [Field F] [Algebra A F]
    (x : F) (hx : x ≠ 0) (P : A[X]) :
    coordinateLocalizationLift x hx
      (algebraMap A[X] (NodeDomain.CoefficientLocalization A) P) = Polynomial.aeval x P :=
  IsLocalization.Away.lift_eq _ _ _

theorem coordinateLocalizationLift_injective {F : Type*} [Field F] [Algebra A F]
    (x : F) (hx : x ≠ 0) (hp : Function.Injective (Polynomial.aeval x : A[X] →ₐ[A] F)) :
    Function.Injective (coordinateLocalizationLift x hx :
      NodeDomain.CoefficientLocalization A →+* F) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (X : A[X]))]
  intro P Q
  simp only [coordinateLocalizationLift_algebraMap]
  constructor
  · intro h
    exact congrArg (Polynomial.aeval x) (IsLocalization.injective
      (NodeDomain.CoefficientLocalization A)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero : (X : A[X]) ≠ 0)) h)
  · intro h
    exact congrArg (algebraMap A[X] (NodeDomain.CoefficientLocalization A)) (hp h)

omit [IsDomain A] in
@[simp]
theorem coordinateLocalizationLift_invSelf {F : Type*} [Field F] [Algebra A F]
    (x : F) (hx : x ≠ 0) :
    coordinateLocalizationLift x hx
      (IsLocalization.Away.invSelf (S := NodeDomain.CoefficientLocalization A) (X : A[X])) =
        x⁻¹ := by
  apply mul_left_cancel₀ hx
  have h := congrArg (coordinateLocalizationLift x hx)
    (IsLocalization.Away.mul_invSelf (S := NodeDomain.CoefficientLocalization A) (X : A[X]))
  have h' : x * coordinateLocalizationLift x hx
      (IsLocalization.Away.invSelf (S := NodeDomain.CoefficientLocalization A) (X : A[X])) = 1 := by
    simpa only [map_mul, map_one, coordinateLocalizationLift_algebraMap, Polynomial.aeval_X] using h
  exact h'.trans (mul_inv_cancel₀ hx).symm

/-- Evaluation of the actual node quotient in a field. -/
def nodeEvaluation {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0) : Node A c →+* F :=
  (coordinateLocalizationLift x hx).comp (nodeLocalizationEmbedding c hc)

theorem nodeEvaluation_injective {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0)
    (hp : Function.Injective (Polynomial.aeval x : A[X] →ₐ[A] F)) :
    Function.Injective (nodeEvaluation c hc x hx) :=
  (coordinateLocalizationLift_injective x hx hp).comp (nodeLocalizationEmbedding_injective c hc)

@[simp]
theorem nodeEvaluation_coordinate0 {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0) :
    nodeEvaluation c hc x hx (coordinate c 0) = x := by
  simp [nodeEvaluation]

@[simp]
theorem nodeEvaluation_coordinate1 {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0) :
    nodeEvaluation c hc x hx (coordinate c 1) = algebraMap A F c / x := by
  simp [nodeEvaluation, NodeDomain.evaluationPoint, div_eq_mul_inv]

@[simp]
theorem nodeEvaluation_C {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0) (a : A) :
    nodeEvaluation c hc x hx (Ideal.Quotient.mk _ (MvPolynomial.C a)) = algebraMap A F a := by
  change coordinateLocalizationLift x hx
    (nodeLocalizationEmbedding c hc (Ideal.Quotient.mk _ (MvPolynomial.C a))) = _
  rw [nodeLocalizationEmbedding_C, coordinateLocalizationLift_algebraMap]
  simp

/-- The injective node evaluation respects the coefficient algebra. -/
def nodeEvaluationAlgHom {F : Type*} [Field F] [Algebra A F]
    (c : A) (hc : c ≠ 0) (x : F) (hx : x ≠ 0) : Node A c →ₐ[A] F where
  __ := nodeEvaluation c hc x hx
  commutes' a := nodeEvaluation_C c hc x hx a

/-- The first node coordinate is algebraically independent over the original coefficient ring. -/
theorem coordinate_aeval_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (coordinate c 0) : A[X] →ₐ[A] Node A c) := by
  let φ : A[X] →+* NodeDomain.CoefficientLocalization A :=
    (nodeLocalizationEmbedding c hc).comp (Polynomial.aeval (coordinate c 0)).toRingHom
  have hφ : φ = algebraMap A[X] (NodeDomain.CoefficientLocalization A) := by
    apply Polynomial.ringHom_ext
    · intro a
      change nodeLocalizationEmbedding c hc (Polynomial.aeval (coordinate c 0) (C a)) = _
      rw [Polynomial.aeval_C]
      exact nodeLocalizationEmbedding_C c hc a
    · change nodeLocalizationEmbedding c hc (Polynomial.aeval (coordinate c 0) X) = _
      rw [Polynomial.aeval_X]
      exact nodeLocalizationEmbedding_coordinate0 c hc
  intro P Q hPQ
  apply IsLocalization.injective (NodeDomain.CoefficientLocalization A)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero : (X : A[X]) ≠ 0))
  rw [← hφ]
  exact congrArg (nodeLocalizationEmbedding c hc) hPQ

omit [IsDomain A] in
/-- Membership of the two coordinate images implies membership of the entire node image. -/
theorem nodeHom_mem {B : Type*} [CommRing B] [Algebra A B] (c : A)
    (f : Node A c →ₐ[A] B) (S : Subalgebra A B)
    (h0 : f (coordinate c 0) ∈ S) (h1 : f (coordinate c 1) ∈ S) (r : Node A c) : f r ∈ S := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C a =>
    change f (algebraMap A (Node A c) a) ∈ S
    rw [AlgHom.commutes]
    exact S.algebraMap_mem a
  | add P Q hP hQ => simpa only [map_add] using S.add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, map_mul]
    apply S.mul_mem hP
    fin_cases i
    · exact h0
    · exact h1

omit [IsDomain A] in
/-- Interchanging the two actual node coordinates preserves their defining equation. -/
def nodeSwap (c : A) : Node A c ≃ₐ[A] Node A c :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv A (Equiv.swap (0 : Fin 2) 1)) (by
    rw [NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
    simp [MvPolynomial.renameEquiv_apply, mul_comm])

omit [IsDomain A] in
@[simp]
theorem nodeSwap_coordinate0 (c : A) : nodeSwap c (coordinate c 0) = coordinate c 1 := by
  simp [nodeSwap, coordinate, MvPolynomial.renameEquiv_apply]

omit [IsDomain A] in
@[simp]
theorem nodeSwap_coordinate1 (c : A) : nodeSwap c (coordinate c 1) = coordinate c 0 := by
  simp [nodeSwap, coordinate, MvPolynomial.renameEquiv_apply]

/-- The second node coordinate is also algebraically independent. -/
theorem coordinate1_aeval_injective (c : A) (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (coordinate c 1) : A[X] →ₐ[A] Node A c) := by
  have hcomp : (nodeSwap c).toAlgHom.comp (Polynomial.aeval (coordinate c 1)) =
      Polynomial.aeval (coordinate c 0) := by
    apply Polynomial.algHom_ext
    simp
  intro P Q hPQ
  apply coordinate_aeval_injective c hc
  rw [← hcomp]
  exact congrArg (nodeSwap c) hPQ

/-- The domain instance for the original node follows from nonzero parameters. -/
instance productNodeDomain (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    IsDomain (Node A (t * q)) :=
  NodeDomain.nodeQuotient_isDomain (t * q) (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0))

section UChart

variable (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)]

/-- The actual ideal of the center `(u,t)` in the original node ring. -/
def centerIdeal : Ideal (Node A (t * q)) :=
  Ideal.span {coordinate (t * q) 0, algebraMap A (Node A (t * q)) t}

/-- The nonzero original coordinate in the fraction field of the node. -/
def fractionCoordinate : FractionRing (Node A (t * q)) :=
  algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (coordinate (t * q) 0)

theorem fractionCoordinate_ne_zero : fractionCoordinate t q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (NodeDomain.nodeCoordinate_ne_zero (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 0)

theorem fractionCoordinate_aeval_injective :
    Function.Injective (Polynomial.aeval (fractionCoordinate t q) :
      A[X] →ₐ[A] FractionRing (Node A (t * q))) := by
  have hcomp : Polynomial.aeval (fractionCoordinate t q) =
      (IsScalarTower.toAlgHom A (Node A (t * q)) (FractionRing (Node A (t * q)))).comp
        (Polynomial.aeval (coordinate (t * q) 0)) := by
    apply Polynomial.algHom_ext
    simp [fractionCoordinate]
  rw [hcomp]
  exact (IsFractionRing.injective (Node A (t * q)) (FractionRing (Node A (t * q)))).comp
    (coordinate_aeval_injective (t * q)
    (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))

/-- The candidate chart maps to the actual original fraction field by `(u,w)=(u,t/u)`. -/
def uChartEvaluation : Node A t →ₐ[A] FractionRing (Node A (t * q)) :=
  nodeEvaluationAlgHom t (Fact.out : t ≠ 0) (fractionCoordinate t q)
    (fractionCoordinate_ne_zero t q)

theorem uChartEvaluation_injective : Function.Injective (uChartEvaluation t q) :=
  nodeEvaluation_injective t (Fact.out : t ≠ 0) (fractionCoordinate t q)
    (fractionCoordinate_ne_zero t q) (fractionCoordinate_aeval_injective t q)

@[simp]
theorem uChartEvaluation_coordinate0 :
    uChartEvaluation t q (coordinate t 0) = fractionCoordinate t q :=
  nodeEvaluation_coordinate0 _ _ _ _

@[simp]
theorem uChartEvaluation_coordinate1 :
    uChartEvaluation t q (coordinate t 1) =
      algebraMap A (FractionRing (Node A (t * q))) t / fractionCoordinate t q :=
  nodeEvaluation_coordinate1 _ _ _ _

/-- In the original fraction field the old coordinate is `v=w*q`. -/
theorem uChartEvaluation_old_coordinate1 :
    algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (coordinate (t * q) 1) =
      uChartEvaluation t q (coordinate t 1) * algebraMap A (FractionRing (Node A (t * q))) q := by
  apply mul_left_cancel₀ (fractionCoordinate_ne_zero t q)
  have hrel := congrArg (algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))))
    (NodeDomain.nodeCoordinateProduct (t * q))
  have hrel' : fractionCoordinate t q *
      algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (coordinate (t * q) 1) =
        algebraMap A (FractionRing (Node A (t * q))) t *
          algebraMap A (FractionRing (Node A (t * q))) q := by
    simpa only [fractionCoordinate, coordinate, map_mul, ← IsScalarTower.algebraMap_apply A (Node A (t * q))
      (FractionRing (Node A (t * q)))] using hrel
  rw [hrel', uChartEvaluation_coordinate1, ← mul_assoc,
    mul_comm (fractionCoordinate t q) (_ / _),
    div_mul_cancel₀ _ (fractionCoordinate_ne_zero t q)]

/-- The candidate image contains the entire original node algebra. -/
theorem original_mem_uChart_range (r : Node A (t * q)) :
    algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) r ∈
      (uChartEvaluation t q).range := by
  apply nodeHom_mem (t * q)
    (IsScalarTower.toAlgHom A (Node A (t * q)) (FractionRing (Node A (t * q))))
  · exact ⟨coordinate t 0, uChartEvaluation_coordinate0 t q⟩
  · rw [show IsScalarTower.toAlgHom A (Node A (t * q)) (FractionRing (Node A (t * q)))
        (coordinate (t * q) 1) =
      algebraMap (Node A (t * q)) (FractionRing (Node A (t * q)))
        (coordinate (t * q) 1) from rfl, uChartEvaluation_old_coordinate1]
    exact (uChartEvaluation t q).range.mul_mem
      ⟨coordinate t 1, rfl⟩ ((uChartEvaluation t q).range.algebraMap_mem q)

/-- Regard the same candidate image as an algebra over the original node. -/
def uChartRangeOverNode : Subalgebra (Node A (t * q)) (FractionRing (Node A (t * q))) where
  __ := (uChartEvaluation t q).range.toSubsemiring
  algebraMap_mem' := original_mem_uChart_range t q

/-- Every genuine ideal fraction lies in the candidate image. -/
theorem idealRatio_mem_uChart_range {a : Node A (t * q)} (ha : a ∈ centerIdeal t q) :
    algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) a /
      fractionCoordinate t q ∈ uChartRangeOverNode t q := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · change fractionCoordinate t q / fractionCoordinate t q ∈ _
      rw [div_self (fractionCoordinate_ne_zero t q)]
      exact (uChartRangeOverNode t q).one_mem
    · have heq : a = algebraMap A (Node A (t * q)) t := Set.mem_singleton_iff.mp ha
      rw [heq, ← IsScalarTower.algebraMap_apply A (Node A (t * q))
        (FractionRing (Node A (t * q)))]
      exact ⟨coordinate t 1, uChartEvaluation_coordinate1 t q⟩
  | zero => simp
  | add a b ha hb hia hib =>
    simpa only [map_add, add_div] using (uChartRangeOverNode t q).add_mem hia hib
  | smul r a ha hia =>
    change algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (r * a) / _ ∈ _
    rw [map_mul, mul_div_assoc]
    exact (uChartRangeOverNode t q).mul_mem ((uChartRangeOverNode t q).algebraMap_mem r) hia

/-- The range equality identifies the genuine fraction subalgebra, including saturation. -/
theorem uChartEvaluation_range : (uChartEvaluation t q).range =
    (affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem t (uChartEvaluation t q)
    · rw [uChartEvaluation_coordinate0]
      exact (affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)).algebraMap_mem _
    · rw [uChartEvaluation_coordinate1]
      change algebraMap (Node A (t * q)) (FractionRing (Node A (t * q)))
        (algebraMap A (Node A (t * q)) t) / fractionCoordinate t q ∈
        affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)
      have htmem : algebraMap A (Node A (t * q)) t ∈ centerIdeal t q :=
        Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      exact Algebra.subset_adjoin (R := Node A (t * q)) (Set.mem_range_self
        (⟨algebraMap A (Node A (t * q)) t, htmem⟩ : centerIdeal t q))
  · have hle : affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0) ≤
        uChartRangeOverNode t q := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      exact idealRatio_mem_uChart_range t q a.2
    exact hle

/-- The actual fraction chart of the blowup of `(u,t)` is the smaller node `uw=t`. -/
def uChartFractionEquiv : Node A t ≃ₐ[A]
    (affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)).restrictScalars A :=
  (AlgEquiv.ofInjective (uChartEvaluation t q) (uChartEvaluation_injective t q)).trans
    (Subalgebra.equivOfEq _ _ (uChartEvaluation_range t q))

@[simp]
theorem coe_uChartFractionEquiv (r : Node A t) :
    (uChartFractionEquiv t q r : FractionRing (Node A (t * q))) = uChartEvaluation t q r := rfl

@[simp]
theorem uChartFractionEquiv_coordinate0 :
    (uChartFractionEquiv t q (coordinate t 0) : FractionRing (Node A (t * q))) =
      fractionCoordinate t q := uChartEvaluation_coordinate0 t q

@[simp]
theorem uChartFractionEquiv_coordinate1 :
    (uChartFractionEquiv t q (coordinate t 1) : FractionRing (Node A (t * q))) =
      algebraMap A (FractionRing (Node A (t * q))) t / fractionCoordinate t q :=
  uChartEvaluation_coordinate1 t q

/-- The actual native Rees basic-open coordinate ring has the proved node presentation. -/
def uChartNativeEquiv :
    reesHomogeneousChart (centerIdeal t q) (coordinate (t * q) 0)
      (Ideal.subset_span (Set.mem_insert _ _)) ≃+* Node A t := by
  letI := reesHomogeneousChartAlgebra (centerIdeal t q) (coordinate (t * q) 0)
    (Ideal.subset_span (Set.mem_insert _ _))
  exact (reesChartFractionEquiv (centerIdeal t q) (coordinate (t * q) 0)
    (Ideal.subset_span (Set.mem_insert _ _))
    (NodeDomain.nodeCoordinate_ne_zero (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 0)).toRingEquiv.trans
    (uChartFractionEquiv t q).symm.toRingEquiv

/-- The original node algebra map into the actual chart, expressed in its smaller-node presentation. -/
def uChartOriginalMap : Node A (t * q) →ₐ[A] Node A t :=
  (uChartFractionEquiv t q).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A (Node A (t * q))
      (affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)))

@[simp]
theorem uChartEvaluation_originalMap (r : Node A (t * q)) :
    uChartEvaluation t q (uChartOriginalMap t q r) =
      algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) r := by
  change (uChartFractionEquiv t q ((uChartFractionEquiv t q).symm
    (algebraMap (Node A (t * q))
      (affineBlowupFractionChart (centerIdeal t q) (coordinate (t * q) 0)) r)) :
      FractionRing (Node A (t * q))) = _
  exact congrArg
    (fun x : (affineBlowupFractionChart (centerIdeal t q)
      (coordinate (t * q) 0)).restrictScalars A => (x : FractionRing (Node A (t * q))))
    ((uChartFractionEquiv t q).apply_symm_apply _)

@[simp]
theorem uChartOriginalMap_coordinate0 :
    uChartOriginalMap t q (coordinate (t * q) 0) = coordinate t 0 := by
  apply uChartEvaluation_injective t q
  rw [uChartEvaluation_originalMap, uChartEvaluation_coordinate0]
  rfl

@[simp]
theorem uChartOriginalMap_coordinate1 :
    uChartOriginalMap t q (coordinate (t * q) 1) =
      coordinate t 1 * algebraMap A (Node A t) q := by
  apply uChartEvaluation_injective t q
  rw [uChartEvaluation_originalMap, map_mul, AlgHom.commutes, uChartEvaluation_old_coordinate1]

/-- The genuine native coordinate-chart open is the spectrum of the smaller node. -/
def uChartSchemeIso :
    (affineBlowupChartOpen (centerIdeal t q) (coordinate (t * q) 0)
      (Ideal.subset_span (Set.mem_insert _ _))).toScheme ≅
        AlgebraicGeometry.Spec (CommRingCat.of (Node A t)) :=
  (affineBlowupChartIso (centerIdeal t q) (coordinate (t * q) 0)
    (Ideal.subset_span (Set.mem_insert _ _))
    (NodeDomain.nodeCoordinate_ne_zero (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 0)).trans
    (AlgebraicGeometry.Scheme.Spec.mapIso
      (uChartFractionEquiv t q).toRingEquiv.toCommRingCatIso.op)

/-- The smaller node is a genuine open chart of the native blowup. -/
def uChartInclusion : AlgebraicGeometry.Spec (CommRingCat.of (Node A t)) ⟶
    affineBlowup (centerIdeal t q) :=
  AlgebraicGeometry.Spec.map (uChartFractionEquiv t q).toRingEquiv.toCommRingCatIso.inv ≫
    affineBlowupChartInclusion (centerIdeal t q) (coordinate (t * q) 0)
      (Ideal.subset_span (Set.mem_insert _ _))
      (NodeDomain.nodeCoordinate_ne_zero (t * q)
        (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 0)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion obtained from the proved chart is an actual open immersion. -/
instance uChartInclusion_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (uChartInclusion t q) := by
  dsimp only [uChartInclusion]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The smaller-node presentation respects the actual blowup morphism to the original node. -/
theorem uChartInclusion_structure :
    uChartInclusion t q ≫ affineBlowupStructure (centerIdeal t q) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (uChartOriginalMap t q).toRingHom) := by
  dsimp only [uChartInclusion, centerIdeal]
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← AlgebraicGeometry.Spec.map_comp]
  congr 1

end UChart

section TChart

variable (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)]

/-- The second original node coordinate in its genuine fraction field. -/
def fractionCoordinate1 : FractionRing (Node A (t * q)) :=
  algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (coordinate (t * q) 1)

theorem fractionCoordinate1_ne_zero : fractionCoordinate1 t q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (NodeDomain.nodeCoordinate_ne_zero (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 1)

theorem fractionCoordinate1_aeval_injective :
    Function.Injective (Polynomial.aeval (fractionCoordinate1 t q) :
      A[X] →ₐ[A] FractionRing (Node A (t * q))) := by
  have hcomp : Polynomial.aeval (fractionCoordinate1 t q) =
      (IsScalarTower.toAlgHom A (Node A (t * q)) (FractionRing (Node A (t * q)))).comp
        (Polynomial.aeval (coordinate (t * q) 1)) := by
    apply Polynomial.algHom_ext
    simp [fractionCoordinate1]
  rw [hcomp]
  exact (IsFractionRing.injective (Node A (t * q)) (FractionRing (Node A (t * q)))).comp
    (coordinate1_aeval_injective (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))

/-- The candidate parameter chart is evaluated by `(v,z)=(v,q/v)`. -/
def tChartEvaluation : Node A q →ₐ[A] FractionRing (Node A (t * q)) :=
  nodeEvaluationAlgHom q (Fact.out : q ≠ 0) (fractionCoordinate1 t q)
    (fractionCoordinate1_ne_zero t q)

theorem tChartEvaluation_injective : Function.Injective (tChartEvaluation t q) :=
  nodeEvaluation_injective q (Fact.out : q ≠ 0) (fractionCoordinate1 t q)
    (fractionCoordinate1_ne_zero t q) (fractionCoordinate1_aeval_injective t q)

@[simp]
theorem tChartEvaluation_coordinate0 :
    tChartEvaluation t q (coordinate q 0) = fractionCoordinate1 t q :=
  nodeEvaluation_coordinate0 _ _ _ _

theorem fractionParameter_ne_zero :
    algebraMap A (FractionRing (Node A (t * q))) t ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply A (Node A (t * q)) (FractionRing (Node A (t * q)))]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    ((map_ne_zero_iff _ (NodeDomain.algebraMap_nodeQuotient_injective (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))).mpr (Fact.out : t ≠ 0))

/-- The genuine original relation identifies `q/v` with the ideal ratio `u/t`. -/
@[simp]
theorem tChartEvaluation_coordinate1 :
    tChartEvaluation t q (coordinate q 1) =
      fractionCoordinate t q / algebraMap A (FractionRing (Node A (t * q))) t := by
  rw [show tChartEvaluation t q (coordinate q 1) =
      algebraMap A (FractionRing (Node A (t * q))) q / fractionCoordinate1 t q from
        nodeEvaluation_coordinate1 _ _ _ _]
  apply (div_eq_div_iff (fractionCoordinate1_ne_zero t q) (fractionParameter_ne_zero t q)).mpr
  have hrel := congrArg (algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))))
    (NodeDomain.nodeCoordinateProduct (t * q))
  simpa only [fractionCoordinate, fractionCoordinate1, coordinate, map_mul,
    ← IsScalarTower.algebraMap_apply A (Node A (t * q)) (FractionRing (Node A (t * q))),
    mul_comm] using hrel.symm

/-- The original first coordinate is `u=t*z` in the parameter chart image. -/
theorem tChartEvaluation_old_coordinate0 :
    fractionCoordinate t q = algebraMap A (FractionRing (Node A (t * q))) t *
      tChartEvaluation t q (coordinate q 1) := by
  rw [tChartEvaluation_coordinate1, mul_comm _ (_ / _),
    div_mul_cancel₀ _ (fractionParameter_ne_zero t q)]

/-- The parameter chart image contains all original node coefficients. -/
theorem original_mem_tChart_range (r : Node A (t * q)) :
    algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) r ∈
      (tChartEvaluation t q).range := by
  apply nodeHom_mem (t * q)
    (IsScalarTower.toAlgHom A (Node A (t * q)) (FractionRing (Node A (t * q))))
  · change fractionCoordinate t q ∈ _
    rw [tChartEvaluation_old_coordinate0]
    exact (tChartEvaluation t q).range.mul_mem
      ((tChartEvaluation t q).range.algebraMap_mem t) ⟨coordinate q 1, rfl⟩
  · exact ⟨coordinate q 0, tChartEvaluation_coordinate0 t q⟩

/-- The parameter-chart image, regarded over the original node ring. -/
def tChartRangeOverNode : Subalgebra (Node A (t * q)) (FractionRing (Node A (t * q))) where
  __ := (tChartEvaluation t q).range.toSubsemiring
  algebraMap_mem' := original_mem_tChart_range t q

/-- Every actual fraction by the parameter belongs to the candidate image. -/
theorem idealRatio_mem_tChart_range {a : Node A (t * q)} (ha : a ∈ centerIdeal t q) :
    algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) a /
      algebraMap A (FractionRing (Node A (t * q))) t ∈ tChartRangeOverNode t q := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨coordinate q 1, tChartEvaluation_coordinate1 t q⟩
    · have heq : a = algebraMap A (Node A (t * q)) t := Set.mem_singleton_iff.mp ha
      rw [heq, ← IsScalarTower.algebraMap_apply A (Node A (t * q))
        (FractionRing (Node A (t * q))), div_self (fractionParameter_ne_zero t q)]
      exact (tChartRangeOverNode t q).one_mem
  | zero => simp
  | add a b ha hb hia hib =>
    simpa only [map_add, add_div] using (tChartRangeOverNode t q).add_mem hia hib
  | smul r a ha hia =>
    change algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) (r * a) / _ ∈ _
    rw [map_mul, mul_div_assoc]
    exact (tChartRangeOverNode t q).mul_mem ((tChartRangeOverNode t q).algebraMap_mem r) hia

/-- The actual fraction chart by `t` is exactly the image of the smaller node `vz=q`. -/
theorem tChartEvaluation_range : (tChartEvaluation t q).range =
    (affineBlowupFractionChart (centerIdeal t q)
      (algebraMap A (Node A (t * q)) t)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem q (tChartEvaluation t q)
    · rw [tChartEvaluation_coordinate0]
      exact (affineBlowupFractionChart (centerIdeal t q)
        (algebraMap A (Node A (t * q)) t)).algebraMap_mem _
    · rw [tChartEvaluation_coordinate1]
      change algebraMap (Node A (t * q)) (FractionRing (Node A (t * q)))
        (coordinate (t * q) 0) /
          algebraMap (Node A (t * q)) (FractionRing (Node A (t * q)))
            (algebraMap A (Node A (t * q)) t) ∈
              affineBlowupFractionChart (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      have humem : coordinate (t * q) 0 ∈ centerIdeal t q :=
        Ideal.subset_span (Set.mem_insert _ _)
      exact Algebra.subset_adjoin (R := Node A (t * q))
        (Set.mem_range_self (⟨coordinate (t * q) 0, humem⟩ : centerIdeal t q))
  · have hle : affineBlowupFractionChart (centerIdeal t q) (algebraMap A (Node A (t * q)) t) ≤
        tChartRangeOverNode t q := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      exact idealRatio_mem_tChart_range t q a.2
    exact hle

/-- The genuine parameter chart is the node algebra `A[v,z]/(vz-q)`. -/
def tChartFractionEquiv : Node A q ≃ₐ[A]
    (affineBlowupFractionChart (centerIdeal t q)
      (algebraMap A (Node A (t * q)) t)).restrictScalars A :=
  (AlgEquiv.ofInjective (tChartEvaluation t q) (tChartEvaluation_injective t q)).trans
    (Subalgebra.equivOfEq _ _ (tChartEvaluation_range t q))

@[simp]
theorem coe_tChartFractionEquiv (r : Node A q) :
    (tChartFractionEquiv t q r : FractionRing (Node A (t * q))) = tChartEvaluation t q r := rfl

/-- The original node map written in its genuine parameter-chart coordinates. -/
def tChartOriginalMap : Node A (t * q) →ₐ[A] Node A q :=
  (tChartFractionEquiv t q).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A (Node A (t * q))
      (affineBlowupFractionChart (centerIdeal t q) (algebraMap A (Node A (t * q)) t)))

@[simp]
theorem tChartEvaluation_originalMap (r : Node A (t * q)) :
    tChartEvaluation t q (tChartOriginalMap t q r) =
      algebraMap (Node A (t * q)) (FractionRing (Node A (t * q))) r := by
  change (tChartFractionEquiv t q ((tChartFractionEquiv t q).symm
    (algebraMap (Node A (t * q))
      (affineBlowupFractionChart (centerIdeal t q) (algebraMap A (Node A (t * q)) t)) r)) :
      FractionRing (Node A (t * q))) = _
  exact congrArg
    (fun x : (affineBlowupFractionChart (centerIdeal t q)
      (algebraMap A (Node A (t * q)) t)).restrictScalars A =>
        (x : FractionRing (Node A (t * q))))
    ((tChartFractionEquiv t q).apply_symm_apply _)

@[simp]
theorem tChartOriginalMap_coordinate0 :
    tChartOriginalMap t q (coordinate (t * q) 0) =
      algebraMap A (Node A q) t * coordinate q 1 := by
  apply tChartEvaluation_injective t q
  rw [tChartEvaluation_originalMap, map_mul, AlgHom.commutes]
  exact tChartEvaluation_old_coordinate0 t q

@[simp]
theorem tChartOriginalMap_coordinate1 :
    tChartOriginalMap t q (coordinate (t * q) 1) = coordinate q 0 := by
  apply tChartEvaluation_injective t q
  rw [tChartEvaluation_originalMap, tChartEvaluation_coordinate0]
  rfl

/-- The actual parameter-chart localization has its genuine smaller-node presentation. -/
def tChartNativeEquiv :
    reesHomogeneousChart (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) ≃+* Node A q := by
  letI := reesHomogeneousChartAlgebra (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact (reesChartFractionEquiv (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    ((map_ne_zero_iff _ (NodeDomain.algebraMap_nodeQuotient_injective (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))).mpr (Fact.out : t ≠ 0))).toRingEquiv.trans
    (tChartFractionEquiv t q).symm.toRingEquiv

/-- The actual native parameter-chart open is the spectrum of the node `vz=q`. -/
def tChartSchemeIso :
    (affineBlowupChartOpen (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))).toScheme ≅
        AlgebraicGeometry.Spec (CommRingCat.of (Node A q)) :=
  (affineBlowupChartIso (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    ((map_ne_zero_iff _ (NodeDomain.algebraMap_nodeQuotient_injective (t * q)
      (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))).mpr (Fact.out : t ≠ 0))).trans
    (AlgebraicGeometry.Scheme.Spec.mapIso
      (tChartFractionEquiv t q).toRingEquiv.toCommRingCatIso.op)

omit [IsDomain A] [Fact (t ≠ 0)] [Fact (q ≠ 0)] in
/-- The literal parameter-chart quotient used by the elimination identities is this same node. -/
def tPresentationNodeEquiv :
    (MvPolynomial (Fin 2) A ⧸ NodeChart.tChartIdeal A q) ≃ₐ[A] Node A q :=
  Ideal.quotientEquivAlgOfEq A (by simp [NodeChart.tChartIdeal, NodeChart.uChartIdeal, mul_comm])

/-- Compatibility with the exact two-variable quotient used in the source elimination identity. -/
def tChartLiteralFractionEquiv :
    (MvPolynomial (Fin 2) A ⧸ NodeChart.tChartIdeal A q) ≃ₐ[A]
      (affineBlowupFractionChart (centerIdeal t q)
        (algebraMap A (Node A (t * q)) t)).restrictScalars A :=
  (tPresentationNodeEquiv q).trans (tChartFractionEquiv t q)

/-- The parameter-node presentation gives a genuine open chart of the native blowup. -/
def tChartInclusion : AlgebraicGeometry.Spec (CommRingCat.of (Node A q)) ⟶
    affineBlowup (centerIdeal t q) :=
  AlgebraicGeometry.Spec.map (tChartFractionEquiv t q).toRingEquiv.toCommRingCatIso.inv ≫
    affineBlowupChartInclusion (centerIdeal t q) (algebraMap A (Node A (t * q)) t)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      ((map_ne_zero_iff _ (NodeDomain.algebraMap_nodeQuotient_injective (t * q)
        (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)))).mpr (Fact.out : t ≠ 0))

set_option backward.isDefEq.respectTransparency false in
/-- The parameter-chart inclusion is an actual open immersion. -/
instance tChartInclusion_isOpenImmersion : AlgebraicGeometry.IsOpenImmersion (tChartInclusion t q) := by
  dsimp only [tChartInclusion]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The actual parameter-chart open respects the original node structure map. -/
theorem tChartInclusion_structure :
    tChartInclusion t q ≫ affineBlowupStructure (centerIdeal t q) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (tChartOriginalMap t q).toRingHom) := by
  dsimp only [tChartInclusion, centerIdeal]
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← AlgebraicGeometry.Spec.map_comp]
  congr 1

end TChart

end DeJongAlterations.Algebra.NodeBlowupChart

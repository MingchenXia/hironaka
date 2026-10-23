import DeJongAlterations.StableModification.Blowups.NodeChart

/-!
# The blow-up of a smooth chart over a domain

Let `A` be a domain (in Temkin's application a valuation ring `R`), `π ∈ A` nonzero and
`a ∈ A`. We study the blow-up of the smooth standard model `Spec A[T]` along the ideal
`(π, T - a)` (`smoothCenter π a`). This is the second stage of M. Temkin, *Stable modification
of relative curves*, proof of Prop 4.3.1 (T:2992–3016), and the separation step of Lemma 4.3.2
(T:3027–3030): `Bl_{(π_a, T-a)}(Spec A[T])` is covered by the charts

* `A[T][(T-a)/π] ≅ A[S]`, `S ↦ (T-a)/π` (`smoothParamChartEquiv`, the `π`-chart, which lies over
  `Spec A` as the smooth model `smoothModel A`), and
* `A[T][π/(T-a)] ≅ A[u,w]/(uw - π)`, `u ↦ T - a`, `w ↦ π/(T-a)` (`smoothCoordChartEquiv`, the
  `(T-a)`-chart, lying over `Spec A` as the node model `nodeModel π`);

hence it is strictly semi-stable (`smoothBlowup_isStrictlySemistable`), a modification
(`smoothBlowup_isModification`) and an isomorphism off `V(π, T - a)`
(`smoothBlowup_isIso`); the locus `V(π, T - a)` is the image of a closed subscheme of `Spec A`
contained in `V(π)` (`smoothLocus`, `isClosedImmersion_smoothLocus_comp`), so over a local `A` its
only closed point is the point `T = a` of the closed fibre.

This is `lem:sm-blowup-smooth-chart` of the blueprint chapter `sm-blowups-valuation.tex`. The
identification of the exceptional fibre with `ℙ¹` stated there is not formalized here; the
consumer only needs the explicit coordinate `S = (T-a)/π` of the `π`-chart.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A] (π a : A) [Fact (π ≠ 0)]

/-- The centre `(π, T - a)` of `A[T]`. -/
def smoothCenter : Ideal A[X] := Ideal.span {C π, X - C a}

omit [IsDomain A] [Fact (π ≠ 0)] in
theorem C_mem_smoothCenter : C π ∈ smoothCenter π a := Ideal.subset_span (Set.mem_insert _ _)

omit [IsDomain A] [Fact (π ≠ 0)] in
theorem X_sub_C_mem_smoothCenter : X - C a ∈ smoothCenter π a :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

omit [IsDomain A] [Fact (π ≠ 0)] in
theorem smoothCenter_fg : (smoothCenter π a).FG :=
  Submodule.fg_span ((Set.finite_singleton _).insert _)

omit [IsDomain A] in
theorem smoothCenter_C_ne_zero : (C π : A[X]) ≠ 0 := C_ne_zero.mpr Fact.out

omit [Fact (π ≠ 0)] in
theorem smoothCenter_X_sub_C_ne_zero : (X - C a : A[X]) ≠ 0 := X_sub_C_ne_zero a

omit [IsDomain A] in
theorem smoothCenter_ne_bot : smoothCenter π a ≠ ⊥ := by
  intro h
  have hmem := C_mem_smoothCenter π a
  rw [h, Ideal.mem_bot] at hmem
  exact smoothCenter_C_ne_zero π hmem

/-- **The blow-up of the smooth chart is a modification.** -/
theorem smoothBlowup_isModification : IsModification (affineBlowupStructure (smoothCenter π a)) :=
  isModification_affineBlowupStructure _ (smoothCenter_ne_bot π a) (smoothCenter_fg π a)

/-- The structure morphism `Bl_{(π, T-a)} Spec A[T] ⟶ Spec A`. -/
def smoothBlowupMorphism : affineBlowup (smoothCenter π a) ⟶ Spec (.of A) :=
  affineBlowupStructure (smoothCenter π a) ≫ smoothModel A

section Fractions

local notation "F" => FractionRing A[X]

omit [IsDomain A] [Fact (π ≠ 0)] in
theorem algebraMap_polynomial_injective : Function.Injective (algebraMap A[X] F) :=
  IsFractionRing.injective A[X] F

omit [Fact (π ≠ 0)] in
/-- The image of `T - a` in the fraction field. -/
theorem algebraMap_X_sub_C_ne_zero : algebraMap A[X] F (X - C a) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap_polynomial_injective)).mpr (smoothCenter_X_sub_C_ne_zero a)

omit [IsDomain A] in
theorem algebraMap_C_ne_zero : algebraMap A[X] F (C π) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap_polynomial_injective)).mpr (smoothCenter_C_ne_zero π)

omit [IsDomain A] [Fact (π ≠ 0)] in
theorem algebraMap_C_eq : algebraMap A[X] F (C π) = algebraMap A F π := by
  rw [IsScalarTower.algebraMap_apply A A[X] F, Polynomial.algebraMap_apply]
  simp

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- Evaluating a polynomial at the image of `T` in `F` is the image of the polynomial. -/
theorem aeval_algebraMap_X (p : A[X]) :
    Polynomial.aeval (algebraMap A[X] F X) p = algebraMap A[X] F p := by
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A A[X] F) X p
  rw [Polynomial.aeval_X_left_apply] at h
  exact h

/-- The coordinate `(T - a)/π` of the `π`-chart. -/
def smoothParamCoordinate : F := algebraMap A[X] F (X - C a) / algebraMap A[X] F (C π)

theorem algebraMap_C_mul_smoothParamCoordinate :
    algebraMap A F π * smoothParamCoordinate π a = algebraMap A[X] F (X - C a) := by
  rw [smoothParamCoordinate, ← algebraMap_C_eq, mul_div_cancel₀ _ (algebraMap_C_ne_zero π)]

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- The Taylor shift `p ↦ p(T - a)` is injective. -/
theorem aeval_X_sub_C_injective :
    Function.Injective (Polynomial.aeval (X - C a) : A[X] →ₐ[A] A[X]) := by
  have h : (Polynomial.aeval (X - C a) : A[X] →ₐ[A] A[X]) = (taylorEquiv (-a)).toAlgHom := by
    apply Polynomial.algHom_ext
    change aeval (X - C a) X = taylor (-a) X
    rw [aeval_X, taylor_X, map_neg, ← sub_eq_add_neg]
  rw [h]
  exact (taylorEquiv (-a)).injective

/-- **The coordinate `(T - a)/π` is transcendental**: `S ↦ (T - a)/π` is injective on `A[S]`. -/
theorem aeval_smoothParamCoordinate_injective :
    Function.Injective (Polynomial.aeval (smoothParamCoordinate π a) : A[X] →ₐ[A] F) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h := Polynomial.scaleRoots_aeval_eq_zero (r := π) hp
  rw [algebraMap_C_mul_smoothParamCoordinate] at h
  change aeval ((IsScalarTower.toAlgHom A A[X] F) (X - C a)) (p.scaleRoots π) = 0 at h
  rw [Polynomial.aeval_algHom_apply] at h
  change algebraMap A[X] F (aeval (X - C a) (p.scaleRoots π)) = 0 at h
  rw [map_eq_zero_iff _ algebraMap_polynomial_injective] at h
  have h2 : p.scaleRoots π = 0 := (aeval_X_sub_C_injective a) (h.trans (map_zero _).symm)
  by_contra hp0
  exact Polynomial.scaleRoots_ne_zero hp0 π h2

/-- The image of `T` is `π·S + a` in the `π`-chart coordinate. -/
theorem algebraMap_X_eq_param :
    algebraMap A[X] F X =
      Polynomial.aeval (smoothParamCoordinate π a) (C π * X + C a) := by
  rw [map_add, map_mul, aeval_C, aeval_X, aeval_C, algebraMap_C_mul_smoothParamCoordinate,
    map_sub, ← algebraMap_C_eq, sub_add_cancel]

/-- The `π`-chart evaluation `A[S] ⟶ F`, `S ↦ (T - a)/π`. -/
def smoothParamChartEval : A[X] →ₐ[A] F := Polynomial.aeval (smoothParamCoordinate π a)

/-- Polynomials in `T` lie in the image of the `π`-chart evaluation. -/
theorem algebraMap_mem_smoothParamChartEval_range (p : A[X]) :
    algebraMap A[X] F p ∈ (smoothParamChartEval π a).range := by
  refine ⟨p.comp (C π * X + C a), ?_⟩
  change aeval (smoothParamCoordinate π a) (p.comp (C π * X + C a)) = _
  rw [aeval_comp, ← algebraMap_X_eq_param, aeval_algebraMap_X]

/-- The `π`-chart evaluation image, as an `A[T]`-subalgebra. -/
def smoothParamRangeOverPolynomial : Subalgebra A[X] F where
  __ := (smoothParamChartEval π a).range.toSubsemiring
  algebraMap_mem' := algebraMap_mem_smoothParamChartEval_range π a

/-- The fraction chart `A[T][(T-a)/π]` is the image of `A[S]`. -/
theorem smoothParamChartEval_range : (smoothParamChartEval π a).range =
    (affineBlowupFractionChart (smoothCenter π a) (C π)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    have hy : smoothParamCoordinate π a ∈
        affineBlowupFractionChart (smoothCenter π a) (C π) :=
      Algebra.subset_adjoin (Set.mem_range_self
        (⟨X - C a, X_sub_C_mem_smoothCenter π a⟩ : smoothCenter π a))
    have hy' : smoothParamCoordinate π a ∈
        (affineBlowupFractionChart (smoothCenter π a) (C π)).restrictScalars A := hy
    change aeval (smoothParamCoordinate π a) p ∈
      ((affineBlowupFractionChart (smoothCenter π a) (C π)).restrictScalars A)
    rw [← Polynomial.aeval_subalgebra_coe p _ ⟨_, hy'⟩]
    exact SetLike.coe_mem _
  · have hle : affineBlowupFractionChart (smoothCenter π a) (C π) ≤
        smoothParamRangeOverPolynomial π a := by
      apply Algebra.adjoin_le
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      obtain ⟨x, z, rfl⟩ := Ideal.mem_span_pair.mp hj
      change algebraMap A[X] F (x * C π + z * (X - C a)) / algebraMap A[X] F (C π) ∈
        (smoothParamChartEval π a).range
      have heq : algebraMap A[X] F (x * C π + z * (X - C a)) / algebraMap A[X] F (C π) =
          algebraMap A[X] F x + algebraMap A[X] F z * smoothParamCoordinate π a := by
        rw [map_add, map_mul, map_mul, add_div, mul_div_assoc,
          div_self (algebraMap_C_ne_zero π), mul_one, smoothParamCoordinate, mul_div_assoc]
      rw [heq]
      exact Subalgebra.add_mem _ (algebraMap_mem_smoothParamChartEval_range π a x)
        (Subalgebra.mul_mem _ (algebraMap_mem_smoothParamChartEval_range π a z)
          ⟨X, aeval_X _⟩)
    exact hle

/-- **The `π`-chart is a polynomial ring**: `A[S] ≃ A[T][(T-a)/π]`, `S ↦ (T - a)/π`. -/
def smoothParamChartEquiv : A[X] ≃ₐ[A]
    (affineBlowupFractionChart (smoothCenter π a) (C π)).restrictScalars A :=
  (AlgEquiv.ofInjective (smoothParamChartEval π a) (aeval_smoothParamCoordinate_injective π a)).trans
    (Subalgebra.equivOfEq _ _ (smoothParamChartEval_range π a))

@[simp]
theorem coe_smoothParamChartEquiv (p : A[X]) :
    (smoothParamChartEquiv π a p : F) = aeval (smoothParamCoordinate π a) p := rfl

/-- The `(T - a)`-chart evaluation `A[u,w]/(uw - π) ⟶ F`, `u ↦ T - a`, `w ↦ π/(T - a)`. -/
def smoothCoordChartEval : Node A π →ₐ[A] F :=
  nodeEvaluationAlgHom π Fact.out (algebraMap A[X] F (X - C a)) (algebraMap_X_sub_C_ne_zero a)

omit [IsDomain A] in
theorem aeval_algebraMap_X_sub_C_injective :
    Function.Injective (Polynomial.aeval (algebraMap A[X] F (X - C a)) : A[X] →ₐ[A] F) := by
  have h : (Polynomial.aeval (algebraMap A[X] F (X - C a)) : A[X] →ₐ[A] F) =
      (IsScalarTower.toAlgHom A A[X] F).comp (Polynomial.aeval (X - C a)) := by
    apply Polynomial.algHom_ext
    simp
  rw [h]
  exact algebraMap_polynomial_injective.comp (aeval_X_sub_C_injective a)

theorem smoothCoordChartEval_injective : Function.Injective (smoothCoordChartEval π a) :=
  nodeEvaluation_injective π Fact.out _ (algebraMap_X_sub_C_ne_zero a)
    (aeval_algebraMap_X_sub_C_injective a)

@[simp]
theorem smoothCoordChartEval_coordinate0 :
    smoothCoordChartEval π a (coordinate π 0) = algebraMap A[X] F (X - C a) :=
  nodeEvaluation_coordinate0 _ _ _ _

@[simp]
theorem smoothCoordChartEval_coordinate1 :
    smoothCoordChartEval π a (coordinate π 1) =
      algebraMap A F π / algebraMap A[X] F (X - C a) :=
  nodeEvaluation_coordinate1 _ _ _ _

/-- Polynomials in `T` lie in the image of the `(T - a)`-chart evaluation. -/
theorem algebraMap_mem_smoothCoordChartEval_range (p : A[X]) :
    algebraMap A[X] F p ∈ (smoothCoordChartEval π a).range := by
  have h : smoothCoordChartEval π a (coordinate π 0 + algebraMap A (Node A π) a) =
      algebraMap A[X] F X := by
    rw [map_add, smoothCoordChartEval_coordinate0, AlgHom.commutes, map_sub,
      IsScalarTower.algebraMap_apply A A[X] F a, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, sub_add_cancel]
  refine ⟨aeval (coordinate π 0 + algebraMap A (Node A π) a) p, ?_⟩
  change smoothCoordChartEval π a (aeval (coordinate π 0 + algebraMap A (Node A π) a) p) = _
  rw [← Polynomial.aeval_algHom_apply, h, aeval_algebraMap_X]

/-- The `(T - a)`-chart evaluation image, as an `A[T]`-subalgebra. -/
def smoothCoordRangeOverPolynomial : Subalgebra A[X] F where
  __ := (smoothCoordChartEval π a).range.toSubsemiring
  algebraMap_mem' := algebraMap_mem_smoothCoordChartEval_range π a

/-- The fraction chart `A[T][π/(T-a)]` is the image of the node `A[u,w]/(uw - π)`. -/
theorem smoothCoordChartEval_range : (smoothCoordChartEval π a).range =
    (affineBlowupFractionChart (smoothCenter π a) (X - C a)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem π (smoothCoordChartEval π a)
    · rw [smoothCoordChartEval_coordinate0]
      exact (affineBlowupFractionChart (smoothCenter π a) (X - C a)).algebraMap_mem _
    · rw [smoothCoordChartEval_coordinate1, ← algebraMap_C_eq]
      have hmem : algebraMap A[X] F (C π) / algebraMap A[X] F (X - C a) ∈
          affineBlowupFractionChart (smoothCenter π a) (X - C a) :=
        Algebra.subset_adjoin (Set.mem_range_self
          (⟨C π, C_mem_smoothCenter π a⟩ : smoothCenter π a))
      exact hmem
  · have hle : affineBlowupFractionChart (smoothCenter π a) (X - C a) ≤
        smoothCoordRangeOverPolynomial π a := by
      apply Algebra.adjoin_le
      rintro _ ⟨⟨j, hj⟩, rfl⟩
      obtain ⟨x, z, rfl⟩ := Ideal.mem_span_pair.mp hj
      change algebraMap A[X] F (x * C π + z * (X - C a)) / algebraMap A[X] F (X - C a) ∈
        (smoothCoordChartEval π a).range
      have heq : algebraMap A[X] F (x * C π + z * (X - C a)) / algebraMap A[X] F (X - C a) =
          algebraMap A[X] F x * smoothCoordChartEval π a (coordinate π 1) +
            algebraMap A[X] F z := by
        rw [smoothCoordChartEval_coordinate1, ← algebraMap_C_eq, map_add, map_mul, map_mul,
          add_div, mul_div_assoc, mul_div_assoc, div_self (algebraMap_X_sub_C_ne_zero a), mul_one]
      rw [heq]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _
        (algebraMap_mem_smoothCoordChartEval_range π a x) ⟨coordinate π 1, rfl⟩)
        (algebraMap_mem_smoothCoordChartEval_range π a z)
    exact hle

/-- **The `(T - a)`-chart is a node**: `A[u,w]/(uw - π) ≃ A[T][π/(T-a)]`. -/
def smoothCoordChartEquiv : Node A π ≃ₐ[A]
    (affineBlowupFractionChart (smoothCenter π a) (X - C a)).restrictScalars A :=
  (AlgEquiv.ofInjective (smoothCoordChartEval π a) (smoothCoordChartEval_injective π a)).trans
    (Subalgebra.equivOfEq _ _ (smoothCoordChartEval_range π a))

@[simp]
theorem coe_smoothCoordChartEquiv (r : Node A π) :
    (smoothCoordChartEquiv π a r : F) = smoothCoordChartEval π a r := rfl

end Fractions

section Charts

/-- The original coordinate ring mapped to the `π`-chart, in the coordinate `S`: `T ↦ πS + a`. -/
def smoothParamOriginalMap : A[X] →ₐ[A] A[X] :=
  (smoothParamChartEquiv π a).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A A[X] (affineBlowupFractionChart (smoothCenter π a) (C π)))

/-- The `π`-chart `Spec A[S]` as an open of the blow-up. -/
def smoothParamChartInclusion : Spec (.of A[X]) ⟶ affineBlowup (smoothCenter π a) :=
  Spec.map (smoothParamChartEquiv π a).toRingEquiv.toCommRingCatIso.inv ≫
    affineBlowupChartInclusion (smoothCenter π a) (C π) (C_mem_smoothCenter π a)
      (smoothCenter_C_ne_zero π)

instance : IsOpenImmersion (smoothParamChartInclusion π a) := by
  dsimp only [smoothParamChartInclusion]
  infer_instance

theorem smoothParamChartInclusion_structure :
    smoothParamChartInclusion π a ≫ affineBlowupStructure (smoothCenter π a) =
      Spec.map (CommRingCat.ofHom (smoothParamOriginalMap π a).toRingHom) := by
  dsimp only [smoothParamChartInclusion]
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← Spec.map_comp]
  congr 1

/-- The original coordinate ring mapped to the `(T - a)`-chart: `T ↦ u + a`. -/
def smoothCoordOriginalMap : A[X] →ₐ[A] Node A π :=
  (smoothCoordChartEquiv π a).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A A[X] (affineBlowupFractionChart (smoothCenter π a) (X - C a)))

/-- The `(T - a)`-chart `Spec A[u,w]/(uw - π)` as an open of the blow-up. -/
def smoothCoordChartInclusion : Spec (.of (Node A π)) ⟶ affineBlowup (smoothCenter π a) :=
  Spec.map (smoothCoordChartEquiv π a).toRingEquiv.toCommRingCatIso.inv ≫
    affineBlowupChartInclusion (smoothCenter π a) (X - C a) (X_sub_C_mem_smoothCenter π a)
      (smoothCenter_X_sub_C_ne_zero a)

instance : IsOpenImmersion (smoothCoordChartInclusion π a) := by
  dsimp only [smoothCoordChartInclusion]
  infer_instance

theorem smoothCoordChartInclusion_structure :
    smoothCoordChartInclusion π a ≫ affineBlowupStructure (smoothCenter π a) =
      Spec.map (CommRingCat.ofHom (smoothCoordOriginalMap π a).toRingHom) := by
  dsimp only [smoothCoordChartInclusion]
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← Spec.map_comp]
  congr 1

/-- The `π`-chart lies over `Spec A` as the smooth model. -/
theorem smoothParamChartInclusion_smoothBlowupMorphism :
    smoothParamChartInclusion π a ≫ smoothBlowupMorphism π a = smoothModel A := by
  rw [smoothBlowupMorphism, ← Category.assoc, smoothParamChartInclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c : 2
  exact (smoothParamOriginalMap π a).commutes c

/-- The `(T - a)`-chart lies over `Spec A` as the node model `nodeModel π`. -/
theorem smoothCoordChartInclusion_smoothBlowupMorphism :
    smoothCoordChartInclusion π a ≫ smoothBlowupMorphism π a = nodeModel π := by
  rw [smoothBlowupMorphism, ← Category.assoc, smoothCoordChartInclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext c : 2
  exact (smoothCoordOriginalMap π a).commutes c

/-- The two charts cover the blow-up. -/
theorem smoothChartInclusions_sup_opensRange :
    (smoothParamChartInclusion π a).opensRange ⊔ (smoothCoordChartInclusion π a).opensRange = ⊤ := by
  have h1 : (smoothParamChartInclusion π a).opensRange =
      affineBlowupChartOpen (smoothCenter π a) (C π) (C_mem_smoothCenter π a) := by
    dsimp only [smoothParamChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso, affineBlowupFractionChartInclusion_opensRange]
  have h2 : (smoothCoordChartInclusion π a).opensRange =
      affineBlowupChartOpen (smoothCenter π a) (X - C a) (X_sub_C_mem_smoothCenter π a) := by
    dsimp only [smoothCoordChartInclusion]
    rw [Scheme.Hom.opensRange_comp_of_isIso, affineBlowupFractionChartInclusion_opensRange]
  rw [h1, h2]
  exact affineBlowupChartOpen_sup_of_span_pair (smoothCenter π a) (C π) (X - C a) rfl

/-- **The blow-up of the smooth chart is strictly semi-stable** (without marks). -/
theorem smoothBlowup_isStrictlySemistable :
    IsStrictlySemistable (smoothBlowupMorphism π a) ⊤ := by
  refine IsStrictlySemistable.of_openCover fun x => ?_
  have hx : x ∈ (smoothParamChartInclusion π a).opensRange ⊔
      (smoothCoordChartInclusion π a).opensRange := by
    rw [smoothChartInclusions_sup_opensRange]
    trivial
  rcases hx with hp | hc
  · refine ⟨_, hp, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [smoothParamChartInclusion_smoothBlowupMorphism]
    exact isStrictlySemistable_smoothModel A
  · refine ⟨_, hc, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [smoothCoordChartInclusion_smoothBlowupMorphism]
    exact isStrictlySemistable_nodeModel π

end Charts

section Locus

omit [Fact (π ≠ 0)] in
/-- **The blow-up of the smooth chart is an isomorphism off `V(π, T - a)`.** -/
theorem smoothBlowup_isIso :
    IsIso (affineBlowupStructure (smoothCenter π a) ∣_
      affineBlowupCenterComplement (smoothCenter π a)) :=
  affineBlowupStructure_centerComplement_isIso _

/-- The closed immersion of `V(π, T - a) = Spec A[T]/(π, T - a)` into the smooth chart. -/
def smoothLocus : Spec (.of (A[X] ⧸ smoothCenter π a)) ⟶ Spec (.of A[X]) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

omit [IsDomain A] [Fact (π ≠ 0)] in
instance isClosedImmersion_smoothLocus : IsClosedImmersion (smoothLocus π a) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- The locus `V(π, T - a)` is the complement of the open where the blow-up is an isomorphism. -/
theorem range_smoothLocus :
    Set.range (smoothLocus π a) =
      ((affineBlowupCenterComplement (smoothCenter π a) : Set (Spec (.of A[X]))))ᶜ := by
  have h : Set.range (smoothLocus π a) =
      Set.range (PrimeSpectrum.comap (S := A[X] ⧸ smoothCenter π a)
        (Ideal.Quotient.mk (smoothCenter π a))) := rfl
  rw [h, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext x
  simp [affineBlowupCenterComplement]

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- The coefficient map `A ⟶ A[T]/(π, T - a)` is surjective. -/
theorem algebraMap_smoothLocus_surjective :
    Function.Surjective (algebraMap A (A[X] ⧸ smoothCenter π a) : A →+* A[X] ⧸ smoothCenter π a) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hX : Ideal.Quotient.mk (smoothCenter π a) X =
      algebraMap A (A[X] ⧸ smoothCenter π a) a := by
    change Ideal.Quotient.mk (smoothCenter π a) X = Ideal.Quotient.mk (smoothCenter π a) (C a)
    exact Ideal.Quotient.eq.mpr (X_sub_C_mem_smoothCenter π a)
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, rfl⟩
  | add p q hp hq =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hq
    exact ⟨c + d, by rw [map_add, hc, hd, map_add]⟩
  | monomial n c hp =>
    obtain ⟨d, hd⟩ := hp
    refine ⟨d * a, ?_⟩
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, hd, hX]

/-- **The locus `V(π, T - a)` is a closed subscheme of the base**: the composite
`V(π, T - a) ⟶ Spec A[T] ⟶ Spec A` is a closed immersion. -/
instance isClosedImmersion_smoothLocus_comp :
    IsClosedImmersion (smoothLocus π a ≫ smoothModel A) := by
  have h : smoothLocus π a ≫ smoothModel A =
      Spec.map (CommRingCat.ofHom (algebraMap A (A[X] ⧸ smoothCenter π a))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  rw [h]
  exact IsClosedImmersion.spec_of_surjective _ (algebraMap_smoothLocus_surjective π a)

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- The image of `V(π, T - a)` in `Spec A` lies in `V(π)`. -/
theorem range_smoothLocus_comp_subset :
    Set.range (smoothLocus π a ≫ smoothModel A) ⊆ PrimeSpectrum.zeroLocus {π} := by
  rintro _ ⟨y, rfl⟩
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  have : (Ideal.Quotient.mk (smoothCenter π a)) (algebraMap A A[X] π) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact C_mem_smoothCenter π a
  change (Ideal.Quotient.mk (smoothCenter π a)) (algebraMap A A[X] π) ∈ y.asIdeal
  rw [this]
  exact y.asIdeal.zero_mem

end Locus

end DeJongAlterations.StableModification.Blowups

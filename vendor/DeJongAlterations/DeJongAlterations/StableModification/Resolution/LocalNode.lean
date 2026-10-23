import DeJongAlterations.StableModification.Resolution.LocalMonomial
import DeJongAlterations.Algebra.NodeFlatPresentation
import DeJongAlterations.Algebra.NodeSingularQuotient
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Monomial normal forms of completed nodes over a normal crossings base

This file is the commutative algebra of de Jong's local description of a semi-stable curve
`f : X → S` over a regular base with a strict normal crossings divisor `D`, smooth over `S ∖ D`
(de Jong 1996, 3.3 and 3.5, `references/dejong96-alterations/tex/page-0014.tex`,
`page-0015.tex`; consumed in 4.24–4.25, `page-0026.tex`).

At a singular point `x` of `f` over `s`, the complete local ring is `B ≅ A'[[u,v]]/(Q - h)`
(de Jong 2.23), where `A'` is finite étale over `A = Ô_{S,s}` and `Q` is a quadratic form with
unit discriminant. The trace of `Sing(f)` on `Spec B` is cut out by the coordinate ideal `(u,v)`
and maps isomorphically onto `V(h) ⊆ Spec A'`; since `f` is smooth over `S ∖ D`,
`V(h) ⊆ V(t_1 ⋯ t_r)`, so `h = ε t_1^{n_1} ⋯ t_r^{n_r}`, and replacing `Q` by `ε⁻¹ Q`,
`B ≅ A'[[u,v]]/(Q - t_1^{n_1} ⋯ t_r^{n_r})`. In the split case `Q = uv`, and the unit is absorbed
by the substitution `u ↦ ε u`.

## Main definitions

* `SplitNodeRing A h`: the split node ring `A[[u,v]]/(uv - h)`, literally the target of Codex's
  `Algebra.NodeFlatPresentation.exists_split_normal_form`.
* `splitCoordinateIdeal A h`: the coordinate ideal `(u, v)`, the trace of the singular locus.
* `splitNodeEvaluation A h`: the evaluation `A[[u,v]]/(uv - h) → A/(h)` at `u = v = 0`, whose
  kernel is the coordinate ideal (`splitNodeEvaluation_kernel`).
* `splitNodeUnitEquiv A ε g`: `A[[u,v]]/(uv - εg) ≃ A[[u,v]]/(uv - g)`, `u ↦ ε u`.
* `Quadratic.unitScale`: a quadratic form multiplied by a unit, and `nodeUnitEquiv`, the identity
  `A[[u,v]]/(Q - εg) = A[[u,v]]/(ε⁻¹Q - g)`.

## Main results

* `exists_node_monomial_normal_form` (de Jong 3.3, nonsplit form): if `h ∈ 𝔪_A`, the `t_i` are
  prime and `t_1 ⋯ t_r` lies in the radical of the coordinate ideal of `A[[u,v]]/(Q - h)`, then
  `h = ε ∏ t_i^{n_i}` with `∑ n_i ≥ 1` and `A[[u,v]]/(Q - h) ≃ A[[u,v]]/(ε⁻¹Q - ∏ t_i^{n_i})`,
  respecting the coordinate ideals.
* `exists_split_monomial_normal_form` (de Jong 3.3, split form, a fixed presentation).
* `exists_split_monomial_normal_form_of_closedFiber` (de Jong 2.23 + 3.3, split, equal residue
  fields): for a flat complete local `A`-algebra `B` with split nodal closed fibre and an ideal
  `J ⊆ B` that every split presentation carries to `(u, v)` (the trace of `Sing(f)`), if
  `t_1 ⋯ t_r ∈ √J` then `B ≃ₐ[A] A[[u,v]]/(uv - ∏ t_i^{n_i})` with `J ↦ (u, v)` and `∑ n_i ≥ 1`.
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution

open MvPowerSeries IsLocalRing

open Algebra.NodeNonsplit (Quadratic)

section SplitNode

variable (A : Type*) [CommRing A]

/-- The split node ring `A[[u,v]]/(uv - h)` (de Jong 2.23, split case). It is literally the
target of `Algebra.NodeFlatPresentation.exists_split_normal_form`. -/
abbrev SplitNodeRing (h : A) : Type _ :=
  MvPowerSeries (Fin 2) A ⧸ Ideal.span {X (0 : Fin 2) * X 1 - C h}

/-- The class of the coordinate `X i` (`u` for `i = 0`, `v` for `i = 1`) in the split node ring. -/
def splitNodeCoordinate (h : A) (i : Fin 2) : SplitNodeRing A h :=
  Ideal.Quotient.mk _ (X i)

/-- The coordinate ideal `(u, v)` of `A[[u,v]]/(uv - h)`: the trace of the singular locus of the
family on the complete local ring (de Jong 2.23, 3.3). -/
def splitCoordinateIdeal (h : A) : Ideal (SplitNodeRing A h) :=
  Ideal.span {splitNodeCoordinate A h 0, splitNodeCoordinate A h 1}

/-- Evaluation at `u = v = 0`, `A[[u,v]]/(uv - h) → A/(h)`. -/
def splitNodeEvaluation (h : A) : SplitNodeRing A h →ₐ[A] A ⧸ Ideal.span {h} :=
  Ideal.Quotient.liftₐ _ (Algebra.NodeSingular.constantReduction h) (by
    change Ideal.span {X (0 : Fin 2) * X 1 - C h} ≤
      RingHom.ker (Algebra.NodeSingular.constantReduction h).toRingHom
    apply Ideal.span_le.mpr
    rintro f rfl
    change Ideal.Quotient.mk (Ideal.span {h}) (constantCoeff (X (0 : Fin 2) * X 1 - C h)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simp)

@[simp]
theorem splitNodeEvaluation_mk (h : A) (f : MvPowerSeries (Fin 2) A) :
    splitNodeEvaluation A h (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk (Ideal.span {h}) (constantCoeff f) := rfl

theorem splitNodeEvaluation_surjective (h : A) :
    Function.Surjective (splitNodeEvaluation A h) := by
  intro a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ (C r), by simp⟩

/-- The parameter `h = uv` lies in the coordinate ideal. -/
theorem algebraMap_parameter_mem_splitCoordinateIdeal (h : A) :
    algebraMap A (SplitNodeRing A h) h ∈ splitCoordinateIdeal A h := by
  have hz : Ideal.Quotient.mk (Ideal.span {X (0 : Fin 2) * X 1 - C h})
      (X (0 : Fin 2) * X 1 - C h) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [map_sub, sub_eq_zero] at hz
  change Ideal.Quotient.mk _ (C h) ∈ splitCoordinateIdeal A h
  rw [← hz, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [splitNodeCoordinate]))

/-- The kernel of evaluation at `u = v = 0` is exactly the coordinate ideal `(u, v)`. -/
theorem splitNodeEvaluation_kernel (h : A) :
    RingHom.ker (splitNodeEvaluation A h).toRingHom = splitCoordinateIdeal A h := by
  apply le_antisymm
  · intro b hb
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hc : constantCoeff f ∈ Ideal.span {h} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hc
    have hconst : Ideal.Quotient.mk (Ideal.span {X (0 : Fin 2) * X 1 - C h})
        (C (constantCoeff f)) ∈ splitCoordinateIdeal A h := by
      rw [hr, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (algebraMap_parameter_mem_splitCoordinateIdeal A h)
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {X (0 : Fin 2) * X 1 - C h}))
      (Algebra.NodeFormalMorse.decomposition f)
    rw [he]
    simp only [map_add, map_mul]
    apply Ideal.add_mem _ (Ideal.add_mem _ hconst ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [splitNodeCoordinate]))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp [splitNodeCoordinate]))
  · apply Ideal.span_le.mpr
    rintro b (rfl | rfl) <;> simp [splitNodeCoordinate]

/-- The quotient by the coordinate ideal: `A[[u,v]]/(uv - h, u, v) ≃ A/(h)` (de Jong 3.3: the
trace of `Sing(f)` maps isomorphically onto `V(h)`). -/
def splitSingularQuotientEquiv (h : A) :
    (SplitNodeRing A h ⧸ splitCoordinateIdeal A h) ≃ₐ[A] A ⧸ Ideal.span {h} :=
  (Ideal.quotientEquivAlgOfEq A (splitNodeEvaluation_kernel A h).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (splitNodeEvaluation_surjective A h))

/-- A coefficient lies in the coordinate ideal `(u, v)` iff it is a multiple of `h`. -/
theorem algebraMap_mem_splitCoordinateIdeal_iff (h a : A) :
    algebraMap A (SplitNodeRing A h) a ∈ splitCoordinateIdeal A h ↔ a ∈ Ideal.span {h} := by
  rw [← splitNodeEvaluation_kernel, RingHom.mem_ker]
  change splitNodeEvaluation A h (algebraMap A _ a) = 0 ↔ _
  rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

/-- A coefficient lies in the radical of `(u, v)` iff it lies in `√(h)`: the trace of `Sing(f)`
on the base is `V(h)`. -/
theorem algebraMap_mem_radical_splitCoordinateIdeal_iff (h a : A) :
    algebraMap A (SplitNodeRing A h) a ∈ (splitCoordinateIdeal A h).radical ↔
      a ∈ (Ideal.span {h}).radical := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, (algebraMap_mem_splitCoordinateIdeal_iff A h (a ^ N)).mp (by rwa [map_pow])⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, by rw [← map_pow]; exact (algebraMap_mem_splitCoordinateIdeal_iff A h _).mpr hN⟩

/-- The scaling vector `(c, 1)`, rescaling only the first coordinate `u`. -/
def scaleFirst (c : A) : Fin 2 → A := fun i => if i = 0 then c else 1

theorem scaleFirst_mul (c d : A) : scaleFirst A c * scaleFirst A d = scaleFirst A (c * d) := by
  funext i
  fin_cases i <;> simp [scaleFirst]

theorem scaleFirst_one : scaleFirst A 1 = 1 := by
  funext i
  fin_cases i <;> simp [scaleFirst]

/-- The substitution `u ↦ ε u`, `v ↦ v` as an `A`-algebra automorphism of `A[[u,v]]`. -/
def rescaleFirstEquiv (ε : Aˣ) : MvPowerSeries (Fin 2) A ≃ₐ[A] MvPowerSeries (Fin 2) A :=
  AlgEquiv.ofAlgHom (rescaleAlgHom (scaleFirst A (ε : A)))
    (rescaleAlgHom (scaleFirst A ((ε⁻¹ : Aˣ) : A)))
    (by rw [← rescaleAlgHom_mul, scaleFirst_mul, Units.inv_mul, scaleFirst_one, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, scaleFirst_mul, Units.mul_inv, scaleFirst_one, rescaleAlgHom_one])

theorem rescaleFirstEquiv_X (ε : Aˣ) (i : Fin 2) :
    rescaleFirstEquiv A ε (X i) = C (scaleFirst A (ε : A) i) * X i := by
  change rescaleAlgHom (scaleFirst A (ε : A)) (X i) = _
  rw [rescaleAlgHom, substAlgHom_X, Pi.smul_apply', smul_eq_C_mul]

theorem rescaleFirstEquiv_X_zero (ε : Aˣ) :
    rescaleFirstEquiv A ε (X 0) = C (ε : A) * X 0 := by
  rw [rescaleFirstEquiv_X]
  simp [scaleFirst]

theorem rescaleFirstEquiv_X_one (ε : Aˣ) :
    rescaleFirstEquiv A ε (X 1) = X 1 := by
  rw [rescaleFirstEquiv_X]
  simp [scaleFirst]

theorem rescaleFirstEquiv_C (ε : Aˣ) (a : A) :
    rescaleFirstEquiv A ε (C a) = C a :=
  (rescaleFirstEquiv A ε).commutes a

/-- The substitution `u ↦ εu` carries `uv - εg` to `ε (uv - g)`. -/
theorem rescaleFirstEquiv_equation (ε : Aˣ) (g : A) :
    rescaleFirstEquiv A ε (X 0 * X 1 - C ((ε : A) * g)) = C (ε : A) * (X 0 * X 1 - C g) := by
  rw [map_sub, map_mul, rescaleFirstEquiv_X_zero, rescaleFirstEquiv_X_one, rescaleFirstEquiv_C,
    map_mul]
  ring

/-- Absorbing a unit into the coordinate `u`: `A[[u,v]]/(uv - εg) ≃ₐ[A] A[[u,v]]/(uv - g)`,
induced by `u ↦ εu`, `v ↦ v` (de Jong 3.3, "we change `Q` into `ε⁻¹Q`"). -/
def splitNodeUnitEquiv (ε : Aˣ) (g : A) :
    SplitNodeRing A ((ε : A) * g) ≃ₐ[A] SplitNodeRing A g :=
  Ideal.quotientEquivAlg _ _ (rescaleFirstEquiv A ε) (by
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {rescaleFirstEquiv A ε (X 0 * X 1 - C ((ε : A) * g))}
    rw [rescaleFirstEquiv_equation]
    exact (Ideal.span_singleton_mul_left_unit (ε.isUnit.map C) _).symm)

theorem splitNodeUnitEquiv_mk (ε : Aˣ) (g : A) (f : MvPowerSeries (Fin 2) A) :
    splitNodeUnitEquiv A ε g (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (rescaleFirstEquiv A ε f) := rfl

/-- The unit absorption carries the coordinate ideal `(u, v)` onto `(u, v)`. -/
theorem splitCoordinateIdeal_map_splitNodeUnitEquiv (ε : Aˣ) (g : A) :
    (splitCoordinateIdeal A ((ε : A) * g)).map (splitNodeUnitEquiv A ε g) =
      splitCoordinateIdeal A g := by
  rw [splitCoordinateIdeal, Ideal.map_span, Set.image_pair]
  have h0 : splitNodeUnitEquiv A ε g (splitNodeCoordinate A _ 0) =
      algebraMap A _ (ε : A) * splitNodeCoordinate A g 0 := by
    rw [splitNodeCoordinate, splitNodeUnitEquiv_mk, rescaleFirstEquiv_X_zero, map_mul]
    rfl
  have h1 : splitNodeUnitEquiv A ε g (splitNodeCoordinate A _ 1) =
      splitNodeCoordinate A g 1 := by
    rw [splitNodeCoordinate, splitNodeUnitEquiv_mk, rescaleFirstEquiv_X_one]
    rfl
  rw [h0, h1, splitCoordinateIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro b (rfl | rfl)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    rintro b (rfl | rfl)
    · have hmem : algebraMap A _ ((ε⁻¹ : Aˣ) : A) *
          (algebraMap A (SplitNodeRing A g) (ε : A) * splitNodeCoordinate A g 0) ∈
          Ideal.span {algebraMap A (SplitNodeRing A g) (ε : A) * splitNodeCoordinate A g 0,
            splitNodeCoordinate A g 1} :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at hmem
    · exact Ideal.subset_span (by simp)

end SplitNode

section Nonsplit

variable {A : Type*} [CommRing A]

/-- A binary quadratic form with unit discriminant multiplied by a unit `c`; its discriminant is
multiplied by `c²`. -/
def unitScale (Q : Quadratic A) (c : Aˣ) : Quadratic A where
  a0 := c * Q.a0
  a1 := c * Q.a1
  a2 := c * Q.a2
  invDiscriminant := ((c⁻¹ : Aˣ) : A) ^ 2 * Q.invDiscriminant
  inverse_discriminant := by
    have hc : ((c⁻¹ : Aˣ) : A) * c = 1 := Units.inv_mul c
    have hQ := Q.inverse_discriminant
    linear_combination (Q.invDiscriminant * (Q.a1 ^ 2 - 4 * Q.a0 * Q.a2) *
      (((c⁻¹ : Aˣ) : A) * c + 1)) * hc + hQ

theorem unitScale_series (Q : Quadratic A) (c : Aˣ) :
    (unitScale Q c).series = C (c : A) * Q.series := by
  simp only [Quadratic.series, Quadratic.value, Quadratic.map, unitScale, map_mul]
  ring

/-- The equation ideals agree: `(Q - εg) = (ε⁻¹Q - g)`. -/
theorem equationIdeal_unitScale (Q : Quadratic A) (ε : Aˣ) (g : A) :
    Algebra.NodeSingular.equationIdeal Q ((ε : A) * g) =
      Algebra.NodeSingular.equationIdeal (unitScale Q ε⁻¹) g := by
  rw [Algebra.NodeSingular.equationIdeal, Algebra.NodeSingular.equationIdeal, unitScale_series]
  have : C ((ε⁻¹ : Aˣ) : A) * Q.series - C g =
      C ((ε⁻¹ : Aˣ) : A) * (Q.series - C ((ε : A) * g)) := by
    rw [mul_sub, map_mul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [this]
  exact (Ideal.span_singleton_mul_left_unit ((ε⁻¹).isUnit.map C) _).symm

/-- Absorbing a unit into the quadratic form: `A[[u,v]]/(Q - εg) = A[[u,v]]/(ε⁻¹Q - g)`
(de Jong 3.3, "we change `Q` into `ε⁻¹Q`"). -/
def nodeUnitEquiv (Q : Quadratic A) (ε : Aˣ) (g : A) :
    Algebra.NodeSingular.Node Q ((ε : A) * g) ≃ₐ[A]
      Algebra.NodeSingular.Node (unitScale Q ε⁻¹) g :=
  Ideal.quotientEquivAlgOfEq A (equationIdeal_unitScale Q ε g)

/-- The unit absorption is the identity on coordinates, so it respects the coordinate ideals. -/
theorem coordinateIdeal_map_nodeUnitEquiv (Q : Quadratic A) (ε : Aˣ) (g : A) :
    (Algebra.NodeSingular.coordinateIdeal Q ((ε : A) * g)).map (nodeUnitEquiv Q ε g) =
      Algebra.NodeSingular.coordinateIdeal (unitScale Q ε⁻¹) g := by
  rw [Algebra.NodeSingular.coordinateIdeal, Ideal.map_span, Set.image_pair]
  rfl

/-- A coefficient lies in the radical of the coordinate ideal of `A[[u,v]]/(Q - h)` iff it lies in
`√(h)` (Codex's `Algebra.NodeSingular.nodeEvaluation_kernel`). -/
theorem algebraMap_mem_radical_coordinateIdeal_iff (Q : Quadratic A) (h a : A) :
    algebraMap A (Algebra.NodeSingular.Node Q h) a ∈
        (Algebra.NodeSingular.coordinateIdeal Q h).radical ↔
      a ∈ (Ideal.span {h}).radical := by
  have key : ∀ b : A, algebraMap A (Algebra.NodeSingular.Node Q h) b ∈
      Algebra.NodeSingular.coordinateIdeal Q h ↔ b ∈ Ideal.span {h} := by
    intro b
    rw [← Algebra.NodeSingular.nodeEvaluation_kernel, RingHom.mem_ker]
    change Algebra.NodeSingular.nodeEvaluation Q h (algebraMap A _ b) = 0 ↔ _
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, (key (a ^ N)).mp (by rwa [map_pow])⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, by rw [← map_pow]; exact (key _).mpr hN⟩

end Nonsplit

section Monomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → A) (ht : ∀ i, Prime (t i))
include ht

/-- **de Jong 3.3 (nonsplit form).** Let `A` be a Noetherian local domain, `t_i ∈ A` prime
elements, `Q` a binary quadratic form with unit discriminant and `h ∈ 𝔪_A`. If `t_1 ⋯ t_r` lies in
the radical of the coordinate ideal `(u, v)` of `A[[u,v]]/(Q - h)` (i.e. `Sing(f) ⊆ f⁻¹(D)` on the
complete local ring), then `h = ε ∏ t_i^{n_i}` with `ε` a unit and `∑ n_i ≥ 1`, and
`A[[u,v]]/(Q - h) ≃ₐ[A] A[[u,v]]/(ε⁻¹Q - ∏ t_i^{n_i})` carrying `(u, v)` onto `(u, v)`. -/
theorem exists_node_monomial_normal_form (Q : Quadratic A) (h : A) (hh : h ∈ maximalIdeal A)
    (hsing : algebraMap A (Algebra.NodeSingular.Node Q h) (∏ i, t i) ∈
      (Algebra.NodeSingular.coordinateIdeal Q h).radical) :
    ∃ (ε : Aˣ) (n : ι → ℕ), h = ε * ∏ i, t i ^ n i ∧ 1 ≤ ∑ i, n i ∧
      ∃ Φ : Algebra.NodeSingular.Node Q h ≃ₐ[A]
          Algebra.NodeSingular.Node (unitScale Q ε⁻¹) (∏ i, t i ^ n i),
        (Algebra.NodeSingular.coordinateIdeal Q h).map Φ =
          Algebra.NodeSingular.coordinateIdeal (unitScale Q ε⁻¹) (∏ i, t i ^ n i) := by
  have hrad := (algebraMap_mem_radical_coordinateIdeal_iff Q h _).mp hsing
  obtain ⟨ε, n, rfl⟩ := exists_unit_mul_prod_pow_of_mem_radical t ht h hrad
  exact ⟨ε, n, rfl, one_le_sum_of_unit_mul_prod_pow_mem_maximalIdeal t ε n hh,
    nodeUnitEquiv Q ε _, coordinateIdeal_map_nodeUnitEquiv Q ε _⟩

/-- **de Jong 3.3 (split form).** If `h ∈ 𝔪_A` and `t_1 ⋯ t_r` lies in the radical of the
coordinate ideal of `A[[u,v]]/(uv - h)`, then `h = ε ∏ t_i^{n_i}`, `∑ n_i ≥ 1`, and
`A[[u,v]]/(uv - h) ≃ₐ[A] A[[u,v]]/(uv - ∏ t_i^{n_i})` carrying `(u, v)` onto `(u, v)`. -/
theorem exists_split_monomial_normal_form (h : A) (hh : h ∈ maximalIdeal A)
    (hsing : algebraMap A (SplitNodeRing A h) (∏ i, t i) ∈ (splitCoordinateIdeal A h).radical) :
    ∃ (ε : Aˣ) (n : ι → ℕ), h = ε * ∏ i, t i ^ n i ∧ 1 ≤ ∑ i, n i ∧
      ∃ Φ : SplitNodeRing A h ≃ₐ[A] SplitNodeRing A (∏ i, t i ^ n i),
        (splitCoordinateIdeal A h).map Φ = splitCoordinateIdeal A (∏ i, t i ^ n i) := by
  have hrad := (algebraMap_mem_radical_splitCoordinateIdeal_iff A h _).mp hsing
  obtain ⟨ε, n, rfl⟩ := exists_unit_mul_prod_pow_of_mem_radical t ht h hrad
  exact ⟨ε, n, rfl, one_le_sum_of_unit_mul_prod_pow_mem_maximalIdeal t ε n hh,
    splitNodeUnitEquiv A ε _, splitCoordinateIdeal_map_splitNodeUnitEquiv A ε _⟩

/-- **de Jong 2.23 + 3.3 (split, equal residue fields).** Let `A` be a complete Noetherian local
domain, `B` a flat complete Noetherian local `A`-algebra whose closed fibre `B/𝔪_A B` is the split
node `κ[[u,v]]/(uv)` over `κ = A/𝔪_A`, and `J ⊆ B` an ideal carried to `(u, v)` by every split
presentation `B ≃ₐ[A] A[[u,v]]/(uv - h)` (the trace of the singular locus, i.e. the first Fitting
ideal of the differentials). If `t_1 ⋯ t_r ∈ √J` for prime elements `t_i` of `A`, then
`B ≃ₐ[A] A[[u,v]]/(uv - ∏ t_i^{n_i})` with `∑ n_i ≥ 1`, carrying `J` onto `(u, v)`. -/
theorem exists_split_monomial_normal_form_of_closedFiber [IsAdicComplete (maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsAdicComplete (maximalIdeal B) B]
    (e : Algebra.NodeFlatPresentation.SplitNode (Algebra.NodeFlatPresentation.CoefficientResidue A)
      ≃ₐ[Algebra.NodeFlatPresentation.CoefficientResidue A]
        Algebra.NodeFlatPresentation.ClosedFiber A B)
    (J : Ideal B)
    (hJ : ∀ (h : A) (φ : B ≃ₐ[A] SplitNodeRing A h), J.map φ = splitCoordinateIdeal A h)
    (hsing : algebraMap A B (∏ i, t i) ∈ J.radical) :
    ∃ n : ι → ℕ, 1 ≤ ∑ i, n i ∧
      ∃ φ : B ≃ₐ[A] SplitNodeRing A (∏ i, t i ^ n i),
        J.map φ = splitCoordinateIdeal A (∏ i, t i ^ n i) := by
  obtain ⟨h, hh, ⟨φ⟩⟩ := Algebra.NodeFlatPresentation.exists_split_normal_form A B e
  have hφ := hJ h φ
  have hsing' : algebraMap A (SplitNodeRing A h) (∏ i, t i) ∈
      (splitCoordinateIdeal A h).radical := by
    obtain ⟨N, hN⟩ := hsing
    refine ⟨N, ?_⟩
    rw [← hφ, ← φ.commutes, ← map_pow]
    exact Ideal.mem_map_of_mem _ hN
  obtain ⟨ε, n, -, hn, Φ, hΦ⟩ := exists_split_monomial_normal_form t ht h hh hsing'
  refine ⟨n, hn, φ.trans Φ, ?_⟩
  have hmap := Ideal.map_map (I := J) (φ : B →+* SplitNodeRing A h)
    (Φ : SplitNodeRing A h →+* SplitNodeRing A (∏ i, t i ^ n i))
  rw [← hΦ, ← hφ]
  exact hmap.symm

end Monomial

end DeJongAlterations.StableModification.Resolution

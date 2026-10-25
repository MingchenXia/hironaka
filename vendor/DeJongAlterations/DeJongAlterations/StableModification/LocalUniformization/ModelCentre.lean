import DeJongAlterations.StableModification.Blowups.SmoothChart
import DeJongAlterations.StableModification.ValCurves.ModificationsFiniteness

/-!
# Centres on the chart blow-ups of the model curves (Temkin, Proposition 4.3.1)

Let `A` be a domain, `L` a field and `V` a valuation ring of `L`. This file computes the centres of
`V` on the two chart blow-ups of BL1 (`Blowups.NodeChart`, `Blowups.SmoothChart`), the two stages of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (`cofinprop`, `semi-stable.tex` lines 2972–3016). Centres are T42's
`ValCurves.IsCentre`; on a blow-up `Bl → Spec B` they are taken with respect to any lift
`η : Spec L → Bl` of the point `Spec L → Spec B` given by an injective ring map `B → L` (there is
only one, `eq_of_comp_eq_of_isIso_restrict`). Blueprint chapter `sm-local-uniformization-model.tex`.

## Main results

* `affineCentre`, `isCentre_affineCentre`: if `V ⊇ g(B)` for `g : B → L`, then `V` is centred on
  `Spec B` at the prime `g⁻¹(𝔪_V)`.
* `nodeBlowup_centre` (**stage 1**, `lem:sm-lu-node-stage`, T:2985–2990): for the node
  `N = A[u,v]/(uv - πb)`, `ι : N → L` injective, `V ⊇ ι(N)` and `|u| = |π|` (i.e. `π/u` a unit
  of `V`), the centres of `V` on `Bl_{(u,π)} N` exist and lie in the smooth open
  `{π/u invertible}` (`Blowups.nodeBlowupSmoothOpen`); `nodeBlowup_centre_of_valuation_eq` is the
  same with the hypothesis `|ι u| = |ι π|` for a valuation `v` with valuation ring `V`.
* `smoothBlowup_centre` (**stage 2**, `lem:sm-lu-smooth-stage`, T:3005–3016): for
  `ι : A[T] → L` injective, `V ⊇ ι(A[T])` and `(T - a)/π ∈ V`, the unique centre of `V` on
  `Bl_{(π, T-a)} A[T]` is the point `smoothBlowupCentre` of the `π`-chart `Spec A[S]`,
  `S = (T - a)/π`, with prime `{q : q(S) ∈ 𝔪_V}`. If `A` is local and this prime is `𝔪_A A[S]`
  (`smoothBlowupCentre_asIdeal`; this holds when the residue of `S` is transcendental over the
  residue field of `A`), the centre is the generic point of the exceptional component over the
  closed point, and `one_le_fiberTrdeg_smoothBlowupCentre` gives
  `trdeg (κ(y)/κ(𝔪_A)) ≥ 1` (strict dimension inequality, `ValCurves.one_add_fiberTrdeg_le_of_specializes`),
  so the centre lies in `(Bl/S)⁰` as soon as all residue transcendence degrees are `≤ 1`
  (`smoothBlowupCentre_mem_fibreGenericSet`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.LocalUniformization

universe u

open ValCurves Blowups Curves Algebra.NodeBlowupChart
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open RiemannZariskiSpace (toSpecValuationSubring specClosedPoint)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Affine

variable {B L : Type u} [CommRing B] [Field L] (g : B →+* L) (V : RiemannZariskiSpace L)
  (hg : ∀ b, g b ∈ V.valuationSubring)

/-- The ring map `B → V` induced by `g : B → L` when `V` contains `g(B)`. -/
def toValuationSubring : B →+* V.valuationSubring := g.codRestrict V.valuationSubring hg

/-- The centre of `V` on `Spec B` when `V ⊇ g(B)`: the prime `g⁻¹(𝔪_V)`. -/
def affineCentre : Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (toValuationSubring g V hg)) (specClosedPoint V)

theorem mem_affineCentre_asIdeal_iff (b : B) :
    b ∈ (affineCentre g V hg).asIdeal ↔
      (⟨g b, hg b⟩ : V.valuationSubring) ∈ maximalIdeal V.valuationSubring :=
  Iff.rfl

/-- **Centres on affine schemes**: if `V ⊇ g(B)`, then `V` is centred on `Spec B` (with respect to
`Spec L → Spec B`) at the prime `g⁻¹(𝔪_V)`. -/
theorem isCentre_affineCentre :
    IsCentre (Spec.map (CommRingCat.ofHom g)) V (affineCentre g V hg) := by
  refine ⟨Spec.map (CommRingCat.ofHom (toValuationSubring g V hg)), ?_, rfl⟩
  rw [toSpecValuationSubring, ← Spec.map_comp]
  rfl

end Affine

section Lift

/-- **Lifts through a morphism which is an isomorphism over an open are unique**: if `p` is an
isomorphism over `W` and `η₁ ≫ p = η₂ ≫ p` lands in `W`, then `η₁ = η₂`. -/
theorem eq_of_comp_eq_of_isIso_restrict {X Y Z : Scheme.{u}} (p : X ⟶ Y) (W : Y.Opens)
    [IsIso (p ∣_ W)] {η₁ η₂ : Z ⟶ X} (h : η₁ ≫ p = η₂ ≫ p) (hW : ∀ z, (η₁ ≫ p) z ∈ W) :
    η₁ = η₂ := by
  have h₁ : Set.range η₁ ⊆ Set.range (p ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hW z
  have h₂ : Set.range η₂ ⊆ Set.range (p ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have := hW z
    rw [h] at this
    exact this
  have e : IsOpenImmersion.lift (p ⁻¹ᵁ W).ι η₁ h₁ ≫ p ∣_ W =
      IsOpenImmersion.lift (p ⁻¹ᵁ W).ι η₂ h₂ ≫ p ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, h]
  rw [cancel_mono] at e
  rw [← IsOpenImmersion.lift_fac (p ⁻¹ᵁ W).ι η₁ h₁, ← IsOpenImmersion.lift_fac (p ⁻¹ᵁ W).ι η₂ h₂,
    e]

/-- The point of `Spec B` given by `g : B → L` lies in `D(f)` if `g f ≠ 0`. -/
theorem specMap_mem_basicOpen {B L : Type u} [CommRing B] [Field L] (g : B →+* L) {f : B}
    (hf : g f ≠ 0) (z : Spec (.of L)) :
    Spec.map (CommRingCat.ofHom g) z ∈ PrimeSpectrum.basicOpen f := by
  rw [Spec.map_apply, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot]
  exact hf

/-- An element `x` of `V` with `x⁻¹ ∈ V` is not in the maximal ideal. -/
theorem not_mem_maximalIdeal_of_inv_mem {L : Type u} [Field L] {V : ValuationSubring L} {x : L}
    (hx : x ∈ V) (hx' : x⁻¹ ∈ V) (hx0 : x ≠ 0) :
    (⟨x, hx⟩ : V) ∉ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ hx0),
    Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

end Lift

section Node

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

/-- The blow-up `Bl_{(u,π)}` of the node is separated. -/
instance isSeparated_nodeBlowup : (affineBlowup (centerIdeal π b)).IsSeparated := by
  have : IsProper (affineBlowupStructure (centerIdeal π b)) :=
    affineBlowupStructure_isProper _ (centerIdeal_fg π b)
  exact isSeparated_of_isSeparated (affineBlowupStructure (centerIdeal π b))

variable {L : Type u} [Field L] {ι : Node A (π * b) →+* L} (hι : Function.Injective ι)
include hι

/-- The `u`-chart `A[u, w]/(uw - π)` of `Bl_{(u,π)}(A[u,v]/(uv - πb))` mapped to `L`:
`u ↦ ι(u)`, `w ↦ ι(π)/ι(u)` (Codex's `uChartEvaluation` followed by the extension of `ι` to the
fraction field). -/
def nodeChartRingHom : Node A π →+* L :=
  (IsFractionRing.lift hι).comp (uChartEvaluation π b).toRingHom

theorem nodeChartRingHom_apply (r : Node A π) :
    nodeChartRingHom π b hι r = IsFractionRing.lift hι (uChartEvaluation π b r) := rfl

theorem nodeChartRingHom_comp :
    (nodeChartRingHom π b hι).comp (uChartOriginalMap π b).toRingHom = ι := by
  refine RingHom.ext fun r ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodeChartRingHom_apply,
    uChartEvaluation_originalMap, IsFractionRing.lift_algebraMap]

theorem nodeChartRingHom_coordinate0 :
    nodeChartRingHom π b hι (coordinate π 0) = ι (coordinate (π * b) 0) := by
  rw [nodeChartRingHom_apply, uChartEvaluation_coordinate0, fractionCoordinate,
    IsFractionRing.lift_algebraMap]

theorem nodeChartRingHom_coordinate1 :
    nodeChartRingHom π b hι (coordinate π 1) =
      ι (algebraMap A (Node A (π * b)) π) / ι (coordinate (π * b) 0) := by
  rw [nodeChartRingHom_apply, uChartEvaluation_coordinate1, map_div₀, fractionCoordinate,
    IsFractionRing.lift_algebraMap,
    IsScalarTower.algebraMap_apply A (Node A (π * b)) (FractionRing (Node A (π * b))),
    IsFractionRing.lift_algebraMap]

theorem nodeChartRingHom_algebraMap (c : A) :
    nodeChartRingHom π b hι (algebraMap A (Node A π) c) = ι (algebraMap A (Node A (π * b)) c) := by
  rw [nodeChartRingHom_apply, AlgHom.commutes,
    IsScalarTower.algebraMap_apply A (Node A (π * b)) (FractionRing (Node A (π * b))),
    IsFractionRing.lift_algebraMap]

/-- If `V ⊇ ι(N)` and `π/u ∈ V`, then `V` contains the image of the `u`-chart. -/
theorem nodeChartRingHom_mem {V : ValuationSubring L} (hO : ∀ r, ι r ∈ V)
    (hw : ι (algebraMap A _ π) / ι (coordinate (π * b) 0) ∈ V) (r : Node A π) :
    nodeChartRingHom π b hι r ∈ V := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C c =>
    change nodeChartRingHom π b hι (algebraMap A (Node A π) c) ∈ V
    rw [nodeChartRingHom_algebraMap]
    exact hO _
  | add P Q hP hQ => simpa only [map_add] using add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, map_mul]
    refine mul_mem hP ?_
    fin_cases i
    · change nodeChartRingHom π b hι (coordinate π 0) ∈ V
      rw [nodeChartRingHom_coordinate0]
      exact hO _
    · change nodeChartRingHom π b hι (coordinate π 1) ∈ V
      rw [nodeChartRingHom_coordinate1]
      exact hw

/-- **Stage 1 of Temkin's Proposition 4.3.1** (`lem:sm-lu-node-stage`, T:2985–2990). Let
`N = A[u,v]/(uv - πb)`, `ι : N → L` injective and `V` a valuation ring of `L` containing `ι(N)`
such that `π/u` is a unit of `V` (i.e. `|u| = |π|`). For every lift `η : Spec L → Bl_{(u,π)} N` of
the point `Spec L → Spec N` given by `ι`, `V` has a centre on `Bl_{(u,π)} N`, and every centre lies
in the smooth open `{π/u invertible}` (`nodeBlowupSmoothOpen`). -/
theorem nodeBlowup_centre (V : RiemannZariskiSpace L) (hO : ∀ r, ι r ∈ V.valuationSubring)
    (hw : ι (algebraMap A _ π) / ι (coordinate (π * b) 0) ∈ V.valuationSubring)
    (hw' : ι (coordinate (π * b) 0) / ι (algebraMap A _ π) ∈ V.valuationSubring)
    {η : Spec (.of L) ⟶ affineBlowup (centerIdeal π b)}
    (hη : η ≫ affineBlowupStructure (centerIdeal π b) = Spec.map (CommRingCat.ofHom ι)) :
    (∃ y, IsCentre η V y) ∧ ∀ y, IsCentre η V y → y ∈ nodeBlowupSmoothOpen π b := by
  have hc : π * b ≠ 0 := mul_ne_zero Fact.out Fact.out
  have hu0 : coordinate (π * b) 0 ≠ 0 := Algebra.NodeDomain.nodeCoordinate_ne_zero (π * b) hc 0
  have hιu : ι (coordinate (π * b) 0) ≠ 0 := (map_ne_zero_iff ι hι).mpr hu0
  have hιπ : ι (algebraMap A _ π) ≠ 0 := (map_ne_zero_iff ι hι).mpr (algebraMap_ne_zero_node π b)
  have hg₀ : ∀ r, (nodeChartRingHom π b hι) r ∈ V.valuationSubring := nodeChartRingHom_mem π b hι hO hw
  have huI : coordinate (π * b) 0 ∈ centerIdeal π b := Ideal.subset_span (Set.mem_insert _ _)
  have : IsIso (affineBlowupStructure (centerIdeal π b) ∣_ PrimeSpectrum.basicOpen
      (coordinate (π * b) 0)) := affineBlowupStructure_restrict_isIso _ _ huI hu0
  have hcomp : Spec.map (CommRingCat.ofHom (nodeChartRingHom π b hι)) ≫ uChartInclusion π b ≫
      affineBlowupStructure (centerIdeal π b) = Spec.map (CommRingCat.ofHom ι) := by
    rw [uChartInclusion_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      nodeChartRingHom_comp]
  have hη₀ : Spec.map (CommRingCat.ofHom (nodeChartRingHom π b hι)) ≫ uChartInclusion π b = η := by
    refine eq_of_comp_eq_of_isIso_restrict (affineBlowupStructure (centerIdeal π b))
      (PrimeSpectrum.basicOpen (coordinate (π * b) 0)) ?_ ?_
    · rw [Category.assoc, hcomp, hη]
    · intro z
      rw [Category.assoc, hcomp]
      exact specMap_mem_basicOpen ι hιu z
  have hcen : IsCentre η V (uChartInclusion π b (affineCentre (nodeChartRingHom π b hι) V hg₀)) := by
    rw [← hη₀]
    exact (isCentre_affineCentre (nodeChartRingHom π b hι) V hg₀).comp (uChartInclusion π b)
  refine ⟨⟨_, hcen⟩, fun y hy ↦ ?_⟩
  rw [hy.unique hcen, nodeBlowupSmoothOpen, Scheme.Hom.apply_mem_image_iff]
  change coordinate π 1 ∉ (affineCentre (nodeChartRingHom π b hι) V hg₀).asIdeal
  rw [mem_affineCentre_asIdeal_iff]
  have hx : (nodeChartRingHom π b hι) (coordinate π 1) = ι (algebraMap A _ π) / ι (coordinate (π * b) 0) :=
    nodeChartRingHom_coordinate1 π b hι
  have := not_mem_maximalIdeal_of_inv_mem (V := V.valuationSubring) (hg₀ (coordinate π 1))
    (by rw [hx, inv_div]; exact hw') (by rw [hx]; exact div_ne_zero hιπ hιu)
  exact this

/-- **Stage 1 with a valuation** (`lem:sm-lu-node-stage`): the hypothesis `π/u ∈ V^×` of
`nodeBlowup_centre` in the form `|ι u| = |ι π|` for a valuation `v` of `L` with valuation ring
`V`. Combined with `exists_node_parameter` (which provides `π, b` with `a = πb` and `|u| = |π|`
when `|L^×| = |K^×|`), this is Temkin's first stage. -/
theorem nodeBlowup_centre_of_valuation_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (hO : ∀ r, v (ι r) ≤ 1)
    (hv : v (ι (coordinate (π * b) 0)) = v (ι (algebraMap A _ π)))
    {η : Spec (.of L) ⟶ affineBlowup (centerIdeal π b)}
    (hη : η ≫ affineBlowupStructure (centerIdeal π b) = Spec.map (CommRingCat.ofHom ι)) :
    (∃ y, IsCentre η ⟨v.valuationSubring⟩ y) ∧
      ∀ y, IsCentre η ⟨v.valuationSubring⟩ y → y ∈ nodeBlowupSmoothOpen π b := by
  have hc : π * b ≠ 0 := mul_ne_zero Fact.out Fact.out
  have hιu : ι (coordinate (π * b) 0) ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr (Algebra.NodeDomain.nodeCoordinate_ne_zero (π * b) hc 0)
  have hvu : v (ι (coordinate (π * b) 0)) ≠ 0 := (map_ne_zero v).mpr hιu
  refine nodeBlowup_centre π b hι ⟨v.valuationSubring⟩
    (fun r ↦ (Valuation.mem_valuationSubring_iff v _).mpr (hO r)) ?_ ?_ hη
  · rw [Valuation.mem_valuationSubring_iff, map_div₀, ← hv, div_self hvu]
  · rw [Valuation.mem_valuationSubring_iff, map_div₀, hv, div_self (hv ▸ hvu)]

end Node

section Smooth

variable {A : Type u} [CommRing A] [IsDomain A] (π a : A) [Fact (π ≠ 0)]

/-- The blow-up `Bl_{(π, T-a)}` of the smooth model is separated. -/
instance isSeparated_smoothBlowup : (affineBlowup (smoothCenter π a)).IsSeparated := by
  have : IsProper (affineBlowupStructure (smoothCenter π a)) :=
    affineBlowupStructure_isProper _ (smoothCenter_fg π a)
  exact isSeparated_of_isSeparated (affineBlowupStructure (smoothCenter π a))

omit [IsDomain A] [Fact (π ≠ 0)] in
/-- The generic point `𝔪_A A[S]` of the closed fibre of `Spec A[S]` has residue field of
transcendence degree at least one over `κ(𝔪_A)`: it specializes properly, within the closed fibre,
to the closed point `(𝔪_A, S)` (strict dimension inequality). -/
theorem one_le_fiberTrdeg_smoothModel [IsLocalRing A] (P : Spec (.of A[X]))
    (hP : P.asIdeal = Ideal.map C (maximalIdeal A)) : 1 ≤ fiberTrdeg (smoothModel A) P := by
  let Q : Spec (.of A[X]) := ⟨Ideal.comap (Polynomial.evalRingHom 0) (maximalIdeal A), inferInstance⟩
  have hPQ : P ⤳ Q := by
    rw [← PrimeSpectrum.le_iff_specializes]
    intro f hf
    change f ∈ P.asIdeal at hf
    rw [hP, Ideal.mem_map_C_iff] at hf
    change Polynomial.eval 0 f ∈ maximalIdeal A
    rw [← coeff_zero_eq_eval_zero]
    exact hf 0
  have hne : P ≠ Q := by
    intro h
    have hX : (X : A[X]) ∈ Q.asIdeal := by
      change Polynomial.eval 0 X ∈ maximalIdeal A
      simp
    rw [← h, hP, Ideal.mem_map_C_iff] at hX
    have := hX 1
    rw [coeff_X_one] at this
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hfib : smoothModel A P = smoothModel A Q := by
    apply PrimeSpectrum.ext
    rw [smoothModel, Spec.map_apply, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
      PrimeSpectrum.comap_asIdeal, hP]
    ext c
    simp only [CommRingCat.hom_ofHom, Ideal.mem_comap, Q, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Ideal.mem_map_C_iff, coeff_C, Polynomial.coe_evalRingHom, eval_C]
    constructor
    · intro h
      simpa using h 0
    · intro h n
      split_ifs
      · exact h
      · exact (maximalIdeal A).zero_mem
  have h := one_add_fiberTrdeg_le_of_specializes (smoothModel A) hPQ hne hfib
  exact le_self_add.trans h


theorem smoothParamChartEval_originalMap (p : A[X]) :
    smoothParamChartEval π a (smoothParamOriginalMap π a p) =
      algebraMap A[X] (FractionRing A[X]) p := by
  change ((smoothParamChartEquiv π a ((smoothParamChartEquiv π a).symm
    (algebraMap A[X] (affineBlowupFractionChart (smoothCenter π a) (C π)) p)) :
      FractionRing A[X])) = _
  exact congrArg (fun x : (affineBlowupFractionChart (smoothCenter π a) (C π)).restrictScalars A ↦
    (x : FractionRing A[X])) ((smoothParamChartEquiv π a).apply_symm_apply _)

variable {L : Type u} [Field L] {ι : A[X] →+* L} (hι : Function.Injective ι)
include hι

/-- The `π`-chart `A[S]` of `Bl_{(π, T-a)} A[T]` mapped to `L`: `S ↦ (ι(T) - ι(a))/ι(π)`
(BL1's `smoothParamChartEval` followed by the extension of `ι` to the fraction field). -/
def smoothChartRingHom : A[X] →+* L :=
  (IsFractionRing.lift hι).comp (smoothParamChartEval π a).toRingHom

omit [Fact (π ≠ 0)] in
theorem smoothChartRingHom_apply (q : A[X]) :
    smoothChartRingHom π a hι q = IsFractionRing.lift hι (smoothParamChartEval π a q) := rfl

theorem smoothChartRingHom_comp :
    (smoothChartRingHom π a hι).comp (smoothParamOriginalMap π a).toRingHom = ι := by
  refine RingHom.ext fun p ↦ ?_
  change IsFractionRing.lift hι (smoothParamChartEval π a (smoothParamOriginalMap π a p)) = ι p
  rw [smoothParamChartEval_originalMap, IsFractionRing.lift_algebraMap]

omit [Fact (π ≠ 0)] in
theorem smoothChartRingHom_X :
    smoothChartRingHom π a hι X = (ι X - ι (C a)) / ι (C π) := by
  rw [smoothChartRingHom_apply, smoothParamChartEval, aeval_X, smoothParamCoordinate, map_div₀,
    IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, map_sub]

omit [Fact (π ≠ 0)] in
theorem smoothChartRingHom_C (c : A) : smoothChartRingHom π a hι (C c) = ι (C c) := by
  rw [smoothChartRingHom_apply, smoothParamChartEval, aeval_C,
    IsScalarTower.algebraMap_apply A A[X] (FractionRing A[X]), IsFractionRing.lift_algebraMap,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

omit [Fact (π ≠ 0)] in
/-- If `V ⊇ ι(A[T])` and `(T - a)/π ∈ V`, then `V` contains the image of the `π`-chart. -/
theorem smoothChartRingHom_mem {V : ValuationSubring L} (hO : ∀ p, ι p ∈ V)
    (hs : (ι X - ι (C a)) / ι (C π) ∈ V) (q : A[X]) : smoothChartRingHom π a hι q ∈ V := by
  induction q using Polynomial.induction_on with
  | C c => rw [smoothChartRingHom_C]; exact hO _
  | add p q hp hq => simpa only [map_add] using add_mem hp hq
  | monomial n c hp =>
    rw [pow_succ, ← mul_assoc, map_mul, smoothChartRingHom_X]
    exact mul_mem hp hs

/-- The centre of `V` on `Bl_{(π, T-a)} A[T]`: the point of the `π`-chart `Spec A[S]` with prime
`{q : q((T - a)/π) ∈ 𝔪_V}`. -/
def smoothBlowupCentre (V : RiemannZariskiSpace L) (hO : ∀ p, ι p ∈ V.valuationSubring)
    (hs : (ι X - ι (C a)) / ι (C π) ∈ V.valuationSubring) : affineBlowup (smoothCenter π a) :=
  smoothParamChartInclusion π a
    (affineCentre (smoothChartRingHom π a hι) V (smoothChartRingHom_mem π a hι hO hs))

/-- **Stage 2 of Temkin's Proposition 4.3.1** (`lem:sm-lu-smooth-stage`, T:3005–3016). Let
`ι : A[T] → L` be injective and `V` a valuation ring of `L` containing `ι(A[T])` and
`(T - a)/π`. For every lift `η : Spec L → Bl_{(π, T-a)} A[T]` of the point given by `ι`, `V` is
centred at `smoothBlowupCentre`, and this is its only centre. -/
theorem smoothBlowup_centre (V : RiemannZariskiSpace L) (hO : ∀ p, ι p ∈ V.valuationSubring)
    (hs : (ι X - ι (C a)) / ι (C π) ∈ V.valuationSubring)
    {η : Spec (.of L) ⟶ affineBlowup (smoothCenter π a)}
    (hη : η ≫ affineBlowupStructure (smoothCenter π a) = Spec.map (CommRingCat.ofHom ι)) :
    IsCentre η V (smoothBlowupCentre π a hι V hO hs) ∧
      ∀ y, IsCentre η V y → y = smoothBlowupCentre π a hι V hO hs := by
  have hg₀ := smoothChartRingHom_mem π a hι hO hs
  have hιπ : ι (C π) ≠ 0 := (map_ne_zero_iff ι hι).mpr (smoothCenter_C_ne_zero π)
  have : IsIso (affineBlowupStructure (smoothCenter π a) ∣_ PrimeSpectrum.basicOpen (C π)) :=
    affineBlowupStructure_restrict_isIso _ _ (C_mem_smoothCenter π a) (smoothCenter_C_ne_zero π)
  have hcomp : Spec.map (CommRingCat.ofHom (smoothChartRingHom π a hι)) ≫ smoothParamChartInclusion π a ≫
      affineBlowupStructure (smoothCenter π a) = Spec.map (CommRingCat.ofHom ι) := by
    rw [smoothParamChartInclusion_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      smoothChartRingHom_comp]
  have hη₀ : Spec.map (CommRingCat.ofHom (smoothChartRingHom π a hι)) ≫ smoothParamChartInclusion π a = η := by
    refine eq_of_comp_eq_of_isIso_restrict (affineBlowupStructure (smoothCenter π a))
      (PrimeSpectrum.basicOpen (C π)) ?_ ?_
    · rw [Category.assoc, hcomp, hη]
    · intro z
      rw [Category.assoc, hcomp]
      exact specMap_mem_basicOpen ι hιπ z
  have hcen : IsCentre η V (smoothBlowupCentre π a hι V hO hs) := by
    rw [← hη₀]
    exact (isCentre_affineCentre (smoothChartRingHom π a hι) V hg₀).comp (smoothParamChartInclusion π a)
  exact ⟨hcen, fun y hy ↦ hy.unique hcen⟩

omit [Fact (π ≠ 0)] in
/-- **The centre is the generic point of the exceptional component** (T:3014–3016): if `A` is local
and an element `q(S)` of the image of the `π`-chart lies in `𝔪_V` exactly when all coefficients of
`q` lie in `𝔪_A` (i.e. the residue of `S = (T - a)/π` is transcendental over the residue field of
`A`, and `V` dominates `A`), then the prime of the centre in the `π`-chart is `𝔪_A A[S]`. -/
theorem smoothBlowupCentre_asIdeal [IsLocalRing A] (V : RiemannZariskiSpace L)
    (hO : ∀ p, ι p ∈ V.valuationSubring) (hs : (ι X - ι (C a)) / ι (C π) ∈ V.valuationSubring)
    (hres : ∀ q : A[X], (⟨smoothChartRingHom π a hι q, smoothChartRingHom_mem π a hι hO hs q⟩ :
      V.valuationSubring) ∈ maximalIdeal V.valuationSubring ↔ ∀ i, q.coeff i ∈ maximalIdeal A) :
    (affineCentre (smoothChartRingHom π a hι) V (smoothChartRingHom_mem π a hι hO hs)).asIdeal =
      Ideal.map C (maximalIdeal A) := by
  ext q
  rw [mem_affineCentre_asIdeal_iff, hres, Ideal.mem_map_C_iff]

/-- **The centre of stage 2 is in `(Bl/S)⁰`, lower bound**: under the hypotheses of
`smoothBlowupCentre_asIdeal`, the centre `y` of `V` on `Bl_{(π, T-a)} A[T]` satisfies
`trdeg (κ(y)/κ(𝔪_A)) ≥ 1`. -/
theorem one_le_fiberTrdeg_smoothBlowupCentre [IsLocalRing A] (V : RiemannZariskiSpace L)
    (hO : ∀ p, ι p ∈ V.valuationSubring) (hs : (ι X - ι (C a)) / ι (C π) ∈ V.valuationSubring)
    (hres : ∀ q : A[X], (⟨smoothChartRingHom π a hι q, smoothChartRingHom_mem π a hι hO hs q⟩ :
      V.valuationSubring) ∈ maximalIdeal V.valuationSubring ↔ ∀ i, q.coeff i ∈ maximalIdeal A) :
    1 ≤ fiberTrdeg (smoothBlowupMorphism π a) (smoothBlowupCentre π a hι V hO hs) := by
  set P := affineCentre (smoothChartRingHom π a hι) V (smoothChartRingHom_mem π a hι hO hs)
  have h1 := one_le_fiberTrdeg_smoothModel P (smoothBlowupCentre_asIdeal π a hι V hO hs hres)
  rw [← smoothParamChartInclusion_smoothBlowupMorphism π a, fiberTrdeg_comp,
    (isAlgebraicAt_iff_fiberTrdeg_eq_zero (smoothParamChartInclusion π a) P).mp
      isAlgebraicAt_of_isIso_stalkMap, add_zero] at h1
  exact h1

/-- **The centre of stage 2 is in `(Bl/S)⁰`** (`𝔵 ∈ Γ₀`, T:3016): if moreover every point of the
blow-up has residue transcendence degree at most one over the base (for instance when the blow-up
is a modification of a relative curve, `ValCurves.fiberTrdeg_le_one`), the centre is a generic
point of its fibre. -/
theorem smoothBlowupCentre_mem_fibreGenericSet [IsLocalRing A] (V : RiemannZariskiSpace L)
    (hO : ∀ p, ι p ∈ V.valuationSubring) (hs : (ι X - ι (C a)) / ι (C π) ∈ V.valuationSubring)
    (hres : ∀ q : A[X], (⟨smoothChartRingHom π a hι q, smoothChartRingHom_mem π a hι hO hs q⟩ :
      V.valuationSubring) ∈ maximalIdeal V.valuationSubring ↔ ∀ i, q.coeff i ∈ maximalIdeal A)
    (hdim : fiberTrdeg (smoothBlowupMorphism π a) (smoothBlowupCentre π a hι V hO hs) ≤ 1) :
    smoothBlowupCentre π a hι V hO hs ∈ fibreGenericSet (smoothBlowupMorphism π a) :=
  le_antisymm hdim (one_le_fiberTrdeg_smoothBlowupCentre π a hι V hO hs hres)

end Smooth

end DeJongAlterations.StableModification.LocalUniformization

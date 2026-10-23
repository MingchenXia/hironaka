import DeJongAlterations.StableModification.Blowups.SeparationCharts

/-!
# Lifting sections through chart blow-ups and their transports

M. Temkin, *Stable modification of relative curves*, Lemma 4.3.2 (T:3019–3046): the strict
transforms of the boundary sections under the chart blow-ups of `Blowups.NodeChart` and
`Blowups.SmoothChart` are computed in the charts (blueprint `sm-boundary-separation.tex`,
`lem:sm-separation-lift` and `lem:sm-separation-transport-lift`):

* `smoothLift π a e`: the section `S ↦ e` of the `π`-chart `Spec A[S]`, `T = πS + a`, of
  `Bl_{(π, T - a)}`; it lifts `T ↦ a + πe` (`smoothLift_comp`), and lifts with `e - e'` a unit
  have distinct closed points (`smoothLift_closedPoint_ne`);
* `nodeLift π b d e`: the section `(v, z) ↦ (d, e)` of the chart `A[v, z]/(vz - b)`, `u = πz`, of
  `Bl_{(u, π)}`; it lifts `(u, v) ↦ (πe, d)` (`nodeLift_comp`);
* `hasSmoothChart_of_smoothChart_lift`, `hasSmoothChart_of_nodeChart_lift`: points of a
  transported blow-up lying over the `π`-chart, respectively over a coordinate open of a node
  chart, have smooth charts;
* `liftThroughChart`, `liftThroughRest`: sections through `x`, respectively avoiding `x` at the
  closed point, lift through the transport (`exists_transport`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section SmoothLift

variable {A : Type u} [CommRing A] [IsDomain A] (π a : A) [Fact (π ≠ 0)]

/-- The `π`-chart map sends `T` to `πS + a`. -/
theorem smoothParamOriginalMap_X : smoothParamOriginalMap π a X = C π * X + C a := by
  have h : (smoothParamChartEquiv π a (C π * X + C a) : FractionRing A[X]) =
      algebraMap A[X] (FractionRing A[X]) X := by
    rw [coe_smoothParamChartEquiv]
    exact (algebraMap_X_eq_param π a).symm
  change (smoothParamChartEquiv π a).symm
    (algebraMap A[X] (affineBlowupFractionChart (smoothCenter π a) (C π)) X) = _
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [h]
  rfl

/-- The lift `S ↦ e` of a section into the `π`-chart of `Bl_{(π, T - a)}`. -/
def smoothLift (e : A) : Spec (.of A) ⟶ affineBlowup (smoothCenter π a) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom e)) ≫ smoothParamChartInclusion π a

/-- **The lift of the section `T ↦ a + πe`.** -/
theorem smoothLift_comp (e : A) :
    smoothLift π a e ≫ affineBlowupStructure (smoothCenter π a) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (a + π * e))) := by
  rw [smoothLift, Category.assoc, smoothParamChartInclusion_structure, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun r ↦ ?_) ?_)
  · change Polynomial.eval e (smoothParamOriginalMap π a (C r)) = Polynomial.eval (a + π * e) (C r)
    have : smoothParamOriginalMap π a (C r) = C r := (smoothParamOriginalMap π a).commutes r
    rw [this]
    simp
  · change Polynomial.eval e (smoothParamOriginalMap π a X) = Polynomial.eval (a + π * e) X
    rw [smoothParamOriginalMap_X]
    simp [add_comm]

/-- The lift is a section of the blow-up over `A`. -/
theorem smoothLift_comp_smoothBlowupMorphism (e : A) :
    smoothLift π a e ≫ smoothBlowupMorphism π a = 𝟙 _ := by
  rw [smoothBlowupMorphism, ← Category.assoc, smoothLift_comp, smoothModel, ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  simp

omit [IsDomain A] in
/-- The closed point of `T ↦ e` in `Spec A[T]`. -/
theorem specMap_evalRingHom_closedPoint_asIdeal [IsLocalRing A] (e : A) :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom e)) (closedPoint A)).asIdeal =
      (maximalIdeal A).comap (Polynomial.evalRingHom e) := rfl

omit [IsDomain A] in
/-- Sections `T ↦ e`, `T ↦ e'` with `e - e'` a unit have distinct closed points. -/
theorem specMap_evalRingHom_closedPoint_ne [IsLocalRing A] {e e' : A} (h : IsUnit (e - e')) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom e)) (closedPoint A) ≠
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom e')) (closedPoint A) := by
  intro heq
  have h1 := congrArg PrimeSpectrum.asIdeal heq
  rw [specMap_evalRingHom_closedPoint_asIdeal, specMap_evalRingHom_closedPoint_asIdeal] at h1
  have hmem : (X - C e : A[X]) ∈ (maximalIdeal A).comap (Polynomial.evalRingHom e) := by
    simp
  rw [h1, Ideal.mem_comap] at hmem
  simp only [coe_evalRingHom, eval_sub, eval_X, eval_C] at hmem
  exact (mem_maximalIdeal _).mp hmem (by rw [← neg_sub]; exact h.neg)

/-- **Lifts with `e - e'` a unit have distinct closed points.** -/
theorem smoothLift_closedPoint_ne [IsLocalRing A] {e e' : A} (h : IsUnit (e - e')) :
    smoothLift π a e (closedPoint A) ≠ smoothLift π a e' (closedPoint A) := by
  rw [smoothLift, smoothLift, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact fun heq ↦ specMap_evalRingHom_closedPoint_ne h
    ((smoothParamChartInclusion π a).isOpenEmbedding.injective heq)

end SmoothLift

section NodeLift

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

/-- The lift `(v, z) ↦ (d, e)` of a section into the chart `A[v, z]/(vz - b)`, `u = πz`,
of `Bl_{(u, π)}`. -/
def nodeLift (d e : A) (h : d * e = b) : Spec (.of A) ⟶ affineBlowup (centerIdeal π b) :=
  Spec.map (CommRingCat.ofHom (nodePoint b d e h).toRingHom) ≫ tChartInclusion π b

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem mul_eq_of_mul_eq {d e : A} (h : d * e = b) : π * e * d = π * b := by
  rw [← h]; ring

/-- **The lift of the section `(u, v) ↦ (πe, d)`.** -/
theorem nodeLift_comp (d e : A) (h : d * e = b) :
    nodeLift π b d e h ≫ affineBlowupStructure (centerIdeal π b) =
      Spec.map (CommRingCat.ofHom (nodePoint (π * b) (π * e) d
        (mul_eq_of_mul_eq π b h)).toRingHom) := by
  rw [nodeLift, Category.assoc, tChartInclusion_structure, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext ?_
  have : (nodePoint b d e h).comp (tChartOriginalMap π b) =
      nodePoint (π * b) (π * e) d (mul_eq_of_mul_eq π b h) := by
    apply node_algHom_ext
    · simp
    · simp
  exact congrArg AlgHom.toRingHom this

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The closed point of the node point `(u, v) ↦ (c, d)`. -/
theorem specMap_nodePoint_closedPoint_asIdeal [IsLocalRing A] (a c d : A) (h : c * d = a) :
    (Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom) (closedPoint A)).asIdeal =
      (maximalIdeal A).comap (nodePoint a c d h).toRingHom := rfl

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The closed point of the node point `(u, v) ↦ (c, d)` lies in `D(v)` if `d` is a unit. -/
theorem specMap_nodePoint_closedPoint_mem_coordinateOpen [IsLocalRing A] (a c d : A)
    (h : c * d = a) (hd : IsUnit d) :
    Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom) (closedPoint A) ∈
      Geometry.NodeFamilySmooth.coordinateOpen a 1 := by
  change coordinate a 1 ∉ (Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom)
    (closedPoint A)).asIdeal
  rw [specMap_nodePoint_closedPoint_asIdeal, Ideal.mem_comap]
  change nodePoint a c d h (coordinate a 1) ∉ maximalIdeal A
  rw [nodePoint_coordinate1]
  exact (mem_maximalIdeal _).not.mpr (not_not.mpr hd)

end NodeLift

section ChartLift

variable {A : Type u} [CommRing A] {C₁ P M' : Scheme.{u}} (g₁ : C₁ ⟶ Spec (.of A))
  (j : P ⟶ C₁) [IsOpenImmersion j] (f : P ⟶ M') [Etale f] (q' : M' ⟶ Spec (.of A))
  (hf : f ≫ q' = j ≫ g₁)

include hf

/-- **Points over a smooth chart of the blow-up have smooth charts.** Let `j : P ⟶ C₁` be an open
immersion and `f : P ⟶ M'` étale over `A`. If `c : Spec A[T] ⟶ M'` is an open immersion over `A`
(a chart of `M'` which is the smooth model) and `f p ∈ c(Spec A[T])`, then `j p` has a smooth
chart. -/
theorem hasSmoothChart_of_smoothChart_lift (c : Spec (.of A[X]) ⟶ M') [IsOpenImmersion c]
    (hc : c ≫ q' = smoothModel A) (p : P) (hp : f p ∈ Set.range c) :
    HasSmoothChart g₁ (j p) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := f) t p ht
  refine ⟨pullback c f, pullback.snd c f ≫ j, inferInstance, pullback.fst c f, inferInstance,
    ⟨z, by rw [Scheme.Hom.comp_apply, hz2]⟩, ?_⟩
  rw [← hc, ← Category.assoc, pullback.condition, Category.assoc, hf, Category.assoc]

/-- **Points over a coordinate open of a node chart of the blow-up have smooth charts.** -/
theorem hasSmoothChart_of_nodeChart_lift (b : A) (c : Spec (.of (Node A b)) ⟶ M')
    [IsOpenImmersion c] (hc : c ≫ q' = nodeModel b) (p : P) (t : Spec (.of (Node A b)))
    (ht : c t = f p) (i : Fin 2) (hti : t ∈ Geometry.NodeFamilySmooth.coordinateOpen b i) :
    HasSmoothChart g₁ (j p) := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := f) t p ht
  have := hasSmoothChart_of_node g₁ (pullback.snd c f ≫ j) b (pullback.fst c f)
    (by rw [← hc, ← Category.assoc, pullback.condition, Category.assoc, hf,
      Category.assoc]) z i (by rw [hz1]; exact hti)
  rwa [Scheme.Hom.comp_apply, hz2] at this

end ChartLift

section TransportLift

variable {A : Type u} [CommRing A] [IsLocalRing A] {C C' M M' : Scheme.{u}}
  (g : C ⟶ Spec (.of A)) {U₀ : C.Opens} (φ₀ : U₀.toScheme ⟶ M) (β₀ : M' ⟶ M) (β : C' ⟶ C)
  (j : pullback β₀ φ₀ ⟶ C') (hj : j ≫ β = pullback.snd β₀ φ₀ ≫ U₀.ι)

/-- **Lifting a section through the chart of a transport.** A section `σ` with `σ(s) ∈ U₀` and
a lift `τ` of `φ₀ ∘ σ` to `M'` give the section `j ∘ (τ, σ)` of `C'` over `σ`. -/
def liftThroughChart (σ : Spec (.of A) ⟶ C) (hσ : σ (closedPoint A) ∈ U₀)
    (τ : Spec (.of A) ⟶ M') (hτ : τ ≫ β₀ = factorThruOpen σ U₀ hσ ≫ φ₀) :
    Spec (.of A) ⟶ C' :=
  pullback.lift τ (factorThruOpen σ U₀ hσ) hτ ≫ j

include hj in
theorem liftThroughChart_comp (σ : Spec (.of A) ⟶ C) (hσ : σ (closedPoint A) ∈ U₀)
    (τ : Spec (.of A) ⟶ M') (hτ : τ ≫ β₀ = factorThruOpen σ U₀ hσ ≫ φ₀) :
    liftThroughChart φ₀ β₀ j σ hσ τ hτ ≫ β = σ := by
  rw [liftThroughChart, Category.assoc, hj, pullback.lift_snd_assoc, factorThruOpen_ι]

/-- The image under `pullback.fst` of the lift is `τ`. -/
theorem liftThroughChart_fst (σ : Spec (.of A) ⟶ C) (hσ : σ (closedPoint A) ∈ U₀)
    (τ : Spec (.of A) ⟶ M') (hτ : τ ≫ β₀ = factorThruOpen σ U₀ hσ ≫ φ₀) :
    pullback.lift τ (factorThruOpen σ U₀ hσ) hτ ≫ pullback.fst β₀ φ₀ = τ :=
  pullback.lift_fst _ _ _

/-- **Lifting a section avoiding the centre.** If the only point of the closed fibre outside `W`
is `x` and `σ(s) ≠ x`, then `σ` factors through `W`. -/
theorem closedPoint_mem_of_ne (W : C.Opens) (x : C)
    (huniq : ∀ y ∉ W, g y = closedPoint A → y = x) (σ : Spec (.of A) ⟶ C) (hσg : σ ≫ g = 𝟙 _)
    (hσx : σ (closedPoint A) ≠ x) : σ (closedPoint A) ∈ W := by
  by_contra h
  exact hσx (huniq _ h (by rw [← Scheme.Hom.comp_apply, hσg]; rfl))

end TransportLift

end DeJongAlterations.StableModification.Blowups

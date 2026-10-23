import DeJongAlterations.StableModification.LocalUniformization.ModelValuation
import DeJongAlterations.StableModification.LocalUniformization.ModelCentre

/-!
# The two stages of local uniformization in the model situations (Temkin, Proposition 4.3.1)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (`cofinprop`, `semi-stable.tex` lines 2967–3016) reduces, by étale localization,
to the two model curves `Spec R[u,v]/(uv - a)` and `Spec R[T]` over a valuation ring `R` with
separably closed fraction field `K`, and a valuation `𝔵` of `L` (the function field of the model,
`trdeg (L̃/K̃) = 1`) whose centre is a closed point of the closed fibre. This file combines the
valuation theory of `LocalUniformization.ModelValuation` with the centre computations of
`LocalUniformization.ModelCentre`. Blueprint chapter `sm-local-uniformization-model.tex`.

Throughout `v_K` is a valuation of `K` with valuation ring `R = v_K.valuationSubring`, and `v_L` a
valuation of a field `L ⊇ K` extending it, with valuation ring `𝒪`.

## Main results

* `node_stage` (**stage 1**, `lem:sm-lu-node-stage`, T:2976–2990): for the node
  `N = R[u,v]/(uv - c)`, `c ≠ 0`, an injective `ι : N → L` over `R` with `𝒪 ⊇ ι(N)` and
  `trdeg (L/K) ≤ 1`, there are `π, b ∈ R∖0` with `c = πb` such that, after identifying `N` with
  `R[u,v]/(uv - πb)` (`nodeCast`), every centre of `𝒪` on `Bl_{(u,π)}` lies in the smooth open
  `{π/u invertible}`.
* `smooth_stage` (**stage 2**, `lem:sm-lu-smooth-stage`, T:2997–3016): for `L = K(T)` with
  `T ∈ 𝒪` and residue of `T` algebraic over `K̃` (centre a closed point of the closed fibre), there
  are `a, π ∈ R`, `π ∈ 𝔪_R ∖ 0`, such that the unique centre of `𝒪` on `Bl_{(π, T-a)} R[T]` is the
  image of the generic point `𝔪_R R[S]` of the closed fibre of the `π`-chart `Spec R[S]`,
  `S = (T - a)/π`, i.e. the generic point of the exceptional component over the closed point; its
  residue field has transcendence degree at least one over `κ(𝔪_R)`.

## Usage

The node stage produces `π, b` with `c = π b`; a consumer working with an étale chart
`e : U → Spec R[u,v]/(uv - c)` with `c` a variable can instead `subst` the equation obtained from
`exists_node_parameter` and apply `nodeBlowup_centre_of_valuation_eq` directly.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.LocalUniformization

universe u

open ValCurves Blowups Curves Algebra.NodeBlowupChart
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

section Node

/-- The identification `R[u,v]/(uv - c) ≅ R[u,v]/(uv - c')` for `c = c'`. -/
def nodeCast {A : Type*} [CommRing A] {c c' : A} (h : c = c') : Node A c ≃ₐ[A] Node A c' :=
  Ideal.quotientEquivAlgOfEq A (congrArg (Algebra.NodeChart.uChartIdeal A) h)

@[simp]
theorem nodeCast_coordinate {A : Type*} [CommRing A] {c c' : A} (h : c = c') (i : Fin 2) :
    nodeCast h (coordinate c i) = coordinate c' i :=
  Ideal.quotientEquivAlgOfEq_mk A _ _

/-- **Stage 1, the parameter** (Temkin, T:2981–2987): let `K` be separably closed,
`trdeg (L/K) ≤ 1`, `L̃/K̃` transcendental, `c ∈ R∖0` and `ι : R[u,v]/(uv - c) → L` a ring map over
`R` with `ι(u) ≠ 0` and `𝒪 ⊇ ι(N)`. Then there are `π, b ∈ R∖0` with `c = πb` and
`|ι(u)| = |π|`. -/
theorem exists_node_parameter_of_trdeg [IsSepClosed K] (htr : Algebra.trdeg K L ≤ 1)
    {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t))
    {c : vK.valuationSubring} (hc : c ≠ 0) {ι : Node vK.valuationSubring c →+* L}
    (hιC : ∀ r, ι (algebraMap vK.valuationSubring (Node vK.valuationSubring c) r) =
      algebraMap K L (r : K)) (hO : ∀ r, vL (ι r) ≤ 1)
    (hu : ι (coordinate c 0) ≠ 0) :
    ∃ π b : vK.valuationSubring, π ≠ 0 ∧ b ≠ 0 ∧ c = π * b ∧
      vL (ι (coordinate c 0)) = vL (algebraMap K L π) := by
  have huv : ι (coordinate c 0) * ι (coordinate c 1) = algebraMap K L c := by
    rw [← map_mul, ← hιC]
    exact congrArg ι (Algebra.NodeDomain.nodeCoordinateProduct c)
  obtain ⟨π, b, hπ, hπ1, hb1, hcπb, hv⟩ := exists_node_parameter vK vL
    (exists_valuation_eq_algebraMap vK vL htr ht) (hO _) (hO _) hu huv
  let π' : vK.valuationSubring := ⟨π, (Valuation.mem_valuationSubring_iff vK π).mpr hπ1⟩
  let b' : vK.valuationSubring := ⟨b, (Valuation.mem_valuationSubring_iff vK b).mpr hb1⟩
  have hc' : c = π' * b' := Subtype.ext hcπb
  refine ⟨π', b', fun h ↦ hπ (congrArg Subtype.val h), fun h ↦ hc (by rw [hc', h, mul_zero]),
    hc', hv⟩

/-- **Stage 1 of Temkin's Proposition 4.3.1** (`lem:sm-lu-node-stage`, T:2976–2990): let `K` be
separably closed, `trdeg (L/K) ≤ 1`, `L̃/K̃` transcendental, `c ∈ R∖0` and
`ι : N = R[u,v]/(uv - c) → L` injective over `R` with `𝒪 ⊇ ι(N)`. Then there are `π, b ∈ R∖0`
with `c = πb` such that, for every lift `η : Spec L → Bl_{(u,π)}(R[u,v]/(uv - πb))` of the point
given by `ι ∘ nodeCast`, `𝒪` has a centre on the blow-up and every centre lies in the smooth
open `{π/u invertible}`. (The blow-up is an isomorphism off `V(u, v, π)`,
`Blowups.nodeBlowup_isIso`.) -/
theorem node_stage [IsSepClosed K] (htr : Algebra.trdeg K L ≤ 1) {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t))
    {c : vK.valuationSubring} (hc : c ≠ 0) {ι : Node vK.valuationSubring c →+* L}
    (hι : Function.Injective ι) (hιC : ∀ r, ι (algebraMap vK.valuationSubring (Node vK.valuationSubring c) r) =
      algebraMap K L (r : K))
    (hO : ∀ r, vL (ι r) ≤ 1) :
    ∃ (π b : vK.valuationSubring) (h : π * b = c) (_ : Fact (π ≠ 0)) (_ : Fact (b ≠ 0)),
      ∀ η : Spec (.of L) ⟶ affineBlowup (centerIdeal π b),
        η ≫ affineBlowupStructure (centerIdeal π b) =
          Spec.map (CommRingCat.ofHom (ι.comp (nodeCast h).toRingEquiv.toRingHom)) →
        (∃ y, IsCentre η ⟨vL.valuationSubring⟩ y) ∧
          ∀ y, IsCentre η ⟨vL.valuationSubring⟩ y → y ∈ nodeBlowupSmoothOpen π b := by
  have hu : ι (coordinate c 0) ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr (Algebra.NodeDomain.nodeCoordinate_ne_zero c hc 0)
  obtain ⟨π, b, hπ, hb, hcπb, hv⟩ := exists_node_parameter_of_trdeg vK vL htr ht hc hιC hO hu
  have : Fact (π ≠ 0) := ⟨hπ⟩
  have : Fact (b ≠ 0) := ⟨hb⟩
  refine ⟨π, b, hcπb.symm, inferInstance, inferInstance, fun η hη ↦ ?_⟩
  set ι' := ι.comp (nodeCast hcπb.symm).toRingEquiv.toRingHom
  have hι' : Function.Injective ι' := hι.comp (nodeCast hcπb.symm).injective
  refine nodeBlowup_centre_of_valuation_eq π b hι' vL (fun r ↦ hO _) ?_ hη
  have h1 : ι' (coordinate (π * b) 0) = ι (coordinate c 0) := by
    simp only [ι', RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, nodeCast_coordinate]
  have h2 : ι' (algebraMap _ (Node vK.valuationSubring (π * b)) π) = algebraMap K L π := by
    simp only [ι', RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, hιC]
  rw [h1, h2, hv]

end Node

section Smooth

/-- The map `R[T] → L`, `T ↦ T`, over `R ⊆ K`. -/
def polynomialMap (T : L) : vK.valuationSubring[X] →+* L :=
  Polynomial.eval₂RingHom ((algebraMap K L).comp vK.valuationSubring.subtype) T

@[simp]
theorem polynomialMap_C (T : L) (r : vK.valuationSubring) :
    polynomialMap vK T (C r) = algebraMap K L r := by
  simp [polynomialMap]

@[simp]
theorem polynomialMap_X (T : L) : polynomialMap vK T X = T := by
  simp [polynomialMap]

/-- `polynomialMap` lands in `𝒪` when `T ∈ 𝒪`: it is the evaluation `R[T] → 𝒪` at `T`. -/
theorem polynomialMap_eq_eval₂ {T : L} (hT : vL T ≤ 1) (p : vK.valuationSubring[X]) :
    polynomialMap vK T p = ((p.eval₂ (algebraMap vK.valuationSubring vL.valuationSubring)
      ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩ : vL.valuationSubring) : L) := by
  rw [← ValuationSubring.subtype_apply, Polynomial.hom_eval₂]
  rfl

theorem polynomialMap_mem {T : L} (hT : vL T ≤ 1) (p : vK.valuationSubring[X]) :
    polynomialMap vK T p ∈ vL.valuationSubring := by
  rw [polynomialMap_eq_eval₂ vK vL hT]
  exact SetLike.coe_mem _

/-- If `L = K(T)` and `L̃/K̃` is transcendental, then `T` is transcendental over `K`. -/
theorem transcendental_of_adjoin_eq_top {T : L} (hgen : IntermediateField.adjoin K {T} = ⊤)
    {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t)) :
    Transcendental K T := by
  intro halg
  have : Algebra.IsAlgebraic K (IntermediateField.adjoin K {T}) :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have hL : Algebra.IsAlgebraic K L := ⟨fun x ↦ by
    have hx : x ∈ IntermediateField.adjoin K {T} := hgen ▸ IntermediateField.mem_top
    exact (isAlgebraic_algHom_iff (IntermediateField.val _) Subtype.val_injective).mpr
      (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : IntermediateField.adjoin K {T}))⟩
  have h0 : Algebra.trdeg K L = 0 := trdeg_eq_zero_iff.mpr hL
  have h := (relRatRank_add_trdeg_le vK vL).trans h0.le
  have h1 := (one_le_trdeg_residueField vK vL ht).trans (le_add_self.trans h)
  exact absurd h1 (by norm_num)

theorem polynomialMap_injective {T : L} (hT : Transcendental K T) :
    Function.Injective (polynomialMap vK T) := by
  intro p q hpq
  have h : ∀ p : vK.valuationSubring[X],
      polynomialMap vK T p = aeval T (p.map vK.valuationSubring.subtype) := by
    intro p
    rw [aeval_def, eval₂_map]
    rfl
  rw [h, h] at hpq
  exact map_injective _ Subtype.val_injective (transcendental_iff_injective.mp hT hpq)

/-- **Stage 2 of Temkin's Proposition 4.3.1** (`lem:sm-lu-smooth-stage`, T:2997–3016): let `K` be
separably closed, `L = K(T)` with `T ∈ 𝒪`, `L̃/K̃` transcendental, and the residue of `T` algebraic
over `K̃` (the centre of `𝒪` on `Spec R[T]` is a closed point of the closed fibre). Then there are
`a, π ∈ R` with `π ∈ 𝔪_R ∖ 0` such that, for every lift `η : Spec L → Bl_{(π, T-a)} R[T]` of the
point given by `R[T] → L`, `𝒪` has a centre on the blow-up, and every centre `y` is the image of
the generic point `𝔪_R R[S]` of the closed fibre of the `π`-chart `Spec R[S]`, `S = (T - a)/π`
(the generic point of the exceptional component over the closed point), with
`trdeg (κ(y)/κ(𝔪_R)) ≥ 1`. (The blow-up is an isomorphism off `V(π, T - a)`,
`Blowups.smoothBlowup_isIso`.) -/
theorem smooth_stage [IsSepClosed K] {T : L} (hgen : IntermediateField.adjoin K {T} = ⊤)
    (hT : vL T ≤ 1) {t : vL.valuationSubring}
    (ht : Transcendental (ResidueField vK.valuationSubring) (residue vL.valuationSubring t))
    (halg : IsAlgebraic (ResidueField vK.valuationSubring)
      (residue vL.valuationSubring ⟨T, (Valuation.mem_valuationSubring_iff vL T).mpr hT⟩)) :
    ∃ (a π : vK.valuationSubring) (_ : Fact (π ≠ 0)), π ∈ maximalIdeal vK.valuationSubring ∧
      ∀ η : Spec (.of L) ⟶ affineBlowup (smoothCenter π a),
        η ≫ affineBlowupStructure (smoothCenter π a) =
          Spec.map (CommRingCat.ofHom (polynomialMap vK T)) →
        (∃ y, IsCentre η ⟨vL.valuationSubring⟩ y) ∧
          ∀ y, IsCentre η ⟨vL.valuationSubring⟩ y →
            (∃ P : Spec (.of vK.valuationSubring[X]),
              P.asIdeal = Ideal.map C (maximalIdeal vK.valuationSubring) ∧
                y = smoothParamChartInclusion π a P) ∧
            1 ≤ fiberTrdeg (smoothBlowupMorphism π a) y := by
  obtain ⟨a, π, ha, hπ, hπ1, -, s, hs, hstr⟩ :=
    exists_transcendental_residue_sub vK vL T hgen hT ht halg
  let a' : vK.valuationSubring := ⟨a, (Valuation.mem_valuationSubring_iff vK a).mpr ha⟩
  let π' : vK.valuationSubring := ⟨π, (Valuation.mem_valuationSubring_iff vK π).mpr hπ1.le⟩
  have hπ' : π' ≠ 0 := fun h ↦ hπ (congrArg Subtype.val h)
  have : Fact (π' ≠ 0) := ⟨hπ'⟩
  have hπm : π' ∈ maximalIdeal vK.valuationSubring := by
    rw [ValuationSubring.valuation_lt_one_iff]
    exact (Valuation.isEquiv_valuation_valuationSubring vK).lt_one_iff_lt_one.mp hπ1
  refine ⟨a', π', this, hπm, fun η hη ↦ ?_⟩
  set ι := polynomialMap vK T
  have hι : Function.Injective ι :=
    polynomialMap_injective vK (transcendental_of_adjoin_eq_top vK vL hgen ht)
  have hO : ∀ p, ι p ∈ vL.valuationSubring := polynomialMap_mem vK vL hT
  have hsL : (ι X - ι (C a')) / ι (C π') = (s : L) := by
    rw [hs, polynomialMap_X, polynomialMap_C, polynomialMap_C]
  have hs' : (ι X - ι (C a')) / ι (C π') ∈ vL.valuationSubring := by
    rw [hsL]
    exact SetLike.coe_mem _
  let V : RiemannZariskiSpace L := ⟨vL.valuationSubring⟩
  obtain ⟨hcen, huniq⟩ := smoothBlowup_centre π' a' hι V hO hs' hη
  -- the residue of `S` is transcendental: the centre in the chart is `𝔪_R R[S]`
  have hres : ∀ q : vK.valuationSubring[X],
      (⟨smoothChartRingHom π' a' hι q, smoothChartRingHom_mem π' a' hι hO hs' q⟩ :
        vL.valuationSubring) ∈ maximalIdeal vL.valuationSubring ↔
        ∀ i, q.coeff i ∈ maximalIdeal vK.valuationSubring := by
    intro q
    have hg : smoothChartRingHom π' a' hι = Polynomial.eval₂RingHom
        (vL.valuationSubring.subtype.comp
          (algebraMap vK.valuationSubring vL.valuationSubring)) (s : L) := by
      refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
      · rw [smoothChartRingHom_C, polynomialMap_C]
        simp
      · rw [smoothChartRingHom_X, hsL]
        simp
    have heq : (⟨smoothChartRingHom π' a' hι q, smoothChartRingHom_mem π' a' hι hO hs' q⟩ :
        vL.valuationSubring) =
          q.eval₂ (algebraMap vK.valuationSubring vL.valuationSubring) s := by
      apply Subtype.ext
      change smoothChartRingHom π' a' hι q = vL.valuationSubring.subtype _
      rw [Polynomial.hom_eval₂, hg]
      rfl
    have hresq : residue vL.valuationSubring
        (q.eval₂ (algebraMap vK.valuationSubring vL.valuationSubring) s) =
          aeval (residue vL.valuationSubring s) (q.map (residue vK.valuationSubring)) := by
      rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
      rfl
    rw [heq, ← residue_eq_zero_iff, hresq]
    constructor
    · intro h i
      have h0 := (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hstr) _ h
      have := congrArg (coeff · i) h0
      simpa [coeff_map, residue_eq_zero_iff] using this
    · intro h
      have h0 : q.map (residue vK.valuationSubring) = 0 := by
        ext i
        simpa [coeff_map, residue_eq_zero_iff] using h i
      rw [h0, map_zero]
  refine ⟨⟨_, hcen⟩, fun y hy ↦ ?_⟩
  rw [huniq y hy]
  exact ⟨⟨_, smoothBlowupCentre_asIdeal π' a' hι V hO hs' hres, rfl⟩,
    one_le_fiberTrdeg_smoothBlowupCentre π' a' hι V hO hs' hres⟩

end Smooth

end DeJongAlterations.StableModification.LocalUniformization

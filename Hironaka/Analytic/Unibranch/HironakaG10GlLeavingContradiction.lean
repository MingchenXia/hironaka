import Hironaka.Analytic.Unibranch.HironakaG10SbLemma445

/-!
# Lemma 4.4.5 (G2): the leaving-point contradiction (Hironaka's disc argument, natively)

Lane G10GL, run 0081, item GL-1 (`work/hironaka-run0081-20261117/G10GL/STATUS.md`).  Consumer: the `hG2` binder of
`Hironaka.Analytic.Unibranch.HironakaG10SbLemma445.hT_of_strictFlat_of_upper`.  Source: Hironaka 1975, Lemma 4.4.5, proof
(printed p. 538): if `|Z_{p1}| ≠ |Z_p^*|`, a point `t ≠ t₀` of `Z_{p1}` near `t₀` lies over `Z_p ∩ D` off the strict
transform, where (4.4.4) and Lemma 3.1 force a nonzero kernel of `F(π t) → F₁(t)`, contradicting the isomorphism
(ii) of fibres along `Z_{p1}`.

Natively, at `x' ∈ T(Z)` and a local flattener `Z₁` of the strict-transform family through `x'`, two LOCAL inputs:

* (hle) `σ^♯ (germFlattener f (σ x')) ≤ Z₁.H x'` (the total transform is flat over `Z₁` at `x'`: Nakayama + Th. 2.5);
* (hfib) near `x'`, at every point `y'` of `|Z₁|` and every point `y` of the old fibre over `σ y'`, there is a point
  `y''` of the strict transform over `(y, y')` whose fibre map `𝒪_{Y,y}/𝔪 → 𝒪_{Y',y''}/𝔪` is injective
  (Hironaka's (ii) along `Z₁`);

give the support-germ inclusion `|Z₁| ⊆ T(Z)` near `x'`:

* `stepQ`, `stepQ_comp` — the strict-transform map `q : Y' ⟶ Y` of one step and its square;
* `eventually_map_le_of_le` — (hle) spreads: `σ^♯ Z.H(σ y') ≤ Z₁.H y'` near `x'` (coherence of `Z`, `Z₁`);
* `onStrictTransform_of_not_mem_nonunitLocus` — off the centre every point is on the germ strict transform;
* `onStrictTransform_of_fibre` — at a point in the centre, a point off the germ strict transform satisfies the leaving
  condition (Lemma 3.2 for sum centres, `principalPullbackAt_of_sumCentre`), hence the fibre decrease (Lemma 3.1,
  `exists_fibre_decrease_of_principal`), which contradicts an injective fibre map;
* `eventually_mem_transportedSupport_of_fibre` — **(G2)** at one point;
* `hG2_of_le_of_fibre` — the `hG2` binder of `hT_of_strictFlat_of_upper`, from (hle) and (hfib) quantified alike.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener

noncomputable section

/-! ### The strict-transform map of one step -/

/-- The strict-transform map `q : Y' ⟶ Y` of one step. -/
def stepQ (s : Stage) (c : AdmissibleCentre s.f) : (nextWith s c).Y ⟶ s.Y :=
  let _ := c.finiteType
  strictQ c.B c.b s.f

/-- The square of one step: `f' ≫ σ = q ≫ f`. -/
theorem stepQ_comp (s : Stage) (c : AdmissibleCentre s.f) :
    (nextWith s c).f ≫ stepσ s c = stepQ s c ≫ s.f := by
  let _ := c.finiteType
  exact strictP_comp c.B c.b c.dense s.f

/-! ### (hle) spreads -/

/-- **The pull-back inclusion spreads.**  If `σ^♯` of the old flattener lies in `Z₁` at a point `x'` with `σ x' ∈ |Z|`
and `x' ∈ |Z₁|`, then `σ^♯ Z.H(σ y') ≤ Z₁.H y'` at every point near `x'`. -/
theorem eventually_map_le_of_le (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    (Z₁ : LocalFlattener (nextWith s c).f) (x' : (nextWith s c).X.obj.left)
    (hx : (stepσ s c).hom.left.base x' ∈ Z.support) (hx₁ : x' ∈ Z₁.V)
    (hle : Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
      (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤ Z₁.H x') :
    ∀ᶠ y' in 𝓝 x', Ideal.map ((stepσ s c).hom.left.stalkMap y').hom
      (Z.H ((stepσ s c).hom.left.base y')) ≤ Z₁.H y' := by
  set σ := (stepσ s c).hom.left with hσ
  obtain ⟨W, hxW, r, sec, hsec⟩ := Z.fg _ hx.1
  rw [← Z.H_eq_germFlattener hx, hsec _ hxW hx.1] at hle
  -- each pulled generator stays in `Z₁` near `x'`
  have hgen : ∀ i, ∀ᶠ y' in 𝓝 x', ∀ (hy : σ.base y' ∈ W),
      (σ.stalkMap y').hom ((s.X.obj.left.presheaf.germ W (σ.base y') hy).hom (sec i)) ∈ Z₁.H y' := by
    intro i
    have hi : (σ.stalkMap x').hom ((s.X.obj.left.presheaf.germ W (σ.base x') hxW).hom (sec i)) ∈ Z₁.H x' :=
      hle (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩))
    rw [stalkMap_germ_hom σ W x' hxW (sec i)] at hi
    obtain ⟨U, hxU, u, hu, hU⟩ := spreads_localFlattener Z₁ x' hx₁ _ hi
    filter_upwards [eventually_germ_eq hxU hxW u ((σ.c.app (op W)).hom (sec i)) hu,
      U.isOpen.mem_nhds hxU] with y' hy' hyU hyW
    rw [stalkMap_germ_hom σ W y' hyW (sec i), ← hy' hyU hyW]
    exact hU y' hyU
  filter_upwards [eventually_all.mpr hgen,
    (W.isOpen.preimage σ.base.hom.continuous).mem_nhds hxW,
    (Z.isOpen.preimage σ.base.hom.continuous).mem_nhds hx.1] with y' hy' hyW hyV
  rw [hsec _ hyW hyV, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hy' i hyW

/-- Near `x'`, every point of `|Z₁|` lies over `|Z|`. -/
theorem eventually_mem_support_of_le (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    (Z₁ : LocalFlattener (nextWith s c).f) (x' : (nextWith s c).X.obj.left)
    (hx : (stepσ s c).hom.left.base x' ∈ Z.support) (hx₁ : x' ∈ Z₁.V)
    (hle : Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
      (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤ Z₁.H x') :
    ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → (stepσ s c).hom.left.base y' ∈ Z.support := by
  filter_upwards [eventually_map_le_of_le s c Z Z₁ x' hx hx₁ hle,
    (Z.isOpen.preimage (stepσ s c).hom.left.base.hom.continuous).mem_nhds hx.1] with y' hy' hyV hy₁
  refine ⟨hyV, fun htop => hy₁.2 ?_⟩
  rw [htop, Ideal.map_top] at hy'
  exact top_le_iff.mp hy'

/-! ### Points on and off the germ strict transform -/

/-- Off the centre every point is on the germ strict transform of every proper ideal. -/
theorem onStrictTransform_of_not_mem_nonunitLocus (s : Stage) (c : AdmissibleCentre s.f)
    (y' : (nextWith s c).X.obj.left)
    (hc : (stepσ s c).hom.left.base y' ∉ nonunitLocus c.B c.b) :
    OnStrictTransform (stepσ s c) y' (germFlattener s.f ((stepσ s c).hom.left.base y'))
      (centreIdeal c ((stepσ s c).hom.left.base y')) := by
  intro G _ hG htop
  have hrange : centreIdeal c ((stepσ s c).hom.left.base y') = ⊤ := by
    by_contra h
    exact hc h
  have hGu : IsUnit G := Ideal.span_singleton_eq_top.mp (hG.symm.trans
    ((congrArg (Ideal.map ((stepσ s c).hom.left.stalkMap y').hom) hrange).trans (Ideal.map_top _)))
  have hle := strictIdeal_le_maximalIdeal_of_isUnit ((stepσ s c).hom.left.stalkMap y').hom
    (germFlattener s.f ((stepσ s c).hom.left.base y')) (centreIdeal c ((stepσ s c).hom.left.base y'))
    (germFlattener_le_maximalIdeal s.f _) G hGu
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- **The leaving-point contradiction** (Hironaka p. 538 with Lemmas 3.1, 3.2): at a point `y'` over the centre of a
sum-centre step, if for every point `y` of the old fibre some point `y''` of the strict transform over `(y, y')` has an
injective fibre map, then `y'` is on the germ strict transform of the old flattener. -/
theorem onStrictTransform_of_fibre (s : Stage) (c : AdmissibleCentre s.f) (β : ℕ)
    (hβ : IsSumCentreFor c.B c.b s.f β) (y' : (nextWith s c).X.obj.left)
    (hc : (stepσ s c).hom.left.base y' ∈ nonunitLocus c.B c.b)
    (hfib : ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
      ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
        (nextWith s c).f.hom.left.base y'' = y' ∧
        Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
          fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    OnStrictTransform (stepσ s c) y' (germFlattener s.f ((stepσ s c).hom.left.base y'))
      (centreIdeal c ((stepσ s c).hom.left.base y')) := by
  let _ := c.finiteType
  by_contra hns
  unfold OnStrictTransform at hns
  push Not at hns
  obtain ⟨G, hG, hD, htop⟩ := hns
  obtain ⟨IS, α, hαβ, hAR, hB⟩ := hβ _ hc
  have hB' : centreIdeal c ((stepσ s c).hom.left.base y') = IS ^ β ⊔
      germFlattener s.f ((stepσ s c).hom.left.base y') := hB
  rw [hB'] at hD htop
  have hP : PrincipalPullbackAt s.f (stepσ s c) (nextWith s c).f y' :=
    principalPullbackAt_of_sumCentre c.B c.b c.dense s.f y' _ IS α β hαβ hAR hB rfl G hG hD htop
  obtain ⟨y, hy, hdec⟩ := exists_fibre_decrease_of_principal s.f (stepσ s c) (nextWith s c).f
    (stepQ s c) (stepQ_comp s c) y' hP
  obtain ⟨y'', hq, hp, hinj⟩ := hfib y hy
  obtain ⟨h, hh, hqh⟩ := hdec y'' hq hp
  exact hh (hinj hqh)

/-! ### (G2) -/

/-- **(G2) at one point** (Hironaka Lemma 4.4.5, proof, p. 538): from (hle) and (hfib), near `x' ∈ T(Z)` every point
of a local flattener `Z₁` of the strict-transform family through `x'` lies in `T(Z)`. -/
theorem eventually_mem_transportedSupport_of_fibre (s : Stage) (c : AdmissibleCentre s.f) (β : ℕ)
    (hβ : IsSumCentreFor c.B c.b s.f β) (Z : LocalFlattener s.f)
    (x' : (nextWith s c).X.obj.left) (hx' : x' ∈ transportedSupport s c Z)
    (Z₁ : LocalFlattener (nextWith s c).f) (hx₁ : x' ∈ Z₁.support)
    (hle : Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
      (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤ Z₁.H x')
    (hfib : ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
      ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
        ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
          (nextWith s c).f.hom.left.base y'' = y' ∧
          Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom (fibreIdealAt (nextWith s c).f y'') ≤
            fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z := by
  filter_upwards [eventually_mem_support_of_le s c Z Z₁ x' hx'.1 hx₁.1 hle, hfib] with y' hZ hf hy₁
  refine ⟨hZ hy₁, ?_⟩
  by_cases hc : (stepσ s c).hom.left.base y' ∈ nonunitLocus c.B c.b
  · exact onStrictTransform_of_fibre s c β hβ y' hc (hf hy₁)
  · exact onStrictTransform_of_not_mem_nonunitLocus s c y' hc

/-- **The `hG2` binder of `HironakaG10SbLemma445.hT_of_strictFlat_of_upper`**, from (hle) and (hfib) quantified like
it. -/
theorem hG2_of_le_of_fibre
    (hle : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
              (germFlattener s.f ((stepσ s c).hom.left.base x')) ≤ Z₁.H x')
    (hfib : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z :=
  fun s hc hp c β hβ hfl Z x' hx' Z₁ hx₁ =>
    eventually_mem_transportedSupport_of_fibre s c β hβ Z x' hx' Z₁ hx₁
      (hle s hc hp c β hβ hfl Z x' hx' Z₁ hx₁) (hfib s hc hp c β hβ hfl Z x' hx' Z₁ hx₁)

end

end Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction

import Hironaka.Resolution.HironakaG10ChowFlatModelOpen
import Hironaka.Analytic.Unibranch.HironakaG10NfPresentation

/-!
# N5.b (P3a): graph-chart presentations from an actual chart square

Lane G10N5, run 0081 (step S3 of the N5.b plan in `G10HT/STATUS.md`).  Let `σ : Y → X` be a morphism of locally ringed
spaces, `F₀ : (N ⊇ D) → X` and `m : (M ⊇ C) → Y` open immersions of actual reduced models, and `f : M → N` a
holomorphic representative of `σ` in these charts: `actualSubspaceMap f ≫ F₀ = m ≫ σ`.  Then at a point `c ∈ C`:

* `chart_square` — the native stalk map of `σ`, read in the two chart quotients `𝒪_{N,f c} ⧸ I_D` and
  `𝒪_{M,c} ⧸ I_C`, is the native germ pullback of `f` at `c`;
* **`graphChartPresentation_of_square`** — if the source chart ideal is the analytic graph chart ideal
  `chartIdeal (evPoly d r b) j g I_D`, the germ pullback of `f` at `c` is the tangential pullback, and the centre
  corresponds to `(g)`, then `σ^♯` at `m c` is a `GraphChartPresentation` (so N5 holds there,
  `HironakaG10NfPresentation.n5Holds_of_presentation`).

Generic (no blowup data); no named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaActualWholeStalkHolomorphicPullback
  HironakaRelativeNormalIdeal HironakaG10ChowFlatModelOpen
  Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation
  Hironaka.Analytic.Unibranch.HironakaG10NfPresentation

noncomputable section

/-! ### Generic stalk transports -/

/-- The ring isomorphism of stalks of an open immersion. -/
def oiStalkEquiv {S T : LocallyRingedSpace.{0}} (k : S ⟶ T) [LocallyRingedSpace.IsOpenImmersion k] (s : S) :
    T.presheaf.stalk (k.base s) ≃+* S.presheaf.stalk s :=
  haveI : IsIso (k.stalkMap s) := LocallyRingedSpace.IsOpenImmersion.stalk_iso k s
  (asIso (k.stalkMap s)).commRingCatIsoToRingEquiv

theorem oiStalkEquiv_apply {S T : LocallyRingedSpace.{0}} (k : S ⟶ T) [LocallyRingedSpace.IsOpenImmersion k]
    (s : S) (r : T.presheaf.stalk (k.base s)) : oiStalkEquiv k s r = (k.stalkMap s).hom r :=
  rfl

/-- The stalk map of `σ` at `y`, read at a point `x` equal to `σ y`. -/
abbrev fibreMap {T S : LocallyRingedSpace.{0}} (σ : T ⟶ S) (x : S) (y : T) (h : σ.base y = x) :
    S.presheaf.stalk x →+* T.presheaf.stalk y :=
  (σ.stalkMap y).hom.comp (eqToHom (congrArg S.presheaf.stalk h.symm)).hom

theorem stalkMap_eq_of_eq {T S : LocallyRingedSpace.{0}} (Θ₁ Θ₂ : T ⟶ S) (H : Θ₁ = Θ₂) (t : T)
    (hb : Θ₂.base t = Θ₁.base t) (r : S.presheaf.stalk (Θ₁.base t)) :
    (Θ₁.stalkMap t).hom r =
      (Θ₂.stalkMap t).hom ((eqToHom (congrArg S.presheaf.stalk hb.symm)).hom r) := by
  subst H
  rfl

/-- A round trip of transports between stalks is the identity. -/
theorem eqToHom_stalk_roundtrip {T : LocallyRingedSpace.{0}} {a b : T} (h₁ : a = b) (h₂ : b = a)
    (r : T.presheaf.stalk a) :
    (eqToHom (congrArg T.presheaf.stalk h₂)).hom ((eqToHom (congrArg T.presheaf.stalk h₁)).hom r) = r := by
  subst h₁
  rfl

/-- **Stalks of a commutative square** (`HironakaG10SbBaseChartStalk.stalk_square_apply`). -/
theorem stalk_square_apply {A B C D : LocallyRingedSpace.{0}} (g : A ⟶ C) (i : C ⟶ D)
    (j : A ⟶ B) (q : B ⟶ D) (H : j ≫ q = g ≫ i) (a : A) (x : D) (h : q.base (j.base a) = x)
    (hc : i.base (g.base a) = x) (u : D.presheaf.stalk (i.base (g.base a))) :
    (j.stalkMap a).hom ((q.stalkMap (j.base a)).hom
      ((eqToHom (congrArg D.presheaf.stalk h.symm)).hom
        ((eqToHom (congrArg D.presheaf.stalk hc)).hom u))) =
      (g.stalkMap a).hom ((i.stalkMap (g.base a)).hom u) := by
  subst h
  have hb : (g ≫ i).base a = (j ≫ q).base a := hc
  have e1 := stalkMap_eq_of_eq (j ≫ q) (g ≫ i) H a hb
    ((eqToHom (congrArg D.presheaf.stalk hc)).hom u)
  have e2 : (eqToHom (congrArg D.presheaf.stalk hb.symm)).hom
      ((eqToHom (congrArg D.presheaf.stalk hc)).hom u) = u :=
    eqToHom_stalk_roundtrip hc hb.symm u
  rw [e2] at e1
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at e1
  exact e1

/-! ### The chart square -/

section Square

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel e) M] [IsComplexManifold e M]
  [ChartedSpace (ComplexModel d) N] [IsComplexManifold d N]
  {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel e) 𝓘(ℂ, ComplexModel d) ∞ f)
  {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D)
  {X Y : LocallyRingedSpace.{0}} (σ : Y ⟶ X)
  (F₀ : actualSubspaceLocallyRingedSpace (n := d) D ⟶ X) [LocallyRingedSpace.IsOpenImmersion F₀]
  (m : actualSubspaceLocallyRingedSpace (n := e) C ⟶ Y) [LocallyRingedSpace.IsOpenImmersion m]
  (hsq : actualSubspaceMap hf hCD ≫ F₀ = m ≫ σ)

omit [LocallyRingedSpace.IsOpenImmersion F₀] [LocallyRingedSpace.IsOpenImmersion m] in
include hsq in
theorem square_base (c : C) :
    σ.base (m.base c) = F₀.base ((actualSubspaceMap hf hCD).base c) :=
  (congrArg (fun k => k.base c) hsq).symm

/-- The base chart isomorphism `𝒪_{X, F₀ s} ≃ 𝒪_{N,s} ⧸ I_D`. -/
def baseEquiv (s : D) :
    X.presheaf.stalk (F₀.base s) ≃+*
      HolGerm (ComplexModel d) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := d) D) s.val s.val
        (mem_chart_source _ _) :=
  (oiStalkEquiv F₀ s).trans (actualSubspaceStalkChartEquiv (n := d) D s)

include hsq in
/-- **The chart square**: the native stalk map of `σ`, read in the chart quotients, is the germ pullback of `f`. -/
theorem chart_square (c : C) (k : HolGerm (ComplexModel d)) :
    actualSubspaceStalkChartEquiv (n := e) C c (oiStalkEquiv m c
      (fibreMap σ _ (m.base c) (square_base hf hCD σ F₀ m hsq c)
        ((baseEquiv F₀ ((actualSubspaceMap hf hCD).base c)).symm (Ideal.Quotient.mk _ k)))) =
      Ideal.Quotient.mk _ (actualHolomorphicGermPullback hf c.val k) := by
  set s := (actualSubspaceMap hf hCD).base c
  set r := (actualStalkChartEquiv (n := d) (f c.val)).symm k
  have hu : (actualSubspaceStalkChartEquiv (n := d) D s).symm (Ideal.Quotient.mk _ k) =
      (actualSubspaceInclusion (n := d) D).stalkMap (actualSubspaceMapTop hf hCD c) r := by
    apply (actualSubspaceStalkChartEquiv (n := d) D s).injective
    rw [RingEquiv.apply_symm_apply]
    have h1 : actualSubspaceStalkChartEquiv (n := d) D s
        ((actualSubspaceInclusion (n := d) D).stalkMap s r) = Ideal.Quotient.mk _ k :=
      (inclusion_stalk_chart (m := d) D s r).trans
        (congrArg (Ideal.Quotient.mk _) ((actualStalkChartEquiv (n := d) (f c.val)).apply_symm_apply k))
    exact h1.symm
  have hw : (baseEquiv F₀ s).symm (Ideal.Quotient.mk _ k) =
      (oiStalkEquiv F₀ s).symm ((actualSubspaceStalkChartEquiv (n := d) D s).symm (Ideal.Quotient.mk _ k)) :=
    rfl
  have key := stalk_square_apply (actualSubspaceMap hf hCD) F₀ m σ hsq.symm c (F₀.base s)
    (square_base hf hCD σ F₀ m hsq c) rfl ((baseEquiv F₀ s).symm (Ideal.Quotient.mk _ k))
  have hF : (F₀.stalkMap s).hom ((baseEquiv F₀ s).symm (Ideal.Quotient.mk _ k)) =
      (actualSubspaceStalkChartEquiv (n := d) D s).symm (Ideal.Quotient.mk _ k) := by
    rw [hw]
    exact RingEquiv.apply_symm_apply (oiStalkEquiv F₀ s) _
  rw [hF, hu] at key
  have hc := actualSubspaceMap_stalk_chart hf hCD c r
  rw [RingEquiv.apply_symm_apply] at hc
  rw [oiStalkEquiv_apply]
  exact (congrArg (actualSubspaceStalkChartEquiv (n := e) C c) key).trans hc

end Square

/-! ### Graph-chart presentations from a chart square -/

section Presentation

variable {d r : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel (d + r)) M] [IsComplexManifold (d + r) M]
  [ChartedSpace (ComplexModel d) N] [IsComplexManifold d N]
  {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel (d + r)) 𝓘(ℂ, ComplexModel d) ∞ f)
  {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D)
  {X Y : LocallyRingedSpace.{0}} (σ : Y ⟶ X)
  (F₀ : actualSubspaceLocallyRingedSpace (n := d) D ⟶ X) [LocallyRingedSpace.IsOpenImmersion F₀]
  (m : actualSubspaceLocallyRingedSpace (n := d + r) C ⟶ Y) [LocallyRingedSpace.IsOpenImmersion m]
  (hsq : actualSubspaceMap hf hCD ≫ F₀ = m ≫ σ)

include hsq in
/-- **N5.b (S3).**  A chart square whose source chart ideal is the analytic graph chart ideal, with tangential germ
pullback and centre `(g)`, gives a graph-chart presentation of the native stalk map. -/
theorem graphChartPresentation_of_square (hr : 0 < r) (b : Fin r → ℂ) (j : Fin r)
    (g : Fin r → HolGerm (ComplexModel d)) (c : C)
    (hK : wholeChartStalkIdeal (vanishingIdeal (n := d + r) C) c.val c.val (mem_chart_source _ _) =
      chartIdeal (evPoly d r b) j g
        (wholeChartStalkIdeal (vanishingIdeal (n := d) D) (f c.val) (f c.val) (mem_chart_source _ _)))
    (hpull : actualHolomorphicGermPullback hf c.val = tangentPullback d r)
    (Dc : Ideal (X.presheaf.stalk (F₀.base ((actualSubspaceMap hf hCD).base c))))
    (hD : Ideal.map (baseEquiv F₀ ((actualSubspaceMap hf hCD).base c)).toRingHom Dc =
      Ideal.map (Ideal.Quotient.mk _) (Ideal.span (Set.range g))) :
    GraphChartPresentation (fibreMap σ _ (m.base c) (square_base hf hCD σ F₀ m hsq c)) Dc := by
  set s := (actualSubspaceMap hf hCD).base c
  set α := baseEquiv F₀ s
  let ρ := (oiStalkEquiv m c).trans ((actualSubspaceStalkChartEquiv (n := d + r) C c).trans
    (Ideal.quotEquivOfEq hK))
  refine ⟨d, r, hr, b, j, g, _, α, ρ, ?_, hD⟩
  intro a
  obtain ⟨k, hk⟩ := Ideal.Quotient.mk_surjective (α a)
  have ha : a = α.symm (Ideal.Quotient.mk _ k) := by rw [hk, RingEquiv.symm_apply_apply]
  subst ha
  rw [RingEquiv.apply_symm_apply, chartMap_mk, evPoly_C]
  change Ideal.quotEquivOfEq hK (actualSubspaceStalkChartEquiv (n := d + r) C c (oiStalkEquiv m c
    (fibreMap σ _ (m.base c) (square_base hf hCD σ F₀ m hsq c) (α.symm (Ideal.Quotient.mk _ k))))) = _
  rw [chart_square hf hCD σ F₀ m hsq c k, hpull, Ideal.quotEquivOfEq_mk]
  rfl

end Presentation

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare

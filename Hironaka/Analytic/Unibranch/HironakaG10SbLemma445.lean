import Hironaka.Analytic.Unibranch.HironakaG10SbTransportGermUpper
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
import Hironaka.Analytic.Unibranch.HironakaG10RdFinal

/-!
# Hironaka's Lemma 4.4.5 for one sum-centre step: the `hT` input of G10, reduced to (i) and (G2)

Lane G10SB, run 0081, G10-03-09 (consumer: `HironakaG10RdFinal.hironakaFlattening_of_frisch`, binder `hT`).
Hironaka 1975, Lemma 4.4.5 and its proof, printed pp. 537–538.  The conclusion below is LITERALLY the type of the
`hT` binder; it holds for EVERY local flattener `Z` of the stage (no trackedness is used anywhere in the chain:
`HironakaG10SbFlattenerSupportGerm`, `HironakaG10SbTransportClosed`, `HironakaG10SbTransportGermUpper`).

* `hT_of_germ` — `hT` from the support-germ statement (Germ) (`Lemma445Germ`-shaped hypothesis, quantified exactly
  as `hT`, so its proof may use compactness, properness, the sum-centre property and flatness over the centre);
* `germ_of_strictFlat_of_upper` — (Germ) from Hironaka's (i) (the strict-transform family is flat over the germ strict
  transform `Z^*`, for the local exceptional generator) and (G2) (`|Z₁| ⊆ T(Z)` near each point of `T(Z)`);
* `hT_of_strictFlat_of_upper` — the composite: **`hT` from (i) and (G2)**;
* `hironakaFlattening_of_frisch_strictFlat_upper` — `HironakaFlattening` from `hF1`, `hF2`, (i), (G2) (type check of
  the splice into `HironakaG10RdFinal.hironakaFlattening_of_frisch`).

No named input; the two remaining hypotheses are explicit binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SbLemma445

open Hironaka HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
  Hironaka.Analytic.Unibranch.HironakaG10SbTransportGermUpper Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds

noncomputable section

/-- **`hT` from the support-germ statement (Germ).**  The conclusion is literally the `hT` binder of
`HironakaG10RdFinal.hironakaFlattening_of_frisch`. -/
theorem hT_of_germ
    (hgerm : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', (y' ∈ transportedSupport s c Z ↔ y' ∈ Z₁.support)) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  fun s hc hp c β hβ hfl Z =>
    exists_localFlattener_transport_of_germs s hp c Z (hgerm s hc hp c β hβ hfl Z)

/-- **(Germ) from Hironaka's (i) and (G2).**  (i): at every point of `T(Z)`, for every section generating the pulled
centre with a regular germ, the strict-transform family is flat over the germ strict transform of the flattener;
(G2): near every point of `T(Z)` the support of every local flattener through it lies in `T(Z)`. -/
theorem germ_of_strictFlat_of_upper
    (hi : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)))
    (hG2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', (y' ∈ transportedSupport s c Z ↔ y' ∈ Z₁.support) := by
  intro s hc hp c β hβ hfl Z x' hx' Z₁ hx₁
  filter_upwards [eventually_mem_support_of_flat_strict s c Z x' hx'
      (hi s hc hp c β hβ hfl Z x' hx') Z₁ hx₁,
    hG2 s hc hp c β hβ hfl Z x' hx' Z₁ hx₁] with y' h1 h2
  exact ⟨h1, h2⟩

/-- **`hT` from Hironaka's (i) and (G2)** (literally the `hT` binder of `hironakaFlattening_of_frisch`). -/
theorem hT_of_strictFlat_of_upper
    (hi : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)))
    (hG2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  hT_of_germ (germ_of_strictFlat_of_upper hi hG2)


/-- **Hironaka's flattening theorem from Frisch's two theorems and Hironaka's (i), (G2) of Lemma 4.4.5.** -/
theorem hironakaFlattening_of_frisch_strictFlat_upper
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hi : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
            (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
            IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
            Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
                (centreIdeal c ((stepσ s c).hom.left.base x')) =
              Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
            FlatOverAt (nextWith s c).f x'
              (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
                (germFlattener s.f ((stepσ s c).hom.left.base x'))
                (centreIdeal c ((stepσ s c).hom.left.base x'))
                ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)))
    (hG2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support → y' ∈ transportedSupport s c Z) :
    HironakaG10ChowFlatteningReduction.HironakaFlattening :=
  HironakaG10RdFinal.hironakaFlattening_of_frisch hF1 hF2 (hT_of_strictFlat_of_upper hi hG2)

end

end Hironaka.Analytic.Unibranch.HironakaG10SbLemma445

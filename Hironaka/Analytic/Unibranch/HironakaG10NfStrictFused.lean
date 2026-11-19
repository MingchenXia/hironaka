import Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonicalPre

/-!
# H3.4 (`strict`, fused generic form): the fibre conjunct from the two MORPHISM squares

Lane G10H3, run 0081 (field `strict` of `HironakaG10NfGeoFibreModel.GeoFibreModel`).

Feeding `HironakaG10NfStrictCanonical.strict_builder` with the stalk-level readouts (`sourceReadout`,
`canonical_square_joint`) at the canonical chart is slow (> 10 min): stalk-level statements of different modules
carry different (defeq) instance constants.  Here both stalk squares are derived INSIDE a generic lemma (in the
variables of `HironakaG10NfChartStalk`): the source readout from the projection law `K ≫ πA = geomProj ≫ chartX`
(`readout_generic`), the target square from the morphism square `ci ≫ (sc ≫ ind) = actualSubspaceMap f ≫ tc`
(`square_apply`, `targetStalkToJoint_strict_square`).

* `strict_generic` — the fibre conjunct `q^{♯-1}(ind^♯ 𝔪) ⊆ F^♯ 𝔪` at a strict chart point, from the two morphism
  squares, the torsion bound `Tors ⊆ ψ(𝔪)` and the native fibre identity.

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStrictFused

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic
  HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  (a : ProductNormalCharts n r P) (hr : 0 < r) (W : Set (P × ComplexModel r)) (j : Fin r)
  (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)
  {m : ℕ} {Yt : Type} [TopologicalSpace Yt] [ChartedSpace (ComplexModel m) Yt] [IsComplexManifold m Yt]
  (f : domG a j v → Yt) (V : Set Yt)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel m) ∞ f) (hV : IsComplexAnalyticSubset (n := m) V)
  (hWa : IsComplexAnalyticSubset (n := n+r) W)
  (h0 : (0 : ComplexModel (n+r)) ∈ recenteredTargetOpen n r j v (canonicalTargetOpen a j))
  (hland : strictG a W j v ⊆ f ⁻¹' V)
  (hraw : ∀ y : domG a j v, Ideal.map ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj)
      (projG_contMDiff a j v hvj)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj y)) ≤
    rawAnalyticIdeal n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) y)

/-- **The fibre conjunct of `strict` from the two morphism squares (fused generic form).** -/
theorem strict_generic {A Xc Bl Yc : LocallyRingedSpace.{0}}
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A) (πA : A ⟶ Xc)
    (chartX : actualSubspaceLocallyRingedSpace (n := n+r) W ⟶ Xc)
    (hsq : K ≫ πA = geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hWa.isClosed ≫ chartX)
    (ind : A ⟶ Bl) (Fm : Xc ⟶ Yc) (tc : actualSubspaceLocallyRingedSpace (n := m) V ⟶ Bl)
    (ci : actualSubspaceLocallyRingedSpace (n := n+r) (strictG a W j v) ⟶
      actualSubspaceLocallyRingedSpace (n := n+r) (strictChartCarrier a W j))
    (hci : (chartIsoG a W j v hvj).hom = ci) [LocallyRingedSpace.IsOpenImmersion ci]
    (sc : actualSubspaceLocallyRingedSpace (n := n+r) (strictChartCarrier a W j) ⟶ A)
    (hsc : strictChartTo a W K j = sc) [LocallyRingedSpace.IsOpenImmersion sc]
    (H : ci ≫ (sc ≫ ind) = actualSubspaceMap hf (fun _ hx => hland hx) ≫ tc)
    (y : domG a j v)
    (hy : y ∈ localDomain n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) h0 (recenteredCoordinateSubset_analytic a j v W hWa))
    (hΓ : projG a j v hvj y ∈ W) (hyS : y ∈ strictG a W j v) (hyV : f y ∈ V)
    (hs : chartX.base ⟨projG a j v hvj y, hΓ⟩ = πA.base (sc.base (ci.base ⟨y, hyS⟩)))
    (hT : pivotTorsion (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
        (WG a W j v) f V y ≤
      Ideal.map ((targetStalkToJoint (n := m) n r j (fun i => v i)
        (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV y hyV).comp
          (tc.stalkMap ⟨f y, hyV⟩).hom) (IsLocalRing.maximalIdeal _))
    (hFI : ∀ rr : Xc.presheaf.stalk (chartX.base ⟨projG a j v hvj y, hΓ⟩),
      betaG a W j v hvj f V hraw y hΓ ((chartX.stalkMap ⟨projG a j v hvj y, hΓ⟩).hom rr) ∈
          Ideal.map ((targetStalkToJoint (n := m) n r j (fun i => v i)
            (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV y hyV).comp
              (tc.stalkMap ⟨f y, hyV⟩).hom) (IsLocalRing.maximalIdeal _) →
        rr ∈ Ideal.map (Fm.stalkMap (chartX.base ⟨projG a j v hvj y, hΓ⟩)).hom (IsLocalRing.maximalIdeal _)) :
    Ideal.comap (πA.stalkMap (sc.base (ci.base ⟨y, hyS⟩))).hom
        (Ideal.map (ind.stalkMap (sc.base (ci.base ⟨y, hyS⟩))).hom (IsLocalRing.maximalIdeal _)) ≤
      Ideal.map (Fm.stalkMap (πA.base (sc.base (ci.base ⟨y, hyS⟩)))).hom (IsLocalRing.maximalIdeal _) := by
  subst hci hsc
  have hp : ind.base ((strictChartTo a W K j).base ((chartIsoG a W j v hvj).hom.base ⟨y, hyS⟩)) =
      tc.base ⟨f y, hyV⟩ :=
    congrArg (fun k => k.base ⟨y, hyS⟩) H
  have hs' : tc.base ((actualSubspaceMap hf (fun _ hx => hland hx)).base ⟨y, hyS⟩) =
      ind.base ((strictChartTo a W K j).base ((chartIsoG a W j v hvj).hom.base ⟨y, hyS⟩)) := hp.symm
  have hsq' := fun a' => (Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare.square_apply
    (chartIsoG a W j v hvj).hom (strictChartTo a W K j) ind
    (actualSubspaceMap hf (fun _ hx => hland hx)) tc H ⟨y, hyS⟩ hs' a').trans
    (targetStalkToJoint_strict_square (n := m) n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV h0
      (recenteredCoordinateSubset_analytic a j v W hWa) hland y hy hyS _).symm
  exact Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical.strict_builder (chartIsoG a W j v hvj).hom
    (chartIsoG a W j v hvj).hom rfl (strictChartTo a W K j) (strictChartTo a W K j) rfl πA ind Fm ⟨y, hyS⟩
    (pivotTorsion (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) f V y)
    (jointStrictStalkMap (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf.continuous hland y hy hyS)
    (jointStrictStalkMap (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf.continuous hland y hy hyS) rfl
    (jointTorsionQuotientEquiv (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf.continuous hland y hy hyS)
    (jointTorsionQuotientEquiv_mk (n := m) n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf.continuous hland y hy hyS)
    (Pq := chartX.base ⟨projG a j v hvj y, hΓ⟩) hs (chartX.stalkMap ⟨projG a j v hvj y, hΓ⟩).hom
    (betaG a W j v hvj f V hraw y hΓ)
    (fun rr => readout_generic a hr W j v hvj f V hf.continuous hWa h0 hland hraw K πA chartX hsq ⟨y, hyS⟩ hy hs rr)
    _ hsq' (((targetStalkToJoint (n := m) n r j (fun i => v i)
        (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V hf hV y hyV).comp
          (tc.stalkMap ⟨f y, hyV⟩).hom).comp (eqToHom (congrArg Bl.presheaf.stalk hp)).hom) (fun _ => rfl)
    (hT.trans (Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical.map_maximal_transport hp _).symm.le)
    (fun rr hr => hFI rr ((Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical.map_maximal_transport hp _).le hr))

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStrictFused

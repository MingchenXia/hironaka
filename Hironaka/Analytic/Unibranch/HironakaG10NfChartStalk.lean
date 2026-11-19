import Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm
import Hironaka.Resolution.HironakaG10ChowRatioGeneration
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic
import Hironaka.Analytic.Unibranch.HironakaG10NfSourceSquare
import Hironaka.Resolution.HironakaG10JointStrictTorsion

/-!
# H3.2 (generic): the recentred strict chart and its blowup projection on stalks

Lane G10H3, run 0081.  For product-normal charts `a` of `P × ℂ^r` along `{q.2 = 0}`, a closed set `W ⊆ P × ℂ^r`, a pivot
`j` and a recentring `v` with zero pivot coordinate (the source side of the canonical machinery is the instance
`a = E.source.charts`, `W = sourceGraphSet`):

* `chartIsoG` — the actual model of the real-open strict transform is the strict chart model
  (the definition of `HironakaG10SbCanonicalStrictTorsion.chartIso`);
* `projG` — the ambient blowup base `w ↦ π(χ w)`;
* `composite_stalk_germ` — the composite `chartIsoG ≫ strictChartInclusion ≫ geometricProjection` on germs;
* **`composite_stalk_incl`** — on stalks the composite sends the class of an ambient germ `h` to the class of `proj^♯ h`.

All statements are in small generic variables (fast elaboration); the canonical instances are definitional.
No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk

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
  HironakaG10RealOpenStrictTorsionKernel HironakaG10JointStrictTorsion

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  (a : ProductNormalCharts n r P) (hr : 0 < r) (W : Set (P × ComplexModel r)) (hW : IsClosed W) (j : Fin r)
  (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)

/-- The recentred real-open chart domain. -/
abbrev domG : Opens (ComplexModel (n+r)) :=
  realOpenChartDomain n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))

/-- The set read in the recentred coordinates. -/
abbrev WG : Set (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) :=
  (arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' (coordinateSubset a j W)

/-- The real-open strict transform. -/
abbrev strictG : Set (domG a j v) :=
  realOpenStrictTransform n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v)

/-- The actual model of the real-open strict transform is the strict chart model. -/
abbrev chartIsoG :
    actualSubspaceLocallyRingedSpace (n := n+r) (strictG a W j v) ≅
      actualSubspaceLocallyRingedSpace (n := n+r) (strictChartCarrier a W j) :=
  actualSubspaceBiholomorphicIso (arbitraryCanonicalRecenteredChart a j v hvj) _ _
    (fun w => Set.ext_iff.mp (original_strict_carrier_conjugacy a j v hvj W) w)

/-- The ambient blowup base of a chart point. -/
abbrev projG : domG a j v → P × ComplexModel r :=
  blowupProj (n+r) {q : P × ComplexModel r | q.2=0} ∘ (Subtype.val ∘ arbitraryCanonicalRecenteredChart a j v hvj)

theorem projG_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞ (projG a j v hvj) :=
  contMDiff_blowupProj.comp (contMDiff_subtype_val.comp (arbitraryCanonicalRecenteredChart a j v hvj).contMDiff)

include hW in
theorem projG_mem (w : domG a j v) (hw : w ∈ strictG a W j v) : projG a j v hvj w ∈ W := by
  have h1 := (Set.ext_iff.mp (original_strict_carrier_conjugacy a j v hvj W) w).mp hw
  exact geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hW h1

/-- **On germs**: the composite sends the class of the germ of `k` to the class of the germ of `k ∘ proj`. -/
theorem composite_stalk_germ (w : strictG a W j v) (k : P × ComplexModel r → ℂ)
    (hk : HolomorphicAt (n+r) k (projG a j v hvj w.val)) :
    (((chartIsoG a W j v hvj).hom ≫ strictChartInclusion a W j ≫
        geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hW).stalkMap w).hom
        ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj w.val, projG_mem a W hW j v hvj w.val w.property⟩
          (actualOriginalFunctionGerm (projG a j v hvj w.val) k hk)) =
      (actualSubspaceInclusion (n := n+r) (strictG a W j v)).stalkMap w
        (actualOriginalFunctionGerm w.val (k ∘ projG a j v hvj)
          (hk.comp_contMDiff (Filter.Eventually.of_forall fun _ => (projG_contMDiff a j v hvj).contMDiffAt))) := by
  have hk1 : HolomorphicAt (n+r) (k ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
      ((arbitraryCanonicalRecenteredChart a j v hvj w.val).val) :=
    HolomorphicAt.comp_contMDiff (f := blowupProj (n+r) {q : P × ComplexModel r | q.2=0})
      (y := (arbitraryCanonicalRecenteredChart a j v hvj w.val).val) hk
      (Filter.Eventually.of_forall fun _ => contMDiff_blowupProj.contMDiffAt)
  have hk2 : HolomorphicAt (n+r) ((k ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2=0}) ∘
        (Subtype.val : strictChartAmbientOpen a j → _)) (arbitraryCanonicalRecenteredChart a j v hvj w.val) :=
    HolomorphicAt.comp_contMDiff (f := (Subtype.val : strictChartAmbientOpen a j → _))
      (y := arbitraryCanonicalRecenteredChart a j v hvj w.val) hk1
      (Filter.Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)
  have hG := HironakaG10ChowRatioGeneration.actualSubspaceMap_stalkMap_germ
    (contMDiff_blowupProj (n := n+r) (C := {q : P × ComplexModel r | q.2=0}))
    (C := actualStrictCarrier (n := n) W) (D := W)
    (fun _ hy => geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hW hy)
    ((strictChartInclusion a W j).base ((chartIsoG a W j v hvj).hom.base w)) k hk
  have hS := HironakaG10ChowRatioGeneration.actualSubspaceMap_stalkMap_germ
    (f := (Subtype.val : strictChartAmbientOpen a j → _))
    contMDiff_subtype_val (C := strictChartCarrier a W j) (D := actualStrictCarrier (n := n) W) (fun _ hx => hx)
    ((chartIsoG a W j v hvj).hom.base w) _ hk1
  have hC := HironakaG10ChowRatioGeneration.actualSubspaceMap_stalkMap_germ
    (arbitraryCanonicalRecenteredChart a j v hvj).contMDiff
    (C := strictG a W j v) (D := strictChartCarrier a W j)
    (fun z hz => (Set.ext_iff.mp (original_strict_carrier_conjugacy a j v hvj W) z).mp hz) w _ hk2
  have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (chartIsoG a W j v hvj).hom
    (strictChartInclusion a W j ≫ geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hW) w)
    ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj w.val, projG_mem a W hW j v hvj w.val w.property⟩
          (actualOriginalFunctionGerm (projG a j v hvj w.val) k hk))
  have c2 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (strictChartInclusion a W j)
    (geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hW) ((chartIsoG a W j v hvj).hom.base w))
    ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj w.val, projG_mem a W hW j v hvj w.val w.property⟩
          (actualOriginalFunctionGerm (projG a j v hvj w.val) k hk))
  exact c1.trans ((congrArg _ (c2.trans ((congrArg _ hG).trans hS))).trans hC)

/-- **On stalks**: the composite sends the class of an ambient germ `h` to the class of `proj^♯ h`. -/
theorem composite_stalk_incl (w : strictG a W j v)
    (h : actualComplexStructureStalk (n := n+r) (projG a j v hvj w.val)) :
    (((chartIsoG a W j v hvj).hom ≫ strictChartInclusion a W j ≫
        geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hW).stalkMap w).hom
        ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj w.val, projG_mem a W hW j v hvj w.val w.property⟩ h) =
      (actualSubspaceInclusion (n := n+r) (strictG a W j v)).stalkMap w
        ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj) (projG_contMDiff a j v hvj)).stalkMap w.val h) := by
  obtain ⟨k, hk, rfl⟩ := Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm.exists_germ_eq (projG a j v hvj w.val) h
  rw [composite_stalk_germ a hr W hW j v hvj w k hk,
    HironakaG10ChowRatioGeneration.stalkMap_originalGerm (projG_contMDiff a j v hvj) w.val k hk]

/-! ### The source readout in generic form -/

section Readout

variable {m : ℕ} {Yt : Type} [TopologicalSpace Yt] [ChartedSpace (ComplexModel m) Yt]
  (f : domG a j v → Yt) (V : Set Yt) (hf : Continuous f)
  (hWa : IsComplexAnalyticSubset (n := n+r) W)
  (h0 : (0 : ComplexModel (n+r)) ∈ recenteredTargetOpen n r j v (canonicalTargetOpen a j))
  (hland : strictG a W j v ⊆ f ⁻¹' V)
  (hraw : ∀ y : domG a j v, Ideal.map ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj)
      (projG_contMDiff a j v hvj)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj y)) ≤
    rawAnalyticIdeal n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) y)

include hraw in
/-- The source map on the ambient quotient `𝒪_{proj y} ⧸ I(W) → JointQuotient y`. -/
def betaQ (y : domG a j v) :
    actualComplexStructureStalk (n := n+r) (projG a j v hvj y) ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj y) →+*
      JointQuotient (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
        (WG a W j v) f V y := by
  exact Ideal.quotientMap (jointIdeal (n := m) n r j (fun i => v i)
      (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V y)
    ((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj) (projG_contMDiff a j v hvj)).stalkMap y).hom
    (Ideal.map_le_iff_le_comap.mp ((hraw y).trans le_sup_left))

/-- **The source map** `β : 𝒪_{Γ, proj y} → JointQuotient y` (class of the pull-back by `proj`). -/
def betaG (y : domG a j v) (hy : projG a j v hvj y ∈ W) :
    ((actualSubspaceLocallyRingedSpace (n := n+r) W).presheaf.stalk ⟨projG a j v hvj y, hy⟩) →+*
      JointQuotient (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
        (WG a W j v) f V y := by
  refine RingHom.comp ?_ (actualSubspaceStalkWholeEquiv (n := n+r) W ⟨projG a j v hvj y, hy⟩).toRingHom
  show actualComplexStructureStalk (n := n+r) (projG a j v hvj y) ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) W) (projG a j v hvj y) →+* _
  exact betaQ a W j v hvj f V hraw y

theorem betaG_incl (y : domG a j v) (hy : projG a j v hvj y ∈ W)
    (h : actualComplexStructureStalk (n := n+r) (projG a j v hvj y)) :
    betaG a W j v hvj f V hraw y hy ((actualSubspaceInclusion (n := n+r) W).stalkMap ⟨projG a j v hvj y, hy⟩ h) =
      Ideal.Quotient.mk (jointIdeal (n := m) n r j (fun i => v i)
        (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V y)
        (((ChartedSpace.locallyRingedSpaceMap (projG a j v hvj) (projG_contMDiff a j v hvj)).stalkMap y).hom h) :=
  congrArg (betaQ a W j v hvj f V hraw y) (actualSubspaceInclusion_stalk (n := n+r) W ⟨projG a j v hvj y, hy⟩ h)

include hland in
/-- The core of the readout: on the graph stalk, the composite is `β` followed by the joint strict stalk map. -/
theorem readout_core (w : strictG a W j v)
    (hw : w.val ∈ localDomain n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) h0 (recenteredCoordinateSubset_analytic a j v W hWa))
    (γ : (actualSubspaceLocallyRingedSpace (n := n+r) W).presheaf.stalk
      ⟨projG a j v hvj w.val, projG_mem a W hWa.isClosed j v hvj w.val w.property⟩) :
    (((chartIsoG a W j v hvj).hom ≫ strictChartInclusion a W j ≫
        geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hWa.isClosed).stalkMap w).hom γ =
      jointStrictStalkMap (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
        (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf hland w.val hw w.property
        (betaG a W j v hvj f V hraw w.val (projG_mem a W hWa.isClosed j v hvj w.val w.property) γ) := by
  obtain ⟨h, rfl⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n+r) W
    ⟨projG a j v hvj w.val, projG_mem a W hWa.isClosed j v hvj w.val w.property⟩ γ
  change _ = jointStrictStalkMap (n := m) n r j (fun i => v i)
    (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) (WG a W j v) f V h0
    (recenteredCoordinateSubset_analytic a j v W hWa) hf hland w.val hw w.property
    (betaG a W j v hvj f V hraw w.val (projG_mem a W hWa.isClosed j v hvj w.val w.property)
      ((actualSubspaceInclusion (n := n+r) W).stalkMap
        ⟨projG a j v hvj w.val, projG_mem a W hWa.isClosed j v hvj w.val w.property⟩ h))
  rw [betaG_incl, jointStrictStalkMap_mk]
  exact composite_stalk_incl a hr W hWa.isClosed j v hvj w h

include hland in
/-- **The source readout (generic)**: the composite through the strict chart of any explicit model `K` of the strict
transform with a projection `πA` satisfying the projection law reads `πA^♯` as `β` on the joint strict stalk. -/
theorem readout_generic {A Xc : LocallyRingedSpace.{0}}
    (K : actualSubspaceLocallyRingedSpace (n := n+r) (actualStrictCarrier (n := n) W) ⟶ A) (πA : A ⟶ Xc)
    (chartX : actualSubspaceLocallyRingedSpace (n := n+r) W ⟶ Xc)
    (hsq : K ≫ πA = geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hWa.isClosed ≫ chartX)
    (w : strictG a W j v)
    (hw : w.val ∈ localDomain n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      (WG a W j v) h0 (recenteredCoordinateSubset_analytic a j v W hWa))
    (hs : chartX.base ⟨projG a j v hvj w.val, projG_mem a W hWa.isClosed j v hvj w.val w.property⟩ =
      πA.base ((strictChartTo a W K j).base ((chartIsoG a W j v hvj).hom.base w)))
    (rr : Xc.presheaf.stalk (πA.base ((strictChartTo a W K j).base ((chartIsoG a W j v hvj).hom.base w)))) :
    ((chartIsoG a W j v hvj).hom.stalkMap w).hom
        (((strictChartTo a W K j).stalkMap ((chartIsoG a W j v hvj).hom.base w)).hom
          ((πA.stalkMap ((strictChartTo a W K j).base ((chartIsoG a W j v hvj).hom.base w))).hom rr)) =
      jointStrictStalkMap (n := m) n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
        (WG a W j v) f V h0 (recenteredCoordinateSubset_analytic a j v W hWa) hf hland w.val hw w.property
        (betaG a W j v hvj f V hraw w.val (projG_mem a W hWa.isClosed j v hvj w.val w.property)
          ((chartX.stalkMap ⟨projG a j v hvj w.val, projG_mem a W hWa.isClosed j v hvj w.val w.property⟩).hom
            ((eqToHom (congrArg Xc.presheaf.stalk hs.symm)).hom rr))) := by
  have hsq' : (chartIsoG a W j v hvj).hom ≫ (strictChartTo a W K j ≫ πA) =
      ((chartIsoG a W j v hvj).hom ≫ strictChartInclusion a W j ≫
        geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hWa.isClosed) ≫ chartX := by
    simp only [strictChartTo, Category.assoc, hsq]
  have sq := Hironaka.Analytic.Unibranch.HironakaG10NfSourceSquare.square_apply_generic (chartIsoG a W j v hvj).hom
    (strictChartTo a W K j) πA
    ((chartIsoG a W j v hvj).hom ≫ strictChartInclusion a W j ≫
      geometricProjection (explicitProductPredicate (n := n) (P := P) hr) hWa.isClosed) chartX hsq' w hs rr
  refine sq.trans ?_
  exact readout_core a hr W j v hvj f V hf hWa h0 hland hraw w hw _

end Readout

end

end Hironaka.Analytic.Unibranch.HironakaG10NfChartStalk

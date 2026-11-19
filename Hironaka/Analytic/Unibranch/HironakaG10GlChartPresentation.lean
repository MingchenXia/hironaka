import Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
import Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer
import Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal
import Hironaka.Resolution.HironakaG10JointNativeScalar
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-!
# N3 + N4 on actual spaces: chart presentations of the three stalk maps and of the joint quotient

Lane G10N34, run 0081 (G10GL's split-off N3+N4).  Generic (no canonical data) actual-space glue for
`HironakaG10GlFlattenerTransfer`:

* `chartQuotientEquiv` — `𝒪_{ℂ^k,0} ⧸ I_C(c) ≅ 𝒪_{Z, i c}` for an open immersion `i` of an actual subspace `C`;
* `subspaceMap_stalk_chart`, `subspaceMap_stalk_graph` — the stalk map of an actual subspace map `g : C → D` on chart
  classes: germ pullback `g^*`, resp. the base action of the relative graph presentation;
* **`oldFamily_square`** — an actual chart square `g ≫ i_D = i_C ≫ F` presents the stalk map of `F` as the relative graph
  chart `𝒪_{ℂ^{k'}} ⧸ I_D → 𝒪_{ℂ^{k'+k}} ⧸ K` (`singularChartMap`);
* **`baseChange_square`** — a square `g ≫ i_D = i_V ≫ σ` (`V` read through a biholomorphism `χ : T ≃ T'`) presents the
  stalk map of `σ` as `g^* : 𝒪_{ℂ^{k'}} ⧸ I_D → 𝒪_{ℂ^e} ⧸ I_{V'}` (`biholoChartEquiv`);
* **`jointChartEquiv`** — the open-chart joint quotient `𝒪_{S,y} ⧸ (π^* I_W + f^* I_V)` of TN
  `HironakaG10JointStrictTorsion` is `𝒪_{ℂ^{d+t},0} ⧸ (π^* J_W + (χ f)^* I_{V'})` (target read through a biholomorphism
  `χ`), and `jointChartEquiv_targetStalk` — its target scalar map `targetStalkToJoint` is `(χ f)^*` on chart classes.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualWholeStalkHolomorphicPullback HironakaChowRelativeGraphPresentation
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
  Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

noncomputable section

/-! ### Stalks of open immersions and point transports -/

/-- The ring isomorphism of stalks of an open immersion. -/
def oiStalkEquiv {S T : LocallyRingedSpace.{0}} (k : S ⟶ T) [LocallyRingedSpace.IsOpenImmersion k] (s : S) :
    T.presheaf.stalk (k.base s) ≃+* S.presheaf.stalk s :=
  (asIso (k.stalkMap s)).commRingCatIsoToRingEquiv

theorem oiStalkEquiv_apply {S T : LocallyRingedSpace.{0}} (k : S ⟶ T) [LocallyRingedSpace.IsOpenImmersion k]
    (s : S) (r : T.presheaf.stalk (k.base s)) : oiStalkEquiv k s r = (k.stalkMap s).hom r :=
  rfl

/-- A point transport between stalks, as a ring isomorphism. -/
def stalkTransport {T : LocallyRingedSpace.{0}} {a b : T} (h : a = b) :
    T.presheaf.stalk a ≃+* T.presheaf.stalk b :=
  (eqToIso (congrArg T.presheaf.stalk h)).commRingCatIsoToRingEquiv

theorem stalkTransport_apply {T : LocallyRingedSpace.{0}} {a b : T} (h : a = b) (r : T.presheaf.stalk a) :
    stalkTransport h r = (eqToHom (congrArg T.presheaf.stalk h)).hom r :=
  rfl

/-- The stalk map of `σ` at `x`, read from the stalk at `y = σ x`. -/
abbrev lrsFibreMap {T S : LocallyRingedSpace.{0}} (σ : T ⟶ S) (y : S) (x : T) (h : σ.base x = y) :
    S.presheaf.stalk y →+* T.presheaf.stalk x :=
  (σ.stalkMap x).hom.comp (eqToHom (congrArg S.presheaf.stalk h.symm)).hom

/-! ### Germ maps depend only on germs -/

section Congr

/-- Germ pullbacks along eventually equal maps agree. -/
theorem compAlgHom_congr {m n : ℕ} {η₁ η₂ : ComplexModel m → ComplexModel n}
    (h₁ : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η₁ z) (h₁0 : η₁ 0 = 0)
    (h₂ : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η₂ z) (h₂0 : η₂ 0 = 0)
    (h : η₁ =ᶠ[𝓝 0] η₂) : compAlgHom η₁ h₁ h₁0 = compAlgHom η₂ h₂ h₂0 := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    rw [compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [h] with z hz
    simp only [Function.comp_apply, hz]

/-- The relative graph ideal depends only on the germ of the map. -/
theorem relativeGraphIdeal_congr (d t : ℕ) {F₁ F₂ : ComplexModel t → ComplexModel d}
    (hF₁ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₁ z) (hF₁0 : F₁ 0 = 0)
    (hF₂ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₂ z) (hF₂0 : F₂ 0 = 0)
    (h : F₁ =ᶠ[𝓝 0] F₂) (J : Ideal (HolGerm (ComplexModel t))) :
    relativeGraphIdeal d t F₁ hF₁ J = relativeGraphIdeal d t F₂ hF₂ J := by
  unfold relativeGraphIdeal
  rw [relativeGraphEquations_eq_span d t F₁ hF₁ hF₁0, relativeGraphEquations_eq_span d t F₂ hF₂ hF₂0,
    compAlgHom_congr hF₁ hF₁0 hF₂ hF₂0 h]

end Congr

/-! ### Translated maps of product maps -/

section Product

open scoped Hironaka.ProductComplexManifold

theorem prodModelEquiv_eq_join (a r : ℕ) (u : ComplexModel a) (v : ComplexModel r) :
    ProductComplexManifold.prodModelEquiv a r (u, v) =
      tangentInclusion a r u + HironakaActualCentreJointJets.actualJointNormalInclusion a r v := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

theorem prodModelEquiv_symm_fst' (a r : ℕ) (z : ComplexModel (a+r)) :
    ((ProductComplexManifold.prodModelEquiv a r).symm z).1 = tangentProjection a r z := by
  ext i
  simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

theorem prodModelEquiv_symm_snd' (a r : ℕ) (z : ComplexModel (a+r)) :
    ((ProductComplexManifold.prodModelEquiv a r).symm z).2 =
      HironakaActualCentreJointJets.actualJointNormalProjection a r z := by
  ext i
  simp [ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

variable {a c r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel a) P] [ChartedSpace (ComplexModel c) Q]

/-- **The translated map of `f × id` is `(f_translated, id)`** in the product charts. -/
theorem actualTranslatedMap_prodMap (f : P → Q) (p : P × ComplexModel r) (z : ComplexModel (a+r)) :
    actualTranslatedMap (n := c+r) (m := a+r) (Prod.map f id) p z =
      Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer.srcMap c a r
        (actualTranslatedMap (n := c) (m := a) f p.1) z := by
  unfold actualTranslatedMap Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer.srcMap
  simp only [ProductComplexManifold.chartAt_prod, ProductComplexManifold.prodChart_apply,
    ProductComplexManifold.prodChart_symm_apply, Prod.map_fst, Prod.map_snd, id, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm, map_add,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [← map_sub, Prod.mk_sub_mk, prodModelEquiv_eq_join]
  simp only [map_sub, Prod.fst_add, Prod.snd_add, prodModelEquiv_symm_fst', prodModelEquiv_symm_snd',
    add_sub_cancel_right]

end Product

/-! ### Chart presentations through open immersions -/

section Chart

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]

/-- The whole defining ideal of `C` at `c`, in translated chart germs. -/
abbrev chartIdealAt (C : Set M) (c : C) : Ideal (HolGerm (ComplexModel k)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := k) C) c.val c.val (mem_chart_source (ComplexModel k) c.val)

/-- **`𝒪_{ℂ^k,0} ⧸ I_C(c) ≅ 𝒪_{Z, z}`** for an open immersion `i` of the actual subspace `C`, at `z = i c`. -/
def chartQuotientEquiv (C : Set M) {Z : LocallyRingedSpace.{0}}
    (i : actualSubspaceLocallyRingedSpace (n := k) C ⟶ Z) [LocallyRingedSpace.IsOpenImmersion i]
    (c : C) (z : Z) (hz : i.base c = z) :
    (HolGerm (ComplexModel k) ⧸ chartIdealAt C c) ≃+* Z.presheaf.stalk z :=
  (actualSubspaceStalkChartEquiv (n := k) C c).symm.trans ((oiStalkEquiv i c).symm.trans (stalkTransport hz))

/-- The chart class of an ambient germ is the inclusion germ. -/
theorem chartEquiv_symm_mk (C : Set M) (c : C) (a : HolGerm (ComplexModel k)) :
    (actualSubspaceStalkChartEquiv (n := k) C c).symm (Ideal.Quotient.mk _ a) =
      ((actualSubspaceInclusion (n := k) C).stalkMap c).hom ((actualStalkChartEquiv (n := k) c.val).symm a) := by
  apply (actualSubspaceStalkChartEquiv (n := k) C c).injective
  rw [RingEquiv.apply_symm_apply]
  have h := inclusion_stalk_chart (n := k) C c ((actualStalkChartEquiv (n := k) c.val).symm a)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

variable {k' : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (ComplexModel k') N] [IsComplexManifold k' N]

/-- The stalk map of an actual subspace map on inclusion germs. -/
theorem subspaceMap_stalk_inclusion {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) (c : C)
    (r : actualComplexStructureStalk (n := k') (g c.val)) :
    ((actualSubspaceMap hg hCD).stalkMap c).hom
        (((actualSubspaceInclusion (n := k') D).stalkMap ((actualSubspaceMap hg hCD).base c)).hom r) =
      ((actualSubspaceInclusion (n := k) C).stalkMap c).hom
        (((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap c.val).hom r) := by
  have hsq := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hg hCD c) r
  simp only [ConcreteCategory.comp_apply] at hsq
  exact hsq

/-- **The stalk map of an actual subspace map on chart classes is the germ pullback.** -/
theorem subspaceMap_stalk_chart {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) (c : C) (a : HolGerm (ComplexModel k')) :
    ((actualSubspaceMap hg hCD).stalkMap c).hom
        ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hCD).base c)).symm
          (Ideal.Quotient.mk _ a)) =
      (actualSubspaceStalkChartEquiv (n := k) C c).symm
        (Ideal.Quotient.mk _ (actualHolomorphicGermPullback hg c.val a)) := by
  rw [chartEquiv_symm_mk, subspaceMap_stalk_inclusion, chartEquiv_symm_mk]
  congr 1
  apply (actualStalkChartEquiv (n := k) c.val).injective
  rw [RingEquiv.apply_symm_apply]
  change actualStalkChartEquiv (n := k) c.val
    (((ChartedSpace.locallyRingedSpaceMap g hg).stalkMap c.val).hom
      ((actualStalkChartEquiv (n := k') (g c.val)).symm a)) = _
  rw [actualNativeStalk_chart_pullback, RingEquiv.apply_symm_apply]

/-- **The stalk map of an actual subspace map on chart classes is the relative graph base action.** -/
theorem subspaceMap_stalk_graph {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) (c : C) (a : HolGerm (ComplexModel k')) :
    ((actualSubspaceMap hg hCD).stalkMap c).hom
        ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hCD).base c)).symm
          (Ideal.Quotient.mk _ a)) =
      nativeRelativeGraphEquiv hg C c (Ideal.Quotient.mk _ (tangentPullback k' k a)) := by
  rw [nativeRelativeGraphEquiv_base, chartEquiv_symm_mk, subspaceMap_stalk_inclusion]
  rfl

/-- The relative graph ideal contains the pulled-back base ideal. -/
theorem chartIdeal_le_graphIdeal {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) (c : C) :
    (chartIdealAt D ((actualSubspaceMap hg hCD).base c)).map (tangentPullback k' k).toRingHom ≤
      nativeRelativeGraphIdeal hg C c := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  apply (nativeRelativeGraphEquiv hg C c).injective
  rw [map_zero]
  change nativeRelativeGraphEquiv hg C c (Ideal.Quotient.mk _ (tangentPullback k' k a)) = 0
  rw [← subspaceMap_stalk_graph hg hCD c a, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

/-- The germ pullback carries the base ideal into the subspace ideal. -/
theorem chartIdeal_le_comap {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) (c : C) :
    chartIdealAt D ((actualSubspaceMap hg hCD).base c) ≤
      (chartIdealAt C c).comap (actualHolomorphicGermPullback hg c.val).toRingHom := by
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  apply (actualSubspaceStalkChartEquiv (n := k) C c).symm.injective
  rw [map_zero]
  change (actualSubspaceStalkChartEquiv (n := k) C c).symm
    (Ideal.Quotient.mk _ (actualHolomorphicGermPullback hg c.val a)) = 0
  rw [← subspaceMap_stalk_chart hg hCD c a, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]

/-! ### The old family -/

/-- **The old family on a chart square.**  If `g ≫ i_D = i_C ≫ F` with `i_C`, `i_D` open immersions of actual
subspaces, the stalk map of `F` at `i_C c` is the relative graph chart of `g` at `c`. -/
theorem oldFamily_square {g : M → N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ g)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, g x ∈ D) {Xs Ys : LocallyRingedSpace.{0}}
    (iC : actualSubspaceLocallyRingedSpace (n := k) C ⟶ Xs) [LocallyRingedSpace.IsOpenImmersion iC]
    (iD : actualSubspaceLocallyRingedSpace (n := k') D ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion iD]
    (Fm : Xs ⟶ Ys) (hsq : actualSubspaceMap hg hCD ≫ iD = iC ≫ Fm) (c : C) (x : Xs) (hx : iC.base c = x)
    (y : Ys) (hy : Fm.base x = y) (hc : iD.base ((actualSubspaceMap hg hCD).base c) = y) :
    (lrsFibreMap Fm y x hy).comp
        (chartQuotientEquiv D iD ((actualSubspaceMap hg hCD).base c) y hc).toRingHom =
      ((nativeRelativeGraphEquiv hg C c).trans ((oiStalkEquiv iC c).symm.trans (stalkTransport hx))).toRingHom.comp
        (singularChartMap k' k (chartIdealAt D ((actualSubspaceMap hg hCD).base c))
          (nativeRelativeGraphIdeal hg C c) (chartIdeal_le_graphIdeal hg hCD c)) := by
  subst hx
  subst hy
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  apply (oiStalkEquiv iC c).injective
  set u := (oiStalkEquiv iD ((actualSubspaceMap hg hCD).base c)).symm
    ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hCD).base c)).symm
      (Ideal.Quotient.mk _ a)) with hu
  have key := stalk_square_apply (actualSubspaceMap hg hCD) iD iC Fm hsq.symm c _ rfl hc u
  have hiu : (iD.stalkMap ((actualSubspaceMap hg hCD).base c)).hom u =
      (actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hCD).base c)).symm
        (Ideal.Quotient.mk _ a) := by
    rw [hu]
    exact (oiStalkEquiv iD ((actualSubspaceMap hg hCD).base c)).apply_symm_apply _
  rw [hiu, subspaceMap_stalk_graph] at key
  have hR : oiStalkEquiv iC c
      ((((nativeRelativeGraphEquiv hg C c).trans ((oiStalkEquiv iC c).symm.trans
        (stalkTransport (rfl : iC.base c = iC.base c)))).toRingHom.comp
        (singularChartMap k' k (chartIdealAt D ((actualSubspaceMap hg hCD).base c))
          (nativeRelativeGraphIdeal hg C c) (chartIdeal_le_graphIdeal hg hCD c))) (Ideal.Quotient.mk _ a)) =
      nativeRelativeGraphEquiv hg C c (Ideal.Quotient.mk _ (tangentPullback k' k a)) := by
    change oiStalkEquiv iC c ((oiStalkEquiv iC c).symm
      (nativeRelativeGraphEquiv hg C c (Ideal.Quotient.mk _ (tangentPullback k' k a)))) = _
    exact RingEquiv.apply_symm_apply _ _
  exact key.trans hR.symm

/-! ### The new base, read through a biholomorphism -/

section Biholo

variable {e : ℕ} {T T' : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel e) T] [IsComplexManifold e T]
  [TopologicalSpace T'] [ChartedSpace (ComplexModel e) T'] [IsComplexManifold e T']
  (χ : T ≃ₘ⟮𝓘(ℂ, ComplexModel e), 𝓘(ℂ, ComplexModel e)⟯ T') (V : Set T) (V' : Set T')
  (hVV' : ∀ x, x ∈ V ↔ χ x ∈ V')

/-- The subspace map of the biholomorphism `χ : V → V'`. -/
abbrev biholoMap : actualSubspaceLocallyRingedSpace (n := e) V ⟶ actualSubspaceLocallyRingedSpace (n := e) V' :=
  actualSubspaceMap χ.contMDiff (fun x hx => (hVV' x).mp hx)

instance biholoMap_isIso : IsIso (biholoMap χ V V' hVV') :=
  inferInstanceAs (IsIso (actualSubspaceBiholomorphicIso χ V V' hVV').hom)

/-- **`𝒪_{ℂ^e,0} ⧸ I_{V'}(χ q) ≅ 𝒪_{Z, i q}`** for an open immersion `i` of `V`, read in the chart of `V'`. -/
def biholoChartEquiv {Z : LocallyRingedSpace.{0}} (i : actualSubspaceLocallyRingedSpace (n := e) V ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion i] (q : V) :
    (HolGerm (ComplexModel e) ⧸ chartIdealAt V' ((biholoMap χ V V' hVV').base q)) ≃+* Z.presheaf.stalk (i.base q) :=
  (actualSubspaceStalkChartEquiv (n := e) V' ((biholoMap χ V V' hVV').base q)).symm.trans
    ((oiStalkEquiv (biholoMap χ V V' hVV') q).trans (oiStalkEquiv i q).symm)

theorem biholoChartEquiv_stalk {Z : LocallyRingedSpace.{0}} (i : actualSubspaceLocallyRingedSpace (n := e) V ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion i] (q : V) (u : HolGerm (ComplexModel e) ⧸ chartIdealAt V' ((biholoMap χ V V' hVV').base q)) :
    (i.stalkMap q).hom (biholoChartEquiv χ V V' hVV' i q u) =
      ((biholoMap χ V V' hVV').stalkMap q).hom ((actualSubspaceStalkChartEquiv (n := e) V' _).symm u) :=
  (oiStalkEquiv i q).apply_symm_apply _

variable {k' : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (ComplexModel k') N] [IsComplexManifold k' N]

/-- **The base change on a chart square, through a biholomorphism.**  If `(g ∘ χ) ≫ i_D = i ≫ σ` with `i`, `i_D`
open immersions of actual subspaces, the stalk map of `σ` at `i q` is the germ pullback `g^*` at `χ q`. -/
theorem baseChange_square {g : T' → N} (hg : ContMDiff 𝓘(ℂ, ComplexModel e) 𝓘(ℂ, ComplexModel k') ∞ g)
    {D : Set N} (hV'D : ∀ x ∈ V', g x ∈ D) {Bl Ys : LocallyRingedSpace.{0}}
    (i : actualSubspaceLocallyRingedSpace (n := e) V ⟶ Bl) [LocallyRingedSpace.IsOpenImmersion i]
    (iD : actualSubspaceLocallyRingedSpace (n := k') D ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion iD]
    (σm : Bl ⟶ Ys)
    (hsq : actualSubspaceMap (hg.comp χ.contMDiff) (fun x hx => hV'D (χ x) ((hVV' x).mp hx)) ≫ iD = i ≫ σm)
    (q : V) (y : Ys) (hy : σm.base (i.base q) = y)
    (hc : iD.base ((actualSubspaceMap hg hV'D).base ((biholoMap χ V V' hVV').base q)) = y) :
    (lrsFibreMap σm y (i.base q) hy).comp
        (chartQuotientEquiv D iD ((actualSubspaceMap hg hV'D).base ((biholoMap χ V V' hVV').base q)) y hc).toRingHom =
      (biholoChartEquiv χ V V' hVV' i q).toRingHom.comp
        (Ideal.quotientMap (chartIdealAt V' ((biholoMap χ V V' hVV').base q))
          (actualHolomorphicGermPullback hg (χ q.val)).toRingHom
          (chartIdeal_le_comap hg hV'D ((biholoMap χ V V' hVV').base q))) := by
  subst hy
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  apply (oiStalkEquiv i q).injective
  set p' := (biholoMap χ V V' hVV').base q
  set u := (oiStalkEquiv iD ((actualSubspaceMap hg hV'D).base p')).symm
    ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hV'D).base p')).symm
      (Ideal.Quotient.mk _ a)) with hu
  have key := stalk_square_apply
    (actualSubspaceMap (hg.comp χ.contMDiff) (fun x hx => hV'D (χ x) ((hVV' x).mp hx))) iD i σm hsq.symm q _ rfl hc u
  have hiu : (iD.stalkMap ((actualSubspaceMap hg hV'D).base p')).hom u =
      (actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hV'D).base p')).symm
        (Ideal.Quotient.mk _ a) := by
    rw [hu]
    exact (oiStalkEquiv iD ((actualSubspaceMap hg hV'D).base p')).apply_symm_apply _
  have hcomp := actualSubspaceMap_comp χ.contMDiff hg (fun x hx => (hVV' x).mp hx) hV'D
  have e1 := Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease.stalkMap_eq_of_eq _ _ hcomp q rfl
    ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hV'D).base p')).symm
      (Ideal.Quotient.mk _ a))
  have e2 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (biholoMap χ V V' hVV')
    (actualSubspaceMap hg hV'D) q)
    ((actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hV'D).base p')).symm
      (Ideal.Quotient.mk _ a))
  simp only [ConcreteCategory.comp_apply] at e2
  have hR : oiStalkEquiv i q
      (((biholoChartEquiv χ V V' hVV' i q).toRingHom.comp
        (Ideal.quotientMap (chartIdealAt V' p') (actualHolomorphicGermPullback hg (χ q.val)).toRingHom
          (chartIdeal_le_comap hg hV'D p'))) (Ideal.Quotient.mk _ a)) =
      ((biholoMap χ V V' hVV').stalkMap q).hom ((actualSubspaceStalkChartEquiv (n := e) V' p').symm
        (Ideal.Quotient.mk _ (actualHolomorphicGermPullback hg (χ q.val) a))) :=
    biholoChartEquiv_stalk χ V V' hVV' i q _
  have hiu' : (iD.stalkMap ((actualSubspaceMap (hg.comp χ.contMDiff)
      (fun x hx => hV'D (χ x) ((hVV' x).mp hx))).base q)).hom u =
      (actualSubspaceStalkChartEquiv (n := k') D ((actualSubspaceMap hg hV'D).base p')).symm
        (Ideal.Quotient.mk _ a) := hiu
  exact key.trans ((congrArg _ hiu').trans (e1.trans (e2.trans
    ((congrArg _ (subspaceMap_stalk_chart hg hV'D p' a)).trans hR.symm))))

end Biholo

end Chart

/-! ### The open-chart joint quotient in chart germs -/

section Joint

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
  {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ, ComplexModel (d+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
  (hW : IsComplexAnalyticSubset (n := d+t) W)
  {Y' : Type} [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
  (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y') (V' : Set Y') (hVV' : ∀ x, x ∈ V ↔ χ x ∈ V')
  (hV' : IsComplexAnalyticSubset (n := n) V')

include hf hVV' hV' in
/-- The pulled target ideal may be read through a biholomorphism of the target. -/
theorem targetIdeal_eq_biholo (y : realOpenChartDomain d t j b U) :
    targetIdeal (n := n) d t j b U f V y = targetIdeal (n := n) d t j b U (χ ∘ f) V' y := by
  unfold targetIdeal
  have hV : V = χ ⁻¹' V' := Set.ext hVV'
  rw [HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp χ.contMDiff hf
      (vanishingIdeal (n := n) V') (CartanIrreducible.cartanCoherence V' hV'),
    HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism χ V', ← hV]

/-- The source ideal `J_W` at the image of `y`, in translated chart germs. -/
abbrev sourceIdealAt (y : realOpenChartDomain d t j b U) : Ideal (HolGerm (ComplexModel (d+t))) :=
  wholeChartStalkIdeal (vanishingIdeal (n := d+t) W) (realOpenProjection d t j b U y)
    (realOpenProjection d t j b U y) (mem_chart_source _ _)

/-- The target ideal `I_{V'}` at the image of `y`, in translated chart germs. -/
abbrev targetIdealAt (y : realOpenChartDomain d t j b U) : Ideal (HolGerm (ComplexModel n)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := n) V') (χ (f y)) (χ (f y)) (mem_chart_source _ _)

/-- The joint ideal in translated chart germs: `π^* J_W + (χ f)^* I_{V'}`. -/
abbrev jointChartIdeal (y : realOpenChartDomain d t j b U) : Ideal (HolGerm (ComplexModel (d+t))) :=
  (sourceIdealAt d t j b U W y).map
      (actualHolomorphicGermPullback (realOpenProjection_contMDiff d t j b U) y).toRingHom ⊔
    (targetIdealAt d t j b U f χ V' y).map (actualHolomorphicGermPullback (χ.contMDiff.comp hf) y).toRingHom

include hW hVV' hV' in
theorem map_jointIdeal (y : realOpenChartDomain d t j b U) :
    (jointIdeal (n := n) d t j b U W f V y).map (actualStalkChartEquiv (n := d+t) y).toRingHom =
      jointChartIdeal d t j b U W f hf χ V' y := by
  unfold jointIdeal
  rw [targetIdeal_eq_biholo d t j b U f V hf χ V' hVV' hV' y, Ideal.map_sup]
  unfold rawAnalyticIdeal targetIdeal realOpenTotalIdeal
  rw [map_actualWholeSheafStalkIdeal, map_actualWholeSheafStalkIdeal,
    ← map_wholeChartStalkIdeal_actual_pullback (realOpenProjection_contMDiff d t j b U)
      (vanishingIdeal (n := d+t) W) (CartanIrreducible.cartanCoherence W hW) y,
    ← map_wholeChartStalkIdeal_actual_pullback (χ.contMDiff.comp hf)
      (vanishingIdeal (n := n) V') (CartanIrreducible.cartanCoherence V' hV') y]
  rfl

/-- **The open-chart joint quotient in chart germs.** -/
def jointChartEquiv (y : realOpenChartDomain d t j b U) :
    JointQuotient (n := n) d t j b U W f V y ≃+*
      HolGerm (ComplexModel (d+t)) ⧸ jointChartIdeal d t j b U W f hf χ V' y :=
  Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := d+t) y)
    (map_jointIdeal d t j b U W f V hf hW χ V' hVV' hV' y).symm

theorem jointChartEquiv_mk (y : realOpenChartDomain d t j b U) (g : AmbientStalk d t j b U y) :
    jointChartEquiv d t j b U W f V hf hW χ V' hVV' hV' y
        (Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y) g) =
      Ideal.Quotient.mk _ (actualStalkChartEquiv (n := d+t) y g) :=
  rfl

/-- **The target scalar map of the joint quotient on chart classes** (through the biholomorphism `χ`): an open
immersion `i` of `V`, read in the chart of `V'` (`biholoChartEquiv`), followed by `targetStalkToJoint`, is
`(χ f)^*` on chart classes. -/
theorem jointChartEquiv_targetStalk (hV : IsComplexAnalyticSubset (n := n) V)
    {Z : LocallyRingedSpace.{0}} (i : actualSubspaceLocallyRingedSpace (n := n) V ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion i] (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V)
    (a : HolGerm (ComplexModel n)) :
    jointChartEquiv d t j b U W f V hf hW χ V' hVV' hV' y
        (targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV
          ((i.stalkMap ⟨f y, hyV⟩).hom (biholoChartEquiv χ V V' hVV' i ⟨f y, hyV⟩ (Ideal.Quotient.mk _ a)))) =
      Ideal.Quotient.mk _ (actualHolomorphicGermPullback (χ.contMDiff.comp hf) y a) := by
  rw [biholoChartEquiv_stalk, chartEquiv_symm_mk, subspaceMap_stalk_inclusion, targetStalkToJoint_inclusion,
    jointChartEquiv_mk]
  congr 1
  have hc : ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
      (((ChartedSpace.locallyRingedSpaceMap χ χ.contMDiff).stalkMap (f y)).hom
        ((actualStalkChartEquiv (n := n) (χ (f y))).symm a)) =
      ((ChartedSpace.locallyRingedSpaceMap (χ ∘ f) (χ.contMDiff.comp hf)).stalkMap y).hom
        ((actualStalkChartEquiv (n := n) (χ (f y))).symm a) := by
    have h := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp
      (ChartedSpace.locallyRingedSpaceMap f hf) (ChartedSpace.locallyRingedSpaceMap χ χ.contMDiff) y)
      ((actualStalkChartEquiv (n := n) (χ (f y))).symm a)
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm
  change actualStalkChartEquiv (n := d+t) y
    (((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap y).hom
      (((ChartedSpace.locallyRingedSpaceMap χ χ.contMDiff).stalkMap (f y)).hom
        ((actualStalkChartEquiv (n := n) (χ (f y))).symm a))) = _
  rw [hc, actualNativeStalk_chart_pullback]
  exact congrArg _ (RingEquiv.apply_symm_apply _ _)

end Joint


end

end Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation

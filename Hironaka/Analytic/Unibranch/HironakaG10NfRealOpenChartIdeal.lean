import Hironaka.Resolution.HironakaRealOpenGeometricStrictSaturation
import Hironaka.Resolution.HironakaActualHolomorphicGraphIdeal
import Hironaka.Resolution.HironakaG10ChowFlatModelOpen
import Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation

/-!
# N5.b (P2): the strict ideal at the origin of a real-open blowup chart is the analytic graph chart ideal

Lane G10N5, run 0081 (step S4 of the N5.b plan in `G10HT/STATUS.md`).  On the real-open blowup chart
`realOpenChartDomain d t j b U` (pivot `j`, recentring `b` with zero pivot coordinate), if the analytic set `W ⊆ U`
is, near the origin, the graph `w = f(u)` of a holomorphic `f` (`f 0 = 0`) over a set germ `X₀ ⊆ (ℂ^d, 0)`, then the
whole vanishing ideal of the real-open strict transform at the origin is the analytic graph chart ideal

`chartIdeal (evPoly d t b') j g IX = (evPoly(L) : X_j^∞)`,  `IX = I(X₀)`, `g_i = (f_i)_0`, `b'_i = b_{d+i}`

of `HironakaG10HtChartSaturation`:

* `vanishingIdeal_le_stalkIdeal`, `stalkIdeal_eq_vanishingIdeal` — the whole chart stalk ideal of a set is the
  germ vanishing ideal of its translated carrier (the reverse inclusion is TN `stalkIdeal_le_vanishingIdeal`);
* `realOpenPullback_eq` — the native germ pullback of the real-open projection at the origin is
  `actualAnalyticBlowupPullback`;
* `realOpen_total_eq` — whole total ideal at the origin = pullback of the whole ideal of `W` at `0`;
* `pullback_graph_eq` — `π^*(I(X₀)·H + (w − f(u))) = evPoly(relIdeal j g IX)`;
* **`realOpen_strict_eq_chartIdeal`**.

Sources: TN `HironakaRealOpenGeometricStrictSaturation.mem_realOpen_geoStrict_iff_exists_pivot_power`,
`HironakaActualHolomorphicGraphIdeal.graph_vanishingIdeal_eq`, `actualAnalyticBlowupPullback_coordinate`.
No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetChartInvariance
  HironakaActualWholeStalkHolomorphicPullback HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower
  HironakaRealOpenGeometricStrictSaturation HironakaActualHolomorphicGraphIdeal HironakaRelativeNormalIdeal
  HironakaG10ChowFlatModelOpen
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation Hironaka.Analytic.Unibranch.HironakaG10HtPolynomialGermFlat
  Hironaka.Analytic.Unibranch.HironakaG10HtChartSaturation

noncomputable section

/-! ### Whole chart stalk ideals are germ vanishing ideals -/

section Bridge

variable {N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- Every germ vanishing on the translated carrier is a whole chart stalk member. -/
theorem vanishingIdeal_le_stalkIdeal (A : Set M) (x : M) :
    AnalyticGermDecomposition.vanishingIdeal (translatedCarrier (N := N) A x) ≤
      stalkIdeal (N := N) A x := by
  rintro _ ⟨f, hf, rfl, hfA⟩
  set e := chartAt (ComplexModel N) x
  let F : M → ℂ := fun y => f (e y - e x)
  have hF : HolomorphicAt N F x := holomorphicAt_comp_preferredChartForward x f hf
  have ht : Tendsto (fun y : M => e y - e x) (𝓝 x) (𝓝 0) := by
    have hc : ContinuousAt (fun y : M => e y - e x) x :=
      (e.continuousAt (mem_chart_source _ x)).sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  have hmem : (vanishingIdeal (n := N) A).mem x F := by
    refine ⟨hF, ?_⟩
    filter_upwards [ht.eventually hfA, e.open_source.mem_nhds (mem_chart_source _ x)] with y hy hys hyA
    apply hy
    refine ⟨?_, ?_⟩
    · rw [sub_add_cancel]
      exact e.map_source hys
    · rw [sub_add_cancel, e.left_inv hys]
      exact hyA
  refine Ideal.subset_span ⟨F, hF, hmem, ?_⟩
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [eventually_translate_mem_target (N := N) x] with z hz
  change f z = f (e (e.symm (z + e x)) - e x)
  rw [e.right_inv hz, add_sub_cancel_right]

/-- **The whole chart stalk ideal of a set is the germ vanishing ideal of its translated carrier.** -/
theorem stalkIdeal_eq_vanishingIdeal (A : Set M) (x : M) :
    stalkIdeal (N := N) A x = AnalyticGermDecomposition.vanishingIdeal (translatedCarrier (N := N) A x) :=
  le_antisymm (stalkIdeal_le_vanishingIdeal A x) (vanishingIdeal_le_stalkIdeal A x)

end Bridge

/-! ### The real-open chart at its origin -/

section RealOpen

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t)))

theorem realOpenProjection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ (realOpenProjection d t j b U) := by
  have hp (i : Fin (d+t)) : ContDiff ℂ ∞ (fun z : ComplexModel (d+t) => z i) :=
    (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).contDiff
  have hc (i : Fin (d+t)) : ContDiff ℂ ∞
      (actualAnalyticBlowupCoordinate (actualTangentCentreVariables d t) (j.natAdd d) b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp _
    · exact (hp _).mul (contDiff_const.add (hp _))
    · exact hp _
  have hπ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) :=
    ((EuclideanSpace.equiv (Fin (d+t)) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff
  exact BlowupRestrictOpen.contMDiff_opens_mk (hπ.comp contMDiff_subtype_val) (fun p => p.property)

variable (h0 : (0 : ComplexModel (d+t)) ∈ U)

/-- The origin of `U`. -/
def baseOrigin : U := ⟨0, h0⟩

theorem realOpenProjection_origin :
    realOpenProjection d t j b U (realOpenOrigin d t j b U h0) = baseOrigin d t U h0 :=
  Subtype.ext (actualAnalyticBlowupMap_zero _ _ _)

/-- In a chart of an open of a model space, the inverse chart has the literal value. -/
theorem opens_chart_symm_val {n : ℕ} {V : Opens (ComplexModel n)} (x : V) {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) x).target) :
    ((chartAt (ComplexModel n) x).symm z).val = z :=
  (chartAt (ComplexModel n) x).right_inv hz

/-- **The native germ pullback of the real-open projection at its origin is the blowup pullback.** -/
theorem realOpenPullback_eq :
    actualHolomorphicGermPullback (realOpenProjection_contMDiff d t j b U) (realOpenOrigin d t j b U h0) =
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback actualAnalyticBlowupPullback
    rw [compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    set o := realOpenOrigin d t j b U h0
    have htarget : (chartAt (ComplexModel (d+t)) o).target ∈ 𝓝 (0 : ComplexModel (d+t)) :=
      (chartAt (ComplexModel (d+t)) o).open_target.mem_nhds
        ((chartAt (ComplexModel (d+t)) o).map_source (mem_chart_source _ o))
    filter_upwards [htarget] with z hz
    change F (((realOpenProjection d t j b U ((chartAt (ComplexModel (d+t)) o).symm (z + 0))).val) -
      (realOpenProjection d t j b U o).val) = F (actualAnalyticBlowupMap _ _ b z)
    rw [add_zero]
    change F (actualAnalyticBlowupMap _ _ b ((chartAt (ComplexModel (d+t)) o).symm z).val -
      actualAnalyticBlowupMap _ _ b 0) = _
    rw [opens_chart_symm_val o hz, actualAnalyticBlowupMap_zero, sub_zero]

variable (W : Set U) (hW : IsComplexAnalyticSubset (n := d+t) W)

include hW in
/-- **The whole total ideal at the origin** is the blowup pullback of the whole ideal of `W` at `0`. -/
theorem realOpen_total_eq :
    wholeChartStalkIdeal (realOpenTotalIdeal d t j b U W) (realOpenOrigin d t j b U h0)
        (realOpenOrigin d t j b U h0) (mem_chart_source _ _) =
      Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
        (stalkIdeal (N := d+t) W (baseOrigin d t U h0)) := by
  have h := map_wholeChartStalkIdeal_actual_pullback (realOpenProjection_contMDiff d t j b U)
    (vanishingIdeal (n := d+t) W) (CartanIrreducible.cartanCoherence W hW) (realOpenOrigin d t j b U h0)
  rw [realOpenProjection_origin, realOpenPullback_eq] at h
  exact h.symm

include hW in
/-- **The whole strict ideal at the origin** is the pivot saturation of the whole total ideal. -/
theorem realOpen_strict_eq_powerSat :
    wholeChartStalkIdeal (vanishingIdeal (n := d+t) (realOpenStrictTransform d t j b U W))
        (realOpenOrigin d t j b U h0) (realOpenOrigin d t j b U h0) (mem_chart_source _ _) =
      powerSat (wholeChartStalkIdeal (realOpenTotalIdeal d t j b U W) (realOpenOrigin d t j b U h0)
        (realOpenOrigin d t j b U h0) (mem_chart_source _ _)) (coordinateGerm (j.natAdd d)) := by
  ext g
  rw [mem_powerSat]
  exact (mem_realOpen_geoStrict_iff_exists_pivot_power d t j b U h0 W hW).2.2 g

end RealOpen

/-! ### The pulled graph relations are the evaluated Rees-chart relations -/

section Graph

variable {d t : ℕ} (j : Fin t) (v : ComplexModel (d+t))

/-- The fibre part `b'_i = v_{d+i}` of the recentring vector. -/
def fibreVec : Fin t → ℂ := fun i => v (i.natAdd d)

variable (f : ComplexModel d → ComplexModel t) (hf : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f x)

/-- The component germs `g_i = (f_i)_0`. -/
def graphGerms (i : Fin t) : HolGerm (ComplexModel d) :=
  HolGerm.mk (fun x => f x i)
    (hf.mono fun _ hx => (EuclideanSpace.proj i : ComplexModel t →L[ℂ] ℂ).differentiableAt.comp _ hx)

/-- The blowup pullback fixes tangential germs. -/
theorem blowupPullback_tangentPullback (a : HolGerm (ComplexModel d)) :
    actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i)
      (tangentPullback d t a) = tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h F hF =>
    unfold tangentPullback actualAnalyticBlowupPullback
    rw [compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    refine Eventually.of_forall fun z => ?_
    change F (tangentProjection d t (actualAnalyticBlowupMap _ _ _ z)) = F (tangentProjection d t z)
    congr 1
    ext i
    rw [tangentProjection_apply, tangentProjection_apply, actualAnalyticBlowupMap_apply,
      actualAnalyticBlowupCoordinate, if_neg]
    rintro ⟨k, hk⟩
    have := congrArg Fin.val hk
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega

/-- The graph equation `w_i − f_i(u)` as a germ expression. -/
theorem graphRelation_eq (i : Fin t) :
    graphRelation f hf i = coordinateGerm (i.natAdd d) - tangentPullback d t (graphGerms f hf i) := by
  unfold graphRelation coordinateGerm graphGerms tangentPullback
  rw [compAlgHom_mk, ← HolGerm.mk_sub]
  rfl

variable (hvj : v (j.natAdd d) = 0)

include hvj in
theorem evPoly_X_pivot :
    evPoly d t (fibreVec v) (MvPolynomial.X j) = coordinateGerm (j.natAdd d) := by
  rw [evPoly_X]
  change HolGerm.constHom (v (j.natAdd d)) + _ = _
  rw [hvj, map_zero, zero_add]

include hvj in
/-- `π^*(w_i − f_i(u)) = ev(X_j X_i − g_i)` (`i ≠ j`), `ev(X_j − g_j)` (`i = j`). -/
theorem blowupPullback_graphRelation (i : Fin t) :
    actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) (fun i => v i)
        (graphRelation f hf i) =
      evPoly d t (fibreVec v) ((if i = j then MvPolynomial.X j else MvPolynomial.X j * MvPolynomial.X i) -
        MvPolynomial.C (graphGerms f hf i)) := by
  rw [graphRelation_eq, map_sub, blowupPullback_tangentPullback, map_sub, evPoly_C,
    actualAnalyticBlowupPullback_coordinate, if_pos ⟨i, rfl⟩]
  congr 1
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, evPoly_X_pivot i v hvj]
  · have hne : i.natAdd d ≠ j.natAdd d := fun h => hij (Fin.ext (by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd] at this
      omega))
    rw [if_neg hne, if_neg hij, map_mul, evPoly_X_pivot j v hvj, evPoly_X]
    rfl

include hvj in
/-- **The pulled graph ideal is the evaluated Rees-chart ideal.** -/
theorem map_relIdeal_eq (IX : Ideal (HolGerm (ComplexModel d))) :
    Ideal.map (evPoly d t (fibreVec v)) (relIdeal j (graphGerms f hf) IX) =
      Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d)
        (fun i => v i)).toRingHom (Ideal.map (tangentPullback d t).toRingHom IX ⊔ graphRelations f hf) := by
  unfold relIdeal graphRelations
  rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_map, Ideal.map_map, Ideal.map_span, Ideal.map_span,
    ← Set.range_comp, ← Set.range_comp]
  congr 1
  · congr 1
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply, evPoly_C]
    exact (blowupPullback_tangentPullback j v a).symm
  · congr 2
    funext i
    exact (blowupPullback_graphRelation j v f hf hvj i).symm

end Graph

/-! ### The main identification -/

variable (d t : ℕ) (j : Fin t) (v : ComplexModel (d+t)) (hvj : v (j.natAdd d) = 0)
  (U : Opens (ComplexModel (d+t))) (h0 : (0 : ComplexModel (d+t)) ∈ U)
  (W : Set U) (hW : IsComplexAnalyticSubset (n := d+t) W)
  (f : ComplexModel d → ComplexModel t) (hf : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f x)
  (hf0 : f 0 = 0) (X₀ : Set (ComplexModel d))

include hvj hW hf0 in
/-- **N5.b (S4).**  If `W` is, near the origin of `U`, the graph of `f` over `X₀`, the whole strict ideal at the
origin of the real-open chart is the analytic graph chart ideal `(evPoly(relIdeal j g I(X₀)) : X_j^∞)`. -/
theorem realOpen_strict_eq_chartIdeal
    (hgraph : translatedCarrier (N := d+t) W (baseOrigin d t U h0) =ᶠ[𝓝 0] graphCarrier f X₀) :
    wholeChartStalkIdeal (vanishingIdeal (n := d+t) (realOpenStrictTransform d t j (fun i => v i) U W))
        (realOpenOrigin d t j (fun i => v i) U h0) (realOpenOrigin d t j (fun i => v i) U h0)
        (mem_chart_source _ _) =
      chartIdeal (evPoly d t (fibreVec v)) j (graphGerms f hf)
        (AnalyticGermDecomposition.vanishingIdeal X₀) := by
  rw [realOpen_strict_eq_powerSat d t j (fun i => v i) U h0 W hW,
    realOpen_total_eq d t j (fun i => v i) U h0 W hW, stalkIdeal_eq_vanishingIdeal,
    AnalyticGermDecomposition.vanishingIdeal_congr hgraph, graph_vanishingIdeal_eq f hf hf0,
    ← map_relIdeal_eq j v f hf hvj]
  unfold chartIdeal
  rw [evPoly_X_pivot j v hvj]

end

end Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

import Hironaka.Resolution.HironakaG11PresLineContact
import Hironaka.Resolution.HironakaG11PresLineState
import Hironaka.Resolution.HironakaActualSingularSubmersionPullback

/-!
# Product coordinates and native point presentations after a product with a line (goal G11, step (3a-lines), part L2)

At a point `p = (x, t)` of `X × ℂ` and centred coordinates `Φ` at `x`, the **line coordinates** `(Φ, s − t)` are centred
coordinates at `p` (the product chart followed by `Φ` on the first factor and a translation on the line). In them:

* the adapted germ of `F ∘ fst` is the pullback along the projection `ℂ^{n+1} → ℂ^n` of the adapted germ of `F`
  (`adaptedGerm_comp_fst`);
* the adapted ideal at `p` of the pullback `fst^* J` of a coherent ideal is the extension of the adapted ideal of `J` at `x`
  (`adaptedIdeal_pullback_fst`; finite generators, as in `HironakaG11PresLineState.adaptedIdeal_pullback_biholomorphic`);
* weighted compressions of the lifted family are the extensions of the old ones (`map_weightedCompression_lift`);
* **`point_presentation_line`**: a native point presentation of `Q` for `W` at `x` (vertex family, five point laws, span
  `= I_{W,x}`, compression identity) gives one of the product record `projectionTest Q` for `W × ℂ` at `p`, with the lifted
  data (`HironakaG11PresLineContact.actualHistoricalFivePointLaws_lift`) and `I_{W×ℂ} = fst^* I_W`
  (`HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion`).

The coordinates `lineCoordinates` are the (private) `productCoordinates` of `HironakaActualProjectionTestRecord`, restated.
Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresLineChart

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ProductComplexManifold HironakaHolomorphicJetChartInvariance HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaSmoothSubmersionGermIdealColon HironakaActualWeightedCoefficientCompression
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision
  HironakaG11PresLineFormal HironakaG11PresLineContact
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{0} n}

/-! ### Line coordinates -/

/-- **Line coordinates at `p = (x, t)`**: `w ↦ (Φ(w_x), w_s − t)` in the product chart. -/
def lineCoordinates (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)) :
    LocalHolomorphicEquivAt (n := n+1) (chartAt (ComplexModel (n+1)) p p) where
  source := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.source
  target := (fun w => ((prodModelEquiv n 1).symm w).1) ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  isOpen_target := Φ.isOpen_target.preimage ((prodModelEquiv n 1).symm.continuous.fst)
  center_mem_source := by
    simpa only [mem_preimage,chartAt_prod,prodChart_apply,ContinuousLinearEquiv.symm_apply_apply]
      using Φ.center_mem_source
  toFun w := prodModelEquiv n 1
    (Φ.toFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2-p.2)
  invFun w := prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm w).1,((prodModelEquiv n 1).symm w).2+p.2)
  toFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp
        (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp
        (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.toFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.sub_const p.2).differentiableOn)
  invFun_holomorphic := by
    have hfst : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).1) :=
      (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp
        (prodModelEquiv n 1).symm.differentiable
    have hsnd : Differentiable ℂ (fun w : ComplexModel (n+1) => ((prodModelEquiv n 1).symm w).2) :=
      (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).differentiable.comp
        (prodModelEquiv n 1).symm.differentiable
    exact (prodModelEquiv n 1).differentiable.comp_differentiableOn
      ((Φ.invFun_holomorphic.comp hfst.differentiableOn (fun _ hz => hz)).prodMk
        (hsnd.add_const p.2).differentiableOn)
  mapsTo_toFun := by
    intro w hw
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_toFun hw
  mapsTo_invFun := by
    intro w hw
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using Φ.mapsTo_invFun hw
  left_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.left_inv _ hw,sub_add_cancel,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w
  right_inv := by
    intro w hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,Φ.right_inv _ hw,add_sub_cancel_right,Prod.mk.eta]
    exact (prodModelEquiv n 1).apply_symm_apply w

theorem lineCoordinates_source_subset (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) p.1).target) :
    (lineCoordinates p Φ).source ⊆ (chartAt (ComplexModel (n+1)) p).target := by
  intro w hw
  rw [chartAt_prod, prodChart_target]
  refine ⟨hΦsrc hw, ?_⟩
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
  exact mem_univ _

theorem lineCoordinates_center (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) p.1 p.1) = 0) :
    (lineCoordinates p Φ).toFun (chartAt (ComplexModel (n+1)) p p) = 0 := by
  have h1 : (prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p) =
      (chartAt (ComplexModel n) p.1 p.1, p.2) := by
    rw [chartAt_prod, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  change prodModelEquiv n 1 (Φ.toFun ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).1,
    ((prodModelEquiv n 1).symm (chartAt (ComplexModel (n+1)) p p)).2 - p.2) = 0
  rw [h1]
  simp only [hΦ0, sub_self, Prod.mk_zero_zero, map_zero]

theorem symm_prodModelEquiv_fst (z : ComplexModel (n+1)) :
    ((prodModelEquiv n 1).symm z).1 = tangentProjection n 1 z := by
  ext i
  rfl

/-- **Adapted germs of functions pulled back along the projection.** -/
theorem adaptedGerm_comp_fst (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) p.1 p.1) = 0)
    (h0' : (lineCoordinates p Φ).toFun (chartAt (ComplexModel (n+1)) p p) = 0)
    (F : X → ℂ) (hF : HolomorphicAt n F p.1) (hF' : HolomorphicAt (n+1) (F ∘ (Prod.fst : projectionAmbient X → X)) p) :
    adaptedGerm p (lineCoordinates p Φ) h0' (F ∘ (Prod.fst : projectionAmbient X → X)) hF' =
      tangentPullback n 1 (adaptedGerm p.1 Φ hΦ0 F hF) := by
  unfold adaptedGerm tangentPullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  refine Eventually.of_forall fun z => ?_
  change F ((chartAt (ComplexModel n) p.1).symm ((prodModelEquiv n 1).symm (prodModelEquiv n 1
    (Φ.invFun ((prodModelEquiv n 1).symm z).1, ((prodModelEquiv n 1).symm z).2 + p.2))).1) =
    F ((chartAt (ComplexModel n) p.1).symm (Φ.invFun (tangentProjection n 1 z)))
  rw [ContinuousLinearEquiv.symm_apply_apply, symm_prodModelEquiv_fst]

/-- **Adapted ideals of a pullback along the projection** are the extensions of the old adapted ideals. -/
theorem adaptedIdeal_pullback_fst (J : GermIdeal n X) (hJ : J.IsCoherent) (p : projectionAmbient X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) p.1 p.1) = 0)
    (h0' : (lineCoordinates p Φ).toFun (chartAt (ComplexModel (n+1)) p p) = 0) :
    adaptedIdeal (GermIdeal.pullback (m := n+1) (Prod.fst : projectionAmbient X → X) J) p (lineCoordinates p Φ) h0' =
      Ideal.map (tangentPullback n 1) (adaptedIdeal J p.1 Φ hΦ0) := by
  obtain ⟨U, hU, hx, s, f, hf, hgen⟩ := hJ p.1
  have hfh (i : Fin s) : HolomorphicAt n (f i) p.1 :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hf i) hx
  have hsm : ∀ᶠ z in 𝓝 p, ContMDiffAt 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ComplexModel n) ∞
      (Prod.fst : projectionAmbient X → X) z :=
    Eventually.of_forall fun _ => (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)).contMDiffAt
  have hfo (i : Fin s) : HolomorphicAt (n+1) (f i ∘ (Prod.fst : projectionAmbient X → X)) p :=
    (hfh i).comp_contMDiff hsm
  have hgo (F : projectionAmbient X → ℂ) :=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation hsm J f hfh (hgen p.1 hx) F
  rw [HironakaActualHistoricalInitialAffineDictionary.actual_native_adapted_ideal_of_whole_generation _ p _ _ _
      hfo hgo,
    HironakaActualHistoricalInitialAffineDictionary.actual_native_adapted_ideal_of_whole_generation J p.1 Φ hΦ0
      f hfh (hgen p.1 hx), Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  congr 1
  funext i
  exact adaptedGerm_comp_fst p Φ hΦ0 h0' (f i) (hfh i) (hfo i)

/-- **Weighted compressions of the lifted family** are the extensions of the old compressions. -/
theorem map_weightedCompression_lift {V : Finset (Fin n →₀ ℕ)} (Γ : V → HolGerm (ComplexModel n)) :
    Ideal.map (tangentPullback n 1) (weightedCompression (fun v : V => normalExponentDegree v.val) Γ) =
      weightedCompression (fun v' : liftVertices V => normalExponentDegree v'.val) (liftGerms Γ) := by
  unfold weightedCompression
  rw [Ideal.map_span, ← Set.range_comp, weightedCommonMark_liftVertices]
  have hfun : (fun v' : liftVertices V => liftGerms Γ v' ^
        (weightedCommonMark (fun v : V => normalExponentDegree v.val) / normalExponentDegree v'.val)) =
      (⇑(tangentPullback n 1) ∘ fun v : V => Γ v ^
        (weightedCommonMark (fun v : V => normalExponentDegree v.val) / normalExponentDegree v.val)) ∘
        (liftVertexEquiv V).symm := by
    funext v'
    simp only [Function.comp_apply, liftGerms, map_pow]
    rw [← normalExponentDegree_liftExp ((liftVertexEquiv V).symm v').val, liftVertexEquiv_symm_val]
  rw [hfun, (liftVertexEquiv V).symm.surjective.range_comp]

/-- `I_{W × ℂ} = fst^* I_W`. -/
theorem vanishingIdeal_line (W : Set X) :
    GermIdeal.pullback (m := n+1) (Prod.fst : projectionAmbient X → X) (vanishingIdeal (n := n) W) =
      vanishingIdeal (n := n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' W) :=
  HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) W

/-- **Native point presentations after a product with a line.** -/
theorem point_presentation_line {V : Finset (Fin n →₀ ℕ)} {k : ℕ} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n) (W : Set X) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent) (p : projectionAmbient X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q p.1) :
    ActualHistoricalNativePointPresentation (liftSelector S) (a.trans (liftVertexEquiv V)) (fun i => liftWord (w i))
      ((Prod.fst : projectionAmbient X → X) ⁻¹' W) (projectionTest Q) p := by
  obtain ⟨Φ, hΦsrc, hΦ0, Γ, hFive, hSpan, hComp⟩ := hAt
  have h0' := lineCoordinates_center p Φ hΦ0
  have hsrc' := lineCoordinates_source_subset p Φ hΦsrc
  have hW' : (vanishingIdeal (n := n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' W)).IsCoherent := by
    rw [← vanishingIdeal_line]
    exact GermIdealPullbackCalculus.isCoherent_pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hW
  have hOld := HironakaActualNativeSourceChartComposition.actual_original_translated_flattened_vanishing_origin_eq_adapted
    p.1 Φ hΦsrc hΦ0 W hW
  have hNew := HironakaActualNativeSourceChartComposition.actual_original_translated_flattened_vanishing_origin_eq_adapted
    p (lineCoordinates p Φ) hsrc' h0' ((Prod.fst : projectionAmbient X → X) ⁻¹' W) hW'
  have hWhole := adaptedIdeal_pullback_fst (vanishingIdeal (n := n) W) hW p Φ hΦ0 h0'
  rw [vanishingIdeal_line] at hWhole
  refine ⟨lineCoordinates p Φ, hsrc', h0', liftGerms Γ, actualHistoricalFivePointLaws_lift S a w Γ hFive, ?_, ?_⟩
  · rw [hNew, hWhole, ← hOld, ← hSpan, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.trans_apply, liftGerms_liftVertexEquiv]
  · change adaptedIdeal (GermIdeal.pullback (m := n+1) (Prod.fst : projectionAmbient X → X) Q.ideal) p _ h0' = _
    rw [adaptedIdeal_pullback_fst Q.ideal hQI p Φ hΦ0 h0', hComp, map_weightedCompression_lift]

end

end Hironaka.HironakaG11PresLineChart

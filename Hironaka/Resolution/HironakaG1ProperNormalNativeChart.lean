import Hironaka.Resolution.HironakaG1ProperCarrierNormalContact
import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary
import Hironaka.Analytic.FiniteGermIdealPullbackGenerators

/-! Adapted germs in the actual coordinate-open normal padding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperNormalNativeChart
noncomputable section

open HolGerm Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualOpenZeroSectionDifferentials HironakaActualCentreJointJets
  HironakaRelativeNormalIdeal HironakaActualIntrinsicStableAmbientIso
  HironakaActualRelativeNormalGeometry HironakaActualZeroCoordinateContactSeed
  HironakaActualGraphFunctionalIdeal HironakaHolomorphicJetMonomialSpan
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualHistoricalInitialAffineDictionary HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualCoherentWeightedCoefficientMarked InvertibleIdealQuotient RestrictedIdealExtension
  HironakaActualWeightedNormalPadding IdealOrderArithmetic RelativePrincipalizationSpan

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem chart_apply {m : ℕ} (O : Opens (ComplexModel m)) (x y : O) :
    chartAt (ComplexModel m) x y = y.val := by
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  rfl

private theorem chart_target {m : ℕ} (O : Opens (ComplexModel m)) (x : O)
    (v : ComplexModel m) :
    v ∈ (chartAt (ComplexModel m) x).target ↔ v ∈ O := by
  constructor
  · intro hv
    have h := (chartAt (ComplexModel m) x).right_inv hv
    rw [chart_apply] at h
    exact h ▸ ((chartAt (ComplexModel m) x).symm v).property
  · intro hv
    have h := AnalyticSubsetOpens.chart_mem_opens_target (n := m) (x := x) (y := ⟨v,hv⟩) (by simp)
    simpa using h

theorem productFlat_source_subset (x : U)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    (productFlat U x Φ).source ⊆
      (chartAt (ComplexModel (n+1)) (zeroSection U x)).target := by
  intro z hz
  apply (chart_target _ _ _).mpr
  exact (chart_target U x _).mp (hΦ hz)

theorem productFlat_center (x : U)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    (productFlat U x Φ).toFun
      (chartAt (ComplexModel (n+1)) (zeroSection U x) (zeroSection U x)) = 0 := by
  have hΦx : Φ.toFun x.val = 0 := (congrArg Φ.toFun (chart_apply U x x)).symm.trans hΦ
  refine (congrArg (productFlat U x Φ).toFun (chart_apply _ _ _)).trans ?_
  change join (Φ.toFun (tangentProjection n 1 (tangentInclusion n 1 x.val)))
    (actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)) = 0
  rw [tangentProjection_tangentInclusion, actualJointNormalProjection_tangent, hΦx]
  simp [HironakaActualIntrinsicStableAmbientIso.join]

theorem adaptedGerm_productFlat_projection (x : U)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (F : U → ℂ) (hF : HolomorphicAt n F x)
    (hComp : HolomorphicAt (n+1) (F ∘ projection U) (zeroSection U x)) :
    adaptedGerm (zeroSection U x) (productFlat U x Φ) (productFlat_center x Φ h0)
        (F ∘ projection U) hComp =
      tangentPullback n 1 (adaptedGerm x Φ h0 F hF) := by
  unfold adaptedGerm tangentPullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hz0 : 0 ∈ (productFlat U x Φ).target :=
    productFlat_center x Φ h0 ▸ (productFlat U x Φ).mapsTo_toFun (productFlat U x Φ).center_mem_source
  filter_upwards [(productFlat U x Φ).isOpen_target.mem_nhds hz0] with z hz
  have hs := (chartAt (ComplexModel (n+1)) (zeroSection U x)).right_inv
    (productFlat_source_subset x Φ hSrc ((productFlat U x Φ).mapsTo_invFun hz))
  have hb := (chartAt (ComplexModel n) x).right_inv (hSrc (Φ.mapsTo_invFun hz))
  rw [chart_apply] at hs hb
  apply congrArg F
  apply Subtype.ext
  change tangentProjection n 1 (((chartAt (ComplexModel (n+1)) (zeroSection U x)).symm
      ((productFlat U x Φ).invFun z)).val) =
    ((chartAt (ComplexModel n) x).symm (Φ.invFun (tangentProjection n 1 z))).val
  rw [hs,hb]
  exact first_join _ _

/-- The actual padded normal generator in the genuine extended chart is the
last linear coordinate germ, with its original exponent. -/
theorem adaptedGerm_productFlat_normalPower (x : U)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (d : ℕ) (hd : HolomorphicAt (n+1) (fun z => relativeNormalCoordinate U z ^ d) (zeroSection U x)) :
    adaptedGerm (zeroSection U x) (productFlat U x Φ) (productFlat_center x Φ h0)
        (fun z => relativeNormalCoordinate U z ^ d) hd = (coordinateGerm (Fin.last n)) ^ d := by
  unfold adaptedGerm coordinateGerm
  rw [← HolGerm.mk_pow]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hz0 : 0 ∈ (productFlat U x Φ).target :=
    productFlat_center x Φ h0 ▸ (productFlat U x Φ).mapsTo_toFun (productFlat U x Φ).center_mem_source
  filter_upwards [(productFlat U x Φ).isOpen_target.mem_nhds hz0] with z hz
  have hs := (chartAt (ComplexModel (n+1)) (zeroSection U x)).right_inv
    (productFlat_source_subset x Φ hSrc ((productFlat U x Φ).mapsTo_invFun hz))
  rw [chart_apply] at hs
  apply congrArg (fun u : ℂ => u ^ d)
  change addedCoordinate n (((chartAt (ComplexModel (n+1)) (zeroSection U x)).symm
      ((productFlat U x Φ).invFun z)).val) = z (Fin.last n)
  rw [hs]
  simp only [addedCoordinate, graphFunction, zeroFunction, WithLp.ofLp_zero, Pi.zero_apply, sub_zero]
  change actualJointNormalProjection n 1
    (join (Φ.invFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z)) 0 = _
  rw [second_join]
  rfl

/-- Exact adapted ideal of the literal padded whole record in the true
extended source chart, at every zero-section point. -/
theorem adaptedIdeal_productFlat_normalPadding (I : GermIdeal n U) (hI : I.IsCoherent)
    (x : U) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (d : ℕ) :
    adaptedIdeal (normalPaddingIdeal I d) (zeroSection U x) (productFlat U x Φ)
        (productFlat_center x Φ h0) =
      Ideal.map (tangentPullback n 1).toRingHom (adaptedIdeal I x Φ h0) ⊔
        Ideal.span {(coordinateGerm (Fin.last n)) ^ d} := by
  obtain ⟨O,hO,hx,j,f,hf,hGen⟩ := hI x
  have hfh (i : Fin j) : HolomorphicAt n (f i) x :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hO (hf i) hx
  have hproj : projection U (zeroSection U x) = x :=
    Subtype.ext (tangentProjection_tangentInclusion n 1 x.val)
  have hsm : ∀ᶠ z in 𝓝 (zeroSection U x),
      ContMDiffAt 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ComplexModel n) ∞ (projection U) z :=
    Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt
  let L := GermIdeal.pullback (m := n+1) (projection U) I
  let K := finiteFunctionIdeal (n := n+1) (fun _ : Unit => fun z => relativeNormalCoordinate U z ^ d)
  let G : Fin j ⊕ Unit → productOpen U → ℂ :=
    Sum.elim (fun i => f i ∘ projection U) (fun _ => fun z => relativeNormalCoordinate U z ^ d)
  have hL (g : productOpen U → ℂ) : L.mem (zeroSection U x) g ↔
      IsInSpanAt (n := n+1) (· ∈ range (fun i => f i ∘ projection U)) (zeroSection U x) g :=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation hsm I f
      (by rw [hproj]; exact hfh) (by rw [hproj]; exact hGen x hx) g
  have hGhol (i : Fin j ⊕ Unit) : HolomorphicAt (n+1) (G i) (zeroSection U x) := by
    cases i with
    | inl i => exact ((hproj.symm ▸ hfh i) : HolomorphicAt n (f i) (projection U (zeroSection U x))).comp_contMDiff hsm
    | inr _ => exact Eventually.of_forall ((normalCoordinate_mdifferentiable U).pow d)
  have hAll (g : productOpen U → ℂ) : (normalPaddingIdeal I d).mem (zeroSection U x) g ↔
      IsInSpanAt (n := n+1) (· ∈ range G) (zeroSection U x) g := by
    change (sumIdeal L K).mem (zeroSection U x) g ↔ _
    rw [mem_sumIdeal_iff]
    constructor
    · intro hg
      apply IsInSpanAt.trans _ hg
      rintro y (h | h)
      · exact ((hL y).mp h).mono (by
          rintro _ ⟨i,rfl⟩
          exact ⟨Sum.inl i,rfl⟩)
      · exact h.mono (by
          rintro _ ⟨i,rfl⟩
          exact ⟨Sum.inr i,rfl⟩)
    · intro hg
      apply hg.mono
      rintro _ ⟨i,rfl⟩
      cases i with
      | inl i => exact Or.inl ((hL _).mpr (isInSpanAt_self ⟨i,rfl⟩ (hGhol (Sum.inl i))))
      | inr i => exact Or.inr (isInSpanAt_self ⟨i,rfl⟩ (hGhol (Sum.inr i)))
  rw [actual_native_adapted_ideal_of_whole_generation _ _ _ _ G hGhol hAll,
    actual_native_adapted_ideal_of_whole_generation I x Φ h0 f hfh (hGen x hx),
    Ideal.map_span, ← Set.range_comp, ← Ideal.span_union]
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i,(adaptedGerm_productFlat_projection x Φ hSrc h0 _ (hfh i) _).symm⟩
    | inr i => exact Or.inr (Set.mem_singleton_iff.mpr
        (adaptedGerm_productFlat_normalPower x Φ hSrc h0 d _))
  · rintro (⟨i,rfl⟩ | hg)
    · exact ⟨Sum.inl i, adaptedGerm_productFlat_projection x Φ hSrc h0 _ (hfh i) _⟩
    · exact ⟨Sum.inr (), (adaptedGerm_productFlat_normalPower x Φ hSrc h0 d _).trans
        (Set.mem_singleton_iff.mp hg).symm⟩

#print axioms adaptedIdeal_productFlat_normalPadding

end
end Hironaka.HironakaG1ProperNormalNativeChart

import Hironaka.Analytic.Unibranch.HironakaG10GlChartCoordinates

/-!
# N3 + N4 assembly: the flattener of the joint chart family from actual chart data

Lane G10N34, run 0081 (G10GL's split-off N3+N4).  Generic (no canonical data): an old family `F` with an actual chart
square over a graph chart of the base, a new base `σ : Bl → Y` with an actual chart square read through a biholomorphism
`χ`, and the open-chart joint quotient `JointQuotient` of TN `HironakaG10JointStrictTorsion` whose four translated chart
maps are in the normal form of `HironakaG10GlFlattenerTransfer` (`(id, B)`, `(G, id)`, `(id, B)`, `(G, id)`), with the
same source ideal.  Then (**`flattener_of_chart_data`**) for every flattener `P` of `F` at the old point, `σ P` is the
flattener of the joint base map `ψ = targetStalkToJoint ∘ (stalk of the new chart)`, and flatness over `V(J)`
base-changes (Hironaka 1975, Th. 2.5).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerAssembly

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaChowRelativeGraphPresentation
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaActualAnalyticBaseChangeCoefficients
  HironakaG10HirFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10SbPulledChartFlat Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer
  Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation Hironaka.Analytic.Unibranch.HironakaG10NfRealOpenChartIdeal

noncomputable section

/-- The pulled chart ideal only depends on the germ of the base change map. -/
theorem pulledIdeal_congr (d t e : ℕ) (K : Ideal (HolGerm (ComplexModel (d+t))))
    {φ₁ φ₂ : ComplexModel e → ComplexModel d}
    (hφ₁ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ₁ v) (hφ₁0 : φ₁ 0 = 0)
    (hφ₂ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ₂ v) (hφ₂0 : φ₂ 0 = 0)
    (h : φ₁ =ᶠ[𝓝 0] φ₂) (I' : Ideal (HolGerm (ComplexModel e))) :
    pulledIdeal d t e K φ₁ hφ₁ hφ₁0 I' = pulledIdeal d t e K φ₂ hφ₂ hφ₂0 I' := by
  unfold pulledIdeal jointBasePullback
  have hp : Tendsto (tangentProjection e t) (𝓝 (0 : ComplexModel (e+t))) (𝓝 0) := by
    simpa only [map_zero] using (tangentProjection e t).continuous.tendsto 0
  rw [compAlgHom_congr _ _ _ _ (show jointBaseMap d e t φ₁ =ᶠ[𝓝 0] jointBaseMap d e t φ₂ from by
    filter_upwards [hp.eventually h] with w hw
    simp only [jointBaseMap, hw])]

section Assembly

variable {nS nT r : ℕ}
  {MX : Type} [TopologicalSpace MX] [ChartedSpace (ComplexModel (nS+r)) MX] [IsComplexManifold (nS+r) MX]
  {NB : Type} [TopologicalSpace NB] [ChartedSpace (ComplexModel (nT+r)) NB] [IsComplexManifold (nT+r) NB]
  {gX : MX → NB} (hgX : ContMDiff 𝓘(ℂ, ComplexModel (nS+r)) 𝓘(ℂ, ComplexModel (nT+r)) ∞ gX)
  {CX : Set MX} {DY : Set NB} (hCD : ∀ x ∈ CX, gX x ∈ DY)
  {Xs Ys Bl : LocallyRingedSpace.{0}}
  (iC : actualSubspaceLocallyRingedSpace (n := nS+r) CX ⟶ Xs) [LocallyRingedSpace.IsOpenImmersion iC]
  (iD : actualSubspaceLocallyRingedSpace (n := nT+r) DY ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion iD]
  (Fm : Xs ⟶ Ys) (hsqX : actualSubspaceMap hgX hCD ≫ iD = iC ≫ Fm)
  {T T' : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel (nT+r)) T] [IsComplexManifold (nT+r) T]
  [TopologicalSpace T'] [ChartedSpace (ComplexModel (nT+r)) T'] [IsComplexManifold (nT+r) T']
  (χ : T ≃ₘ⟮𝓘(ℂ, ComplexModel (nT+r)), 𝓘(ℂ, ComplexModel (nT+r))⟯ T') (V : Set T) (V' : Set T')
  (hVV' : ∀ z, z ∈ V ↔ χ z ∈ V')
  {φt : T' → NB} (hφt : ContMDiff 𝓘(ℂ, ComplexModel (nT+r)) 𝓘(ℂ, ComplexModel (nT+r)) ∞ φt)
  (hV'D : ∀ p ∈ V', φt p ∈ DY)
  (tcm : actualSubspaceLocallyRingedSpace (n := nT+r) V ⟶ Bl) [LocallyRingedSpace.IsOpenImmersion tcm]
  (σm : Bl ⟶ Ys)
  (hsqT : actualSubspaceMap (hφt.comp χ.contMDiff) (fun z hz => hV'D (χ z) ((hVV' z).mp hz)) ≫ iD = tcm ≫ σm)
  (j : Fin r) (bv : Fin (nS+r) → ℂ) (U : Opens (ComplexModel (nS+r))) (W : Set U)
  (f : realOpenChartDomain nS r j bv U → T)
  (hf : ContMDiff 𝓘(ℂ, ComplexModel (nS+r)) 𝓘(ℂ, ComplexModel (nT+r)) ∞ f)
  (hW : IsComplexAnalyticSubset (n := nS+r) W) (hV : IsComplexAnalyticSubset (n := nT+r) V)
  (hV' : IsComplexAnalyticSubset (n := nT+r) V')
  (w : realOpenChartDomain nS r j bv U) (hwV : f w ∈ V)
  (γ : CX) (x₁ : Xs) (hx₁ : iC.base γ = x₁) (hbase : Fm.base x₁ = σm.base (tcm.base ⟨f w, hwV⟩))
  (hdq : (actualSubspaceMap hφt hV'D).base ((biholoMap χ V V' hVV').base ⟨f w, hwV⟩) =
    (actualSubspaceMap hgX hCD).base γ)
  (G : ComplexModel nS → ComplexModel nT) (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0)
  (B : ComplexModel r → ComplexModel r) (hB : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ B z) (hB0 : B 0 = 0)
  (hPi : actualTranslatedMap (n := nS+r) (m := nS+r) (realOpenProjection nS r j bv U) w =ᶠ[𝓝 0] blowMap nS r B)
  (hPsi : actualTranslatedMap (n := nT+r) (m := nS+r) (χ ∘ f) w =ᶠ[𝓝 0] srcMap nT nS r G)
  (hφ : actualTranslatedMap (n := nT+r) (m := nT+r) φt (χ (f w)) =ᶠ[𝓝 0] blowMap nT r B)
  (hF₀ : actualTranslatedMap (n := nT+r) (m := nS+r) gX γ.val =ᶠ[𝓝 0] srcMap nT nS r G)
  (hJ : sourceIdealAt nS r j bv U W w = chartIdealAt (k := nS+r) CX γ)

include hsqX hsqT hdq hx₁ hbase hPi hPsi hφ hF₀ hJ hG hG0 hB hB0 hW hV' in
/-- **Hironaka Th. 2.5 on actual chart data.**  The image of every flattener of the old family is the flattener of
the joint base map, and flatness base-changes. -/
theorem flattener_of_chart_data :
    (∀ P : Ideal (Ys.presheaf.stalk (Fm.base x₁)), IsFlattenerIdeal (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) P →
      IsFlattenerIdeal ((targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV).comp
          (tcm.stalkMap ⟨f w, hwV⟩).hom)
        (P.map (lrsFibreMap σm (Fm.base x₁) (tcm.base ⟨f w, hwV⟩) hbase.symm))) ∧
    (∀ J₀ : Ideal (Ys.presheaf.stalk (Fm.base x₁)), (quotMap (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) J₀).Flat →
      (quotMap ((targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV).comp
          (tcm.stalkMap ⟨f w, hwV⟩).hom)
        (J₀.map (lrsFibreMap σm (Fm.base x₁) (tcm.base ⟨f w, hwV⟩) hbase.symm))).Flat) := by
  -- the old family
  set q : V := ⟨f w, hwV⟩
  set dγ := (actualSubspaceMap hgX hCD).base γ
  have hc : iD.base dγ = Fm.base x₁ := by
    rw [← hx₁]
    exact congrArg (fun k => k.base γ) hsqX
  set eA := chartQuotientEquiv DY iD dγ (Fm.base x₁) hc
  have hBsq := oldFamily_square hgX hCD iC iD Fm hsqX γ x₁ hx₁ (Fm.base x₁) rfl hc
  -- the new base
  set I' := chartIdealAt (k := nT+r) V' ((biholoMap χ V V' hVV').base q)
  have hJI : chartIdealAt (k := nT+r) DY dγ ≤ I'.comap (actualHolomorphicGermPullback hφt (χ q.val)).toRingHom := by
    have h := chartIdeal_le_comap hφt hV'D ((biholoMap χ V V' hVV').base q)
    rw [hdq] at h
    exact h
  have hA' : (lrsFibreMap σm (Fm.base x₁) (tcm.base q) hbase.symm).comp eA.toRingHom =
      (biholoChartEquiv χ V V' hVV' tcm q).toRingHom.comp
        (Ideal.quotientMap I' (actualHolomorphicGermPullback hφt (χ q.val)).toRingHom hJI) := by
    have key : ∀ (d₀ : DY) (hd : (actualSubspaceMap hφt hV'D).base ((biholoMap χ V V' hVV').base q) = d₀)
        (hc₀ : iD.base d₀ = Fm.base x₁)
        (hJI₀ : chartIdealAt (k := nT+r) DY d₀ ≤ I'.comap (actualHolomorphicGermPullback hφt (χ q.val)).toRingHom),
        (lrsFibreMap σm (Fm.base x₁) (tcm.base q) hbase.symm).comp
            (chartQuotientEquiv DY iD d₀ (Fm.base x₁) hc₀).toRingHom =
          (biholoChartEquiv χ V V' hVV' tcm q).toRingHom.comp
            (Ideal.quotientMap I' (actualHolomorphicGermPullback hφt (χ q.val)).toRingHom hJI₀) := by
      intro d₀ hd hc₀ hJI₀
      subst hd
      exact baseChange_square χ V V' hVV' hφt hV'D tcm iD σm hsqT q (Fm.base x₁) hbase.symm hc₀
    exact key dγ hdq hc hJI
  -- the joint quotient and the normal form
  set J := chartIdealAt (k := nS+r) CX γ
  have hPi' : actualHolomorphicGermPullback (realOpenProjection_contMDiff nS r j bv U) w =
      blowPullback B hB hB0 :=
    compAlgHom_congr _ _ _ _ hPi
  have hPsi' : actualHolomorphicGermPullback (χ.contMDiff.comp hf) w = srcPullback G hG hG0 :=
    compAlgHom_congr _ _ _ _ hPsi
  have hjoint : jointChartIdeal nS r j bv U W f hf χ V' w = jointGermIdeal G hG hG0 B hB hB0 J I' := by
    unfold jointChartIdeal jointGermIdeal
    rw [hPi', hPsi', hJ]
    rfl
  have hK : nativeRelativeGraphIdeal hgX CX γ =
      relativeGraphIdeal (nT+r) (nS+r) (srcMap nT nS r G) (srcMap_differentiable G hG) J :=
    relativeGraphIdeal_congr (nT+r) (nS+r) (actualTranslatedMap_holomorphic hgX γ.val)
      (actualTranslatedMap_zero gX γ.val) (srcMap_differentiable G hG) (srcMap_zero G hG0) hF₀ J
  have hpull : pulledIdeal (nT+r) (nS+r) (nT+r) (nativeRelativeGraphIdeal hgX CX γ)
      (actualTranslatedMap (n := nT+r) (m := nT+r) φt (χ q.val)) (actualTranslatedMap_holomorphic hφt (χ q.val))
      (actualTranslatedMap_zero φt (χ q.val)) I' = normalPulledIdeal G hG B hB hB0 J I' := by
    rw [hK]
    exact pulledIdeal_congr _ _ _ _ _ _ _ _ hφ I'
  set eC := (Ideal.quotEquivOfEq hpull).trans ((pulledJointEquiv G hG hG0 B hB hB0 J I').trans
    ((Ideal.quotEquivOfEq hjoint.symm).trans
      (jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w).symm))
  have hC : ((targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV).comp
        (tcm.stalkMap q).hom).comp (biholoChartEquiv χ V V' hVV' tcm q).toRingHom =
      eC.toRingHom.comp (pulledChartMap (nT+r) (nS+r) (nT+r) (nativeRelativeGraphIdeal hgX CX γ)
        (actualTranslatedMap (n := nT+r) (m := nT+r) φt (χ q.val)) (actualTranslatedMap_holomorphic hφt (χ q.val))
        (actualTranslatedMap_zero φt (χ q.val)) I') := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    apply (jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w).injective
    have hL := jointChartEquiv_targetStalk nS r j bv U W f V hf hW χ V' hVV' hV' hV tcm w hwV a
    have hR : jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w
        (eC (Ideal.Quotient.mk _ (tangentPullback (nT+r) (nS+r) a))) =
        Ideal.Quotient.mk _ (srcPullback G hG hG0 a) := by
      change jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w
        ((jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w).symm
          (Ideal.quotEquivOfEq hjoint.symm (pulledJointEquiv G hG hG0 B hB hB0 J I'
            (Ideal.Quotient.mk _ (tangentPullback (nT+r) (nS+r) a))))) = _
      rw [RingEquiv.apply_symm_apply, pulledJointEquiv_mk, substPullback_tangentPullback]
      rfl
    change jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w
        (targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV
          ((tcm.stalkMap q).hom (biholoChartEquiv χ V V' hVV' tcm q (Ideal.Quotient.mk _ a)))) =
      jointChartEquiv nS r j bv U W f V hf hW χ V' hVV' hV' w
        (eC (Ideal.Quotient.mk _ (tangentPullback (nT+r) (nS+r) a)))
    rw [hL, hR, hPsi']
  refine ⟨fun P hP => ?_, fun J₀ hJ₀ => ?_⟩
  · exact isFlattenerIdeal_map_of_presentations (nT+r) (nS+r) (nT+r) (chartIdealAt (k := nT+r) DY dγ)
      (nativeRelativeGraphIdeal hgX CX γ) (chartIdeal_le_graphIdeal hgX hCD γ)
      (actualTranslatedMap (n := nT+r) (m := nT+r) φt (χ q.val)) (actualTranslatedMap_holomorphic hφt (χ q.val))
      (actualTranslatedMap_zero φt (χ q.val)) I' hJI
      (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) (lrsFibreMap σm (Fm.base x₁) (tcm.base q) hbase.symm)
      ((targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV).comp (tcm.stalkMap q).hom)
      eA _ hBsq (biholoChartEquiv χ V V' hVV' tcm q) hA' eC hC P hP
  · exact flat_map_of_presentations (nT+r) (nS+r) (nT+r) (chartIdealAt (k := nT+r) DY dγ)
      (nativeRelativeGraphIdeal hgX CX γ) (chartIdeal_le_graphIdeal hgX hCD γ)
      (actualTranslatedMap (n := nT+r) (m := nT+r) φt (χ q.val)) (actualTranslatedMap_holomorphic hφt (χ q.val))
      (actualTranslatedMap_zero φt (χ q.val)) I' hJI
      (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) (lrsFibreMap σm (Fm.base x₁) (tcm.base q) hbase.symm)
      ((targetStalkToJoint (n := nT+r) nS r j bv U W f V hf hV w hwV).comp (tcm.stalkMap q).hom)
      eA _ hBsq (biholoChartEquiv χ V V' hVV' tcm q) hA' eC hC J₀ hJ₀

end Assembly

end

end Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerAssembly

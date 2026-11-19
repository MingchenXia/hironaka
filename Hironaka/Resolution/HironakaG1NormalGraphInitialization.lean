import Hironaka.Resolution.HironakaG1NormalSelectorGraph

/-! The normal graph construction over a change of actual source coordinates. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NormalGraphInitialization

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers GermIdealPullbackCalculus InvertibleIdealQuotient RestrictedIdealExtension
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualOpenZeroSectionDifferentials HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedNormalPadding HironakaSmoothSubmersionRelativeRestriction
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaActualPowerBoundaryExponents
  HironakaG1NormalSelectorGraph HironakaG8LocalHistory ResolutionInvariantSpec
  MarkedIdealOperationsAlong.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals

variable {n : ℕ} {U V W : Opens (ComplexModel n)}

private abbrev base (U : Opens (ComplexModel n)) := CMfd.of (n := n) U
private abbrev ambient (U : Opens (ComplexModel n)) := CMfd.of (n := n + 1) (productOpen U)

def baseLift (b : U → V) (z : productOpen U) : productOpen V :=
  ⟨join (b (projection U z)).val (actualJointNormalProjection n 1 z.val), by
    change tangentProjection n 1 (join _ _) ∈ V
    rw [first_join]
    exact (b (projection U z)).property⟩

@[simp] theorem projection_baseLift (b : U → V) (z : productOpen U) :
    projection V (baseLift b z) = b (projection U z) :=
  Subtype.ext (first_join _ _)

@[simp] theorem normal_baseLift (b : U → V) (z : productOpen U) :
    actualJointNormalProjection n 1 (baseLift b z).val =
      actualJointNormalProjection n 1 z.val :=
  second_join _ _

theorem baseLift_contMDiff {b : U → V}
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel (n + 1)) ∞ (baseLift b) := by
  apply (ContMDiff.subtypeVal_comp_iff (productOpen V) _).mp
  exact ((tangentInclusion n 1).contMDiff.comp
    (contMDiff_subtype_val.comp (hb.comp (projection_contMDiff U)))).add
    ((actualJointNormalInclusion n 1).contMDiff.comp
      ((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val))

private theorem baseLift_inverse (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    (z : productOpen U) : baseLift b.symm (baseLift b z) = z := by
  apply Subtype.ext
  change join (b.symm (projection V (baseLift b z))).val
    (actualJointNormalProjection n 1 (baseLift b z).val) = z.val
  rw [normal_baseLift, projection_baseLift, Diffeomorph.symm_apply_apply]
  exact
    join_projections z.val

/-- The actual product chart change of a source biholomorphism. -/
def baseLiftEquiv (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V) :
    productOpen U ≃ₘ⟮𝓘(ℂ, ComplexModel (n + 1)), 𝓘(ℂ, ComplexModel (n + 1))⟯ productOpen V where
  toEquiv := ⟨baseLift b, baseLift b.symm, baseLift_inverse b, baseLift_inverse b.symm⟩
  contMDiff_toFun := baseLift_contMDiff b.contMDiff
  contMDiff_invFun := baseLift_contMDiff b.symm.contMDiff

theorem baseLift_preimage_selectorCarrier (b : U → V) (g : V → ComplexModel 1) (A : Set V) :
    baseLift b ⁻¹' selectorCarrier g A = selectorCarrier (g ∘ b) (b ⁻¹' A) := by
  ext z
  change (projection V (baseLift b z) ∈ A ∧
    actualJointNormalProjection n 1 (baseLift b z).val = g (projection V (baseLift b z))) ↔
      (b (projection U z) ∈ A ∧ actualJointNormalProjection n 1 z.val = g (b (projection U z)))
  rw [projection_baseLift, normal_baseLift]

/-- Changing source coordinates pulls back the actual graph padding, including
all ambient boundary slots, before any selector shift in the new chart. -/
theorem pullback_baseLift_selectorMarked {b : U → V}
    (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b)
    {g : V → ComplexModel 1}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (Q : MarkedIdeal n V) (hQ : Q.ideal.IsCoherent) (F : List (Set (productOpen V))) :
    MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (baseLift b) (selectorMarked g Q F) =
      selectorMarked (g ∘ b) (MarkedIdeal.pullback (M := base V) (M' := base U) b Q)
        (F.map (baseLift b ⁻¹' ·)) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact baseLift_preimage_selectorCarrier b g Q.N
  · change (F ++ Q.E.map (projection V ⁻¹' ·)).map (baseLift b ⁻¹' ·) =
      F.map (baseLift b ⁻¹' ·) ++ (Q.E.map (b ⁻¹' ·)).map (projection U ⁻¹' ·)
    rw [List.map_append, List.map_map, List.map_map]
    simp only [preimage_preimage, Function.comp_def, projection_baseLift]
  · let c : productOpen V → ℂ :=
      fun z => (actualJointNormalProjection n 1 z.val - g (projection V z)) 0
    have hc : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ) ∞ c :=
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
        (((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val).sub
          (hg.comp (projection_contMDiff V)))
    have hGen : MDifferentiable 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ) (fun z => c z ^ Q.d) :=
      (hc.mdifferentiable (by simp)).pow _
    have hLift := baseLift_contMDiff hb
    change GermIdeal.pullback (m := n + 1) (baseLift b)
      (sumIdeal (GermIdeal.pullback (m := n + 1) (projection V) Q.ideal)
        (finiteFunctionIdeal (fun _ : Unit => fun z => c z ^ Q.d))) = _
    rw [pullback_sumIdeal_dimensions hLift (isCoherent_pullback (projection_contMDiff V) hQ)
      (isCoherent_finiteFunctionIdeal _ (fun _ => hGen)),
      ← coherent_pullback_comp (projection_contMDiff V) hLift Q.ideal hQ,
      finiteFunctionIdeal_pullback _ (fun _ => hGen) _ hLift]
    have hProj : projection V ∘ baseLift b = b ∘ projection U :=
      funext (projection_baseLift b)
    rw [hProj, coherent_pullback_comp hb (projection_contMDiff U) Q.ideal hQ]
    congr 1
    congr 1
    funext _ z
    change c (baseLift b z) ^ Q.d =
      ((actualJointNormalProjection n 1 z.val - g (b (projection U z))) 0) ^ Q.d
    simp only [c, projection_baseLift, normal_baseLift]
  · rfl


/-- The actual chart map for unrelated selector functions over a given source
biholomorphism. The selector shift is taken after expressing the second
selector in the first source coordinates. -/
def selectorChartEquiv (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel 1} {g : V → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g) :
    productOpen U ≃ₘ⟮𝓘(ℂ, ComplexModel (n + 1)), 𝓘(ℂ, ComplexModel (n + 1))⟯ productOpen V :=
  (graphShiftEquiv f (g ∘ b) hf (hg.comp b.contMDiff)).trans (baseLiftEquiv b)

@[simp] theorem projection_selectorChartEquiv
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel 1} {g : V → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (z : productOpen U) :
    projection V (selectorChartEquiv b hf hg z) = b (projection U z) := by
  change projection V (baseLift b (graphShift f (g ∘ b) z)) = _
  rw [projection_baseLift, projection_graphShift]

private theorem normal_selectorChartEquiv
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel 1} {g : V → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (z : productOpen U) :
    actualJointNormalProjection n 1 (selectorChartEquiv b hf hg z).val =
      actualJointNormalProjection n 1 z.val - f (projection U z) + g (b (projection U z)) := by
  change actualJointNormalProjection n 1 (baseLift b (graphShift f (g ∘ b) z)).val = _
  rw [normal_baseLift]
  exact second_join _ _

/-- Consecutive changes of source coordinates and independent selectors compose
as actual ambient maps. This supplies compatibility on chains of charts. -/
theorem selectorChartEquiv_comp
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    (c : V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ W)
    {f : U → ComplexModel 1} {g : V → ComplexModel 1} {h : W → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ h) :
    (selectorChartEquiv c hg hh : productOpen V → productOpen W) ∘ selectorChartEquiv b hf hg =
      selectorChartEquiv (b.trans c) hf hh := by
  funext z
  change selectorChartEquiv c hg hh (selectorChartEquiv b hf hg z) =
    selectorChartEquiv (b.trans c) hf hh z
  let x := selectorChartEquiv c hg hh (selectorChartEquiv b hf hg z)
  let y := selectorChartEquiv (b.trans c) hf hh z
  have hBase : projection W x = projection W y := by
    simp only [x, y, projection_selectorChartEquiv]
    rfl
  have hNormal : actualJointNormalProjection n 1 x.val = actualJointNormalProjection n 1 y.val := by
    simp only [x, y, normal_selectorChartEquiv, projection_selectorChartEquiv]
    change _ - _ + h (c (b (projection U z))) = _ - _ + h (c (b (projection U z)))
    abel
  apply Subtype.ext
  exact (join_projections x.val).symm.trans
    ((congrArg₂ join (congrArg Subtype.val hBase) hNormal).trans (join_projections y.val))

theorem locWPEquiv_selectorChartEquiv_commonPower
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel 1} {g : V → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    {k l : ℕ} (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (e e' : ℕ)
    (hPow : RestrictEquiv (powerMarked (X := base U) P e)
      (MarkedIdeal.pullback (M := base V) (M' := base U) b (powerMarked (X := base V) Q e')))
    (F : List (Set (productOpen V))) :
    LocWPEquiv (X := ambient U)
      (powerMarked (selectorMarked f P (F.map (selectorChartEquiv b hf hg ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (selectorChartEquiv b hf hg)
        (powerMarked (X := ambient V) (selectorMarked g Q F) e')) := by
  let Q' := MarkedIdeal.pullback (M := base V) (M' := base U) b Q
  let R := powerMarked (X := ambient V) (selectorMarked g Q F) e'
  let s := graphShift f (g ∘ b)
  have hM := hQ.isWellFormed.isCoherent
  have hQ' : IsInvDomain l Q' := InvDomainTowerAlong.isInvDomain_pullback b hQ
  have hLift := baseLift_contMDiff b.contMDiff
  have hShift := graphShift_contMDiff hf (hg.comp b.contMDiff)
  have hPullPower := HironakaG11PresClassTransport.pullback_powerMarked
    (M := base V) (M' := base U) (f := b) b.contMDiff Q hM e'
  have hPow' : RestrictEquiv (powerMarked (X := base U) P e) (powerMarked (X := base U) Q' e') := by
    rw [hPullPower] at hPow
    exact hPow
  let c : productOpen V → ℂ :=
    fun z => (actualJointNormalProjection n 1 z.val - g (projection V z)) 0
  have hc : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ) ∞ c :=
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
      (((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val).sub
        (hg.comp (projection_contMDiff V)))
  have hPad : (selectorMarked g Q F).ideal.IsCoherent :=
    isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff V) hM)
      (isCoherent_finiteFunctionIdeal (fun _ : Unit => fun z => c z ^ Q.d)
        (fun _ => (hc.mdifferentiable (by simp)).pow _))
  have hR : R.ideal.IsCoherent := isCoherent_idealPow hPad e'
  have hComp :
      MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (selectorChartEquiv b hf hg) R =
        MarkedIdeal.pullback (M := ambient U) (M' := ambient U) s
          (MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (baseLift b) R) :=
    whole_markedPullback_comp hLift hShift R hR
  change LocWPEquiv (X := ambient U) _
    (MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (selectorChartEquiv b hf hg) R)
  rw [hComp]
  have hBase :
      MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (baseLift b) R =
        powerMarked (X := ambient U) (selectorMarked (g ∘ b) Q' (F.map (baseLift b ⁻¹' ·))) e' := by
    change MarkedIdeal.pullback (M := ambient V) (M' := ambient U) (baseLift b)
      (powerMarked (X := ambient V) (selectorMarked g Q F) e') = _
    rw [HironakaG11PresClassTransport.pullback_powerMarked
      (M := ambient V) (M' := ambient U) (f := baseLift b) hLift _ hPad,
      pullback_baseLift_selectorMarked b.contMDiff hg Q hM F]
  rw [hBase]
  have hF : F.map (selectorChartEquiv b hf hg ⁻¹' ·) =
      (F.map (baseLift b ⁻¹' ·)).map (s ⁻¹' ·) := by
    rw [List.map_map]
    rfl
  rw [hF]
  exact locWPEquiv_pullback_commonPower_selectorMarked hf (hg.comp b.contMDiff)
    P Q' hP hQ' e e' hPow' (F.map (baseLift b ⁻¹' ·))

end

end Hironaka.HironakaG1NormalGraphInitialization

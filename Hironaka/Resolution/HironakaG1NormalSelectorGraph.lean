import Hironaka.Resolution.HironakaG1NormalWeightedClass
import Hironaka.Resolution.HironakaG11PresClassTransport

/-! The fixed-chart transport between two holomorphic selector graphs. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NormalSelectorGraph

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers RestrictedIdealExtension
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualIntrinsicStableAmbientIso HironakaActualOpenZeroSectionDifferentials
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding HironakaSmoothSubmersionRelativeRestriction
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaActualPowerBoundaryExponents
  HironakaSmoothSubmersionCoefficientIdeals HironakaActualRelativeNormalGeometry
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1NormalWeightedClass ResolutionInvariantSpec
  HironakaActualOpenSectionRepresentative HironakaG8LocalContactStage HironakaG8LocalHistory
  MarkedIdealOperationsAlong.MarkedIdeal RestrictLeCalculus HironakaActualSectionBoundaryGeometry

variable {n : ℕ} {U : Opens (ComplexModel n)}

private abbrev ambient (U : Opens (ComplexModel n)) := CMfd.of (n := n + 1) (productOpen U)

private def normal (z : productOpen U) : ComplexModel 1 :=
  actualJointNormalProjection n 1 z.val

/-- The translation carries the graph of `f` to the graph of `g` over the same base. -/
def graphShift (f g : U → ComplexModel 1) (z : productOpen U) : productOpen U :=
  ⟨join (projection U z).val (normal z - f (projection U z) + g (projection U z)), by
    change tangentProjection n 1 (join _ _) ∈ U
    rw [first_join]
    exact (projection U z).property⟩

@[simp] theorem projection_graphShift (f g : U → ComplexModel 1) (z : productOpen U) :
    projection U (graphShift f g z) = projection U z := by
  apply Subtype.ext
  exact first_join _ _

@[simp] private theorem normal_graphShift (f g : U → ComplexModel 1) (z : productOpen U) :
    normal (graphShift f g z) = normal z - f (projection U z) + g (projection U z) :=
  second_join _ _

theorem graphShift_contMDiff {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel (n + 1)) ∞ (graphShift f g) := by
  apply (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp
  have hNormal : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel 1) ∞
      (normal (U := U)) := (actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val
  have hBase : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel n) ∞
      (fun z => (projection U z).val) := contMDiff_subtype_val.comp (projection_contMDiff U)
  exact ((tangentInclusion n 1).contMDiff.comp hBase).add
    ((actualJointNormalInclusion n 1).contMDiff.comp
      ((hNormal.sub (hf.comp (projection_contMDiff U))).add (hg.comp (projection_contMDiff U))))

private theorem graphShift_inverse (f g : U → ComplexModel 1) (z : productOpen U) :
    graphShift g f (graphShift f g z) = z := by
  apply Subtype.ext
  change join (projection U (graphShift f g z)).val
    (normal (graphShift f g z) - g (projection U (graphShift f g z)) +
      f (projection U (graphShift f g z))) = z.val
  simp only [projection_graphShift, normal_graphShift]
  rw [show normal z - f (projection U z) + g (projection U z) - g (projection U z) +
    f (projection U z) = normal z by abel]
  exact join_projections z.val

/-- Holomorphic equivalence of the two actual selector charts. -/
def graphShiftEquiv (f g : U → ComplexModel 1)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g) :
    productOpen U ≃ₘ⟮𝓘(ℂ, ComplexModel (n + 1)), 𝓘(ℂ, ComplexModel (n + 1))⟯ productOpen U where
  toEquiv := ⟨graphShift f g, graphShift g f, graphShift_inverse f g, graphShift_inverse g f⟩
  contMDiff_toFun := graphShift_contMDiff hf hg
  contMDiff_invFun := graphShift_contMDiff hg hf

/-- The graph over the given proper source carrier. -/
def selectorCarrier (f : U → ComplexModel 1) (A : Set U) : Set (productOpen U) :=
  {z | projection U z ∈ A ∧ normal z = f (projection U z)}

theorem graphShift_preimage_selectorCarrier (f g : U → ComplexModel 1) (A : Set U) :
    graphShift f g ⁻¹' selectorCarrier g A = selectorCarrier f A := by
  ext z
  change (projection U (graphShift f g z) ∈ A ∧
    normal (graphShift f g z) = g (projection U (graphShift f g z))) ↔
      (projection U z ∈ A ∧ normal z = f (projection U z))
  simp [sub_eq_zero]

private def selectorCoordinate (f : U → ComplexModel 1) (z : productOpen U) : ℂ :=
  (normal z - f (projection U z)) 0

private theorem selectorCoordinate_contMDiff {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ) ∞ (selectorCoordinate f) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
    (((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val).sub
      (hf.comp (projection_contMDiff U)))

/-- The whole padding ideal on the actual graph support, with its full boundary. -/
def selectorMarked (f : U → ComplexModel 1) (Q : MarkedIdeal n U)
    (F : List (Set (productOpen U))) : MarkedIdeal (n + 1) (ambient U) :=
  ⟨selectorCarrier f Q.N, F ++ Q.E.map (projection U ⁻¹' ·),
    sumIdeal (GermIdeal.pullback (m := n + 1) (projection U) Q.ideal)
      (finiteFunctionIdeal (fun _ : Unit => fun z => selectorCoordinate f z ^ Q.d)), Q.d⟩

private theorem selectorMarked_coherent {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    {Q : MarkedIdeal n U} (hQ : Q.ideal.IsCoherent) (F : List (Set (productOpen U))) :
    (selectorMarked f Q F).ideal.IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hQ)
    (isCoherent_finiteFunctionIdeal _ (fun _ => (selectorCoordinate_contMDiff hf).mdifferentiable (by simp) |>.pow Q.d))

/-- The triangular change transports the entire graph-supported powered record.
Every extra boundary slot is pulled back as an actual ambient subset. -/
theorem pullback_power_selectorMarked {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent)
    (F : List (Set (productOpen U))) (e : ℕ) :
    MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g)
      (powerMarked (selectorMarked g Q F) e) =
        powerMarked (selectorMarked f Q (F.map (graphShift f g ⁻¹' ·))) e := by
  rw [HironakaG11PresClassTransport.pullback_powerMarked (M := ambient U) (M' := ambient U)
    (f := graphShift f g) (graphShift_contMDiff hf hg)
    (selectorMarked g Q F) (selectorMarked_coherent hg hQ F) e]
  congr 1
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact graphShift_preimage_selectorCarrier f g Q.N
  · change (F ++ Q.E.map (projection U ⁻¹' ·)).map (graphShift f g ⁻¹' ·) = _
    rw [List.map_append, List.map_map]
    simp only [selectorMarked, preimage_preimage, Function.comp_def, projection_graphShift]
  · have hShift := graphShift_contMDiff hf hg
    have hBase := isCoherent_pullback (projection_contMDiff U) hQ
    have hGen : MDifferentiable 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ)
        (fun z => selectorCoordinate g z ^ Q.d) :=
      ((selectorCoordinate_contMDiff hg).mdifferentiable (by simp)).pow Q.d
    change GermIdeal.pullback (m := n + 1) (graphShift f g)
      (sumIdeal (GermIdeal.pullback (m := n + 1) (projection U) Q.ideal)
        (finiteFunctionIdeal (fun _ : Unit => fun z => selectorCoordinate g z ^ Q.d))) = _
    rw [pullback_sumIdeal_dimensions hShift hBase
      (isCoherent_finiteFunctionIdeal _ (fun _ => hGen)),
      ← coherent_pullback_comp (projection_contMDiff U) hShift Q.ideal hQ,
      finiteFunctionIdeal_pullback _ (fun _ => hGen) _ hShift]
    have hProj : projection U ∘ graphShift f g = projection U :=
      funext (projection_graphShift f g)
    rw [hProj]
    congr 1
    congr 1
    funext _ z
    change selectorCoordinate g (graphShift f g z) ^ Q.d = selectorCoordinate f z ^ Q.d
    unfold selectorCoordinate
    simp
  · rfl


/-- The section parametrizing an actual selector graph. -/
def selectorSection (f : U → ComplexModel 1) : U → productOpen U :=
  graphShift 0 f ∘ zeroSection U

/-- Restricting the whole powered graph padding along its own section recovers
the whole source power and pulls back each extra boundary member in order. -/
theorem markedPullback_power_selectorSection {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    {k : ℕ} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (F : List (Set (productOpen U))) (e : ℕ) :
    markedPullback (m := n) (selectorSection f) (powerMarked (selectorMarked f Q F) e) =
      { powerMarked (X := CMfd.of (n := n) U) Q e with E := F.map (selectorSection f ⁻¹' ·) ++ Q.E } := by
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (0 : U → ComplexModel 1) := contMDiff_const
  have hProj : projection U ∘ selectorSection f = id := by
    funext x
    change projection U (graphShift 0 f (zeroSection U x)) = x
    rw [projection_graphShift]
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 x.val
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change selectorSection f ⁻¹' selectorCarrier f Q.N = Q.N
    change zeroSection U ⁻¹' (graphShift 0 f ⁻¹' selectorCarrier f Q.N) = Q.N
    rw [graphShift_preimage_selectorCarrier]
    ext x
    change (projection U (zeroSection U x) ∈ Q.N ∧ normal (zeroSection U x) = 0) ↔ x ∈ Q.N
    have hBase : projection U (zeroSection U x) = x :=
      Subtype.ext (tangentProjection_tangentInclusion n 1 x.val)
    rw [hBase]
    simp [normal, zeroSection]
  · change (F ++ Q.E.map (projection U ⁻¹' ·)).map (selectorSection f ⁻¹' ·) =
      F.map (selectorSection f ⁻¹' ·) ++ Q.E
    rw [List.map_append, List.map_map]
    congr 1
    change Q.E.map (fun H => (projection U ∘ selectorSection f) ⁻¹' H) = Q.E
    rw [hProj]
    exact List.map_id Q.E
  · have hCoherent := isCoherent_idealPow (selectorMarked_coherent hf hQ.isWellFormed.isCoherent F) e
    have hShift := graphShift_contMDiff hZero hf
    have hTransport := congrArg (fun R : MarkedIdeal (n + 1) (ambient U) => R.ideal)
      (pullback_power_selectorMarked hZero hf Q hQ.isWellFormed.isCoherent F e)
    change GermIdeal.pullback (m := n + 1) (graphShift 0 f)
        (powerMarked (selectorMarked f Q F) e).ideal =
      (powerMarked (selectorMarked 0 Q (F.map (graphShift 0 f ⁻¹' ·))) e).ideal at hTransport
    change GermIdeal.pullback (m := n) (graphShift 0 f ∘ zeroSection U)
      (powerMarked (selectorMarked f Q F) e).ideal = _
    have hComp : GermIdeal.pullback (m := n) (graphShift 0 f ∘ zeroSection U)
        (powerMarked (selectorMarked f Q F) e).ideal =
      GermIdeal.pullback (m := n) (zeroSection U)
        (GermIdeal.pullback (m := n + 1) (graphShift 0 f)
          (powerMarked (selectorMarked f Q F) e).ideal) :=
      coherent_pullback_comp hShift (zeroSection_contMDiff U) _ hCoherent
    rw [hComp, hTransport]
    have hTrace := congrArg (fun R : MarkedIdeal n U => R.ideal) (markedPullback_power_properNormal Q hQ e)
    exact hTrace
  · rfl


private theorem selectorSection_fixes {f : U → ComplexModel 1} {A : Set U}
    {z : productOpen U} (hz : z ∈ selectorCarrier f A) :
    selectorSection f (projection U z) = z := by
  have hBase : projection U (zeroSection U (projection U z)) = projection U z :=
    Subtype.ext (tangentProjection_tangentInclusion n 1 (projection U z).val)
  have hNormal : normal (zeroSection U (projection U z)) = 0 := by simp [normal, zeroSection]
  have hGraph : normal z = f (projection U z) := hz.2
  apply Subtype.ext
  dsimp only [selectorSection, Function.comp_apply, graphShift]
  rw [hBase, hNormal]
  simp only [Pi.zero_apply, sub_zero, zero_add]
  rw [← hGraph]
  exact join_projections z.val

private theorem powered_graph_restriction {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    {k : ℕ} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (F : List (Set (productOpen U))) (e : ℕ) :
    RestrictEquiv (powerMarked (selectorMarked f Q F) e)
      { powerMarked (selectorMarked f Q F) e with
        ideal := GermIdeal.pullback (m := n + 1) (projection U)
          (powerMarked (X := CMfd.of (n := n) U) Q e).ideal } := by
  let R := powerMarked (selectorMarked f Q F) e
  have hCoherent : R.ideal.IsCoherent := isCoherent_idealPow
    (selectorMarked_coherent hf hQ.isWellFormed.isCoherent F) e
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (0 : U → ComplexModel 1) := contMDiff_const
  have hSec : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + 1)) ∞
      (selectorSection f) := (graphShift_contMDiff hZero hf).comp (zeroSection_contMDiff U)
  have hTrace : GermIdeal.pullback (m := n) (selectorSection f) R.ideal =
      (powerMarked (X := CMfd.of (n := n) U) Q e).ideal :=
    congrArg (fun M : MarkedIdeal n U => M.ideal) (markedPullback_power_selectorSection hf Q hQ F e)
  have hr : GermIdeal.pullback (m := n + 1) (selectorSection f ∘ projection U) R.ideal =
      GermIdeal.pullback (m := n + 1) (projection U) (powerMarked (X := CMfd.of (n := n) U) Q e).ideal := by
    rw [coherent_pullback_comp hSec (projection_contMDiff U) R.ideal hCoherent, hTrace]
  have hRet := restrictEquiv_retraction R.N R.E R.d _ (hSec.comp (projection_contMDiff U))
    (fun _ (hz : _ ∈ selectorCarrier f Q.N) => selectorSection_fixes hz) R.ideal
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCoherent hg)
  rwa [hr] at hRet

/-- Transport across the actual selector chart and compare different source
records using restricted agreement of their common-mark whole powers. -/
theorem restrictEquiv_pullback_commonPower_selectorMarked {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    {k l : ℕ} (P Q : MarkedIdeal n U) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (e e' : ℕ)
    (hPow : RestrictEquiv (powerMarked (X := CMfd.of (n := n) U) P e)
      (powerMarked (X := CMfd.of (n := n) U) Q e'))
    (F : List (Set (productOpen U))) :
    RestrictEquiv (powerMarked (selectorMarked f P (F.map (graphShift f g ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g)
        (powerMarked (selectorMarked g Q F) e')) := by
  rw [pullback_power_selectorMarked hf hg Q hQ.isWellFormed.isCoherent F e']
  let F' := F.map (graphShift f g ⁻¹' ·)
  have hLeft := powered_graph_restriction hf P hP F' e
  have hRight := powered_graph_restriction hf Q hQ F' e'
  have hN : selectorCarrier f P.N = selectorCarrier f Q.N := congrArg (selectorCarrier f) hPow.N_eq
  have hE : F' ++ P.E.map (projection U ⁻¹' ·) = F' ++ Q.E.map (projection U ⁻¹' ·) :=
    congrArg (fun E => F' ++ E.map (projection U ⁻¹' ·)) hPow.E_eq
  refine ⟨hN, hE, hPow.d_eq, ?_, ?_⟩
  · have hLe := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (projection_contMDiff U) (fun _ (hx : _ ∈ selectorCarrier f P.N) => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_idealPow hQ.isWellFormed.isCoherent e') hg) hPow.le
    have hEnd := hRight.ge
    change RestrictedIdealWeight.RestrictLe (selectorCarrier f Q.N) _ _ at hEnd
    rw [← hN] at hEnd
    exact RestrictLe.trans hLeft.le (RestrictLe.trans hLe hEnd)
  · have hGe := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
      (projection_contMDiff U) (fun _ (hx : _ ∈ selectorCarrier f P.N) => hx.1)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
        (isCoherent_idealPow hP.isWellFormed.isCoherent e) hg) hPow.ge
    have hStart := hRight.le
    change RestrictedIdealWeight.RestrictLe (selectorCarrier f Q.N) _ _ at hStart
    rw [← hN] at hStart
    exact RestrictLe.trans hStart (RestrictLe.trans hGe hLeft.ge)


/-- The actual powered graph records have the same local test class after the
triangular change of charts, including every transported ambient boundary slot. -/
theorem locWPEquiv_pullback_commonPower_selectorMarked {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    {k l : ℕ} (P Q : MarkedIdeal n U) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (e e' : ℕ)
    (hPow : RestrictEquiv (powerMarked (X := CMfd.of (n := n) U) P e)
      (powerMarked (X := CMfd.of (n := n) U) Q e'))
    (F : List (Set (productOpen U))) :
    LocWPEquiv (X := ambient U)
      (powerMarked (selectorMarked f P (F.map (graphShift f g ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g)
        (powerMarked (selectorMarked g Q F) e')) := by
  have hRE := restrictEquiv_pullback_commonPower_selectorMarked hf hg P Q hP hQ e e' hPow F
  have hz : selectorCarrier (0 : U → ComplexModel 1) P.N = liftedCarrier P.N := rfl
  have hN : IsClosedSubmanifold (n + 1) (selectorCarrier f P.N) := by
    rw [← graphShift_preimage_selectorCarrier f 0, hz]
    have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
        (0 : U → ComplexModel 1) := contMDiff_const
    exact MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
      (graphShift_contMDiff hf hZero) (graphShift_contMDiff hZero hf)
      (graphShift_inverse 0 f) (graphShift_inverse f 0)
      (liftedCarrier_closed_submanifold hP.isWellFormed.isClosedSubmanifold_N)
  have hIP := isCoherent_idealPow (selectorMarked_coherent hf hP.isWellFormed.isCoherent
    (F.map (graphShift f g ⁻¹' ·))) e
  have hIQ := isCoherent_pullback (graphShift_contMDiff hf hg)
    (isCoherent_idealPow (selectorMarked_coherent hg hQ.isWellFormed.isCoherent F) e')
  exact locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hRE hN hIP hIQ


end

end Hironaka.HironakaG1NormalSelectorGraph

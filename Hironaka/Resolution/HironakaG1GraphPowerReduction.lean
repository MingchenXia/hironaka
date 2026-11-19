import Hironaka.Resolution.HironakaG1NormalGraphFlags
import Hironaka.Resolution.HironakaG1CarrierPowerReduction
import Hironaka.Resolution.HironakaG8LocalTransport
import Hironaka.Blowup.BlowupExistenceCodimOne

/-! Source-ideal reductions on actual finite normal graph records. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1GraphPowerReduction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan IdealWeightPowers GermIdealPullbackCalculus
  ResolutionInvariantSpec MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  RestrictedIdealWeight RestrictLeCalculus HironakaActualPowerBoundaryExponents
  HironakaG1NormalGraphFlags HironakaG8LocalHistory HironakaG1CarrierPowerReduction
  NormalCrossings MarkedIdealBiholomorphism InvDomainTowerAlong
  HironakaG8LocalTransport

private theorem block_trace {n t : ℕ} {U : Opens (ComplexModel n)}
    {f : U → ComplexModel t} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    {P : MarkedIdeal n U} {k : ℕ} (hP : IsInvDomain k P) (F : List (Set (blockOpen U t)))
    (hCoherent : (blockMarked f P F).ideal.IsCoherent) :
    RestrictEquiv (blockMarked f P F)
      { blockMarked f P F with ideal := GermIdeal.pullback (m := n + t) blockProjection P.ideal } := by
  have h0 := FactorizationFromResolution.idealPow_one_of_isCoherent hP.isWellFormed.isCoherent
  simpa only [powerMarked, h0, Nat.mul_one,
    FactorizationFromResolution.idealPow_one_of_isCoherent hCoherent] using
    restrictEquiv_blockPower_trace hf P hP.isWellFormed.isCoherent hP.one_le_d F 1

/-- A source reduction transports to the actual normal graph and all its
ordered extra boundary slots. This uses the real graph invariant domains
and the carrier-relative reduction, which may hold for distinct ideals. -/
theorem locWPEquiv_blockMarked_of_source_power_reduction {n t e r : ℕ}
    {U : Opens (ComplexModel n)} {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (P Q : MarkedIdeal n U) {k l k' l' : ℕ} (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (F : List (Set (blockOpen U t)))
    (hPG : IsInvDomain k' (blockMarked f P F)) (hQG : IsInvDomain l' (blockMarked f Q F))
    (hN : P.N = Q.N) (hE : P.E = Q.E) (he : 1 ≤ e) (hMark : P.d = e * Q.d)
    (hIncl : RestrictLe P.N P.ideal (idealPow Q.ideal e))
    (hProd : RestrictLe P.N (idealPow Q.ideal (e + r)) (P.ideal.mul (idealPow Q.ideal r))) :
    LocWPEquiv (X := CMfd.of (n := n + t) (blockOpen U t))
      (blockMarked f P F) (blockMarked f Q F) := by
  let A := blockMarked f P F
  let B := blockMarked f Q F
  let π : blockOpen U t → U := blockProjection
  let I := GermIdeal.pullback (m := n + t) π Q.ideal
  let J := GermIdeal.pullback (m := n + t) π P.ideal
  have hAN : A.N = B.N := congrArg (blockGraph f) hN
  have hBE : B.E = A.E := congrArg (fun E : List (Set U) =>
    F ++ E.map (fun D => π ⁻¹' D)) hE.symm
  have hA : RestrictEquiv A {A with ideal := J} := block_trace hf hP F hPG.isWellFormed.isCoherent
  have hB : RestrictEquiv B {B with ideal := I} := block_trace hf hQ F hQG.isWellFormed.isCoherent
  have hB₁ : RestrictLe A.N B.ideal I := hAN.symm ▸ hB.le
  have hB₂ : RestrictLe A.N I B.ideal := hAN.symm ▸ hB.ge
  have hSource : ∀ z ∈ A.N, π z ∈ P.N := fun _ hz => hz.1
  have hπ := blockProjection_contMDiff U t
  have hHol {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel m) X]
      [IsComplexManifold m X] {L : GermIdeal m X} (hc : L.IsCoherent) :
      ∀ x g, L.mem x g → HolomorphicAt m g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg
  have hQcoh := hQ.isWellFormed.isCoherent
  have hIncl' := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe
    hπ hSource (hHol (isCoherent_idealPow hQcoh e)) hIncl
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hπ hQcoh] at hIncl'
  have hProd' := HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hπ hSource
    (hHol (isCoherent_mul hP.isWellFormed.isCoherent
      (isCoherent_idealPow hQcoh r))) hProd
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hπ hP.isWellFormed.isCoherent
      (isCoherent_idealPow hQcoh r), HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hπ hQcoh,
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hπ hQcoh] at hProd'
  have hLeft : RestrictLe A.N A.ideal (idealPow B.ideal e) :=
    RestrictLe.trans hA.le (RestrictLe.trans hIncl'
      (restrictLe_idealPow (hHol hQG.isWellFormed.isCoherent) hB₂ e))
  have hRight : RestrictLe A.N (idealPow B.ideal (e + r)) (A.ideal.mul (idealPow B.ideal r)) :=
    RestrictLe.trans (restrictLe_idealPow (hHol (isCoherent_pullback hπ hQcoh)) hB₁ (e + r))
      (RestrictLe.trans hProd' (restrictLe_mul (hHol hPG.isWellFormed.isCoherent)
        (hHol (isCoherent_idealPow hQG.isWellFormed.isCoherent r))
        hA.ge (restrictLe_idealPow (hHol hQG.isWellFormed.isCoherent) hB₂ r)))
  exact locWPEquiv_of_restricted_power_reduction he hPG hQG hAN hBE hMark hLeft hRight

/-- A carrier-relative source reduction gives the weak test comparison
after an actual change of base charts and independent graph selectors.
The graph domains follow from the source domains and the geometry of
the common ordered boundary. -/
theorem locWPEquiv_pullback_blockMarked_of_source_power_reduction {n t e r k l : ℕ}
    {U V : Opens (ComplexModel n)}
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (he : 1 ≤ e)
    (F : List (Set (blockOpen V t))) :
    let X := CMfd.of (n := n+t) (blockOpen U t)
    let Y := CMfd.of (n := n+t) (blockOpen V t)
    let Q' := MarkedIdeal.pullback (M := CMfd.of (n := n) V) (M' := CMfd.of (n := n) U) b Q
    let G := blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·))
    P.N = Q'.N → P.E = Q'.E → P.d = e * Q'.d →
    IsSNCDivisor (n+t) G.E → IsTransverse (n+t) G.N G.E →
    RestrictLe P.N P.ideal (idealPow Q'.ideal e) →
    RestrictLe P.N (idealPow Q'.ideal (e+r)) (P.ideal.mul (idealPow Q'.ideal r)) →
    LocWPEquiv (X := X) G (MarkedIdeal.pullback (M := Y) (M' := X)
      (blockChartMap b f g) (blockMarked g Q F)) := by
  intro X Y Q' G hN hE hMark hSNC hTr hIncl hProd
  rw [pullback_blockMarked b.contMDiff hf hg Q hQ.isWellFormed.isCoherent F]
  let F' := F.map (blockChartMap b f g ⁻¹' ·)
  have hQ' : IsInvDomain l Q' := isInvDomain_pullback b hQ
  have hE' : (blockMarked f Q' F').E = G.E := by
    change F' ++ Q'.E.map (fun D => blockProjection ⁻¹' D) =
      F' ++ P.E.map (fun D => blockProjection ⁻¹' D)
    rw [hE]
  have hN' : (blockMarked f Q' F').N = G.N := congrArg (blockGraph f) hN.symm
  have hQG : IsInvDomain l (blockMarked f Q' F') :=
    blockMarked_isInvDomain hf Q' hQ' F' (hE'.symm ▸ hSNC) (by
      change IsTransverse (n+t) (blockMarked f Q' F').N (blockMarked f Q' F').E
      rw [hN', hE']
      exact hTr)
  exact locWPEquiv_blockMarked_of_source_power_reduction (e := e) (r := r)
    hf P Q' hP hQ' F' (blockMarked_isInvDomain hf P hP F' hSNC hTr) hQG
    hN hE he hMark hIncl hProd

/-- Two independently reduced source records give the same weak test
class on their actual normal graphs. The reference uses one source
chart, while the original graph selectors and compression marks may
differ. -/
theorem locWPEquiv_pullback_blockMarked_of_common_reduction
    {n t e r e' r' k l j : ℕ} {U V : Opens (ComplexModel n)}
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (P : MarkedIdeal n U) (Q R : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (hR : IsInvDomain j R)
    (he : 1 ≤ e) (he' : 1 ≤ e') (F : List (Set (blockOpen V t))) :
    let X := CMfd.of (n := n+t) (blockOpen U t)
    let Y := CMfd.of (n := n+t) (blockOpen V t)
    let R' := MarkedIdeal.pullback (M := CMfd.of (n := n) V) (M' := CMfd.of (n := n) U) b R
    let G := blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·))
    let H := blockMarked g Q F
    P.N = R'.N → P.E = R'.E → P.d = e * R'.d →
    Q.N = R.N → Q.E = R.E → Q.d = e' * R.d →
    IsSNCDivisor (n+t) H.E → IsTransverse (n+t) H.N H.E →
    RestrictLe P.N P.ideal (idealPow R'.ideal e) →
    RestrictLe P.N (idealPow R'.ideal (e+r)) (P.ideal.mul (idealPow R'.ideal r)) →
    RestrictLe Q.N Q.ideal (idealPow R.ideal e') →
    RestrictLe Q.N (idealPow R.ideal (e'+r')) (Q.ideal.mul (idealPow R.ideal r')) →
    LocWPEquiv (X := X) G (MarkedIdeal.pullback (M := Y) (M' := X)
      (blockChartMap b f g) H) := by
  intro X Y R' G H hPN hPE hPM hQN hQE hQM hSNC hTr hPI hPP hQI hQP
  let B := blockMarked g R F
  have hBE : B.E = H.E := congrArg (fun E : List (Set V) =>
    F ++ E.map (fun D => (blockProjection : blockOpen V t → V) ⁻¹' D)) hQE.symm
  have hBN : B.N = H.N := congrArg (blockGraph g) hQN.symm
  have hBD : IsInvDomain j B := blockMarked_isInvDomain hg R hR F (hBE.symm ▸ hSNC) (by
    change IsTransverse (n+t) B.N B.E
    rw [hBN, hBE]
    exact hTr)
  have hHD : IsInvDomain l H := blockMarked_isInvDomain hg Q hQ F hSNC hTr
  have hRight := locWPEquiv_blockMarked_of_source_power_reduction (e := e') (r := r')
    hg Q R hQ hR F hHD hBD
    hQN hQE he' hQM hQI hQP
  let c := blockChartEquiv b hf hg
  have hRight' := HironakaG8LocalTransport.LocEquiv.pullback_diffeo (κ := Kinds.wp)
    (X := Y) (X' := X) rfl c hHD.isWellFormed.isCoherent hBD.isWellFormed.isCoherent hRight
  have hPull := (isInvDomain_pullback c hBD).isWellFormed
  change (MarkedIdeal.pullback (M := Y) (M' := X) (blockChartMap b f g) B).IsWellFormed at hPull
  rw [show B = blockMarked g R F from rfl,
    pullback_blockMarked b.contMDiff hf hg R hR.isWellFormed.isCoherent F] at hPull
  have hGN : G.N = (blockMarked f R' (F.map (blockChartMap b f g ⁻¹' ·))).N :=
    congrArg (blockGraph f) hPN
  have hGE : G.E = (blockMarked f R' (F.map (blockChartMap b f g ⁻¹' ·))).E := by
    change F.map _ ++ P.E.map _ = F.map _ ++ R'.E.map _
    rw [hPE]
  have hLeft := locWPEquiv_pullback_blockMarked_of_source_power_reduction (e := e) (r := r)
    b hf hg P R hP hR he F hPN hPE hPM (hGE.symm ▸ hPull.isSNCDivisor)
    (by rw [hGN, hGE]; exact hPull.isTransverse) hPI hPP
  exact hLeft.trans hRight'.symm

open HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression

/-- An actual uniform-weight native family has the same finite graph
test class as the graph of its original uncompressed analytic source. -/
theorem locWPEquiv_blockMarked_of_uniformNative
    {n t k l k' l' j : ℕ} {U : Opens (ComplexModel n)}
    {V : Finset (Fin n →₀ ℕ)} [Nonempty V]
    (S : ActualFixedInheritedSelector V) (a : Fin j ≃ V) (words : Fin j → CoordinateWord n)
    (w : ℕ) (hw : 0 < w) (hUniform : ∀ v : V, normalExponentDegree v.val = w)
    (W : Set U) (P : MarkedIdeal n U) (hP : IsInvDomain k P)
    (hd : P.d = weightedCommonMark (fun _ : V => w))
    (hAt : ∀ x ∈ P.N, ActualHistoricalNativePointPresentation (X := CMfd.of (n := n) U) S a words W P x)
    {f : U → ComplexModel t} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (F : List (Set (blockOpen U t))) :
    let Q : MarkedIdeal n U := ⟨P.N, P.E, vanishingIdeal (n := n) W, w⟩
    IsInvDomain l Q → IsInvDomain k' (blockMarked f P F) →
      IsInvDomain l' (blockMarked f Q F) →
      LocWPEquiv (X := CMfd.of (n := n + t) (blockOpen U t)) (blockMarked f P F) (blockMarked f Q F) := by
  intro Q hQ hPG hQG
  obtain ⟨e, r, he, hMark, hIncl, hProd⟩ := restricted_powerReduction_of_uniformNative
    (X := CMfd.of (n := n) U) S a words w hw hUniform W P hP hd hQ hAt
  exact locWPEquiv_blockMarked_of_source_power_reduction (e := e) (r := r)
    hf P Q hP hQ F hPG hQG rfl rfl he hMark hIncl hProd

/-- Independent uniform-weight native point presentations compare on
their actual finite normal graphs over biholomorphic source charts.
The source analytic set, carrier and ordered boundary are pulled back
along the chart map, and the literal common marks may differ. -/
theorem locWPEquiv_independent_uniformNative_blockGraphs
    {n t k l d a a' : ℕ} {U V : Opens (ComplexModel n)}
    {S T : Finset (Fin n →₀ ℕ)} [Nonempty S] [Nonempty T]
    (s : ActualFixedInheritedSelector S) (i : Fin a ≃ S) (v : Fin a → CoordinateWord n)
    (s' : ActualFixedInheritedSelector T) (i' : Fin a' ≃ T) (v' : Fin a' → CoordinateWord n)
    (w : ℕ) (hw : 0 < w) (hS : ∀ x : S, normalExponentDegree x.val = w)
    (hT : ∀ x : T, normalExponentDegree x.val = w)
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (W : Set V) (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = b ⁻¹' Q.N) (hE : P.E = Q.E.map (fun H => b ⁻¹' H))
    (hPd : P.d = weightedCommonMark (fun _ : S => w))
    (hQd : Q.d = weightedCommonMark (fun _ : T => w))
    (hBase : IsInvDomain d (⟨Q.N, Q.E, vanishingIdeal (n := n) W, w⟩ : MarkedIdeal n V))
    (hAt : ∀ x ∈ P.N, ActualHistoricalNativePointPresentation s i v (b ⁻¹' W) P x)
    (hAt' : ∀ x ∈ Q.N, ActualHistoricalNativePointPresentation s' i' v' W Q x)
    (F : List (Set (blockOpen V t)))
    (hSNC : IsSNCDivisor (n+t) (blockMarked g Q F).E)
    (hTr : IsTransverse (n+t) (blockMarked g Q F).N (blockMarked g Q F).E) :
    LocWPEquiv (X := CMfd.of (n := n+t) (blockOpen U t))
      (blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·)))
      (MarkedIdeal.pullback (M := CMfd.of (n := n+t) (blockOpen V t))
        (M' := CMfd.of (n := n+t) (blockOpen U t)) (blockChartMap b f g) (blockMarked g Q F)) := by
  let R : MarkedIdeal n V := ⟨Q.N, Q.E, vanishingIdeal (n := n) W, w⟩
  let R' := MarkedIdeal.pullback (M := CMfd.of (n := n) V) (M' := CMfd.of (n := n) U) b R
  let A : MarkedIdeal n U := ⟨P.N, P.E, vanishingIdeal (n := n) (b ⁻¹' W), w⟩
  have hIW : GermIdeal.pullback (m := n) (id : U → U) (vanishingIdeal (n := n) (b ⁻¹' W)) =
      vanishingIdeal (n := n) (b ⁻¹' W) := by
    ext x g
    exact BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff
  have hI : R'.ideal = A.ideal := by
    have hMap := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      b.contMDiff b.symm.contMDiff b.apply_symm_apply b.symm_apply_apply
      (g := (id : U → U)) contMDiff_id W
    change GermIdeal.pullback (m := n) (id : U → U) (vanishingIdeal (n := n) (b ⁻¹' W)) =
      R'.ideal at hMap
    rw [hIW] at hMap
    exact hMap.symm
  have hAeq : R' = A :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN.symm hE.symm hI rfl
  have hAD : IsInvDomain d A := hAeq ▸ isInvDomain_pullback b hBase
  obtain ⟨e, r, he, hPm, hPI, hPP⟩ :=
    restricted_powerReduction_of_uniformNative (X := CMfd.of (n := n) U)
      s i v w hw hS (b ⁻¹' W) P hP hPd hAD hAt
  obtain ⟨e', r', he', hQm, hQI, hQP⟩ :=
    restricted_powerReduction_of_uniformNative (X := CMfd.of (n := n) V)
      s' i' v' w hw hT W Q hQ hQd hBase hAt'
  have hRI : R'.ideal = vanishingIdeal (n := n) (b ⁻¹' W) := hI
  rw [← hRI] at hPI hPP
  exact locWPEquiv_pullback_blockMarked_of_common_reduction (e := e) (r := r)
    (e' := e') (r' := r') b hf hg P Q R hP hQ hBase he he' F
    hN hE hPm rfl rfl hQm hSNC hTr hPI hPP hQI hQP

end Hironaka.HironakaG1GraphPowerReduction

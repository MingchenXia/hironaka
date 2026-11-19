import Hironaka.Resolution.HironakaG1RatioGraphFiniteTower
import Hironaka.Resolution.HironakaG8LocalTransport

/-! The full and supported finite graph records have the same local weak test class. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphFiniteTestClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CoefficientIdealRestriction HironakaG8LocalHistory HironakaG8LocalTransport
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1FiniteSourceWeakClassGraphLift HironakaG1SourceWeakClassGraphLift HironakaG1IteratedProperNormalNativeState
  HironakaG1IteratedNormalBlockIdeal HironakaG1NormalGraphFlags HironakaG1RatioGraphFiniteTower
  HironakaG1RatioSectionBlowup HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCoefficientIdeals

variable {n : ℕ} {U : Opens (ComplexModel n)}

private def supportedIteratedMarked (Q : MarkedIdeal n U) (t : ℕ) :
    MarkedIdeal (n+t) (iteratedNormalOpen U t) :=
  withN (iteratedNormalMarked Q t) (iteratedNormalCarrier Q.N t)

private theorem iteratedSupportedClass (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) (t : ℕ) :
    let X := CMfd.of (n := n+t) (iteratedNormalOpen U t)
    IsInvDomain (n+t) (iteratedNormalMarked Q t) ∧
      IsInvDomain n (supportedIteratedMarked Q t) ∧
      LocWPEquiv (X := X) (iteratedNormalMarked Q t) (supportedIteratedMarked Q t) := by
  induction t with
  | zero =>
    have h : supportedIteratedMarked Q 0 = Q := by
      cases Q
      rfl
    change IsInvDomain n Q ∧ IsInvDomain n (supportedIteratedMarked Q 0) ∧ _
    rw [h]
    exact ⟨hQ,hQ,LocEquiv.refl _ _⟩
  | succ t ih =>
    obtain ⟨hP,hS,hL⟩ := ih
    obtain ⟨_,hNext,hClass⟩ := supported_normal_data (supportedIteratedMarked Q t) hS
    have hPad := locWPEquiv_properNormalMarked_of_source _ _ hP hS hL []
    simp only [List.nil_append] at hPad
    change IsInvDomain (n+t+1) (iteratedNormalMarked Q (t+1)) ∧
      IsInvDomain n (supportedNormalMarked (supportedIteratedMarked Q t)) ∧
      LocWPEquiv (X := CMfd.of (n := n+t+1) (iteratedNormalOpen U (t+1)))
        (properNormalMarked (iteratedNormalMarked Q t))
        (supportedNormalMarked (supportedIteratedMarked Q t))
    exact ⟨properNormalMarked_isInvDomain _ hP,hNext,hPad.trans hClass⟩

private theorem supportedIterated_pullback {t : ℕ} (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) :
    MarkedIdeal.pullback (iteratedNormalBlockEquiv U t) (supportedIteratedMarked Q t) =
      blockMarked (0 : U → ComplexModel t) Q [] := by
  have h := iteratedNormalMarked_pullback_blockEquiv Q hQ.isWellFormed.isCoherent t
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact iteratedNormalCarrier_preimage_blockEquiv Q.N
  · change (MarkedIdeal.pullback (iteratedNormalBlockEquiv U t) (iteratedNormalMarked Q t)).E =
      (blockAmbientMarked (0 : U → ComplexModel t) Q).E
    exact congrArg MarkedIdeal.E h
  · change (MarkedIdeal.pullback (iteratedNormalBlockEquiv U t) (iteratedNormalMarked Q t)).ideal =
      (blockAmbientMarked (0 : U → ComplexModel t) Q).ideal
    exact congrArg MarkedIdeal.ideal h
  · change (MarkedIdeal.pullback (iteratedNormalBlockEquiv U t) (iteratedNormalMarked Q t)).d =
      (blockAmbientMarked (0 : U → ComplexModel t) Q).d
    exact congrArg MarkedIdeal.d h

/-- Arbitrary finite nonlinear graph padding and its carrier reset have
identical local weak test classes. The finite induction uses the genuine
single-normal controlled test equivalence at each adjoining coordinate. -/
theorem blockAmbientMarked_locWPEquiv_blockMarked {t : ℕ} {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) :
    LocWPEquiv (X := CMfd.of (n := n+t) (blockOpen U t))
      (blockAmbientMarked f Q) (blockMarked f Q []) := by
  obtain ⟨hP,hS,hL⟩ := iteratedSupportedClass Q hQ t
  let e := iteratedNormalBlockEquiv U t
  let z : U → ComplexModel t := 0
  have hz : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ z := contMDiff_const
  have hP0 := iteratedNormalMarked_pullback_blockEquiv Q hQ.isWellFormed.isCoherent t
  have hS0 := supportedIterated_pullback (t := t) Q hQ
  let A := CMfd.of (n := n+t) (blockOpen U t)
  have hL0 := LocEquiv.pullback_diffeo (X' := A) rfl e hP.isWellFormed.isCoherent hS.isWellFormed.isCoherent hL
  rw [hP0,hS0] at hL0
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥U) ∞) hf hz
  have hCo := blockMarked_coherent hz hQ.isWellFormed.isCoherent []
  have hAo : (blockAmbientMarked z Q).ideal.IsCoherent := hCo
  have hLb := LocEquiv.pullback_diffeo (X := A) (X' := A) rfl b
    (M := blockAmbientMarked z Q) (M' := blockMarked z Q []) hAo hCo hL0
  have hLeft := blockAmbientMarked_pullback_shift f hf Q hQ.isWellFormed.isCoherent
  have hRight := pullback_blockMarked (b := (id : U → U)) contMDiff_id hf hz Q hQ.isWellFormed.isCoherent []
  have hId : MarkedIdeal.pullback (M := CMfd.of (n := n) U) (M' := CMfd.of (n := n) U)
      (id : U → U) Q = Q := ContactCanonicalAlong.pullback_id Q hQ.isWellFormed.isCoherent
  rw [hId,List.map_nil] at hRight
  change MarkedIdeal.pullback b (blockMarked z Q []) = blockMarked f Q [] at hRight
  rwa [hLeft,hRight] at hLb


/-- The weak class equality restricts to the actual ratio-window chart,
with its literal pullbacks of the two records. -/
theorem ratioGraph_sameTestClass {t : ℕ} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    LocWPEquiv P (withN P (P.N ∩ sectionSupport e f)) := by
  intro P
  let A := CMfd.of (n := n+t) (blockOpen U t)
  let B := CMfd.of (n := n+t) O
  have hbEq : e = (Subtype.val : O → blockOpen U t) ∘ b := funext hb
  have hL := blockAmbientMarked_locWPEquiv_blockMarked hf Q hQ
  have hLo := hL.restrict O
  have hCo : (blockMarked f Q []).ideal.IsCoherent := blockMarked_coherent hf hQ.isWellFormed.isCoherent []
  have hAo : (blockAmbientMarked f Q).ideal.IsCoherent := hCo
  have hPull := GermIdealPullbackCalculus.isCoherent_pullback
    (m := n+t) (n := n+t) (contMDiff_subtype_val (U := O)) hCo
  have hPullA := GermIdealPullbackCalculus.isCoherent_pullback
    (m := n+t) (n := n+t) (contMDiff_subtype_val (U := O)) hAo
  have hLX := LocEquiv.pullback_diffeo rfl b hPullA hPull hLo
  have hP : P = markedPullback (m := n+t) b
      (markedPullback (m := n+t) (Subtype.val : O → blockOpen U t) (blockAmbientMarked f Q)) := by
    change markedPullback (m := n+t) e (blockAmbientMarked f Q) = _
    rw [hbEq]
    exact whole_markedPullback_comp (X := A) (Y := B) (Z := X)
      contMDiff_subtype_val b.contMDiff _ hAo
  have hS := whole_markedPullback_comp (X := A) (Y := B) (Z := X)
    contMDiff_subtype_val b.contMDiff (blockMarked f Q []) hCo
  rw [withN_blockAmbientMarked_eq (e := e) (f := f) Q, hP, hbEq, hS]
  exact hLX

/-- On every actual tower, including at every prefix, the admissible tests
of the whole cylinder and the carrier-reset record are identical. -/
theorem ratioGraph_isGeoTestTower_iff {t : ℕ} {X Y : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) (T : BlowupTower X Y) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    P.IsGeoTestTower T ↔ (withN P (P.N ∩ sectionSupport e f)).IsGeoTestTower T :=
  ((ratioGraph_sameTestClass b hb hf Q hQ).wEquiv.2 T).1


open HironakaActualNativeSectionFiniteHistory HironakaG1RatioGraphNativeSource
  HironakaG11PresLineState MarkedIdealOperationsAlong.MarkedIdeal HironakaBaseChange

set_option maxHeartbeats 1100000 in
/-- The whole cylinder's actual finite test tower suffices to descend the
entire strict graph. Its endpoint cosupport is the inverse image along
the strict embedding. Controlled record equality uses the supported
transform, and the whole transform agrees on that strict carrier. -/
theorem exists_ratioGraph_finite_tower_of_cylinder {t : ℕ} {X Y : CMfd.{0} (n+t)}
    (hpos : 0 < n+t) {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    {D : Set U} {H : ℕ → ℕ} (hState : NativeHSState (X := CMfd.of (n := n) U) Q D H)
    (T : BlowupTower X Y) :
    let he : IsOpenHoloEmbedding (n+t) e := ⟨O,b,hb⟩
    let W := sectionSupport e f
    let hW := sectionSupport_regular he hf
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let S := withN P (P.N ∩ W)
    let S₀ := nativePullback (Nat.le_add_right n t) W hW P
    ∀ (_hT : IsGeoTestTower P T),
      ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n+t) V y n)
        (B : BlowupTower (nativeManifold (Nat.le_add_right n t) W hW)
          (nativeManifold (Nat.le_add_right n t) V hV)),
        Lift (Nat.le_add_right n t) W (sectionSupport_closed he hf) hW P.E T V hVc hV B ∧
        B.length = T.length ∧ IsGeoTestTower S₀ B ∧
        MarkedIdeal.pullback (sectionBaseEquiv b hb hf) S₀ =
          markedPullback (m := n) (Subtype.val : sectionBaseOpen (O := O) hf → U) Q ∧
        (∀ z : nativeManifold (Nat.le_add_right n t) V hV, T.proj z.val = (B.proj z).val) ∧
        geoTransformAlong S₀ B = nativePullback (Nat.le_add_right n t) V hV (geoTransformAlong S T) ∧
        (geoTransformAlong S₀ B).d = Q.d ∧
        (geoTransformAlong S₀ B).E =
          (geoTransformAlong P T).E.map ((Subtype.val : V → Y) ⁻¹' ·) ∧
        (geoTransformAlong S₀ B).cosupp =
          (Subtype.val : V → Y) ⁻¹' (geoTransformAlong P T).cosupp ∧
        RestrictEquiv (withN (geoTransformAlong P T) (geoTransformAlong S T).N)
          (geoTransformAlong S T) := by
  intro he W hW P S S₀ hT
  have hWeak := (ratioGraph_sameTestClass b hb hf Q hQ).wEquiv
  obtain ⟨hTest,hCut⟩ := hWeak.2 T
  obtain ⟨V,hVc,hV,B,hLift,hLen,_,hNative,hSource,hSquare,hRecord,hMark,hE,hCos,hRestrict⟩ :=
    exists_ratioGraph_supported_finite_tower b hb hf hpos Q hQ hState T (hTest.mp hT)
  refine ⟨V,hVc,hV,B,hLift,hLen,hNative,hSource,hSquare,hRecord,hMark,hE,?_,hRestrict hT⟩
  rw [hCos, hCut hT]

end
end Hironaka.HironakaG1RatioGraphFiniteTestClass

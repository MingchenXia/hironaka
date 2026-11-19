import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.HadamardBridgeAlong

/-! Whole controlled-ideal restriction on the ACTUAL smaller strict carrier.
Blueprint FIRST: hironaka-g1-controlled-carrier-restriction.tex.
Current ambient ideals are not equated. Cancellation is only along the
full actual strict carrier, never an arbitrary family quotient. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1ControlledCarrierRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupStrictSubmanifold
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealOpenBiholomorphism
  RestrictedIdealWeight RestrictedIdealExtension RestrictedIdealQuotient
  RelativePrincipalizationSpan RestrictLeCalculus IdealWeightPowers
  GermIdealPullbackCalculus BlowupExceptionalDivisor
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials
  HironakaActualWeightedNormalAmbientDerivatives CoefficientIdealRestriction
  ResolutionInvariantSpec

private theorem narrow {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] {A N : Set X} {I J : GermIdeal n X}
    (hAN : A ⊆ N) (h : RestrictLe N I J) : RestrictLe A I J := by
  intro x hx f hf
  obtain ⟨K,s,c,hs,hc,he⟩:=h x (hAN hx) f hf
  exact ⟨K,s,c,hs,hc,he.mono (fun _ hy hyA=>hy (hAN hyA))⟩

private theorem whole_restriction_eq {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] {A : Set X} {I J : GermIdeal n X}
    (hA : IsClosed A) (hIJ : RestrictLe A I J) (hJI : RestrictLe A J I) :
    restrictOn n A I=restrictOn n A J := by
  have key : ∀{I J : GermIdeal n X}, RestrictLe A I J →
      ∀x f,(restrictOn n A I).mem x f→(restrictOn n A J).mem x f := by
    intro I J h x f hf
    by_cases hx : x∈A
    · exact ⟨hf.1,IsInSpanOnAt.trans (fun s hs=>h x hx s hs) hf.2⟩
    · exact restrictOn_eq_top_of_disjoint hA.isOpen_compl hx
        (by ext y;simp) hf.1
  exact GermIdeal.ext (funext fun x=>funext fun f=>propext ⟨key hIJ x f,key hJI x f⟩)

private theorem strict_mono {n : ℕ} {X Y : CMfd.{u} n} {π : Y → X}
    {C A N : Set X} (hAN : A⊆N) :
    geoStrictTransform π C A⊆geoStrictTransform π C N :=
  closure_mono (fun _ hx=>⟨hAN hx.1,hx.2⟩)

private theorem factors {n : ℕ} {X Y : CMfd.{u} n}
    (P : MarkedIdeal n X) (hP : P.IsWellFormed) {C : Set X} {π : Y→X}
    (hC : P.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) :
    let L:=idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) P.d
    RestrictLe (P.geoTransform C π).N
      ((P.geoTransform C π).ideal.mul L) (GermIdeal.pullback (m := n) π P.ideal) ∧
    RestrictLe (P.geoTransform C π).N
      (GermIdeal.pullback (m := n) π P.ideal) ((P.geoTransform C π).ideal.mul L) := by
  let L:=idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) P.d
  have hIC:=isCoherent_vanishingIdeal_centre hπ
  have hN':=isClosedSubmanifold_geoTransform_N hP.isClosedSubmanifold_N hC hπ
  have hF:=isCoherent_pullback hπ.contMDiff hP.isCoherent
  have hL:=isInvertibleAlong_geoStrictTransform hπ P.N P.d
  have hSource:=HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport
    hP.isCoherent hP.isClosedSubmanifold_N hC.1 hC.subset_N hC.2.1
  have hMap:=geoStrictTransform_subset_preimage (C := C)
    hπ.contMDiff.continuous hP.isClosedSubmanifold_N.1
  have hDiv : RestrictLe (P.geoTransform C π).N
      (GermIdeal.pullback (m := n) π P.ideal) L := by
    dsimp only [L]
    rw [←BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC]
    exact RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
      (fun _ hy=>hMap hy) (isCoherent_idealPow hIC P.d) hSource
  have hBack:=restrictLe_mul_colon' hF
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
      (𝔩 := L)
  have hForward:=restrictLe_mul_colon hF hL hDiv
  change RestrictLe (P.geoTransform C π).N
      ((P.geoTransform C π).ideal.mul L) (GermIdeal.pullback (m := n) π P.ideal) ∧ _
  change RestrictLe (P.geoTransform C π).N
      (L.mul (P.geoTransform C π).ideal) (GermIdeal.pullback (m := n) π P.ideal) at hBack
  change RestrictLe (P.geoTransform C π).N
      (GermIdeal.pullback (m := n) π P.ideal) (L.mul (P.geoTransform C π).ideal) at hForward
  rw [mul_comm' L (P.geoTransform C π).ideal] at hBack hForward
  exact ⟨hBack,hForward⟩

/-- One real SAME-centre controlled step preserves the WHOLE ideal image
on the actual smaller strict carrier. Current comparison is induction data. -/
theorem geoTransform_restricted_ideals {n : ℕ} {X Y : CMfd.{u} n}
    (P M : MarkedIdeal n X) (hP : P.IsWellFormed) (hM : M.IsWellFormed)
    (hN : M.N⊆P.N) (hd : P.d=M.d)
    (hIJ : RestrictLe M.N P.ideal M.ideal) (hJI : RestrictLe M.N M.ideal P.ideal)
    {C : Set X} {π : Y→X} (hC : P.IsAdmissibleCentre C)
    (hCM : M.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) :
    (M.geoTransform C π).N⊆(P.geoTransform C π).N ∧
      RestrictLe (M.geoTransform C π).N (P.geoTransform C π).ideal (M.geoTransform C π).ideal ∧
      RestrictLe (M.geoTransform C π).N (M.geoTransform C π).ideal (P.geoTransform C π).ideal ∧
      restrictOn n (M.geoTransform C π).N (P.geoTransform C π).ideal=
        restrictOn n (M.geoTransform C π).N (M.geoTransform C π).ideal := by
  let L:=idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) P.d
  have hSub : (M.geoTransform C π).N⊆(P.geoTransform C π).N:=strict_mono hN
  obtain ⟨hPB,hPF⟩:=factors P hP hC hπ
  obtain ⟨hMB,hMF⟩:=factors M hM hCM hπ
  rw [←hd] at hMB hMF
  have hMap:=geoStrictTransform_subset_preimage (C := C)
    hπ.contMDiff.continuous hM.isClosedSubmanifold_N.1
  have hPullIJ:=RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
    (fun _ hy=>hMap hy) hM.isCoherent hIJ
  have hPullJI:=RestrictLeCalculus.restrictLe_pullback hπ.contMDiff
    (fun _ hy=>hMap hy) hP.isCoherent hJI
  have hPI:=HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
    hP.isClosedSubmanifold_N hP.isCoherent hC hπ
  have hMI:=HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
    hM.isClosedSubmanifold_N hM.isCoherent hCM hπ
  have hL : IsInvertibleAlong n (M.geoTransform C π).N L:=
    isInvertibleAlong_geoStrictTransform hπ M.N P.d
  have hNextIJ:=restrictLe_of_restrictLe_mul_mul hPI hMI hL
    (RestrictLeCalculus.RestrictLe.trans
      (RestrictLeCalculus.RestrictLe.trans (narrow hSub hPB) hPullIJ) hMF)
  have hNextJI:=restrictLe_of_restrictLe_mul_mul hMI hPI hL
    (RestrictLeCalculus.RestrictLe.trans
      (RestrictLeCalculus.RestrictLe.trans hMB hPullJI) (narrow hSub hPF))
  exact ⟨hSub,hNextIJ,hNextJI,whole_restriction_eq
    (isClosedSubmanifold_geoTransform_N hM.isClosedSubmanifold_N hCM hπ).1 hNextIJ hNextJI⟩

/-- Finite induction from INITIAL whole restricted ideals and both actual tests.
No future restriction/record comparison is supplied. -/
theorem geoTransformAlong_restricted_ideals {n : ℕ} {X Y : CMfd.{u} n}
    (P M : MarkedIdeal n X) (hP : P.IsWellFormed) (hM : M.IsWellFormed)
    (hN : M.N⊆P.N) (hd : P.d=M.d)
    (hIJ : RestrictLe M.N P.ideal M.ideal) (hJI : RestrictLe M.N M.ideal P.ideal)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) (hMT : IsGeoTestTower M T) :
    (geoTransformAlong M T).N⊆(geoTransformAlong P T).N ∧
      RestrictLe (geoTransformAlong M T).N (geoTransformAlong P T).ideal (geoTransformAlong M T).ideal ∧
      RestrictLe (geoTransformAlong M T).N (geoTransformAlong M T).ideal (geoTransformAlong P T).ideal ∧
      restrictOn n (geoTransformAlong M T).N (geoTransformAlong P T).ideal=
        restrictOn n (geoTransformAlong M T).N (geoTransformAlong M T).ideal := by
  induction T with
  | refl => exact ⟨hN,hIJ,hJI,whole_restriction_eq hM.isClosedSubmanifold_N.1 hIJ hJI⟩
  | step T C π hπ ih =>
      obtain ⟨hSub,hF,hB,_⟩:=ih hT.1 hMT.1
      exact geoTransform_restricted_ideals (geoTransformAlong P T) (geoTransformAlong M T)
        (isWellFormed_geoTransformAlong hP T hT.1) (isWellFormed_geoTransformAlong hM T hMT.1)
        hSub (by simpa only [d_geoTransformAlong] using hd) hF hB hT.2 hMT.2 hπ

/-- Actual upper TESTs internally yield whole controlled restriction equality
on the literal supported current carrier, with arbitrary proper Q/full E. -/
theorem properNormal_supported_restricted_ideals {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    (geoTransformAlong (supportedNormalMarked Q) T).N⊆(geoTransformAlong (properNormalMarked Q) T).N ∧
      RestrictLe (geoTransformAlong (supportedNormalMarked Q) T).N
        (geoTransformAlong (properNormalMarked Q) T).ideal (geoTransformAlong (supportedNormalMarked Q) T).ideal ∧
      RestrictLe (geoTransformAlong (supportedNormalMarked Q) T).N
        (geoTransformAlong (supportedNormalMarked Q) T).ideal (geoTransformAlong (properNormalMarked Q) T).ideal ∧
      restrictOn (n+1) (geoTransformAlong (supportedNormalMarked Q) T).N
        (geoTransformAlong (properNormalMarked Q) T).ideal=
      restrictOn (n+1) (geoTransformAlong (supportedNormalMarked Q) T).N
        (geoTransformAlong (supportedNormalMarked Q) T).ideal := by
  have hP:=properNormalMarked_isInvDomain Q hQ
  obtain ⟨_,hM,hPM⟩:=supported_normal_data Q hQ
  have hMT:=(hPM.wEquiv.2 T).1.mp hT
  have hN : (supportedNormalMarked Q).N⊆(properNormalMarked Q).N:=fun _ hx=>hx.1
  exact geoTransformAlong_restricted_ideals (properNormalMarked Q) (supportedNormalMarked Q)
    hP.isWellFormed hM.isWellFormed hN rfl
    (restrictLe_refl hP.isWellFormed.isCoherent) (restrictLe_refl hP.isWellFormed.isCoherent)
    T hT hMT

/-- Only the carrier is explicitly reset; all actual current marks and every
chronological boundary slot remain literal. No ambient ideal equality. -/
theorem properNormal_supported_restrictEquiv {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    RestrictEquiv (withN (geoTransformAlong (properNormalMarked Q) T)
      (geoTransformAlong (supportedNormalMarked Q) T).N)
      (geoTransformAlong (supportedNormalMarked Q) T) := by
  obtain ⟨_,hIJ,hJI,_⟩:=properNormal_supported_restricted_ideals Q hQ T hT
  refine ⟨rfl,?_,?_,hIJ,hJI⟩
  · exact MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := properNormalMarked Q) (𝔫 := supportedNormalMarked Q) rfl T
  · simp only [withN_d,d_geoTransformAlong]
    rfl

end
end Hironaka.HironakaG1ControlledCarrierRestriction

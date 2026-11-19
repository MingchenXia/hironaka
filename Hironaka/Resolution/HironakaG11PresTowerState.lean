import Hironaka.Resolution.HironakaActualHistoricalNativeGivenTower
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite
import Hironaka.Resolution.HironakaResolutionSpace
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Blowup.BlowupStrictIdeal

/-!
# The Hilbert–Samuel presentation along multiple test blow-ups (goal G11, step (3a))

Step (3a) of the Hilbert–Samuel route to `g11:general` (human decision Option 1, inbox I-1296):
a record presenting the Hilbert–Samuel function `H` keeps presenting it along every multiple test
blow-up (Bierstone–Milman 1997 Thms 9.4, 9.6; Bierstone–Milman 2008 §1: a presentation of `H_{X,·}`
has the same test sequences as `(M, ∅, X, H)`), together with Bennett's properties (1)–(3)
(singular points, semicontinuity, no increase after permissible blowups). The classical content is
already formalized in the library ("native historical" Hilbert–Samuel phase,
`HironakaActualHistoricalNativeGivenTower.actual_native_given_test_tower_state`); this file states it
in the form used by the G11 route (lane G11A's `HSPresentation`, iterated strict transforms
`strictAlong`) and makes it invariant under biholomorphisms of the ambient manifold.

* **`HSTowerState Q W H`**: along every multiple test blow-up `T` of `Q`, the strict transform `W_T`
  (`strictAlong`) is analytic, contains the cosupport of `Q_T`, has Hilbert–Samuel function `≤ H`
  everywhere, the cosupport of `Q_T` is exactly the locus where it equals `H`, and lies in the singular
  set of `W_T`;
* `strictAlong_eq_strictTransform_of_singular`: along a multiple test blow-up whose transformed
  cosupports lie in the singular sets of the strict transforms, `strictAlong T W` is the library's
  strict transform `strictTransform n T.proj W` (thinness of the centres);
* `hsTowerState_of_strictTransform`, **`hsTowerState_of_native`**: the native stage-0 data (cut,
  upper bound, five-law point presentations, reference singular point) give `HSTowerState`;
* **`HSTowerState.pullback`**: invariance under a biholomorphism `Φ : X' ≅ X` of the ambient
  (`IsTowerIso` naturality of transforms, strict transforms, Hilbert–Samuel functions and singular
  sets).

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-tower-state.tex`.
-/

set_option autoImplicit false

open Set Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresTowerState

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal BlowupTowerIsomorphism MarkedIdealTowerTransport MarkedIdealBiholomorphism
  HironakaActualHistoricalNativeGivenTower HironakaActualHistoricalNativeStageStep
  HironakaActualFixedInheritedSelector HironakaActualHistoricalWholeJetFrames
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualWeightedCoefficientCompression
open HomogenizedGlueingTower (strictAlong strictAlong_step)

universe u

variable {n : ℕ}

/-! ### The state -/

/-- **The Hilbert–Samuel presentation along the multiple test blow-ups** of `Q` (closed analytic
`W ⊆ X`, value `H`): along every multiple test blow-up `T` of `Q`, the strict transform `W_T` is
analytic, contains the cosupport of `Q_T`, its Hilbert–Samuel function is `≤ H` at every point,
the cosupport of `Q_T` is the locus where it equals `H`, and lies in the singular set of `W_T`. -/
def HSTowerState {X : CMfd.{u} n} (Q : MarkedIdeal n X) (W : Set X) (H : ℕ → ℕ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
    IsComplexAnalyticSubset (n := n) (strictAlong T W) ∧
    (geoTransformAlong Q T).cosupp ⊆ strictAlong T W ∧
    (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong T W)) z ℓ ≤ H ℓ) ∧
    (∀ z, z ∈ (geoTransformAlong Q T).cosupp ↔
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong T W)) z ℓ = H ℓ) ∧
    (geoTransformAlong Q T).cosupp ⊆ singularSet (n := n) (strictAlong T W)

/-! ### Iterated strict transforms -/

section Strict

variable {X : CMfd.{u} n}

/-- The strict transform along the empty tower. -/
theorem strictTransform_id {W : Set X} (hW : IsClosed W) : strictTransform n (id : X → X) W = W := by
  rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id, hW.closure_eq]

/-- **Iterated strict transforms along thin centres**: along a multiple test blow-up `T` of `Q` such
that at every stage the strict transform `strictTransform n T.proj W` is analytic and contains the
transformed cosupport in its singular set, the iterated geometric strict transform `strictAlong T W`
is the library's strict transform along the projection. -/
theorem strictAlong_eq_strictTransform_of_singular (Q : MarkedIdeal n X) {W : Set X}
    (hW : IsClosed W)
    (hst : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      IsComplexAnalyticSubset (n := n) (strictTransform n T.proj W) ∧
        (geoTransformAlong Q T).cosupp ⊆ singularSet (n := n) (strictTransform n T.proj W)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      strictAlong T W = strictTransform n T.proj W
  | _, .refl, _ => (strictTransform_id hW).symm
  | _, .step T C π hπ, hT => by
      obtain ⟨hTt, hC⟩ := hT
      have ih := strictAlong_eq_strictTransform_of_singular Q hW hst T hTt
      obtain ⟨hA, hSing⟩ := hst T hTt
      have hthin : strictTransform n T.proj W ⊆ closure (strictTransform n T.proj W \ C) :=
        (HironakaResolutionSpace.subset_closure_diff_singularSet hA).trans
          (closure_mono (sdiff_subset_sdiff_right (hC.2.1.trans hSing)))
      rw [strictAlong_step, ih, BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hthin,
        BlowupTower.proj_step,
        StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff W]

/-- **The state from the strict-transform form.** -/
theorem hsTowerState_of_strictTransform (Q : MarkedIdeal n X) {W : Set X} (hW : IsClosed W)
    (H : ℕ → ℕ)
    (hst : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      IsComplexAnalyticSubset (n := n) (strictTransform n T.proj W) ∧
      (∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ ≤ H ℓ) ∧
      (geoTransformAlong Q T).cosupp = {z | ∀ ℓ,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n T.proj W)) z ℓ = H ℓ} ∧
      (geoTransformAlong Q T).cosupp ⊆ singularSet (n := n) (strictTransform n T.proj W)) :
    HSTowerState Q W H := by
  intro Y T hT
  have heq := strictAlong_eq_strictTransform_of_singular Q hW
    (fun T hT => ⟨(hst T hT).1, (hst T hT).2.2.2⟩) T hT
  obtain ⟨hA, hle, hcut, hsing⟩ := hst T hT
  rw [heq]
  refine ⟨hA, hsing.trans (singularSet_subset _), hle, fun z => ?_, hsing⟩
  rw [hcut]
  rfl

end Strict

/-! ### The native presentation -/

section Native

variable {m : ℕ} {X₀ : Type} [TopologicalSpace X₀] [ChartedSpace (ComplexModel m) X₀]
  [IsComplexManifold m X₀]

/-- **The native Hilbert–Samuel presentation along test towers** (Bierstone–Milman 1997 Thms 9.4,
9.6 with Bennett's properties, in the library's native form): a record `Q` on `X` with `N = univ`,
coherent ideal, the common mark of a fixed five-law vertex family, cut = the locus where the
Hilbert–Samuel function of `W` equals that `H` of a singular reference point, `HS(W) ≤ H`
everywhere, and native point presentations at every point of its cosupport, satisfies
`HSTowerState Q W H`. -/
theorem hsTowerState_of_native
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n := m) W₀) (a₀ : X₀)
    (ha₀ : a₀ ∈ singularSet (n := m) W₀)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N = univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    {k : ℕ} (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (hPositive : ∀ v : V, 0 < normalExponentDegree v.val)
    (hOwn : ∀ i, historicalOwner w (wordExponent (w i)) = some i)
    (hQMark : Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (hCut : Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := m) W₀) a₀ ℓ})
    (hUpper : ∀ x ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := m) W₀) a₀ ℓ)
    (hAt : ∀ x ∈ Q.cosupp, ActualHistoricalNativePointPresentation S a w W Q x) :
    HSTowerState Q W (hilbertSamuelAt (vanishingIdeal (n := m) W₀) a₀) := by
  apply hsTowerState_of_strictTransform Q hW.isClosed
  intro Y T hT
  obtain ⟨⟨hA, -, -, -, hle, hcut, -, hsing⟩, -⟩ :=
    actual_native_given_test_tower_state W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPositive hOwn
      hQMark hCut hUpper hAt T hT
  exact ⟨hA, hle, hcut, hsing⟩

end Native

/-! ### Invariance under biholomorphisms of the ambient -/

section Pullback

variable {X X' : CMfd.{u} n}

/-- **The presentation is invariant under a biholomorphism** `Φ : X' ≅ X` of the ambient manifold:
`HSTowerState Q W H` gives `HSTowerState (Φ^*Q) (Φ⁻¹W) H` (for `Q` with closed submanifold `N` and
coherent ideal). Every multiple test blow-up of `Φ^*Q` is isomorphic over `Φ` to one of `Q`
(the transport along `Φ⁻¹`), and transforms, strict transforms, Hilbert–Samuel functions and
singular sets correspond under the last-stage biholomorphism. -/
theorem HSTowerState.pullback (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {Q : MarkedIdeal n X} (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent)
    {W : Set X} {H : ℕ → ℕ} (h : HSTowerState Q W H) :
    HSTowerState (MarkedIdeal.pullback Φ Q) (Φ ⁻¹' W) H := by
  intro Y' T' hT'
  let tr := transport Φ.symm T'
  have hiso : IsTowerIso Φ T' tr.tower tr.back.symm :=
    BlowupTowerSplitIso.IsTowerIso.congr_base (transport_isTowerIso Φ.symm T').symm (fun _ => rfl)
  have hT : IsGeoTestTower Q tr.tower := (IsTowerIso.isGeoTestTower_iff Φ hN hI hiso).mp hT'
  obtain ⟨hA, hsub, hle, hcut, hsing⟩ := h tr.tower hT
  set χ := tr.back.symm with hχ
  have hstrict : strictAlong T' (Φ ⁻¹' W) = χ ⁻¹' strictAlong tr.tower W :=
    IsTowerIso.strictAlong_eq hiso W
  have hcos : (geoTransformAlong (MarkedIdeal.pullback Φ Q) T').cosupp =
      χ ⁻¹' (geoTransformAlong Q tr.tower).cosupp :=
    IsTowerIso.cosupp_geoTransformAlong Φ hN hI hiso hT
  have hHS (z : Y') (ℓ : ℕ) :
      hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong T' (Φ ⁻¹' W))) z ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong tr.tower W)) (χ z) ℓ := by
    rw [hstrict]
    exact HironakaActualVanishingIntrinsicHSTransport.hilbertSamuelAt_vanishing_actual_biholomorphic_any
      χ _ z ℓ
  have hsingEq : singularSet (n := n) (strictAlong T' (Φ ⁻¹' W)) =
      χ ⁻¹' singularSet (n := n) (strictAlong tr.tower W) := by
    rw [hstrict]
    exact HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism χ) _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hstrict]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage χ.contMDiff hA
  · rw [hcos, hstrict]
    exact preimage_mono hsub
  · intro z ℓ
    rw [hHS]
    exact hle (χ z) ℓ
  · intro z
    rw [hcos, mem_preimage, hcut]
    simp only [hHS]
  · rw [hcos, hsingEq]
    exact preimage_mono hsing

end Pullback

end

end Hironaka.HironakaG11PresTowerState

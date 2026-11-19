import Hironaka.Resolution.HironakaG1LiteralRatioFullSupport
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaActualNativeSectionHilbertSamuel

/-! Entire literal Hilbert–Samuel profiles on the common ratio cut. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1LiteralRatioPointProfiles
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceIntrinsicHS
  HironakaActualAnalyticSubspacePresentationIndependence HironakaActualVanishingIntrinsicHSTransport
  HironakaG1NormalGraphFlags HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaG1SNCReaderNormalization HironakaG1RelativeReaderWindow HironakaG1RelativeBoundaryProjections
  HironakaG1ReaderProductSubmersions HironakaG1RatioGraphProductEquations HironakaG1RatioBlockGraphAdapters
  HironakaG1RatioBlockNativeStates HironakaReducedComplexAnalyticSpaces HironakaHolomorphicJetChartInvariance

/-- A genuine open-image chart preserves the entire original reduced
vanishing-ideal profile, even written in two different model indices. -/
theorem hs_of_actual_openImage {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (e : X → Y) (O : Opens Y)
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel m)⟯ O)
    (hb : ∀ x, e x = (b x).val)
    (C : Set Y) (x : X) (hx : e x ∈ C) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (e ⁻¹' C)) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := m) C) (e x) ℓ := by
  let A := e ⁻¹' C
  let B := (Subtype.val : O → Y) ⁻¹' C
  have hAB : ∀ x ∈ A, b x ∈ B := fun x hx => by
    change (b x).val ∈ C
    rwa [← hb]
  have hBA : ∀ y ∈ B, b.symm y ∈ A := by
    intro y hy
    change e (b.symm y) ∈ C
    rwa [hb,b.apply_symm_apply]
  let E := actualSubspaceMutualRestrictionIso b.contMDiff b.symm.contMDiff hAB hBA
    (fun x _ => b.symm_apply_apply x) (fun y _ => b.apply_symm_apply y)
  have h := hilbertSamuelAt_vanishing_intrinsic_iso E
    (actualSubspaceMap_point b.contMDiff hAB) ⟨x,hx⟩ ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n) A) x ℓ =
    hilbertSamuelAt (vanishingIdeal (n := m) B) (b x) ℓ at h
  exact h.trans ((hilbertSamuelAt_vanishing_actual_open_any O C (b x) ℓ).trans
    (congrArg (fun y => hilbertSamuelAt (vanishingIdeal (n := m) C) y ℓ) (hb x).symm))

/-- Holomorphic graph padding leaves every order of the reduced profile
at every actual graph point equal to the original base profile. -/
theorem hs_blockGraph_point {n t : ℕ} {U : Opens (ComplexModel n)}
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (A : Set U) (z : blockOpen U t) (hz : z ∈ blockGraph f A) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n+t) (blockGraph f A)) z ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) A) (blockProjection z) ℓ := by
  have hAB : ∀ z ∈ blockGraph f A, (blockProjection z) ∈ A := fun _ hz => hz.1
  have hBA : ∀ x ∈ A, blockSection f x ∈ blockGraph f A := by
    intro x hx
    refine ⟨by simpa only [blockProjection_blockSection] using hx,?_⟩
    rw [blockProjection_blockSection]
    exact second_join _ _
  have hBack : ∀ z ∈ blockGraph f A, blockSection f (blockProjection z) = z := by
    intro z hz
    apply Subtype.ext
    change join (blockProjection z).val (f (blockProjection z)) = z.val
    rw [← hz.2]
    exact join_projections z.val
  have hp := blockProjection_contMDiff U t
  let E := actualSubspaceMutualRestrictionIso hp (blockSection_contMDiff hf) hAB hBA hBack
    (fun x _ => blockProjection_blockSection f x)
  exact hilbertSamuelAt_vanishing_intrinsic_iso E (actualSubspaceMap_point hp hAB) ⟨z,hz⟩ ℓ


/-- At every paired ratio point, every order of the common cut profile is
the corresponding original profile on both sides. This compares the
entire reduced ideal and places no equality constraint on dimensions
or on the profile values at different points of the cut. -/
theorem actual_ratioCut_point_profiles
    {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {p : M} {q : N}
    {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
    (R : RelativeReaders p q E F τ) (U : Opens M) (V : Opens N)
    {C : Set M} {D : Set N} {G : Set (readerUnitWindow R)}
    (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x)
    (hb : ∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U)
    (hg : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel R.a) ∞ backward V)
    (hL : ∀ z : readerUnitWindow R, z ∈ G ↔ firstReaderMap R z ∈ C ∩ (U : Set M) ∧
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (firstReaderMap R z))
    (hR : ∀ z : readerUnitWindow R, z ∈ G ↔ secondReaderMap R z ∈ D ∩ (V : Set N) ∧
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (secondReaderMap R z)) :
    let d := (R.r+R.a)+(R.r+R.b)
    let K := graphEquationWindowToRatio R U V ⁻¹' G
    ∀ z ∈ K, ∀ ℓ,
      let w := graphEquationWindowToRatio R U V z
      let h := hilbertSamuelAt (vanishingIdeal (n := d) K) z ℓ
      h = hilbertSamuelAt (vanishingIdeal (n := n) C) (firstReaderMap R w) ℓ ∧
      h = hilbertSamuelAt (vanishingIdeal (n := m) D) (secondReaderMap R w) ℓ := by
  intro d K z hz ℓ w h
  let X := CMfd.of (n := d) (Common R U V)
  let NL := CMfd.of (n := R.r+R.a) (LBase R U)
  let NR := CMfd.of (n := R.r+R.b) (RBase R V)
  let BL := CMfd.of (n := d) (blockOpen (LBase R U) (R.r+R.b))
  let BR := CMfd.of (n := (R.r+R.b)+(R.r+R.a)) (blockOpen (RBase R V) (R.r+R.a))
  obtain ⟨hKL,hKR⟩ := blockGraph_preimages R U V a b forward backward hL hR
  obtain ⟨OL,eL,hOL⟩ := leftBlockMap_openImage R U V
  obtain ⟨OR,eR,hOR⟩ := rightBlockMap_openImage R U V
  obtain ⟨UL,cL,hUL⟩ := normalizedBaseMap_openImage R.sourceDiffeomorph U
  obtain ⟨VR,cR,hVR⟩ := normalizedBaseMap_openImage R.targetDiffeomorph V
  have hMemL : z ∈ leftBlockMap R U V ⁻¹'
      blockGraph (leftBlockGraphValue R U a forward) (normalizedBaseMap R.sourceDiffeomorph U ⁻¹' C) :=
    hKL.symm ▸ hz
  have hMemR : z ∈ rightBlockMap R U V ⁻¹'
      blockGraph (rightBlockGraphValue R V b backward) (normalizedBaseMap R.targetDiffeomorph V ⁻¹' D) :=
    hKR.symm ▸ hz
  constructor
  · have h₁ := hs_of_actual_openImage (X := X) (Y := BL) _ OL eL hOL (blockGraph (leftBlockGraphValue R U a forward)
      (normalizedBaseMap R.sourceDiffeomorph U ⁻¹' C)) z hMemL ℓ
    have h₂ := hs_blockGraph_point (leftBlockGraphValue_hol R U a forward ha hf) _ _ hMemL ℓ
    have h₃ := hs_of_actual_openImage (X := NL) (Y := M) _ UL cL hUL C _ hMemL.1 ℓ
    rw [hKL] at h₁
    rw [leftBlockMap_base] at h₃
    exact h₁.trans (h₂.trans h₃)
  · have h₁ := hs_of_actual_openImage (X := X) (Y := BR) _ OR eR hOR (blockGraph (rightBlockGraphValue R V b backward)
      (normalizedBaseMap R.targetDiffeomorph V ⁻¹' D)) z hMemR ℓ
    have h₂ := hs_blockGraph_point (rightBlockGraphValue_hol R V b backward hb hg) _ _ hMemR ℓ
    have h₃ := hs_of_actual_openImage (X := NR) (Y := N) _ VR cR hVR D _ hMemR.1 ℓ
    rw [hKR] at h₁
    rw [rightBlockMap_base] at h₃
    exact h₁.trans (h₂.trans h₃)


open HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionHilbertSamuel

/-- A cut inside a strict native support keeps its original pointwise
profile under exact section restriction. This applies to a common
endpoint cut independently of the dimensions of the two strict supports. -/
theorem native_section_preimage_profile {d k : ℕ} {Y : CMfd.{0} d}
    (hk : k ≤ d) {V K : Set Y} (hV : ∀ y ∈ V, RegularAtDim (n := d) V y k)
    (hKV : K ⊆ V) (y : Y) (hy : y ∈ K) (ℓ : ℕ) :
    let Z := nativeManifold hk V hV
    let A : Set Z := (Subtype.val : V → Y) ⁻¹' K
    hilbertSamuelAt (vanishingIdeal (n := k) A) ⟨y,hKV hy⟩ ℓ =
      hilbertSamuelAt (vanishingIdeal (n := d) K) y ℓ := by
  intro Z A
  have hIm : (Subtype.val : V → Y) '' A = K := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x,hKV hx⟩,hx,rfl⟩
  have h := hilbertSamuelAt_native_image hk hV A ⟨y,hKV hy⟩ hy ℓ
  rw [hIm] at h
  exact h.symm

/-- The two strict sections over the same ambient endpoint cut carry
exactly the same entire point profile at its paired anchors. No native
clock alignment, common full support, or numerical padding is needed. -/
theorem paired_strict_section_profiles {d k₁ k₂ : ℕ} {Y : CMfd.{0} d}
    (hk₁ : k₁ ≤ d) (hk₂ : k₂ ≤ d) {V₁ V₂ K : Set Y}
    (hV₁ : ∀ y ∈ V₁, RegularAtDim (n := d) V₁ y k₁)
    (hV₂ : ∀ y ∈ V₂, RegularAtDim (n := d) V₂ y k₂)
    (hK₁ : K ⊆ V₁) (hK₂ : K ⊆ V₂) (y : Y) (hy : y ∈ K) :
    let Z₁ := nativeManifold hk₁ V₁ hV₁
    let Z₂ := nativeManifold hk₂ V₂ hV₂
    let A₁ : Set Z₁ := (Subtype.val : V₁ → Y) ⁻¹' K
    let A₂ : Set Z₂ := (Subtype.val : V₂ → Y) ⁻¹' K
    (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := k₁) A₁) ⟨y,hK₁ hy⟩ ℓ) =
      (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := k₂) A₂) ⟨y,hK₂ hy⟩ ℓ) := by
  intro Z₁ Z₂ A₁ A₂
  funext ℓ
  exact (native_section_preimage_profile hk₁ hV₁ hK₁ y hy ℓ).trans
    (native_section_preimage_profile hk₂ hV₂ hK₂ y hy ℓ).symm


open MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec NormalCrossings
  HironakaG8LocalHistory HironakaActualNativeSectionOrderHistory RelativePrincipalizationSpan

/-- On a common supported actual test, the two controlled native
cosupports have the same reduced profile at every paired endpoint.
The carrier dimensions, true marks and native invariant clocks may differ. -/
theorem paired_lift_endpoint_profiles {d k₁ k₂ q₁ q₂ : ℕ} {X Y : CMfd.{0} d}
    (hd : 0 < d) (hk₁ : k₁ ≤ d) (hk₂ : k₂ ≤ d)
    {W₁ W₂ : Set X} {hwc₁ : IsClosed W₁} {hwc₂ : IsClosed W₂}
    {hw₁ : ∀ x ∈ W₁, RegularAtDim (n := d) W₁ x k₁}
    {hw₂ : ∀ x ∈ W₂, RegularAtDim (n := d) W₂ x k₂}
    {V₁ V₂ : Set Y} {hvc₁ : IsClosed V₁} {hvc₂ : IsClosed V₂}
    {hv₁ : ∀ y ∈ V₁, RegularAtDim (n := d) V₁ y k₁}
    {hv₂ : ∀ y ∈ V₂, RegularAtDim (n := d) V₂ y k₂}
    {T : BlowupTower X Y}
    {B₁ : BlowupTower (nativeManifold hk₁ W₁ hw₁) (nativeManifold hk₁ V₁ hv₁)}
    {B₂ : BlowupTower (nativeManifold hk₂ W₂ hw₂) (nativeManifold hk₂ V₂ hv₂)}
    (P Q : MarkedIdeal d X) (hPD : IsInvDomain q₁ P) (hQD : IsInvDomain q₂ Q)
    (hP : P.N ⊆ W₁) (hQ : Q.N ⊆ W₂)
    (hTr₁ : IsTransverse d W₁ P.E) (hTr₂ : IsTransverse d W₂ Q.E)
    (L₁ : Lift hk₁ W₁ hwc₁ hw₁ P.E T V₁ hvc₁ hv₁ B₁)
    (L₂ : Lift hk₂ W₂ hwc₂ hw₂ Q.E T V₂ hvc₂ hv₂ B₂)
    (hClass : LocWPEquiv P Q) (hT : P.IsGeoTestTower T) :
    let C₁ := (geoTransformAlong (nativePullback hk₁ W₁ hw₁ P) B₁).cosupp
    let C₂ := (geoTransformAlong (nativePullback hk₂ W₂ hw₂ Q) B₂).cosupp
    ∀ (x : nativeManifold hk₁ V₁ hv₁) (y : nativeManifold hk₂ V₂ hv₂),
      x ∈ C₁ → x.val = y.val →
      y ∈ C₂ ∧ (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := k₁) C₁) x ℓ) =
        (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := k₂) C₂) y ℓ) := by
  intro C₁ C₂ x y hx hxy
  let K := (geoTransformAlong P T).cosupp
  have hE : K = (geoTransformAlong Q T).cosupp := (hClass.wEquiv.2 T).2 hT
  have hC₁ : C₁ = (Subtype.val : V₁ → Y) ⁻¹' K :=
    HironakaActualNativeSectionOrderHistory.Lift.current_cosupport L₁ hd hPD.isWellFormed.isSNCDivisor
      hTr₁ P rfl hP (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hPD.isWellFormed.isCoherent h)
  have hC₂ : C₂ = (Subtype.val : V₂ → Y) ⁻¹' K := by
    rw [hE]
    exact HironakaActualNativeSectionOrderHistory.Lift.current_cosupport L₂ hd hQD.isWellFormed.isSNCDivisor
      hTr₂ Q rfl hQ (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hQD.isWellFormed.isCoherent h)
  have hK₁ : K ⊆ V₁ := fun _ h =>
    HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset L₁ P hP
      ((geoTransformAlong P T).cosupp_subset_N h)
  have hK₂ : K ⊆ V₂ := by
    rw [hE]
    exact fun _ h => HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset L₂ Q hQ
      ((geoTransformAlong Q T).cosupp_subset_N h)
  have hxK : x.val ∈ K := by rw [hC₁] at hx; exact hx
  have hyK : y.val ∈ K := hxy ▸ hxK
  refine ⟨hC₂.symm ▸ hyK,?_⟩
  rw [hC₁,hC₂]
  funext ℓ
  exact (native_section_preimage_profile hk₁ hv₁ hK₁ x.val hxK ℓ).trans
    ((congrArg (fun z => hilbertSamuelAt (vanishingIdeal (n := d) K) z ℓ) hxy).trans
      (native_section_preimage_profile hk₂ hv₂ hK₂ y.val hyK ℓ).symm)

end
end Hironaka.HironakaG1LiteralRatioPointProfiles

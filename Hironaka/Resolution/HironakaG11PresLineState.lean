import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Resolution.HironakaActualHistoricalNativeOpenRestriction
import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal
import Hironaka.Analytic.FiniteGermIdealPullbackGenerators
import Hironaka.Analytic.RegularAtDimTransport

/-!
# The native Hilbert–Samuel state and the local equivalence of native records (goal G11, (3a-lines))

Step (3a) of the Hilbert–Samuel route to `g11:general` (human decisions Option 1 and (B')): lane G11B's class-functorial
invariant (`HironakaG11InvBMClass.BMInvariant LocWPEquiv`) compares two window records on an overlap through G8's local
equivalence `LocWPEquiv` (Bierstone–Milman's `s(i,ii)` with local blowings-up: admissible blowups, products with a line,
restrictions to open subsets; BM97 §1, BM08 Defn 2.5 without exceptional blowups, BPRIME-PLAN D1).  This module isolates
the one ingredient of that comparison which concerns the Hilbert–Samuel records themselves.

* `lineHS H` (`ℓ ↦ ∑_{j ≤ ℓ} H j`): the Hilbert–Samuel function of `X × ℂ` at `(x, t)` when `H` is that of `X` at `x`
  (`HironakaActualProjectionIntrinsicHS.hilbertSamuelAt_actual_projection_convolution` with one normal variable);
* `IsSingularHSValue H`: `H` is the Hilbert–Samuel function of a singular point of an analytic set;
* **`NativeHSState Q W H`**: the stage data of the library's native historical Hilbert–Samuel phase (Hironaka's
  standard-basis presentation with the five point laws, BM97 Thms 9.4, 9.6): carrier `univ`, coherent ideal, the common
  mark of a five-law vertex family, cosupport = `{HS(W) = H}`, `HS(W) ≤ H`, native point presentations on the cosupport;
* its consequences and stability: `NativeHSState.cosupp_eq`, `.hsTowerState`, **`.geoTransform`** (one admissible blowup,
  `HironakaActualHistoricalNativeStageStep.actual_native_all_point_stage_step`), **`.restrict`** (open subsets,
  `HironakaActualHistoricalNativeOpenRestriction.actual_native_point_presentation_open_restriction`);
* **`NativeLineStability`** (named proposition, step "(3a-lines)"): the state is stable under the product with a line —
  `NativeHSState Q W H → NativeHSState (projectionTest Q) (W × ℂ) (lineHS H)` (BM97 Thm 9.4, test (ii): a standard basis
  of `I` at `x` is one of `I·𝒪_{X×ℂ}` at `(x, t)`, with the same vertices, degrees and five laws in `n + 1` variables);
* **`locWPEquiv_of_nativeHSState`**: under `NativeLineStability`, two marked ideals in the native state for the same
  `(W, H)` and the same boundary are `LocWPEquiv` (G8's coinduction principle `LocEquiv.of_isLocStable`).

Nothing here proves or assumes G11.  Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresLineState

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualHistoricalWholeJetFrames HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression HironakaG11PresTowerState
  HironakaActualVanishingIntrinsicHSTransport HironakaSmoothSubmersionGermIdealColon
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open scoped ProductComplexManifold

variable {n : ℕ}

/-! ### The state -/

/-- **The Hilbert–Samuel function after a product with a line**: `(lineHS H) ℓ = ∑_{j ≤ ℓ} H j`. -/
def lineHS (H : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (ℓ + 1), H j

/-- **`H` is the Hilbert–Samuel function of a singular point** of a closed analytic subset of a complex manifold. -/
def IsSingularHSValue (H : ℕ → ℕ) : Prop :=
  ∃ (m : ℕ) (X₀ : CMfd.{0} m) (W₀ : Set X₀) (a₀ : X₀), IsComplexAnalyticSubset (n := m) W₀ ∧
    a₀ ∈ singularSet (n := m) W₀ ∧ hilbertSamuelAt (vanishingIdeal (n := m) W₀) a₀ = H

/-- **The native Hilbert–Samuel state** of a marked ideal `Q` on `X` for the analytic set `W ⊆ X` and the value `H` (the
stage data of the library's native historical Hilbert–Samuel phase, i.e. Hironaka's standard-basis presentation): `H` is a
singular Hilbert–Samuel value, `W` is analytic, `Q` has carrier `univ` and coherent ideal, its mark is the common mark of a
vertex family with the five point laws, its cosupport is the locus `{HS(W) = H}`, `HS(W) ≤ H` everywhere, and `Q` has a
native point presentation (same family) at every point of its cosupport. -/
def NativeHSState {X : CMfd.{0} n} (Q : MarkedIdeal n X) (W : Set X) (H : ℕ → ℕ) : Prop :=
  IsSingularHSValue H ∧ IsComplexAnalyticSubset (n := n) W ∧ Q.N = univ ∧ Q.ideal.IsCoherent ∧
  ∃ (V : Finset (Fin n →₀ ℕ)) (S : ActualFixedInheritedSelector V) (k : ℕ) (a : Fin k ≃ V)
    (w : Fin k → CoordinateWord n),
    (∀ i, wordExponent (w i) = (a i).val) ∧ (∀ v : V, 0 < normalExponentDegree v.val) ∧
    (∀ i, historicalOwner w (wordExponent (w i)) = some i) ∧
    Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val) ∧
    Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ} ∧
    (∀ x ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ ≤ H ℓ) ∧
    ∀ x ∈ Q.cosupp, ActualHistoricalNativePointPresentation S a w W Q x

section State

variable {X : CMfd.{0} n} {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}

/-- The cosupport of a record in the native state is the locus where the Hilbert–Samuel function equals `H`. -/
theorem NativeHSState.cosupp_eq (h : NativeHSState Q W H) :
    Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCut, -⟩ := h
  exact hCut

/-- **The native state presents `H` along all multiple test blow-ups** (`hsTowerState_of_native`). -/
theorem NativeHSState.hsTowerState (h : NativeHSState Q W H) : HSTowerState Q W H := by
  obtain ⟨hH, hW, hQN, hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, hCut, hUpper, hAt⟩ := h
  obtain ⟨m, X₀, W₀, a₀, hW₀, ha₀, rfl⟩ := hH
  intro Y T hT
  exact hsTowerState_of_native W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPos hOwn hMark hCut hUpper hAt T hT

/-- **One admissible blowup** (BM97 Thm 9.4 for one blowup; the library's all-point native stage step): the transform of a
record in the native state along the blowup of a closed submanifold `C` of its cosupport is in the native state for the
strict transform of `W` and the same `H`. -/
theorem NativeHSState.geoTransform (h : NativeHSState Q W H) {C : Set X} (hC : IsClosedSubmanifold n C)
    (hCQ : C ⊆ Q.cosupp) {Z : CMfd.{0} n} {π : Z → X} (hπ : IsBlowupAlong n C π) :
    NativeHSState (Q.geoTransform C π) (strictTransform n π W) H := by
  obtain ⟨hH, hW, hQN, hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, hCut, hUpper, hAt⟩ := h
  obtain ⟨m, X₀, W₀, a₀, hW₀, ha₀, rfl⟩ := hH
  obtain ⟨hA, hN', hI', hMark', hUp', hCut', hAt', -⟩ :=
    actual_native_all_point_stage_step W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPos hOwn hMark hCut hUpper hAt
      hC hCQ hπ
  exact ⟨⟨m, X₀, W₀, a₀, hW₀, ha₀, rfl⟩, hA, hN', hI', V, S, k, a, w, hw, hPos, hOwn, hMark', hCut', hUp', hAt'⟩

/-- **Restriction to an open subset.** -/
theorem NativeHSState.restrict (h : NativeHSState Q W H) (U : Opens X) :
    NativeHSState (X := CMfd.of (n := n) U) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) Q)
      ((Subtype.val : U → X) ⁻¹' W) H := by
  obtain ⟨hH, hW, hQN, hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, hCut, hUpper, hAt⟩ := h
  have hcos : (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) Q).cosupp =
      (Subtype.val : U → X) ⁻¹' Q.cosupp :=
    MarkedIdealRestrictOpen.cosupp_pullback_val Q (fun _ _ hg => holomorphicAt_of_mem_coherent Q.ideal hQI hg) U
  refine ⟨hH, AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW, ?_,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hQI, V, S, k, a, w, hw, hPos, hOwn, hMark,
    ?_, ?_, ?_⟩
  · change (Subtype.val : U → X) ⁻¹' Q.N = univ
    rw [hQN, preimage_univ]
  · rw [hcos, hCut]
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hilbertSamuelAt_vanishing_actual_open_any]
  · intro x ℓ
    rw [hilbertSamuelAt_vanishing_actual_open_any]
    exact hUpper _ ℓ
  · intro x hx
    rw [hcos] at hx
    exact HironakaActualHistoricalNativeOpenRestriction.actual_native_point_presentation_open_restriction S a w W
      (CartanIrreducible.cartanCoherence W hW) Q hQI U x (hAt _ hx)

end State

/-! ### Invariance under biholomorphisms of the ambient -/

section Biholomorphic

variable {X X' : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']

/-- **Centred coordinates transported along a biholomorphism**: coordinates `Φ` centred at `ψ x'` give coordinates `Θ`
centred at `x'` (the composite with the chart transition of `ψ`) in which every function `F` near `ψ x'` and its pullback
`F ∘ ψ` have the same adapted germ. -/
theorem exists_biholomorphic_adapted_chart (ψ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (x' : X')
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (ψ x') (ψ x')))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (ψ x') (ψ x')) = 0) :
    ∃ (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x' x'))
      (_ : Θ.source ⊆ (chartAt (ComplexModel n) x').target)
      (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x' x') = 0),
      ∀ (F : X → ℂ) (hF : HolomorphicAt n F (ψ x')) (hFψ : HolomorphicAt n (F ∘ ψ) x'),
        adaptedGerm x' Θ hΘ0 (F ∘ ψ) hFψ = adaptedGerm (ψ x') Φ hΦ0 F hF := by
  have hrange : range 𝓘(ℂ, ComplexModel n) = univ := by simp
  let e := chartAt (ComplexModel n) x'
  let e' := chartAt (ComplexModel n) (ψ x')
  let F : ComplexModel n → ComplexModel n := fun u => e' (ψ (e.symm u))
  let N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (ψ ⁻¹' e'.source)
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target (e'.open_source.preimage ψ.continuous)
  have hzN : e x' ∈ N := ⟨e.map_source (mem_chart_source _ x'), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ x')]
    exact mem_chart_source _ (ψ x')⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (ψ.contMDiff.contMDiffOn (s := univ))).2 x' (ψ x')
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2, mem_univ _⟩
  have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x' :=
    (ψ.contMDiff x').mdifferentiableAt (by simp)
  have hderiv : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ x' = fderiv ℂ F (e x') := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e x')) := by
    have := MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse ψ.contMDiff ψ.symm.contMDiff
      ψ.apply_symm_apply ψ.symm_apply_apply x'
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rw [hderiv] at this
    exact this.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e x') = e' (ψ x') := by
    show e' (ψ (e.symm (e x'))) = e' (ψ x')
    rw [e.left_inv (mem_chart_source _ x')]
  let Θ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz)
  have hΘ0 : Θ.toFun (e x') = 0 := by
    change Φ.toFun (Ψ.toFun (e x')) = 0
    rw [hΨF, hFz]
    exact hΦ0
  refine ⟨Θ, fun u hu => (hΨN hu.1).1, hΘ0, ?_⟩
  intro G hG hGψ
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0 : (0 : ComplexModel n) ∈ Θ.target := by
    simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds h0] with z hz
  have hz2 : Φ.invFun z ∈ Ψ.target := hz.2
  have hu : Ψ.invFun (Φ.invFun z) ∈ Ψ.source := Ψ.mapsTo_invFun hz2
  have huN := hΨN hu
  have hFu : F (Ψ.invFun (Φ.invFun z)) = Φ.invFun z := by
    rw [← hΨF]
    exact Ψ.right_inv _ hz2
  have hψu : ψ (e.symm (Ψ.invFun (Φ.invFun z))) = e'.symm (Φ.invFun z) := by
    have h1 : e' (ψ (e.symm (Ψ.invFun (Φ.invFun z)))) = Φ.invFun z := hFu
    calc ψ (e.symm (Ψ.invFun (Φ.invFun z)))
        = e'.symm (e' (ψ (e.symm (Ψ.invFun (Φ.invFun z))))) := (e'.left_inv huN.2).symm
      _ = e'.symm (Φ.invFun z) := by rw [h1]
  change G (ψ (e.symm (Ψ.invFun (Φ.invFun z)))) = G (e'.symm (Φ.invFun z))
  rw [hψu]

/-- **Adapted ideals of a pullback along a biholomorphism**, in the transported coordinates. -/
theorem adaptedIdeal_pullback_biholomorphic (ψ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (x' : X')
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (ψ x') (ψ x')))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (ψ x') (ψ x')) = 0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x' x'))
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x' x') = 0)
    (hgerm : ∀ (F : X → ℂ) (hF : HolomorphicAt n F (ψ x')) (hFψ : HolomorphicAt n (F ∘ ψ) x'),
      adaptedGerm x' Θ hΘ0 (F ∘ ψ) hFψ = adaptedGerm (ψ x') Φ hΦ0 F hF)
    (J : GermIdeal n X) (hJ : J.IsCoherent) :
    adaptedIdeal (GermIdeal.pullback (m := n) ψ J) x' Θ hΘ0 = adaptedIdeal J (ψ x') Φ hΦ0 := by
  obtain ⟨U, hU, hx, s, f, hf, hgen⟩ := hJ (ψ x')
  have hfh (i : Fin s) : HolomorphicAt n (f i) (ψ x') :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hf i) hx
  have hfo (i : Fin s) : HolomorphicAt n (f i ∘ ψ) x' :=
    (hfh i).comp_contMDiff (Eventually.of_forall fun _ => ψ.contMDiff.contMDiffAt)
  have hgo (F : X' → ℂ) :=
    FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _ => ψ.contMDiff.contMDiffAt) J f hfh (hgen (ψ x') hx) F
  rw [HironakaActualHistoricalInitialAffineDictionary.actual_native_adapted_ideal_of_whole_generation _ x' _ _ _
      hfo hgo,
    HironakaActualHistoricalInitialAffineDictionary.actual_native_adapted_ideal_of_whole_generation J (ψ x') Φ hΦ0
      f hfh (hgen (ψ x') hx)]
  apply congrArg Ideal.span
  congr 1
  funext i
  exact hgerm (f i) (hfh i) (hfo i)

/-- **Native point presentations pull back along biholomorphisms** (same family, words and selector). -/
theorem point_presentation_biholomorphic {V : Finset (Fin n →₀ ℕ)} {k : ℕ} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n) (W : Set X) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent)
    (ψ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (x' : X')
    (hAt : ActualHistoricalNativePointPresentation S a w W Q (ψ x')) :
    ActualHistoricalNativePointPresentation S a w (ψ ⁻¹' W) (MarkedIdealBiholomorphism.MarkedIdeal.pullback ψ Q)
      x' := by
  obtain ⟨Φ, hΦsrc, hΦ0, Γ, hFive, hSpan, hComp⟩ := hAt
  obtain ⟨Θ, hΘsrc, hΘ0, hgerm⟩ := exists_biholomorphic_adapted_chart ψ x' Φ hΦ0
  have hW' : (vanishingIdeal (n := n) (ψ ⁻¹' W)).IsCoherent := by
    rw [← HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism]
    exact GermIdealPullbackCalculus.isCoherent_pullback ψ.contMDiff hW
  have hOld := HironakaActualNativeSourceChartComposition.actual_original_translated_flattened_vanishing_origin_eq_adapted
    (ψ x') Φ hΦsrc hΦ0 W hW
  have hNew := HironakaActualNativeSourceChartComposition.actual_original_translated_flattened_vanishing_origin_eq_adapted
    x' Θ hΘsrc hΘ0 (ψ ⁻¹' W) hW'
  have hWhole := adaptedIdeal_pullback_biholomorphic ψ x' Φ hΦ0 Θ hΘ0 hgerm (vanishingIdeal (n := n) W) hW
  rw [HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism] at hWhole
  refine ⟨Θ, hΘsrc, hΘ0, Γ, hFive, hSpan.trans (hOld.trans (hWhole.symm.trans hNew.symm)), ?_⟩
  exact (adaptedIdeal_pullback_biholomorphic ψ x' Φ hΦ0 Θ hΘ0 hgerm Q.ideal hQI).trans hComp

end Biholomorphic

/-- **The native state pulls back along biholomorphisms** of the ambient. -/
theorem NativeHSState.pullback {X X' : CMfd.{0} n} (ψ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ} (h : NativeHSState Q W H) :
    NativeHSState (MarkedIdealBiholomorphism.MarkedIdeal.pullback ψ Q) (ψ ⁻¹' W) H := by
  obtain ⟨hH, hW, hQN, hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, hCut, hUpper, hAt⟩ := h
  have hcos : (MarkedIdealBiholomorphism.MarkedIdeal.pullback ψ Q).cosupp = ψ ⁻¹' Q.cosupp :=
    MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback ψ.contMDiff ψ.symm.contMDiff ψ.apply_symm_apply ψ.symm_apply_apply Q
      (fun _ _ hg => holomorphicAt_of_mem_coherent Q.ideal hQI hg)
  refine ⟨hH, AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage ψ.contMDiff hW, ?_,
    GermIdealPullbackCalculus.isCoherent_pullback ψ.contMDiff hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, ?_, ?_, ?_⟩
  · change ψ ⁻¹' Q.N = univ
    rw [hQN, preimage_univ]
  · rw [hcos, hCut]
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hilbertSamuelAt_vanishing_actual_biholomorphic_any]
  · intro x ℓ
    rw [hilbertSamuelAt_vanishing_actual_biholomorphic_any]
    exact hUpper _ ℓ
  · intro x hx
    rw [hcos] at hx
    exact point_presentation_biholomorphic S a w W (CartanIrreducible.cartanCoherence W hW) Q hQI ψ x (hAt _ hx)

/-! ### Products with a line and the local equivalence -/

/-- **Step (3a-lines): the native state is stable under the product with a line** (BM97 Thm 9.4, test (ii)). For a record
`Q` in the native state for `(W, H)` on `X`, the product record `projectionTest Q` on `X × ℂ` (ordinary pullback of the
ideal, carrier `univ`, the pulled-back boundary and the horizontal divisor `X × {0}`, the same mark) is in the native state for
`W × ℂ` and `lineHS H`.  Classically: the standard basis of `I_{W,x}` (vertices `V`, degrees, five point laws) pulled back
along the projection is a standard basis of `I_{W×ℂ,(x,t)} = I_{W,x}·𝒪_{X×ℂ,(x,t)}` with the lifted vertices (no exponent in
the new variable) and the same degrees, hence the same common mark; the cosupport of the pullback is `cosupp Q × ℂ`; the
Hilbert–Samuel function of `W × ℂ` at `(x, t)` is `lineHS` of that of `W` at `x` (convolution formula), and `lineHS` is
injective and monotone; `(a₀, 0)` is a singular point of `W₀ × ℂ` with Hilbert–Samuel function `lineHS H`. -/
def NativeLineStability : Prop :=
  ∀ {n : ℕ} {X : CMfd.{0} n} (Q : MarkedIdeal n X) (W : Set X) (H : ℕ → ℕ),
    NativeHSState Q W H →
      NativeHSState (projectionTest Q) ((Prod.fst : projectionAmbient X → X) ⁻¹' W) (lineHS H)

/-- Two marked ideals with the same boundary, both in the native state for one `(W, H)`. -/
def NativeRel {m : ℕ} {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop :=
  Q.E = P.E ∧ ∃ (W : Set Y) (H : ℕ → ℕ), NativeHSState P W H ∧ NativeHSState Q W H

/-- The boundary of the product record only depends on the boundary. -/
theorem projectionTest_E_congr {m : ℕ} {Y : CMfd.{0} m} {P Q : MarkedIdeal m Y} (h : Q.E = P.E) :
    (projectionTest Q).E = (projectionTest P).E := by
  obtain ⟨N, E, I, d⟩ := P
  obtain ⟨N', E', I', d'⟩ := Q
  change E' = E at h
  subst h
  rfl

/-- **The relation `NativeRel` is stable under the local test actions** without exceptional blowups (admissible blowups,
products with a line, restrictions to open subsets), given `NativeLineStability`. -/
theorem isLocStable_nativeRel (hL : NativeLineStability) :
    IsLocStable Kinds.wp (fun {m} {Y} P Q => NativeRel (m := m) (Y := Y) P Q) where
  E_eq h := h.1
  cosupp_eq h := by
    obtain ⟨-, W, H, hP, hQ⟩ := h
    rw [hP.cosupp_eq, hQ.cosupp_eq]
  controlled := by
    intro m Y P Q h C Z π hπ hC
    obtain ⟨hE, W, H, hP, hQ⟩ := h
    have hCQ : C ⊆ Q.cosupp := by
      rw [hQ.cosupp_eq, ← hP.cosupp_eq]
      exact hC.2.1
    refine ⟨?_, strictTransform m π W, H, hP.geoTransform hC.1 hC.2.1 hπ, hQ.geoTransform hC.1 hCQ hπ⟩
    show Q.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C] =
      P.E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]
    rw [hE]
  projection := by
    intro _ m Y P Q h
    obtain ⟨hE, W, H, hP, hQ⟩ := h
    exact ⟨projectionTest_E_congr hE, _, _, hL P W H hP, hL Q W H hQ⟩
  restrict := by
    intro m Y P Q h U
    obtain ⟨hE, W, H, hP, hQ⟩ := h
    refine ⟨?_, _, H, hP.restrict U, hQ.restrict U⟩
    show Q.E.map ((Subtype.val : U → Y) ⁻¹' ·) = P.E.map ((Subtype.val : U → Y) ⁻¹' ·)
    rw [hE]

/-- **Native records for the same `(W, H)` are locally equivalent** (`s(i,ii)` with local blowings-up), given the
stability (3a-lines) under products with a line. -/
theorem locWPEquiv_of_nativeHSState (hL : NativeLineStability) {X : CMfd.{0} n} {P Q : MarkedIdeal n X}
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (hQ : NativeHSState Q W H) (hE : Q.E = P.E) :
    LocWPEquiv P Q :=
  LocEquiv.of_isLocStable (isLocStable_nativeRel hL) rfl ⟨hE, W, H, hP, hQ⟩

end

end Hironaka.HironakaG11PresLineState

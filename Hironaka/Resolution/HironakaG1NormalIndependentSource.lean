import Hironaka.Resolution.HironakaG1NormalGraphFlags
import Hironaka.Resolution.HironakaG11PresLineState
import Hironaka.Resolution.HironakaG11InvCommonMark

/-! Independent one-vertex native source presentations give the same ideal
stalk when they present the same analytic source. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1NormalIndependentSource

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualHistoricalNormalizedWeakPresentation HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualWeightedCoefficientCompression HironakaSmoothSubmersionGermIdealColon
  HironakaActualNativeSourceChartComposition InvertibleIdealQuotient
  HironakaActualPowerBoundaryExponents HironakaG1NormalGraphFlags HironakaG8LocalHistory
  HironakaG11PresLineState GermIdealPullbackCalculus

private theorem weightedCompression_unique {ι R : Type*} [Unique ι] [Fintype ι] [CommRing R]
    (w : ι → ℕ) (Γ : ι → R) (hw : 0 < w default) :
    weightedCompression w Γ = Ideal.span (range Γ) := by
  unfold weightedCompression
  congr 1
  have hProd : weightedCommonMark w = w default := by
    unfold weightedCommonMark
    simp
  have hExp : ∀ i, weightedCommonMark w / w i = 1 := by
    intro i
    rw [Unique.eq_default i, hProd, Nat.div_self hw]
  simp [hExp]

variable {n : ℕ} {X : CMfd.{0} n}

/-- A one-vertex native presentation retains the entire original analytic
ideal stalk. The chart and vertex generator come from that presentation. -/
theorem native_singleVertex_mem_iff
    {V : Finset (Fin n →₀ ℕ)} [Unique V] {k : ℕ}
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hPos : 0 < normalExponentDegree ((default : V).val))
    (W : Set X) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent) (x : X)
    (hNative : ActualHistoricalNativePointPresentation S a w W Q x)
    (F : X → ℂ) :
    Q.ideal.mem x F ↔ (vanishingIdeal (n := n) W).mem x F := by
  obtain ⟨Φ, hΦsrc, hΦ0, Γ, _hLaws, hSpan, hComp⟩ := hNative
  have hRange : range (Γ ∘ a) = range Γ := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨a i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := a.surjective i
      exact ⟨j, rfl⟩
  have hAdapt : adaptedIdeal Q.ideal x Φ hΦ0 =
      adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ0 := by
    rw [hComp, weightedCompression_unique (fun v : V => normalExponentDegree v.val) Γ hPos, ← hRange]
    exact hSpan.trans
      (actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hΦsrc hΦ0 W hW)
  constructor
  · intro hF
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hQ hF
    exact (mem_adaptedIdeal_iff _ hW x Φ hΦ0 F hh).mp
      (hAdapt ▸ (mem_adaptedIdeal_iff _ hQ x Φ hΦ0 F hh).mpr hF)
  · intro hF
    have hh := GermIdeal.IsCoherent.holomorphicAt_mem hW hF
    exact (mem_adaptedIdeal_iff _ hQ x Φ hΦ0 F hh).mp
      (hAdapt.symm ▸ (mem_adaptedIdeal_iff _ hW x Φ hΦ0 F hh).mpr hF)

/-- Each carrier point may use its own native chart, selector, vertex and
generator. This hypothesis only asks for actual one-vertex presentations. -/
def HasOneVertexPresentation (W : Set X) (Q : MarkedIdeal n X) (x : X) : Prop :=
  ∃ (V : Finset (Fin n →₀ ℕ)) (u : Unique V) (k : ℕ)
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n),
      0 < normalExponentDegree u.default.val ∧ ActualHistoricalNativePointPresentation S a w W Q x

private theorem oneVertex_mem_iff {W : Set X} {Q : MarkedIdeal n X} {x : X}
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (hQ : Q.ideal.IsCoherent)
    (h : HasOneVertexPresentation W Q x) (F : X → ℂ) :
    Q.ideal.mem x F ↔ (vanishingIdeal (n := n) W).mem x F := by
  obtain ⟨V, u, k, S, a, w, hPos, hAt⟩ := h
  let _ := u
  exact native_singleVertex_mem_iff S a w hPos W hW Q hQ x hAt F

/-- Independent one-vertex native presentations over a common analytic
source give restricted equivalence at their common mark, along the proper
carrier on which both provide actual point presentations. -/
theorem restrictEquiv_of_oneVertexPresentations {W : Set X} {P Q : MarkedIdeal n X}
    (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent)
    (hN : P.N = Q.N) (hE : P.E = Q.E) (hd : P.d = Q.d)
    (hAtP : ∀ x ∈ P.N, HasOneVertexPresentation W P x)
    (hAtQ : ∀ x ∈ Q.N, HasOneVertexPresentation W Q x) :
    RestrictEquiv P Q := by
  refine ⟨hN, hE, hd, ?_, ?_⟩
  · intro x hx F hF
    have hCommon := (oneVertex_mem_iff hW hP (hAtP x hx) F).mp hF
    have hMem := (oneVertex_mem_iff hW hQ (hAtQ x (hN ▸ hx)) F).mpr hCommon
    exact IsInSpanAt.restrict (isInSpanAt_self hMem (GermIdeal.IsCoherent.holomorphicAt_mem hQ hMem))
  · intro x hx F hF
    have hCommon := (oneVertex_mem_iff hW hQ (hAtQ x (hN ▸ hx)) F).mp hF
    have hMem := (oneVertex_mem_iff hW hP (hAtP x hx) F).mpr hCommon
    exact IsInSpanAt.restrict (isInSpanAt_self hMem (GermIdeal.IsCoherent.holomorphicAt_mem hP hMem))


theorem HasOneVertexPresentation.pullback {Y : CMfd.{0} n}
    (b : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} (hW : (vanishingIdeal (n := n) W).IsCoherent)
    {Q : MarkedIdeal n X} (hQ : Q.ideal.IsCoherent) {y : Y}
    (h : HasOneVertexPresentation W Q (b y)) :
    HasOneVertexPresentation (b ⁻¹' W) (MarkedIdeal.pullback b Q) y := by
  obtain ⟨V, u, k, S, a, w, hPos, hAt⟩ := h
  exact ⟨V, u, k, S, a, w, hPos, point_presentation_biholomorphic S a w W hW Q hQ b y hAt⟩

variable {U V : Opens (ComplexModel n)} {t : ℕ}

private abbrev base (O : Opens (ComplexModel n)) := CMfd.of (n := n) O
private abbrev graphAmbient (O : Opens (ComplexModel n)) (t : ℕ) :=
  CMfd.of (n := n + t) (blockOpen O t)

/-- The finite normal graph test comparison for two independently presented
one-vertex records of the same analytic source in biholomorphic base charts. -/
theorem locWPEquiv_blockMarked_of_oneVertexPresentations
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (W : Set V) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    {k l : ℕ} (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = b ⁻¹' Q.N) (hE : P.E = Q.E.map (b ⁻¹' ·)) (hd : P.d = Q.d)
    (hAtP : ∀ x ∈ P.N, HasOneVertexPresentation (X := base U) (b ⁻¹' W) P x)
    (hAtQ : ∀ y ∈ Q.N, HasOneVertexPresentation (X := base V) W Q y)
    (F : List (Set (blockOpen V t))) (e : ℕ) :
    LocWPEquiv (X := graphAmbient U t)
      (powerMarked (blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·))) e)
      (MarkedIdeal.pullback (M := graphAmbient V t) (M' := graphAmbient U t) (blockChartMap b f g)
        (powerMarked (blockMarked g Q F) e)) := by
  let Q' := MarkedIdeal.pullback (M := base V) (M' := base U) b Q
  have hQ' : IsInvDomain l Q' := InvDomainTowerAlong.isInvDomain_pullback b hQ
  have hW' : (vanishingIdeal (n := n) (b ⁻¹' W)).IsCoherent := by
    rw [← HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism]
    exact isCoherent_pullback b.contMDiff hW
  have hR : RestrictEquiv P Q' :=
    restrictEquiv_of_oneVertexPresentations (X := base U) hW' hP.isWellFormed.isCoherent
      hQ'.isWellFormed.isCoherent hN hE hd hAtP
      (fun y hy => (hAtQ (b y) hy).pullback (X := base V) (Y := base U) b hW hQ.isWellFormed.isCoherent)
  apply locWPEquiv_pullback_commonPower_blockMarked b hf hg P Q hP hQ e e _ F
  rw [HironakaG11PresClassTransport.pullback_powerMarked (M := base V) (M' := base U)
    (f := b) b.contMDiff Q hQ.isWellFormed.isCoherent]
  exact HironakaG11InvCommonMark.restrictEquiv_powerMarked (X := base U) hR
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent h)
    (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hQ'.isWellFormed.isCoherent h) e

end

end Hironaka.HironakaG1NormalIndependentSource

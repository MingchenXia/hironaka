import Hironaka.Resolution.HironakaG3EmptyAwareCanonicalTransport
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison
import Hironaka.Resolution.HironakaG8LocalTransport
import Hironaka.Resolution.HironakaG3EmptyAwareBornSlots
import Hironaka.Resolution.HironakaG3UniverseNonmonomialOrder

/-! Original finite prefix transport under the actual empty-aware overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Classical
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OriginalOverlapPrefixTransport

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  ResolutionDriver HironakaStageCenters HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition
  HironakaG3InteriorEmptyAligned HironakaOriginalInteriorEmptyHistory
  HironakaOriginalActualEmptyNormalization HironakaOriginalFiniteEmptyCompression
  HironakaOriginalRecursiveBoundaryHistoryMap G3EmptyAwareCanonicalTransport
  G3NonemptyPhysicalCanonicalTransport HironakaOriginalBoundaryEmptyFilterComparison BlowupTowerSplit

private theorem physical_original_compression {n : ℕ} {X Y : CMfd.{0} n} (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length≤T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ ∧
      (geoTransformAlong M T).cosupp=χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y∈(geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y=F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      (IsGeoResolution M T ↔ IsGeoResolution M Q) := by
  classical
  generalize hlen : T.length=ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · refine ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,emptyAware_of_isTowerIso (IsTowerIso.refl_self T),?_,fun _ _ => rfl,Iff.rfl⟩
      rfl
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hi,hcanD,hcosD,hvalD,hresD⟩ :=
      original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hcan
    have hlt : (H.append S').length<ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length+1+S.length=ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,hresQ⟩ :=
      ih _ hlt (H.append S') hcanD rfl
    refine ⟨Z,Q,χQ.trans χD,FQ.comp (recursiveHistoryShiftEmbedding k (M.E.length+H.length)),
      hneQ,?_,hcanQ,?_,?_,?_,hresD.trans hresQ⟩
    · exact hleQ.trans hlt.le
    · have hDel := HironakaG3EmptyAwareComposition.trans
        (interior_empty_aligned H S') (emptyAware_of_isTowerIso hi)
      have hFinal := HironakaG3EmptyAwareComposition.trans hprojQ hDel
      simpa only [Diffeomorph.refl_trans] using hFinal
    · ext y
      change y∈(geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp ↔
        χQ.symm (χD.symm y)∈(geoTransformAlong M Q).cosupp
      rw [hcosD]
      change χD.symm y∈(geoTransformAlong M (H.append S')).cosupp ↔ _
      rw [hcosQ]
      rfl
    · intro y hy
      have hyD : χD.symm y∈(geoTransformAlong M (H.append S')).cosupp := by
        rw [hcosD] at hy
        exact hy
      have hv := hvalD y hy
      rw [hvalQ (χD.symm y) hyD] at hv
      exact hv

open HironakaG8LocalTransport

set_option maxHeartbeats 1500000 in
/-- An actual empty-aware comparison of finite prefixes transports original
canonicality and the maximum center. Each actual pruning keeps its own
literal chronological value embedding, so the transported comparison is
an equality of cuts even when the raw recursive values differ. -/
theorem original_prefix_transport_of_emptyAware {n k : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (hn : 0 < n) (M : MarkedIdeal n X₂) (hM : IsInvDomain k M)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    let M₁ := MarkedIdeal.pullback Φ M
    let R := invFamily hn k
    (IsCanonical M₁ (R.inv M₁) T₁ ↔ IsCanonical M (R.inv M) T₂) ∧
    (IsCanonical M (R.inv M) T₂ →
      (geoTransformAlong M₁ T₁).cosupp = ψ ⁻¹' (geoTransformAlong M T₂).cosupp ∧
      (∀ x ∈ (geoTransformAlong M₁ T₁).cosupp, ∀ y ∈ (geoTransformAlong M₁ T₁).cosupp,
        R.inv M₁ T₁ x ≤ R.inv M₁ T₁ y ↔ R.inv M T₂ (ψ x) ≤ R.inv M T₂ (ψ y)) ∧
      maxLocus (R.inv M₁ T₁) (geoTransformAlong M₁ T₁).cosupp =
        ψ ⁻¹' maxLocus (R.inv M T₂) (geoTransformAlong M T₂).cosupp) := by
  intro M₁ R
  have hM₁ : IsInvDomain k M₁ := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  have hCan₁ := original_family_canonical_of_emptyAware hn hM Φ hM₁ h
  have hBack : MarkedIdeal.pullback Φ.symm M₁ = M := pullback_symm_pullback Φ hM.isWellFormed.isCoherent
  have hCan₂ (hC : IsCanonical M₁ (R.inv M₁) T₁) : IsCanonical M (R.inv M) T₂ := by
    have hY := original_family_canonical_of_emptyAware hn hM₁ Φ.symm
      (hBack.symm ▸ hM) (HironakaG3EmptyAwareSymmetry.symm h) hC
    rwa [hBack] at hY
  refine ⟨⟨hCan₂, hCan₁⟩, fun hC => ?_⟩
  obtain ⟨Z₁, Q₁, χ₁, F₁, hn₁, _, hQ₁, hAware₁, hCos₁, hVal₁, _⟩ :=
    physical_original_compression hn k M₁ hM₁ T₁ (hCan₁ hC)
  obtain ⟨Z₂, Q₂, χ₂, F₂, hn₂, _, hQ₂, hAware₂, hCos₂, hVal₂, _⟩ :=
    physical_original_compression hn k M hM T₂ hC
  let η := χ₁.trans (ψ.trans χ₂.symm)
  have hQ : EmptyAwareTowerIso Φ Q₁ Q₂ η := by
    have hQ := HironakaG3EmptyAwareComposition.trans hAware₁
      (HironakaG3EmptyAwareComposition.trans h (HironakaG3EmptyAwareSymmetry.symm hAware₂))
    have he : (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X₂ ∞).symm =
        Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X₂ ∞ := by ext x; rfl
    simpa only [η, Diffeomorph.refl_trans, Diffeomorph.trans_refl, he] using hQ
  have hIso := isTowerIso_of_emptyAware_nonempty hQ hn₁ hn₂
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM Q₂ hQ₂
  have hCosQ := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hIso hTest
  have hCos : (geoTransformAlong M₁ T₁).cosupp = ψ ⁻¹' (geoTransformAlong M T₂).cosupp := by
    rw [hCos₁, hCos₂, hCosQ]
    ext x
    simp [η]
  have hCompare (x : Y₁) (hx : x ∈ (geoTransformAlong M₁ T₁).cosupp) :
      R.inv M₁ T₁ x = F₁ (R.inv M Q₂ (χ₂.symm (ψ x))) ∧
        R.inv M T₂ (ψ x) = F₂ (R.inv M Q₂ (χ₂.symm (ψ x))) := by
    have hxR : x ∈ ψ ⁻¹' (geoTransformAlong M T₂).cosupp := hCos ▸ hx
    have hxQ : ψ x ∈ χ₂.symm ⁻¹' (geoTransformAlong M Q₂).cosupp := hCos₂ ▸ hxR
    have hv := R.isInvValue.towerIso Φ M hM Q₁ Q₂ η hIso hQ₂ (χ₁.symm x)
      (by simpa [η] using hxQ)
    refine ⟨(hVal₁ x hx).trans (congrArg F₁ ?_), hVal₂ (ψ x) hxR⟩
    simpa [η] using hv
  have hOrd (x : Y₁) (hx : x ∈ (geoTransformAlong M₁ T₁).cosupp)
      (y : Y₁) (hy : y ∈ (geoTransformAlong M₁ T₁).cosupp) :
      R.inv M₁ T₁ x ≤ R.inv M₁ T₁ y ↔ R.inv M T₂ (ψ x) ≤ R.inv M T₂ (ψ y) := by
    rw [(hCompare x hx).1, (hCompare y hy).1, (hCompare x hx).2, (hCompare y hy).2]
    exact F₁.strictMono.le_iff_le.trans F₂.strictMono.le_iff_le.symm
  refine ⟨hCos, hOrd, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hMax⟩
    have hx' : x ∈ ψ ⁻¹' (geoTransformAlong M T₂).cosupp := hCos ▸ hx
    refine ⟨hx', fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := ψ.surjective y
    have hz : z ∈ (geoTransformAlong M₁ T₁).cosupp := hCos.symm ▸ hy
    exact (hOrd z hz x hx).mp (hMax z hz)
  · rintro ⟨hx, hMax⟩
    have hx' : x ∈ (geoTransformAlong M₁ T₁).cosupp := hCos.symm ▸ hx
    exact ⟨hx', fun z hz => (hOrd z hz x hx').mpr (hMax (ψ z) (show z ∈ ψ ⁻¹' (geoTransformAlong M T₂).cosupp from hCos ▸ hz))⟩

open Hironaka.HolomorphicIdealSheaves HironakaG3EmptyAwareBornSlots
  HironakaG3UniverseMonomialVanishing

set_option maxHeartbeats 950000 in
/-- The actual marked-ideal records of a labelled native or embedded
overlap transport original canonicality and the whole maximum locus
through its empty-aware prefix map. The chart data are precisely carrier
agreement and equality of the nonempty ordered boundary slots. -/
theorem original_native_overlap_prefix_read {n : ℕ} (hn : 0 < n)
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (W : Set X₂) (W₁ : Set X₁) (E : List (Set X₂)) (E₁ : List (Set X₁))
    (hW : W₁ = Φ ⁻¹' W) (hW₁ : IsComplexAnalyticSubset (n := n) W₁)
    (hE : E₁.filter (fun H => decide H.Nonempty) =
      (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (hIso : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    let M : MarkedIdeal n X₂ := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
    let M₁ : MarkedIdeal n X₁ := ⟨univ, E₁, vanishingIdeal (n := n) W₁, 1⟩
    IsInvDomain n M →
    (IsCanonical M₁ ((canonicalInvariant n).inv M₁) T₁ ↔
      IsCanonical M ((canonicalInvariant n).inv M) T₂) ∧
    (IsCanonical M ((canonicalInvariant n).inv M) T₂ →
      (geoTransformAlong M₁ T₁).cosupp = ψ ⁻¹' (geoTransformAlong M T₂).cosupp ∧
      maxLocus ((canonicalInvariant n).inv M₁ T₁) (geoTransformAlong M₁ T₁).cosupp =
        ψ ⁻¹' maxLocus ((canonicalInvariant n).inv M T₂) (geoTransformAlong M T₂).cosupp) := by
  intro M M₁ hM
  have hRecord : nonemptyBoundary M₁ = MarkedIdeal.pullback Φ (nonemptyBoundary M) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ.symm
    · change E₁.filter (fun H => decide H.Nonempty) =
        (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·)
      rw [hE, filter_map_bijection Φ Φ.surjective]
    · change vanishingIdeal (n := n) W₁ = GermIdeal.pullback (m := n) Φ (vanishingIdeal (n := n) W)
      have hI := CartanIrreducible.cartanCoherence W₁ hW₁
      rw [hW] at hI ⊢
      exact (pullback_vanishingIdeal_diffeo Φ W hI).symm
    · rfl
  have h := original_prefix_transport_of_emptyAware hn (nonemptyBoundary M)
    (isInvDomain_nonemptyBoundary M hM) Φ T₁ T₂ ψ hIso
  change (_ ↔ _) ∧ (_ → _) at h
  rw [← hRecord] at h
  have hFam : invFamily hn n = canonicalInvariant n := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [hFam] at h
  have hL := isCanonical_nonemptyBoundary_iff M₁ T₁
  have hR := isCanonical_nonemptyBoundary_iff M T₂
  refine ⟨hL.symm.trans (h.1.trans hR), fun hCan => ?_⟩
  obtain ⟨hC, _, hMax⟩ := h.2 (hR.mpr hCan)
  rw [cosupp_nonemptyBoundary_along M₁ T₁, cosupp_nonemptyBoundary_along M T₂] at hC hMax
  rw [maxLocus_nonemptyBoundary M₁ T₁, maxLocus_nonemptyBoundary M T₂] at hMax
  exact ⟨hC, hMax⟩

/-- Every literal right prefix of an actual overlap has a matching left
prefix. Unmatched empty steps may be dropped on either side. -/
theorem exists_aligned_prefix_of_emptyAware {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (j : ℕ) :
    ∃ i ≤ T₁.length,
      ∃ η : (split T₁ i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split T₂ j).1,
        EmptyAwareTowerIso Φ (head T₁ i) (head T₂ j) η := by
  induction h generalizing j with
  | refl =>
    cases j <;> exact ⟨0, Nat.zero_le _, Φ, .refl⟩
  | step h hπ₁ hπ₂ χ hComm hCentre ih =>
    cases j with
    | zero => exact ⟨0, Nat.zero_le _, χ, .step h hπ₁ hπ₂ χ hComm hCentre⟩
    | succ j =>
      obtain ⟨i, hi, η, hη⟩ := ih j
      exact ⟨i + 1, Nat.succ_le_succ hi, η, hη⟩
  | leftEmpty h hπ φ hφ ih =>
    obtain ⟨i, hi, η, hη⟩ := ih j
    exact ⟨i + 1, Nat.succ_le_succ hi, η, hη⟩
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψ₀ h ρ hπ φ hφ ih =>
    cases j with
    | zero =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      cases T₁ <;> exact ⟨ψ₀.trans φ.symm, .rightEmpty h hπ φ hφ⟩
    | succ j => exact ih j

/-- A canonical right history yields canonicality and its exact maximum
center on each matching left prefix, via the actual overlap comparison. -/
theorem original_prefix_centres_of_canonical_overlap {n k : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (hn : 0 < n) (M : MarkedIdeal n X₂) (hM : IsInvDomain k M)
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
    (hCan : IsCanonical M ((invFamily hn k).inv M) T₂) (j : ℕ) :
    let M₁ := MarkedIdeal.pullback Φ M
    ∃ i ≤ T₁.length,
      ∃ η : (split T₁ i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split T₂ j).1,
        EmptyAwareTowerIso Φ (head T₁ i) (head T₂ j) η ∧
        IsCanonical M₁ ((invFamily hn k).inv M₁) (head T₁ i) ∧
        maxLocus ((invFamily hn k).inv M₁ (head T₁ i)) (geoTransformAlong M₁ (head T₁ i)).cosupp =
          η ⁻¹' maxLocus ((invFamily hn k).inv M (head T₂ j)) (geoTransformAlong M (head T₂ j)).cosupp := by
  intro M₁
  obtain ⟨i, hi, η, hη⟩ := exists_aligned_prefix_of_emptyAware h j
  have hC := isCanonical_head M ((invFamily hn k).inv M) T₂ j hCan
  have hRead := original_prefix_transport_of_emptyAware hn M hM Φ (head T₁ i) (head T₂ j) η hη
  exact ⟨i, hi, η, hη, hRead.1.mpr hC, (hRead.2 hC).2.2⟩

/-- Every prefix on the canonical side of a labelled chart overlap has a
matching actual prefix whose original maximum center is the pullback. -/
theorem original_native_prefix_centres_of_canonical_overlap {n : ℕ} (hn : 0 < n)
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (W : Set X₂) (W₁ : Set X₁) (E : List (Set X₂)) (E₁ : List (Set X₁))
    (hW : W₁ = Φ ⁻¹' W) (hW₁ : IsComplexAnalyticSubset (n := n) W₁)
    (hE : E₁.filter (fun H => decide H.Nonempty) =
      (E.map (Φ ⁻¹' ·)).filter (fun H => decide H.Nonempty))
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (hIso : EmptyAwareTowerIso Φ T₁ T₂ ψ) (j : ℕ) :
    let M : MarkedIdeal n X₂ := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
    let M₁ : MarkedIdeal n X₁ := ⟨univ, E₁, vanishingIdeal (n := n) W₁, 1⟩
    IsInvDomain n M →
    IsCanonical M ((canonicalInvariant n).inv M) T₂ →
    ∃ i ≤ T₁.length,
      ∃ η : (split T₁ i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split T₂ j).1,
        EmptyAwareTowerIso Φ (head T₁ i) (head T₂ j) η ∧
        IsCanonical M₁ ((canonicalInvariant n).inv M₁) (head T₁ i) ∧
        maxLocus ((canonicalInvariant n).inv M₁ (head T₁ i)) (geoTransformAlong M₁ (head T₁ i)).cosupp =
          η ⁻¹' maxLocus ((canonicalInvariant n).inv M (head T₂ j)) (geoTransformAlong M (head T₂ j)).cosupp := by
  intro M M₁ hM hCan
  obtain ⟨i, hi, η, hη⟩ := exists_aligned_prefix_of_emptyAware hIso j
  have hC := isCanonical_head M ((canonicalInvariant n).inv M) T₂ j hCan
  have hRead := original_native_overlap_prefix_read hn Φ W W₁ E E₁ hW hW₁ hE
    (head T₁ i) (head T₂ j) η hη hM
  exact ⟨i, hi, η, hη, hRead.1.mpr hC, (hRead.2 hC).2⟩

end Hironaka.HironakaG8OriginalOverlapPrefixTransport

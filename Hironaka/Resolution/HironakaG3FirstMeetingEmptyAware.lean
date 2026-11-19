import Hironaka.Resolution.HironakaG3EmptyAwareComposition
import Hironaka.Resolution.HironakaG3InteriorEmptyComparison
import Hironaka.Resolution.HironakaOriginalFirstMeetingPrefixUniqueness
import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
import Hironaka.Resolution.HironakaG3FirstMeetingComparison
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3InteriorEmptyAligned
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareComposition HironakaG3InteriorEmptyComparison
  HironakaOriginalInteriorEmptyHistory HironakaOriginalActualEmptyNormalization
  HironakaOriginalFiniteEmptyCompression HironakaOriginalRecursiveBoundaryHistoryMap
  HironakaOriginalTerminalChoiceComparison HironakaOriginalTerminalProjectionUniqueness
  HironakaOriginalFirstMeetingPrefixUniqueness
  HironakaStageCenters CanonicalCentres RestrictEmptyTower BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG3EmptyAwareComposition
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.HolomorphicIdealSheaves HironakaDisjointFiniteControlledHistory

variable {n : ℕ} {X A B Y Y' : CMfd.{0} n}

theorem interior_empty_aligned {n : ℕ} {X A Y : CMfd.{0} n}
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (H.append S) (interiorEmptyHistory H S)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞) := by
  have hp : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      H (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) := by
    have heq : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞).symm =
        Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞ := by ext x; rfl
    simpa only [Diffeomorph.refl_trans, heq] using
      (EmptyAwareTowerIso.rightEmpty (emptyAware_of_isTowerIso (IsTowerIso.refl_self H))
        BlowupExistenceCodimOne.isBlowupAlong_id_empty
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) (fun _ => rfl))
  exact emptyAware_append_isTowerIso hp (IsTowerIso.refl_self S)

private theorem centresAvoid_of_isTowerIso_id
    {T' : BlowupTower X Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hi : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ) (O : Opens X) :
    CentresAvoid O T' ↔ CentresAvoid O T := by
  induction hi with
  | refl => exact Iff.rfl
  | @step Y' Y Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    change (CentresAvoid O T' ∧ Disjoint C' (T'.proj ⁻¹' (O : Set X))) ↔
      (CentresAvoid O T ∧ Disjoint C (T.proj ⁻¹' (O : Set X)))
    rw [ih]
    have hp : T'.proj ⁻¹' (O : Set X) = χ ⁻¹' (T.proj ⁻¹' (O : Set X)) := by
      ext z
      change T'.proj z ∈ O ↔ T.proj (χ z) ∈ O
      rw [← hi.proj_comm]
      rfl
    rw [← hC, hp]
    exact and_congr_right fun _ => Set.disjoint_preimage_iff (f := (χ : Y' → Y)) χ.surjective

private theorem centresAvoid_interiorEmptyHistory_iff
    (H : BlowupTower X A) (S : BlowupTower A Y) (O : Opens X) :
    CentresAvoid O (interiorEmptyHistory H S) ↔ CentresAvoid O (H.append S) := by
  rw [interiorEmptyHistory, centresAvoid_append_iff, centresAvoid_append_iff]
  change ((CentresAvoid O H ∧ Disjoint (∅ : Set A) _) ∧
    CentresAvoid (openPreimage H O) S) ↔ _
  simp

theorem aligned_compression_with_avoidance (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ z, T.proj (χ z) = Q.proj z) ∧
      (geoTransformAlong M T).cosupp = χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y = F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      CentresAvoid O Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ := by
  classical
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,fun _ => rfl,rfl,fun _ _ => rfl,hav, emptyAware_of_isTowerIso (IsTowerIso.refl_self T)⟩
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Y',S',χD,hlenD,hi,hcanD,hcosD,hvalD,_hresD⟩ :=
      original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hcan
    have havI := (centresAvoid_of_isTowerIso_id hi O).mpr hav
    have havD := (centresAvoid_interiorEmptyHistory_iff H S' O).mp havI
    have hlt : (H.append S').length < ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length+1+S.length=ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,havQ,haQ⟩ :=
      ih _ hlt (H.append S') hcanD havD rfl
    refine ⟨Z,Q,χQ.trans χD,FQ.comp (recursiveHistoryShiftEmbedding k (M.E.length+H.length)),
      hneQ,hleQ.trans hlt.le,hcanQ,?_,?_,?_,havQ,?_⟩
    · intro q
      change ((H.step ∅ π hπ).append S).proj (χD (χQ q)) = Q.proj q
      have hp := hi.proj_comm (χQ q)
      change (interiorEmptyHistory H S').proj (χQ q) =
        ((H.step ∅ π hπ).append S).proj (χD (χQ q)) at hp
      rw [proj_interiorEmptyHistory] at hp
      exact hp.symm.trans (hprojQ q)
    · ext y
      change y ∈ (geoTransformAlong M ((H.step ∅ π hπ).append S)).cosupp ↔
        χQ.symm (χD.symm y) ∈ (geoTransformAlong M Q).cosupp
      rw [hcosD]
      change χD.symm y ∈ (geoTransformAlong M (H.append S')).cosupp ↔ _
      rw [hcosQ]
      rfl
    · intro y hy
      have hyD : χD.symm y ∈ (geoTransformAlong M (H.append S')).cosupp := by
        rw [hcosD] at hy
        exact hy
      have hv := hvalD y hy
      rw [hvalQ (χD.symm y) hyD] at hv
      exact hv
    · have haI := interior_empty_aligned H S'
      have haT := emptyAware_of_isTowerIso hi
      have haD := HironakaG3EmptyAwareComposition.trans haI haT
      have ha := HironakaG3EmptyAwareComposition.trans haQ (by
        simpa only [Diffeomorph.refl_trans] using haD)
      simpa only [Diffeomorph.refl_trans] using ha


private theorem maxLocus_transport_orderEmbedding_local {Λ : Type} [LinearOrder Λ]
    {P Q : Type*} (e : P ≃ Q) (F : Λ ↪o Λ) (S : Set P) (S' : Set Q)
    (u : P → Λ) (v : Q → Λ) (hs : S = e ⁻¹' S')
    (hv : ∀ p ∈ S, u p = F (v (e p))) :
    maxLocus u S = e ⁻¹' maxLocus v S' := by
  ext p
  constructor
  · intro hp
    refine ⟨by change p ∈ e ⁻¹' S'; rw [← hs]; exact hp.1,?_⟩
    intro q hq
    have hpq : e.symm q ∈ S := by rw [hs]; simpa using hq
    have hh := hp.2 (e.symm q) hpq
    rw [hv _ hpq,hv _ hp.1] at hh
    simpa using F.le_iff_le.mp hh
  · intro hp
    have hpS : p ∈ S := by rw [hs]; exact hp.1
    refine ⟨hpS,?_⟩
    intro q hq
    rw [hv _ hq,hv _ hpS]
    apply F.monotone
    apply hp.2
    change q ∈ e ⁻¹' S'
    rwa [← hs]

/-- Actual finite empty deletion retains the original avoided open and
transports the next whole maximal-locus encounter in both directions. -/
theorem aligned_compression_preserves_first_meeting (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ z, T.proj (χ z) = Q.proj z) ∧
      (geoTransformAlong M T).cosupp = χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y = F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      CentresAvoid O Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T χ ∧
      ((∃ c ∈ maxLocus ((invFamily hn k).inv M T) (geoTransformAlong M T).cosupp,
          T.proj c ∈ O) ↔
        ∃ c ∈ maxLocus ((invFamily hn k).inv M Q) (geoTransformAlong M Q).cosupp,
          Q.proj c ∈ O) := by
  obtain ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha,hAlign⟩ := aligned_compression_with_avoidance hn k M hM T hcan O hav
  have hmax := maxLocus_transport_orderEmbedding_local χ.symm.toEquiv F _ _ _ _ hs hv
  refine ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha,hAlign,?_⟩
  constructor
  · rintro ⟨c,hc,hcO⟩
    refine ⟨χ.symm c,?_,?_⟩
    · rw [hmax] at hc
      exact hc
    · rw [← hp,χ.apply_symm_apply]
      exact hcO
  · rintro ⟨c,hc,hcO⟩
    refine ⟨χ c,?_,?_⟩
    · rw [hmax]
      change χ.symm (χ c) ∈ maxLocus ((invFamily hn k).inv M Q) (geoTransformAlong M Q).cosupp
      rw [χ.symm_apply_apply]
      exact hc
    · rw [hp]
      exact hcO



/-- Original canonical first-meeting histories admit the actual empty-aware
alignment, with every removed empty stage accounted for. -/
theorem original_first_meeting_emptyAware (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (hc₁ : IsCanonical M ((invFamily hn k).inv M) T₁)
    (hc₂ : IsCanonical M ((invFamily hn k).inv M) T₂)
    (O : Opens X) (ha₁ : CentresAvoid O T₁) (ha₂ : CentresAvoid O T₂)
    (hm₁ : ∃ c ∈ maxLocus ((invFamily hn k).inv M T₁) (geoTransformAlong M T₁).cosupp,
      T₁.proj c ∈ O)
    (hm₂ : ∃ c ∈ maxLocus ((invFamily hn k).inv M T₂) (geoTransformAlong M T₂).cosupp,
      T₂.proj c ∈ O) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
  obtain ⟨Z₁,Q₁,χ₁,F₁,hne₁,_hlen₁,hcQ₁,hp₁,hs₁,hv₁,haQ₁,hAlign₁,hmQ₁⟩ :=
    aligned_compression_preserves_first_meeting hn k M hM T₁ hc₁ O ha₁
  obtain ⟨Z₂,Q₂,χ₂,F₂,hne₂,_hlen₂,hcQ₂,hp₂,hs₂,hv₂,haQ₂,hAlign₂,hmQ₂⟩ :=
    aligned_compression_preserves_first_meeting hn k M hM T₂ hc₂ O ha₂
  have hseg₁ := isCanonicalSegment_of_actual_nonempty_centres M
    ((invFamily hn k).inv M) Q₁ hcQ₁ hne₁
  have hseg₂ := isCanonicalSegment_of_actual_nonempty_centres M
    ((invFamily hn k).inv M) Q₂ hcQ₂ hne₂
  obtain ⟨_hlen,ψ,hi⟩ := first_meeting_nonempty_lengths_eq
    (invFamily hn k) M hM Q₁ Q₂ hseg₁ hseg₂ O haQ₁ haQ₂ (hmQ₁.mp hm₁) (hmQ₂.mp hm₂)
  have hrev := HironakaG3EmptyAwareSymmetry.symm hAlign₁
  have hmid := emptyAware_of_isTowerIso hi
  have h₁ := HironakaG3EmptyAwareComposition.trans hrev hmid
  have h₂ := HironakaG3EmptyAwareComposition.trans h₁ hAlign₂
  refine ⟨(χ₁.symm.trans ψ).trans χ₂, ?_⟩
  have hRefl : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).symm =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞ := by ext x; rfl
  simpa only [hRefl, Diffeomorph.refl_trans] using h₂

/-- First-meeting canonical histories, including arbitrary actual empty stages,
have compatible comparisons of their actual ambient coupled lifts. -/
theorem original_first_meeting_emptyAware_ambient (hn : 0 < n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (hc₁ : IsCanonical M ((invFamily hn k).inv M) T₁)
    (hc₂ : IsCanonical M ((invFamily hn k).inv M) T₂)
    (O : Opens X) (ha₁ : CentresAvoid O T₁) (ha₂ : CentresAvoid O T₂)
    (hm₁ : ∃ c ∈ maxLocus ((invFamily hn k).inv M T₁) (geoTransformAlong M T₁).cosupp,
      T₁.proj c ∈ O)
    (hm₂ : ∃ c ∈ maxLocus ((invFamily hn k).inv M T₂) (geoTransformAlong M T₂).cosupp,
      T₂.proj c ∈ O)
    {t : ℕ} {P : CMfd.{0} (n+t)} {N : Set P} {B : List (Set P)}
    {J : GermIdeal (n+t) P} {ι : X → P}
    {Z₁ Z₂ : CMfd.{0} (n+t)} {U₁ : BlowupTower P Z₁} {U₂ : BlowupTower P Z₂}
    {η₁ : Y₁ → Z₁} {η₂ : Y₂ → Z₂}
    (hU₁ : CoupledHistory N B J ι M T₁ U₁ η₁)
    (hU₂ : CoupledHistory N B J ι M T₂ U₂ η₂) :
    ∃ (ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂)
      (β : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ Z₂),
      (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := original_first_meeting_emptyAware hn k M hM T₁ T₂ hc₁ hc₂ O ha₁ ha₂ hm₁ hm₂
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) hψ (fun _ => rfl) hU₁ hU₂
  exact ⟨ψ,β,hβ,hη⟩

end
end Hironaka.HironakaG3InteriorEmptyAligned

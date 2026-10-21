/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalStoppedPrefixSmoothComparison

/-!
# Intrinsic uniqueness of the actual canonical first-meeting prefix

Empty steps are internally removed while retaining avoidance of the same
original open.  The next whole maximum encounter forces equal nonempty
lengths; actual equal-length tower uniqueness then compares the original
stopped maps despite different actual empty-step counts.

No terminality, comparison map, common stopping index or singular
vanishing-ideal smooth-pullback equality is assumed.
Blueprint: `hironaka-original-first-meeting-prefix-uniqueness-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaOriginalFirstMeetingPrefixUniqueness

noncomputable section

open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplit
  HironakaStageCenters CanonicalCentres RestrictEmptyTower
  HironakaOriginalFiniteEmptyCompression HironakaOriginalActualEmptyNormalization
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveBoundaryHistoryMap
  HironakaOriginalTerminalChoiceComparison HironakaOriginalTerminalProjectionUniqueness

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus IsCanonicalSegment)

variable {n : ℕ} {X A B Y Y' : CMfd.{u} n}

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

private theorem compression_with_avoidance (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ z, T.proj (χ z) = Q.proj z) ∧
      (geoTransformAlong M T).cosupp = χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y = F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      CentresAvoid O Q := by
  classical
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing Y with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨Y,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,fun _ => rfl,rfl,fun _ _ => rfl,hav⟩
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
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,havQ⟩ :=
      ih _ hlt (H.append S') hcanD havD rfl
    refine ⟨Z,Q,χQ.trans χD,FQ.comp (recursiveHistoryShiftEmbedding k (M.E.length+H.length)),
      hneQ,hleQ.trans hlt.le,hcanQ,?_,?_,?_,havQ⟩
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

private theorem maxLocus_transport_orderEmbedding {Λ : Type v} [LinearOrder Λ]
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
theorem empty_free_compression_preserves_avoidance (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ z, T.proj (χ z) = Q.proj z) ∧
      (geoTransformAlong M T).cosupp = χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y = F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      CentresAvoid O Q ∧
      ((∃ c ∈ maxLocus ((invFamily hn k).inv M T) (geoTransformAlong M T).cosupp,
          T.proj c ∈ O) ↔
        ∃ c ∈ maxLocus ((invFamily hn k).inv M Q) (geoTransformAlong M Q).cosupp,
          Q.proj c ∈ O) := by
  obtain ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha⟩ := compression_with_avoidance hn k M hM T hcan O hav
  have hmax := maxLocus_transport_orderEmbedding χ.symm.toEquiv F _ _ _ _ hs hv
  refine ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha,?_⟩
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

private theorem maximum_disjoint_of_nonempty_canonical_tail {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeal n X) (inv : ∀ {D : CMfd.{u} n}, BlowupTower X D → D → Λ)
    (H : BlowupTower X A) (O : Opens X) :
    ∀ {D : CMfd.{u} n} (S : BlowupTower A D),
      IsCanonicalSegment M inv (H.append S) → CentresAvoid O (H.append S) → 0<S.length →
      Disjoint (maxLocus (inv H) (geoTransformAlong M H).cosupp) (H.proj ⁻¹' (O : Set X)) := by
  intro D S
  induction S with
  | refl => exact fun _ _ h => False.elim (Nat.not_lt_zero _ h)
  | @step D Z S C π hπ ih =>
    intro hc ha hpos
    cases S with
    | refl =>
      have hC : C = maxLocus (inv H) (geoTransformAlong M H).cosupp := hc.2.2
      rw [← hC]
      exact ha.2
    | step S C' π' hπ' => exact ih hc.1 ha.1 (Nat.succ_pos _)

private theorem first_meeting_nonempty_length_le {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (L : BlowupTower X Y) (S : BlowupTower X Y')
    (hL : IsCanonicalSegment M (R.inv M) L) (hS : IsCanonicalSegment M (R.inv M) S)
    (O : Opens X) (havL : CentresAvoid O L)
    (hmeetS : ∃ c ∈ maxLocus (R.inv M S) (geoTransformAlong M S).cosupp, S.proj c ∈ O) :
    L.length ≤ S.length := by
  by_contra hle
  have hlt : S.length < L.length := Nat.lt_of_not_ge hle
  let r := L.length-S.length
  have hsegH : IsCanonicalSegment M (R.inv M) (head L r) :=
    CanonicalResolution.isCanonicalSegment_of_append M (R.inv M) (head L r) (tail L r)
      (by rw [head_append_tail]; exact hL)
  have hlen : S.length = (head L r).length := by rw [length_head]; dsimp only [r]; omega
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M = M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  obtain ⟨χ,hi⟩ := CanonicalResolution.exists_isTowerIso_of_length_eq R hM Φ S (head L r)
    (by rw [hpull]; exact hS) hsegH hlen
  have hcanH : IsCanonical M (R.inv M) (head L r) :=
    ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment _ _ hsegH
  have htH := R.isInvValue.isGeoTestTower_of_isCanonical hM (head L r) hcanH
  have hcos := IsTowerIso.cosupp_geoTransformAlong Φ hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hi htH
  rw [hpull] at hcos
  have hv : ∀ p, χ p ∈ (geoTransformAlong M (head L r)).cosupp →
      R.inv M S p = R.inv M (head L r) (χ p) := by
    intro p hp
    have hv := R.isInvValue.towerIso Φ M hM S (head L r) χ hi hcanH p hp
    simpa only [hpull] using hv
  have hmax : maxLocus (R.inv M S) (geoTransformAlong M S).cosupp =
      χ ⁻¹' maxLocus (R.inv M (head L r)) (geoTransformAlong M (head L r)).cosupp := by
    rw [hcos]
    exact ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.surjective hv
  have hpos : 0 < (tail L r).length := by rw [length_tail]; dsimp only [r]; omega
  have hd := maximum_disjoint_of_nonempty_canonical_tail M (R.inv M) (head L r) O (tail L r)
    (by rw [head_append_tail]; exact hL) (by rw [head_append_tail]; exact havL) hpos
  obtain ⟨c,hc,hcO⟩ := hmeetS
  have hcH : χ c ∈ maxLocus (R.inv M (head L r)) (geoTransformAlong M (head L r)).cosupp := by
    rw [hmax] at hc
    exact hc
  apply Set.disjoint_left.mp hd hcH
  change (head L r).proj (χ c) ∈ O
  rw [← hi.proj_comm]
  exact hcO

/-- The first-meeting condition forces the nonempty lengths to agree;
equal-length uniqueness then constructs an actual tower isomorphism. -/
theorem first_meeting_nonempty_lengths_eq {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hT' : IsCanonicalSegment M (R.inv M) T') (hT : IsCanonicalSegment M (R.inv M) T)
    (O : Opens X) (hav' : CentresAvoid O T') (hav : CentresAvoid O T)
    (hm' : ∃ c ∈ maxLocus (R.inv M T') (geoTransformAlong M T').cosupp, T'.proj c ∈ O)
    (hm : ∃ c ∈ maxLocus (R.inv M T) (geoTransformAlong M T).cosupp, T.proj c ∈ O) :
    T'.length = T.length ∧
      ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ := by
  have hlen : T'.length = T.length := Nat.le_antisymm
    (first_meeting_nonempty_length_le R M hM T' T hT' hT O hav' hm)
    (first_meeting_nonempty_length_le R M hM T T' hT hT' O hav hm')
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ M = M :=
    ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  exact ⟨hlen, CanonicalResolution.exists_isTowerIso_of_length_eq R hM Φ T' T
    (by rw [hpull]; exact hT') hT hlen⟩

/-- Two actual original canonical first-meeting prefixes have one intrinsic
over-base biholomorphism, allowing every actual empty-step count. -/
theorem first_meeting_prefixes_existsUnique_biholomorphism
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (ha' : CentresAvoid O T') (ha : CentresAvoid O T)
    (hm' : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T') (geoTransformAlong M T').cosupp,
      T'.proj c ∈ O)
    (hm : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y) = T'.proj y := by
  have hex : ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y) = T'.proj y := by
    cases n with
    | zero =>
      have ht := (canonicalInvariant 0).isInvValue.isGeoTestTower_of_isCanonical hM T hc
      have he := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
      obtain ⟨c,hc,_⟩ := hm
      have hs := hc.1
      rw [he] at hs
      exact hs.elim
    | succ n =>
      obtain ⟨Z',Q',χ',F',hne',_hlen',hcQ',hp',_hs',_hv',haQ',hmQ'⟩ :=
        empty_free_compression_preserves_avoidance (Nat.succ_pos n) (n+1) M hM T' hc' O ha'
      obtain ⟨Z,Q,χ,F,hne,_hlen,hcQ,hp,_hs,_hv,haQ,hmQ⟩ :=
        empty_free_compression_preserves_avoidance (Nat.succ_pos n) (n+1) M hM T hc O ha
      have hseg' := isCanonicalSegment_of_actual_nonempty_centres M
        ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q' hcQ' hne'
      have hseg := isCanonicalSegment_of_actual_nonempty_centres M
        ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q hcQ hne
      obtain ⟨_hlen,ψ,hi⟩ := first_meeting_nonempty_lengths_eq
        (invFamily (Nat.succ_pos n) (n+1)) M hM Q' Q hseg' hseg O haQ' haQ
          (hmQ'.mp hm') (hmQ.mp hm)
      refine ⟨(χ'.symm.trans ψ).trans χ,?_⟩
      intro y
      change T.proj (χ (ψ (χ'.symm y))) = T'.proj y
      rw [hp]
      have hpi := hi.proj_comm (χ'.symm y)
      have hps := hp' (χ'.symm y)
      rw [χ'.apply_symm_apply] at hps
      exact hpi.symm.trans hps.symm
  obtain ⟨η,hη⟩ := hex
  refine ⟨η,hη,?_⟩
  intro η' hη'
  exact biholomorphisms_eq_of_actual_proj_eq T η' η (fun y => (hη' y).trans (hη y).symm)

end

end Hironaka.HironakaOriginalFirstMeetingPrefixUniqueness

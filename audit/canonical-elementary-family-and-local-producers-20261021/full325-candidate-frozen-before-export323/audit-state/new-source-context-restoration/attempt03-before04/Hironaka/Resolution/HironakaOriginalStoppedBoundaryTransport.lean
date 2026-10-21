/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalIndependentStoppedSource

/-!
# The actual boundary of independent canonical stopped maps

Actual empty compression preserves the ordered list of nonempty boundary
members.  This identifies the independently stopped smooth source's own
boundary, and gives normal crossings with that actual boundary.
The source marked record remains literally the smooth pullback record.

Blueprint: `hironaka-original-stopped-boundary-transport-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaOriginalStoppedBoundaryTransport

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RestrictEmptyTower CanonicalCentres EmbeddedFromResolution HironakaStageCenters
  HironakaOriginalTerminalChoiceComparison
  HironakaOriginalFiniteEmptyCompression HironakaOriginalActualEmptyNormalization
  HironakaOriginalInteriorEmptyHistory HironakaOriginalRecursiveBoundaryHistoryMap
  HironakaOriginalTerminalProjectionUniqueness HironakaOriginalFirstMeetingPrefixUniqueness
  HironakaOriginalIndependentStoppedSource HironakaOriginalStoppedPrefixSmoothComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalCompactTerminal HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open ResolutionInvariantExt (IsEmptyTower)

variable {n m : ℕ} {X A B D D' : CMfd.{u} n} {Y E F : CMfd.{u} m}

private theorem hasNormalCrossings_of_nonempty_mem {C : Set X} {L L' : List (Set X)}
    (hmem : ∀ H ∈ L, H.Nonempty → H ∈ L') (h : HasNormalCrossings n C L') :
    HasNormalCrossings n C L := by
  classical
  intro x hx
  obtain ⟨S₀,S,hcoord,hcard⟩ := h x hx
  have hj : ∀ (i : Fin L.length), x ∈ L.get i → ∃ j : Fin L'.length, L'.get j = L.get i := by
    intro i hi
    exact List.get_of_mem (hmem _ (List.get_mem _ _) ⟨x,hi⟩)
  let idx (i : Fin L.length) (hi : x ∈ L.get i) : Fin L'.length := Classical.choose (hj i hi)
  have hidx (i : Fin L.length) (hi : x ∈ L.get i) : L'.get (idx i hi) = L.get i :=
    Classical.choose_spec (hj i hi)
  let S' (i : Fin L.length) := if hi : x ∈ L.get i then S (idx i hi) else ∅
  obtain ⟨Φ,hsrc,h0,hchart⟩ := hcoord
  refine ⟨S₀,S',⟨Φ,hsrc,h0,?_⟩,?_⟩
  · rintro (_ | i) hi z hz hzΦ
    · exact hchart none hi hz hzΦ
    · change x ∈ L.get i at hi
      have hxi : x ∈ L'.get (idx i hi) := by rw [hidx i hi]; exact hi
      have hh := hchart (some (idx i hi)) hxi hz hzΦ
      change z ∈ L'.get (idx i hi) ↔ _ at hh
      rw [hidx i hi] at hh
      simpa only [Option.elim_some,S',dif_pos hi] using hh
  · intro i hi
    have hxi : x ∈ L'.get (idx i hi) := by rw [hidx i hi]; exact hi
    simpa only [S',dif_pos hi] using hcard (idx i hi) hxi

/-- Empty members impose no local coordinate requirement. -/
theorem hasNormalCrossings_filter_nonempty_iff (C : Set X) (L : List (Set X)) :
    HasNormalCrossings n C (L.filter (fun H => decide H.Nonempty)) ↔ HasNormalCrossings n C L := by
  classical
  constructor
  · exact hasNormalCrossings_of_nonempty_mem (fun H hH hne => by simp [hH,hne])
  · exact hasNormalCrossings_of_nonempty_mem (fun H hH _ => (List.mem_filter.mp hH).1)

private theorem filter_nonempty_insert_empty {P : Type*} (L : List (Set P)) (j : ℕ) :
    (L.insertIdx j ∅).filter (fun H => decide H.Nonempty) =
      L.filter (fun H => decide H.Nonempty) := by
  classical
  induction L generalizing j with
  | nil => cases j <;> simp
  | cons H L ih =>
    cases j with
    | zero => simp
    | succ j => by_cases hne : H.Nonempty <;> simp [hne,ih]

private theorem filter_nonempty_map_preimage {P Q : Type*} (f : P → Q)
    (hf : Surjective f) (L : List (Set Q)) :
    (L.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
      (L.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  classical
  induction L with
  | nil => rfl
  | cons H L ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]

private theorem boundary_of_isTowerIso_id {Z Z' : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {T' : BlowupTower X Z'} {T : BlowupTower X Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hi : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T χ)
    (ht : IsGeoTestTower M T) :
    (geoTransformAlong M T').E = (geoTransformAlong M T).E.map (χ ⁻¹' ·) := by
  have hh := hi.geoTransformAlong_eq (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
    hM.isClosedSubmanifold_N hM.isCoherent ht
  have hpull : MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isCoherent
  rw [hpull] at hh
  exact congrArg MarkedIdeal.E hh

private theorem centresAvoid_of_isTowerIso_id
    {T' : BlowupTower X D'} {T : BlowupTower X D}
    {χ : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D}
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
    (H : BlowupTower X A) (S : BlowupTower A D) (O : Opens X) :
    CentresAvoid O (interiorEmptyHistory H S) ↔ CentresAvoid O (H.append S) := by
  rw [interiorEmptyHistory, centresAvoid_append_iff, centresAvoid_append_iff]
  change ((CentresAvoid O H ∧ Disjoint (∅ : Set A) _) ∧
    CentresAvoid (openPreimage H O) S) ↔ _
  simp

private theorem compression_with_boundary (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X D)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D) (F : ValTy k ↪o ValTy k),
      StageCentres (fun _ C => C.Nonempty) Q ∧ Q.length ≤ T.length ∧
      IsCanonical M ((invFamily hn k).inv M) Q ∧
      (∀ z, T.proj (χ z) = Q.proj z) ∧
      (geoTransformAlong M T).cosupp = χ.symm ⁻¹' (geoTransformAlong M Q).cosupp ∧
      (∀ y ∈ (geoTransformAlong M T).cosupp,
        (invFamily hn k).inv M T y = F ((invFamily hn k).inv M Q (χ.symm y))) ∧
      CentresAvoid O Q ∧
      ((geoTransformAlong M T).E.map (χ ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
        (geoTransformAlong M Q).E.filter (fun H => decide H.Nonempty) := by
  classical
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing D with
  | h ℓ ih =>
    by_cases hne : StageCentres (fun _ C => C.Nonempty) T
    · exact ⟨D,T,Diffeomorph.refl 𝓘(ℂ,ComplexModel n) D ∞,OrderEmbedding.id _,
        hne,hlen.le,hcan,fun _ => rfl,rfl,fun _ _ => rfl,hav,by simp⟩
    obtain ⟨A,B,H,π,hπ,S,heq⟩ := exists_actual_empty_step_split T hne
    subst T
    obtain ⟨Z',S',χD,hlenD,hi,hcanD,hcosD,hvalD,_hresD⟩ :=
      original_recursive_family_actual_empty_deletion hn k M hM H π hπ S hcan
    have havI := (centresAvoid_of_isTowerIso_id hi O).mpr hav
    have havD := (centresAvoid_interiorEmptyHistory_iff H S' O).mp havI
    have hlt : (H.append S').length < ℓ := by
      rw [BlowupTower.length_append,hlenD]
      rw [BlowupTower.length_append] at hlen
      change H.length+1+S.length=ℓ at hlen
      omega
    obtain ⟨Z,Q,χQ,FQ,hneQ,hleQ,hcanQ,hprojQ,hcosQ,hvalQ,havQ,hEQ⟩ :=
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

    · have htOrig := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hM
        ((H.step ∅ π hπ).append S) hcan
      have htD := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hM
        (H.append S') hcanD
      have htH := (isGeoTestTower_append_iff M H S').mp htD |>.1
      have hEI := boundary_of_isTowerIso_id M hM.isWellFormed hi htOrig
      have hDI := (geometric_dictionary M hM.isWellFormed H htH S').2.1
      have hED : ((geoTransformAlong M ((H.step ∅ π hπ).append S)).E.map (χD ⁻¹' ·)).filter
          (fun H => decide H.Nonempty) =
          (geoTransformAlong M (H.append S')).E.filter (fun H => decide H.Nonempty) := by
        rw [← hEI,hDI,filter_nonempty_insert_empty]
      have hcomp : (geoTransformAlong M ((H.step ∅ π hπ).append S)).E.map
          ((χQ.trans χD) ⁻¹' ·) =
          ((geoTransformAlong M ((H.step ∅ π hπ).append S)).E.map (χD ⁻¹' ·)).map (χQ ⁻¹' ·) := by
        simp only [List.map_map]
        rfl
      rw [hcomp,filter_nonempty_map_preimage χQ χQ.surjective,hED,
        ← filter_nonempty_map_preimage χQ χQ.surjective]
      exact hEQ

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
theorem empty_free_compression_preserves_boundary (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X D)
    (hcan : IsCanonical M ((invFamily hn k).inv M) T) (O : Opens X)
    (hav : CentresAvoid O T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z)
      (χ : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D) (F : ValTy k ↪o ValTy k),
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
          Q.proj c ∈ O) ∧
      ((geoTransformAlong M T).E.map (χ ⁻¹' ·)).filter (fun H => decide H.Nonempty) =
        (geoTransformAlong M Q).E.filter (fun H => decide H.Nonempty) := by
  obtain ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha,hE⟩ := compression_with_boundary hn k M hM T hcan O hav
  have hmax := maxLocus_transport_orderEmbedding χ.symm.toEquiv F _ _ _ _ hs hv
  refine ⟨Z,Q,χ,F,hne,hle,hc,hp,hs,hv,ha,?_,hE⟩
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



/-- Any over-base comparison of genuine first-meeting prefixes preserves the
ordered boundary after deleting exactly its empty members. -/
theorem first_meeting_boundary_transport
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X D') (T : BlowupTower X D)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (O : Opens X) (ha' : CentresAvoid O T') (ha : CentresAvoid O T)
    (hm' : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T') (geoTransformAlong M T').cosupp,
      T'.proj c ∈ O)
    (hm : ∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp,
      T.proj c ∈ O)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (hη : ∀ z, T.proj (η z) = T'.proj z) :
    (geoTransformAlong M T').E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M T).E.map (η ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
  cases n with
  | zero =>
    have ht := (canonicalInvariant 0).isInvValue.isGeoTestTower_of_isCanonical hM T hc
    have he := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
    obtain ⟨c,hc,_⟩ := hm
    have hs := hc.1
    rw [he] at hs
    exact hs.elim
  | succ n =>
    obtain ⟨Z',Q',χ',F',hne',_hlen',hcQ',hp',_hs',_hv',haQ',hmQ',hE'⟩ :=
      empty_free_compression_preserves_boundary (Nat.succ_pos n) (n+1) M hM T' hc' O ha'
    obtain ⟨Z,Q,χ,F,hne,_hlen,hcQ,hp,_hs,_hv,haQ,hmQ,hE⟩ :=
      empty_free_compression_preserves_boundary (Nat.succ_pos n) (n+1) M hM T hc O ha
    have hseg' := isCanonicalSegment_of_actual_nonempty_centres M
      ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q' hcQ' hne'
    have hseg := isCanonicalSegment_of_actual_nonempty_centres M
      ((invFamily (Nat.succ_pos n) (n+1)).inv M) Q hcQ hne
    obtain ⟨_hlen,ψ,hi⟩ := first_meeting_nonempty_lengths_eq
      (invFamily (Nat.succ_pos n) (n+1)) M hM Q' Q hseg' hseg O haQ' haQ
        (hmQ'.mp hm') (hmQ.mp hm)
    let η₀ := (χ'.symm.trans ψ).trans χ
    have hη₀ : ∀ y, T.proj (η₀ y) = T'.proj y := by
      intro y
      change T.proj (χ (ψ (χ'.symm y))) = T'.proj y
      rw [hp]
      have hpi := hi.proj_comm (χ'.symm y)
      have hps := hp' (χ'.symm y)
      rw [χ'.apply_symm_apply] at hps
      exact hpi.symm.trans hps.symm
    have heq : η = η₀ := biholomorphisms_eq_of_actual_proj_eq T η η₀
      (fun y => (hη y).trans (hη₀ y).symm)
    rw [heq,filter_nonempty_map_preimage η₀ η₀.surjective]
    have hinj : Injective (fun H : Set D' => χ' ⁻¹' H) := by
      intro H K hHK
      ext z
      have hh := Set.ext_iff.mp hHK (χ'.symm z)
      simpa only [mem_preimage,χ'.apply_symm_apply] using hh
    apply List.map_injective_iff.mpr hinj
    have htQ := (invFamily (Nat.succ_pos n) (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM Q hcQ
    have hIsoE := boundary_of_isTowerIso_id M hM.isWellFormed hi htQ
    calc
      ((geoTransformAlong M T').E.filter (fun H => decide H.Nonempty)).map (χ' ⁻¹' ·) =
          (geoTransformAlong M Q').E.filter (fun H => decide H.Nonempty) := by
        rw [← filter_nonempty_map_preimage χ' χ'.surjective]
        exact hE'
      _ = ((geoTransformAlong M Q).E.filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
        rw [hIsoE,filter_nonempty_map_preimage ψ ψ.surjective]
      _ = (((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (χ ⁻¹' ·)).map
          (ψ ⁻¹' ·) := by
        rw [← filter_nonempty_map_preimage χ χ.surjective,hE]
      _ = (((geoTransformAlong M T).E.filter (fun H => decide H.Nonempty)).map (η₀ ⁻¹' ·)).map
          (χ' ⁻¹' ·) := by
        simp only [List.map_map]
        congr 1
        funext H
        ext z
        change χ (ψ z) ∈ H ↔ χ (ψ (χ'.symm (χ' z))) ∈ H
        rw [χ'.symm_apply_apply]



private theorem empty_history_boundary_members (M : MarkedIdeal n X) (hE : M.E = []) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower X D), IsEmptyTower T →
      ∀ H ∈ (geoTransformAlong M T).E, H = ∅
  | _, .refl, _, H, hH => by simp only [geoTransformAlong_refl,hE,List.not_mem_nil] at hH
  | _, .step T C π hπ, he, H, hH => by
    rcases he with ⟨heT,rfl⟩
    change H ∈ ((geoTransformAlong M T).geoTransform ∅ π).E at hH
    rw [geoTransform_E] at hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩ := List.mem_map.mp hH
      rw [empty_history_boundary_members M hE T heT K hK]
      simp [BlowupStrictSubmanifold.geoStrictTransform]
    · simpa only [List.mem_singleton,preimage_empty] using hH

private theorem empty_history_filtered_boundary (M : MarkedIdeal n X) (hE : M.E = [])
    (T : BlowupTower X D) (he : IsEmptyTower T) :
    (geoTransformAlong M T).E.filter (fun H => decide H.Nonempty) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro H hH
  obtain ⟨hm,hne⟩ := List.mem_filter.mp hH
  have heq := empty_history_boundary_members M hE T he H hm
  subst H
  simp at hne

private theorem exists_cartesian_endpoint_comparison {b : Y → X}
    {Q : BlowupTower Y E} {T : BlowupTower X D} {g : E → D}
    (hQ : IsActualTowerPullback b Q T g) (S : BlowupTower Y F) (G : F → D)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G)
    (hproj : ∀ z, T.proj (G z) = b (S.proj z))
    (hS : HolomorphicSquarePullback b G S.proj T.proj) :
    ∃ η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E,
      (∀ z, Q.proj (η z) = S.proj z) ∧ (∀ z, g (η z) = G z) := by
  obtain ⟨a,ha,_⟩ := hQ.universal m F S.proj G S.contMDiff_proj hG (fun z => (hproj z).symm)
  obtain ⟨c,hc,_⟩ := hS m E Q.proj g Q.contMDiff_proj hQ.isSubmersion.contMDiff
    (fun z => (hQ.proj_comm z).symm)
  have hca : c ∘ a = id :=
    (hS m F S.proj G S.contMDiff_proj hG (fun z => (hproj z).symm)).unique
      ⟨hc.1.comp ha.1,fun z => (hc.2.1 (a z)).trans (ha.2.1 z),
        fun z => (hc.2.2 (a z)).trans (ha.2.2 z)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  have hac : a ∘ c = id :=
    (hQ.universal m E Q.proj g Q.contMDiff_proj hQ.isSubmersion.contMDiff
      (fun z => (hQ.proj_comm z).symm)).unique
      ⟨ha.1.comp hc.1,fun z => (ha.2.1 (c z)).trans (hc.2.1 z),
        fun z => (ha.2.2 (c z)).trans (hc.2.2 z)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  let η : F ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E :=
    { toEquiv := ⟨a,c,fun z => congrFun hca z,fun z => congrFun hac z⟩
      contMDiff_toFun := ha.1
      contMDiff_invFun := hc.1 }
  exact ⟨η,ha.2⟩



/-- The actual own source boundary, up to exactly empty members, is forced
by any genuine Cartesian upper submersion for the same first-meeting maps. -/
theorem independent_stopped_square_boundary
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (T : BlowupTower X D)
    (hcT : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      ((canonicalInvariant n).inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (haT : CentresAvoid (regularOpen V) T)
    (hmT : ∃ c ∈ maxLocus ((canonicalInvariant n).inv
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp,
        T.proj c ∈ regularOpen V) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let N := markedPullback (m := m) b M
    let U : Opens Y := ⟨b ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage hb.contMDiff.continuous⟩
    ∀ (S : BlowupTower Y F), IsCanonical N ((canonicalInvariant m).inv N) S → CentresAvoid U S →
      ((b ⁻¹' V.carrier).Nonempty →
        ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S) (geoTransformAlong N S).cosupp, S.proj z ∈ U) →
      ∀ (G : F → D), Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G →
      (∀ z, T.proj (G z) = b (S.proj z)) → HolomorphicSquarePullback b G S.proj T.proj →
      (geoTransformAlong N S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
      ∀ (C : Set D), HasNormalCrossings n C (geoTransformAlong M T).E →
        HasNormalCrossings m (G ⁻¹' C) (geoTransformAlong N S).E := by
  dsimp only
  intro S hcS haS hmS G hG hproj hcart
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let N := markedPullback (m := m) b M
  let U : Opens Y := ⟨b ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage hb.contMDiff.continuous⟩
  let hM : IsInvDomain n M := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  let hN := original_ambient_domain_pullback hb M hM
  obtain ⟨E,Q,g,hQ⟩ := exists_actual_tower hb T
  obtain ⟨η,hη,hηG⟩ := exists_cartesian_endpoint_comparison hQ S G hG.contMDiff hproj hcart
  have htT := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hcT
  have hcQ := HironakaSmoothSubmersionOriginalAmbientCanonical.IsActualTowerPullback.original_ambient_canonical
    hQ M hM hcT
  have haQ : CentresAvoid U Q :=
    HironakaOriginalStoppedPrefixSmoothComparison.IsActualTowerPullback.centresAvoid_preimage
      hb hQ (regularOpen V) haT
  have hrecord := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    hQ M hM.isWellFormed htT).2
  have hEQ : (geoTransformAlong N Q).E = (geoTransformAlong M T).E.map (g ⁻¹' ·) :=
    congrArg MarkedIdeal.E hrecord
  have hEη : (geoTransformAlong N S).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong N Q).E.map (η ⁻¹' ·)).filter (fun H => decide H.Nonempty) := by
    by_cases hne : (b ⁻¹' V.carrier).Nonempty
    · have hmQ := source_maximum_meets_pulled_regular_open V hV hcoh hb hQ hcT haT hmT hne
      exact first_meeting_boundary_transport N hN S Q hcS hcQ U haS haQ (hmS hne) hmQ η hη
    · have hcos : N.cosupp = b ⁻¹' V.carrier := by
        have hh : N.cosupp = b ⁻¹' M.cosupp :=
          HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq hb hcoh M.N M.d
        rw [hh,SmoothCentreLocus.cosupp_vanishingIdeal V.isClosed_carrier (subset_univ _)]
      have hzero : N.cosupp = ∅ := hcos.trans (Set.not_nonempty_iff_eq_empty.mp hne)
      have heS := (canonical_histories_empty_of_original_cosupp_empty N hN hzero S hcS).1
      have heQ := (canonical_histories_empty_of_original_cosupp_empty N hN hzero Q hcQ).1
      have hNE : N.E = [] := rfl
      rw [empty_history_filtered_boundary N hNE S heS,
        filter_nonempty_map_preimage η η.surjective,empty_history_filtered_boundary N hNE Q heQ,List.map_nil]
  have hmaps : ((geoTransformAlong M T).E.map (g ⁻¹' ·)).map (η ⁻¹' ·) =
      (geoTransformAlong M T).E.map (G ⁻¹' ·) := by
    simp only [List.map_map]
    congr 1
    funext H
    ext z
    change g (η z) ∈ H ↔ G z ∈ H
    rw [hηG]
  rw [hEQ,hmaps] at hEη
  refine ⟨hEη,?_⟩
  intro C hNC
  apply (hasNormalCrossings_filter_nonempty_iff _ _).mp
  rw [hEη]
  exact (hasNormalCrossings_filter_nonempty_iff _ _).mpr
    (hasNormalCrossings_preimage_submersion hG hNC)


/-- The original independent stopped smooth source has normal crossings with its own actual boundary. -/
theorem exists_original_independently_stopped_smooth_source_own_boundary [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n)
    (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
    let hM := isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
    let P := compactCanonicalTower M hM
    let B := chosenActualTower defaultSmoothBlowupChoices hb P.2.val
    let N := markedPullback (m := m) b M
    let O := regularOpen V
    let U : Opens Y := ⟨b ⁻¹' (O : Set X), O.isOpen.preimage hb.contMDiff.continuous⟩
    ∃ (D₀ : CMfd.{u} n) (T : BlowupTower X D₀) (R : BlowupTower D₀ P.1)
      (E₀ : CMfd.{u} m) (S : BlowupTower Y E₀) (R' : BlowupTower E₀ B.1) (G : E₀ → D₀),
      HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' V.carrier)) (geoTransformAlong N S).E ∧
      (geoTransformAlong N S).E.filter (fun H => decide H.Nonempty) =
        ((geoTransformAlong M T).E.map (G ⁻¹' ·)).filter (fun H => decide H.Nonempty) ∧
      T.append R = P.2.val ∧ S.append R' = B.2.1 ∧
      IsCanonical M ((canonicalInvariant n).inv M) T ∧ CentresAvoid O T ∧
      (∃ c ∈ maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp, T.proj c ∈ O) ∧
      IsCanonical N ((canonicalInvariant m).inv N) S ∧ CentresAvoid U S ∧
      ((b ⁻¹' V.carrier).Nonempty →
        ∃ z ∈ maxLocus ((canonicalInvariant m).inv N S) (geoTransformAlong N S).cosupp, S.proj z ∈ U) ∧
      (¬ (b ⁻¹' V.carrier).Nonempty → S.length = 0 ∧ IsEmptyTower B.2.1) ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, T.proj (G z) = b (S.proj z)) ∧ HolomorphicSquarePullback b G S.proj T.proj ∧
      strictTransform m S.proj (b ⁻¹' V.carrier) = G ⁻¹' strictTransform n T.proj V.carrier ∧
      IsGeoTestTower N S ∧ IsSNCDivisor m (geoTransformAlong N S).E ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj V.carrier) ∧
      (∀ z ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) z V.dim) ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier) (geoTransformAlong M T).E ∧
      IsIsomorphismOver n T.proj (O : Set X) ∧
      IsClosedSubmanifold m (strictTransform m S.proj (b ⁻¹' V.carrier)) ∧
      (∀ z ∈ strictTransform m S.proj (b ⁻¹' V.carrier),
        RegularAtDim (n := m) (strictTransform m S.proj (b ⁻¹' V.carrier)) z (V.dim+(m-n))) ∧
      HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' V.carrier))
        ((geoTransformAlong M T).E.map (G ⁻¹' ·)) ∧
      CentresOver (b ⁻¹' singularLocus V) S ∧
      HironakaAdmissibleSequence.IsAdmissibleBlowupSequence m Y [] (b ⁻¹' singularLocus V)
        E₀ S.proj (geoTransformAlong N S).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ S.proj ∧
      IsProperMap S.proj ∧ Surjective S.proj ∧
      S.proj '' exceptionalLocus m S.proj ⊆ b ⁻¹' singularLocus V ∧
      IsIsomorphismOver m S.proj (U : Set Y) := by
  dsimp only
  obtain ⟨D₀,T,R,E₀,S,R',G,h⟩ := exists_original_independently_stopped_smooth_source V hV hcoh hb
  have hcopy := h
  rcases hcopy with ⟨hTR,hSR,hcT,haT,hmT,hcS,haS,hmS,heS,hG,hproj,hcart,hstrict,
    htS,hSNCS,hSNCT,hSMT,hrT,hNCT,hisoT,hSMS,hrS,hNCPull,hoverS,hadmS,hholS,
    hproperS,hsurjS,hExcS,hisoS⟩
  have hB := independent_stopped_square_boundary V hV hcoh hb T hcT haT hmT S hcS haS hmS
    G hG hproj hcart
  have hNC : HasNormalCrossings m (strictTransform m S.proj (b ⁻¹' V.carrier))
      (geoTransformAlong (markedPullback (m := m) b
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) S).E := by
    rw [hstrict]
    exact hB.2 _ hNCT
  exact ⟨D₀,T,R,E₀,S,R',G,hNC,hB.1,h⟩

end

end Hironaka.HironakaOriginalStoppedBoundaryTransport

import Hironaka.Resolution.HironakaNormalCrossingsLabelledPhasePreservation
import Hironaka.Blowup.BlowupTowerSplitIso

/-!
# Whole original labelled histories through genuine extension and append

Actual whole tower isomorphisms and actual split/restriction comparisons
retain the complete original labelled list and every current born position.
Blueprint: `hironaka-normal-crossings-labelled-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsLabelledHistoryExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerSplitIso BlowupTowerIsomorphism
  HomogenizedGlueingTower MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings NormalCrossingsInvariance
  HironakaNormalCrossingsLabelledBoundary HironakaNormalCrossingsLabelledBoundaryTransport
  HironakaNormalCrossingsLabelledPhasePreservation HironakaNormalCrossingsHighestPhasePermissions
  HironakaNormalCrossingsJointPermissionTransport RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X X' Y Y' Z : CMfd.{u} n}

theorem labelledNC_of_towerIso (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (L : List (Set X))
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (he : IsTowerIso Φ S T e) (hT : IsGeoTestTower M T)
    (hSource : IsNormalCrossingsBoundary (n:=n)
      ((L.map (Φ ⁻¹' ·)).map (strictAlong S)++(geoTransformAlong (MarkedIdeal.pullback Φ M) S).E)) :
    IsNormalCrossingsBoundary (n:=n) (L.map (strictAlong T)++(geoTransformAlong M T).E) := by
  have hLabels : (L.map (Φ ⁻¹' ·)).map (strictAlong S)=
      (L.map (strictAlong T)).map (e ⁻¹' ·) := by
    rw [List.map_map,List.map_map]
    apply List.map_congr_left
    intro A _hA
    exact he.strictAlong_eq A
  have hRecord:=IsTowerIso.geoTransformAlong_eq
    (𝔪:=M) (T':=S) (T:=T) (χ:=e) Φ hN hI he hT
  rw [hLabels,hRecord] at hSource
  have hPullback : IsNormalCrossingsBoundary (n:=n)
      ((L.map (strictAlong T)++(geoTransformAlong M T).E).map (e ⁻¹' ·)) := by
    simpa only [List.map_append,MarkedIdeal.pullback] using hSource
  exact (isNormalCrossingsBoundary_diffeomorph_iff e _).mp hPullback

private theorem labelledNC_of_identity_towerIso (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (L : List (Set X))
    (S : BlowupTower X Y') (T : BlowupTower X Y)
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) S T e)
    (hT : IsGeoTestTower M T)
    (hSource : IsNormalCrossingsBoundary (n:=n) (L.map (strictAlong S)++(geoTransformAlong M S).E)) :
    IsNormalCrossingsBoundary (n:=n) (L.map (strictAlong T)++(geoTransformAlong M T).E) := by
  apply labelledNC_of_towerIso M hN hI L (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) S T e he hT
  change IsNormalCrossingsBoundary (n:=n)
    ((L.map ((id : X→X) ⁻¹' ·)).map (strictAlong S)++
      (geoTransformAlong (MarkedIdeal.pullback (id : X→X) M) S).E)
  rw [ContactCanonicalAlong.pullback_id M hI]
  simpa only [preimage_id_eq,List.map_id] using hSource

private theorem restricted_labelled_list
    (M : MarkedIdeal n X) (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (L : List (Set X)) (U : Opens X) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    (L.map ((Subtype.val : U→X) ⁻¹' ·)).map (strictAlong (restrict U T))++
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X) M) (restrict U T)).E=
      (L.map (strictAlong T)++(geoTransformAlong M T).E).map
        ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) := by
  have hOld : (L.map ((Subtype.val : U→X) ⁻¹' ·)).map (strictAlong (restrict U T))=
      (L.map (strictAlong T)).map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) := by
    rw [List.map_map,List.map_map]
    apply List.map_congr_left
    intro A _hA
    exact strictAlong_restrict U T A
  rw [hOld,geoTransformAlong_restrict U hN hI T hT,List.map_append]
  rfl

theorem labelledNC_of_restrict_whole_cosupport
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    (U : Opens X) (hU : (⟨univ,E,I,d⟩ : MarkedIdeal n X).cosupp⊆U)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (hRestricted : IsNormalCrossingsBoundary (n:=n)
      ((L.map ((Subtype.val : U→X) ⁻¹' ·)).map (strictAlong (restrict U T))++
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X)
          (⟨univ,E,I,d⟩ : MarkedIdeal n X)) (restrict U T)).E)) :
    IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong T)++(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) T).E) := by
  let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
  have hM : M.IsWellFormed:=⟨isClosedSubmanifold_univ,hI,hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  have hClosed : ∀ A∈L.map (strictAlong T)++(geoTransformAlong M T).E,IsClosed A := by
    intro A hA
    rcases List.mem_append.mp hA with hOld|hBorn
    · obtain ⟨D,hD,rfl⟩:=List.mem_map.mp hOld
      exact isClosed_strictAlong T (h.1 D (List.mem_append_left _ hD))
    · exact hWF.isSNCDivisor.1 A hBorn
  apply isNormalCrossingsBoundary_of_open_traces hClosed
  intro y
  by_cases hy : T.proj y∈U
  · rw [restricted_labelled_list M isClosedSubmanifold_univ hI L U T hT] at hRestricted
    exact ⟨openPreimage T U,hy,hRestricted⟩
  · have hcos : IsClosed M.cosupp:=GiraudAlong.isClosed_cosupport_along hI isClosedSubmanifold_univ d
    let W : Opens X:=⟨M.cosuppᶜ,hcos.isOpen_compl⟩
    have hyW : T.proj y∈W:=fun hp=>hy (hU hp)
    have he : IsEmptyTower (restrict W T):=isEmptyTower_restrict_of_centresOver W
      (by exact disjoint_compl_left) T
      (HironakaAdmissibleSequence.centresOver_cosupp M isClosedSubmanifold_univ hI T hT)
    have hLocal:=isNormalCrossingsBoundary_open W h
    rw [List.map_append] at hLocal
    have hEW : IsSNCDivisor n (E.map ((Subtype.val : W→X) ⁻¹' ·)):=
      isSNCDivisor_map_preimage (pullsBackCoordinates_val W) continuous_subtype_val hE
    have hIW : (GermIdeal.pullback (m:=n) (Subtype.val : W→X) I).IsCoherent:=
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
    have hTW:=isGeoTestTower_restrict W isClosedSubmanifold_univ hI T hT
    let MW : MarkedIdeal n W:=⟨univ,E.map ((Subtype.val : W→X) ⁻¹' ·),
      GermIdeal.pullback (m:=n) (Subtype.val : W→X) I,d⟩
    have hMW : MW=MarkedIdeal.pullback (Subtype.val : W→X) M := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · exact preimage_univ.symm
      · rfl
      · rfl
      · rfl
    have hTW' : IsGeoTestTower MW (restrict W T):=by rw [hMW];exact hTW
    have hNC:=labelledNC_empty_test_history
      (GermIdeal.pullback (m:=n) (Subtype.val : W→X) I) hIW d hLocal hEW (restrict W T) hTW' he
    change IsNormalCrossingsBoundary (n:=n)
      ((L.map ((Subtype.val : W→X) ⁻¹' ·)).map (strictAlong (restrict W T))++
        (geoTransformAlong MW (restrict W T)).E) at hNC
    rw [hMW,restricted_labelled_list M isClosedSubmanifold_univ hI L W T hT] at hNC
    exact ⟨openPreimage T W,hyW,hNC⟩

theorem exists_labelled_history_extension
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    (hK : IsCompact (⟨univ,E,I,d⟩ : MarkedIdeal n X).cosupp)
    (U : Opens X) (hU : (⟨univ,E,I,d⟩ : MarkedIdeal n X).cosupp⊆U)
    (S : BlowupTower (CMfd.of (n:=n) U) Z)
    (hS : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U→X)
      (⟨univ,E,I,d⟩ : MarkedIdeal n X)) S)
    (hp : HasJointBranchPermissions (MarkedIdeal.pullback (Subtype.val : U→X)
      (⟨univ,E,I,d⟩ : MarkedIdeal n X)) ((Subtype.val : U→X) ⁻¹' (⋃ A∈L,A)) S)
    (hHeads : ∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
      ((L.map ((Subtype.val : U→X) ⁻¹' ·)).map (strictAlong (head S j))++
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X)
          (⟨univ,E,I,d⟩ : MarkedIdeal n X)) (head S j)).E)) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),
      IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) Q ∧
      HasJointBranchPermissions (⟨univ,E,I,d⟩ : MarkedIdeal n X) (⋃ A∈L,A) Q ∧
      (∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
        (L.map (strictAlong (head Q j))++
          (geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) (head Q j)).E)) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) S (restrict U Q) e := by
  let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
  let MU:=MarkedIdeal.pullback (Subtype.val : U→X) M
  let LU:=L.map ((Subtype.val : U→X) ⁻¹' ·)
  obtain ⟨Y,Q,hQ,hPerm,e,he⟩:=exists_extension_with_permissions M
    isClosedSubmanifold_univ hI hK (⋃ A∈L,A) U hU S hS hp
  have hNU : IsClosedSubmanifold n MU.N:=BlowupRestrictOpen.isClosedSubmanifold_preimage_val
    isClosedSubmanifold_univ U
  have hIU : MU.ideal.IsCoherent:=GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hQU : IsGeoTestTower MU (restrict U Q):=isGeoTestTower_restrict U isClosedSubmanifold_univ hI Q hQ
  refine ⟨Y,Q,hQ,hPerm,?_,e,he⟩
  intro j
  have hQj:=((isGeoTestTower_iff_head_tail M Q j).mp hQ).1
  obtain ⟨e₁,he₁,_htail⟩:=BlowupTowerSplitIso.IsTowerIso.exists_split he j
  have hQHU:=((isGeoTestTower_iff_head_tail MU (restrict U Q) j).mp hQU).1
  have hFirst:=labelledNC_of_identity_towerIso MU hNU hIU LU
    (head S j) (head (restrict U Q) j) e₁ he₁ hQHU (hHeads j)
  obtain ⟨e₂,he₂,_htail'⟩:=exists_isTowerIso_split_restrict U Q j
  have hSecond:=labelledNC_of_identity_towerIso MU hNU hIU LU
    (head (restrict U Q) j) (restrict U (head Q j)) e₂ he₂
    (isGeoTestTower_restrict U isClosedSubmanifold_univ hI (head Q j) hQj) hFirst
  exact labelledNC_of_restrict_whole_cosupport I hI d h hE U hU (head Q j) hQj hSecond

theorem labelledNC_append_heads (M : MarkedIdeal n X) (L : List (Set X)) (P : BlowupTower X Y)
    (hP : ∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong (head P j))++(geoTransformAlong M (head P j)).E)) :
    ∀ {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      (∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
        ((L.map (strictAlong P)).map (strictAlong (head Q j))++
          (geoTransformAlong (geoTransformAlong M P) (head Q j)).E)) →
      ∀ j : ℕ,IsNormalCrossingsBoundary (n:=n)
        (L.map (strictAlong (head (P.append Q) j))++
          (geoTransformAlong M (head (P.append Q) j)).E)
  | _,.refl,_,j => hP j
  | _,.step Q C π hπ,hQ,0 => by
    have h:=hQ 0
    change IsNormalCrossingsBoundary (n:=n)
      ((L.map (strictAlong P)).map (strictAlong (.step Q C π hπ))++
        (geoTransformAlong (geoTransformAlong M P) (.step Q C π hπ)).E) at h
    change IsNormalCrossingsBoundary (n:=n)
      (L.map (strictAlong (P.append (.step Q C π hπ)))++
        (geoTransformAlong M (P.append (.step Q C π hπ))).E)
    rw [geoTransformAlong_append]
    have hLabels : L.map (strictAlong (P.append (.step Q C π hπ)))=
        (L.map (strictAlong P)).map (strictAlong (.step Q C π hπ)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro A _hA
      exact MemberInterLocusAlong.strictAlong_append P A (.step Q C π hπ)
    rw [hLabels]
    exact h
  | _,.step Q _ _ _,hQ,j+1 => labelledNC_append_heads M L P hP Q (fun k=>hQ (k+1)) j

end
end Hironaka.HironakaNormalCrossingsLabelledHistoryExtension

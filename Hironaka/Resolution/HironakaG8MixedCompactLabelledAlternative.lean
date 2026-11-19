import Hironaka.Resolution.HironakaG8MixedSmoothCuspCentre
import Hironaka.Resolution.HironakaG8RestartedEmptyEpoch
import Hironaka.Resolution.HironakaG8LabelledNativeResolution

/-! # Empty-prefix stable obstruction and native HS-epoch replacement -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8MixedCompactLabelledAlternative
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres HironakaEmbeddedAnalytic HironakaStageCenters
  MarkedIdealBiholomorphism RegularAtDimTransport NonmonomialOrderLocal
  HironakaOriginalEmptyHeadPrefix HironakaG8RestartedEmptyEpoch
  HironakaOriginalBoundaryEmptyFilterComparison HironakaActualOpenEmbeddingVanishingIdeal
  HironakaG8InitialSmoothSpecialCentre HironakaG8MixedSmoothCuspCentre
  HironakaG8LabelledNativeResolution HironakaG8LabelledNativeHistory
  HironakaHolomorphicJetChartInvariance NormalCrossings
open ResolutionInvariantExt (IsEmptyTower)

private abbrev original {A : CMfd.{0} 3} (W : Set A) : MarkedIdeal 3 A :=
  ⟨univ,[],vanishingIdeal (n := 3) W,1⟩

private abbrev inv := canonicalInvariant 3

private theorem diffeo_nonexceptional {A B : CMfd.{0} 3}
    (β : B ≃ₘ⟮𝓘(ℂ,ComplexModel 3), 𝓘(ℂ,ComplexModel 3)⟯ A) (z : B) :
    z ∉ exceptionalLocus 3 β :=
  notMem_exceptionalLocus_of_inverse β.contMDiff β.symm.contMDiff
    β.apply_symm_apply β.symm_apply_apply z

private theorem strict_eq_of_empty {A B : CMfd.{0} 3} {W : Set A}
    (hW : IsClosed W) (H : BlowupTower A B)
    (β : B ≃ₘ⟮𝓘(ℂ,ComplexModel 3), 𝓘(ℂ,ComplexModel 3)⟯ A)
    (hβ : ∀ z, β z = H.proj z) : strictTransform 3 H.proj W = β ⁻¹' W := by
  have hExc : exceptionalLocus 3 β = ∅ := Set.eq_empty_iff_forall_notMem.mpr (diffeo_nonexceptional β)
  rw [← funext hβ,strictTransform,hExc,sdiff_empty,(hW.preimage β.continuous).closure_eq]

/-- The first occupied original canonical centre after any actual empty
leading tower contains the transported hypersurface point. It is regular
on the actual current strict transform. -/
theorem hypersurface_point_in_first_occupied_canonical_after_empty
    {A B C : CMfd.{0} 3} (W : Set A) (hW : IsClosed W)
    (hM : IsInvDomain 3 (original W))
    (hOrder : ∀ x ∈ W, nmOrd (original W) x = 1)
    (x : A) (hx : RegularAtDim (n := 3) W x 2)
    (H : BlowupTower A B) (he : IsEmptyTower H)
    (D : Set B) (hD : D.Nonempty) (π : C → B) (hπ : IsBlowupAlong 3 D π)
    (hCan : IsCanonical (original W) (inv.inv (original W)) (.step H D π hπ)) :
    ∃ z ∈ D, H.proj z = x ∧ RegularAtDim (n := 3) (strictTransform 3 H.proj W) z 2 := by
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection H he
  let z : B := β.symm x
  have hzx : β z = x := β.apply_symm_apply x
  have hStrict := strict_eq_of_empty hW H β hβ
  let W' := strictTransform 3 H.proj W
  let M' := original W'
  have hPull : MarkedIdealBiholomorphism.MarkedIdeal.pullback β (original W) = M' := by
    change (⟨β ⁻¹' (univ : Set A),[],GermIdeal.pullback (m := 3) β
      (vanishingIdeal (n := 3) W),1⟩ : MarkedIdeal 3 B) = M'
    rw [preimage_univ,pullback_vanishingIdeal_of_biholomorphism]
    exact congrArg original hStrict.symm
  have hMD := InvDomainTowerAlong.isInvDomain_pullback β hM
  rw [hPull] at hMD
  have hR : RegularAtDim (n := 3) W' z 2 := by
    rw [show W' = β ⁻¹' W from hStrict]
    exact regularAtDim_of_preimage β.contMDiff (diffeo_nonexceptional β z)
      isOpen_univ (mem_univ z) (fun _ _ => Iff.rfl) (hzx.symm ▸ hx)
  have hW' : IsClosed W' := by
    rw [show W' = β ⁻¹' W from hStrict]
    exact hW.preimage β.continuous
  have hCos : M'.cosupp = β ⁻¹' W :=
    (HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW' []).trans hStrict
  have hOrd' (a : B) (ha : a ∈ M'.cosupp) : nmOrd M' a = 1 := by
    rw [← hPull, nmOrd_pullback_diffeo (by decide : 0 < 3) β hM.isWellFormed hM.isNonzeroAlongAt]
    rw [hCos] at ha
    exact hOrder _ ha
  have hB := whole_record_on_empty_prefix W hW hM H he
  let S : BlowupTower B C := .step .refl D π hπ
  have hCanS : IsCanonical (geoTransformAlong (original W) H)
      (inv.inv (geoTransformAlong (original W) H)) S :=
    (canonical_empty_prefix_append_iff (original W) hM H he S).mp hCan
  have hFilter : nonemptyBoundary (geoTransformAlong (original W) H) = M' := by
    rw [hB]
    exact nonemptyBoundary_padded M' rfl H.length
  have hCan' : IsCanonical M' (inv.inv M') S := by
    have h := (isCanonical_nonemptyBoundary_iff (geoTransformAlong (original W) H) S).mpr hCanS
    rwa [hFilter] at h
  have hzD := initial_regular_hypersurface_in_canonical_centre
    (k := 2) (j := 2) (by decide : 0 < 3) M' hMD rfl rfl hOrd' z
    (AnalyticIrreducibleComponents.regularAtDim_univ z)
    (by rw [hCos, ← hStrict]; exact hR) D hD π hπ hCan'
  exact ⟨z,hzD,(hβ z).symm.trans hzx,hR⟩

/-- On a source with this hypersurface competitor, a conventional
canonical finite history with singular-only centres has only empties. -/
theorem only_empty_of_singular_only_mark_one_canonical
    {A B : CMfd.{0} 3} (W : Set A) (hW : IsClosed W)
    (hM : IsInvDomain 3 (original W))
    (hOrder : ∀ x ∈ W, nmOrd (original W) x = 1)
    (x : A) (hx : RegularAtDim (n := 3) W x 2)
    (T : BlowupTower A B)
    (hCan : IsCanonical (original W) (inv.inv (original W)) T)
    (hSing : StageCentres (fun P D => D ⊆ singularSet (n := 3) (strictTransform 3 P.proj W)) T) :
    IsEmptyTower T := by
  induction T with
  | refl => trivial
  | @step B C H D π hπ ih =>
    have he := ih hCan.1 hSing.1
    refine ⟨he,?_⟩
    by_contra hne
    have hD := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨z,hz,_,hReg⟩ := hypersurface_point_in_first_occupied_canonical_after_empty
      W hW hM hOrder x hx H he D hD π hπ hCan
    exact (mem_singularSet_iff.mp (hSing.2 hz)).2 2 hReg

/-- On an all-empty tower any source singularity still occurs over that
same source point on the current strict transform. -/
theorem singular_point_survives_all_empty
    {A B : CMfd.{0} 3} (W : Set A) (hW : IsClosed W)
    (T : BlowupTower A B) (he : IsEmptyTower T)
    {x : A} (hx : x ∈ singularSet (n := 3) W) :
    ∃ z ∈ singularSet (n := 3) (strictTransform 3 T.proj W), T.proj z = x := by
  obtain ⟨β,hβ⟩ := exists_empty_tower_projection T he
  have hS := strict_eq_of_empty hW T β hβ
  let z : B := β.symm x
  have hzx : β z = x := β.apply_symm_apply x
  refine ⟨z,?_,(hβ z).symm.trans hzx⟩
  rw [hS,mem_singularSet_iff]
  have hs := mem_singularSet_iff.mp hx
  refine ⟨show β z ∈ W from hzx.symm ▸ hs.1, fun j hReg => ?_⟩
  apply hs.2 j
  exact regularAtDim_of_preimage β.symm.contMDiff (diffeo_nonexceptional β.symm x)
    isOpen_univ (mem_univ x) (fun a _ => by change a ∈ W ↔ β (β.symm a) ∈ W; rw [β.apply_symm_apply])
    hReg

/-- Every conventional canonical, singular-only finite history over a
neighborhood retaining both task points has a strict-transform singularity
still lying over the cusp point. -/
theorem mixed_compact_task_singular_survivor_of_original_canonical
    (U : Opens X) (h0 : (0 : X) ∈ U) (hp : smoothPoint ∈ U)
    {Z : CMfd.{0} 3} (T : BlowupTower (CMfd.of (n := 3) U) Z) :
    let W := (Subtype.val : U → X) ⁻¹' source
    let P := original (A := CMfd.of (n := 3) U) W
    IsCanonical P (inv.inv P) T →
    StageCentres (fun H D => D ⊆ singularSet (n := 3) (strictTransform 3 H.proj W)) T →
    ∃ z ∈ singularSet (n := 3) (strictTransform 3 T.proj W), T.proj z = (⟨0,h0⟩ : U) := by
  intro W P hCan hStage
  have hEq : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M = P :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal U [] source
  have hPD := InvDomainTowerAlong.isInvDomain_pullback_val U source_domain
  rw [hEq] at hPD
  have hUniform (x : U) (hx : x ∈ W) : nmOrd P x = 1 := by
    rw [← hEq, nmOrd_pullback_val (by decide : 0 < 3)
      source_domain.isWellFormed source_domain.isNonzeroAlongAt U x]
    exact source_uniform_nonmonomial_order x.val (source_cosupport.symm ▸ hx)
  have hWC : IsClosed W := source_analytic.isClosed.preimage continuous_subtype_val
  have hReg : RegularAtDim (n := 3) W (⟨smoothPoint,hp⟩ : U) 2 :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr smoothPoint_regular_source
  have he := only_empty_of_singular_only_mark_one_canonical W hWC hPD hUniform _ hReg T hCan hStage
  apply singular_point_survives_all_empty W hWC T he
  rw [mem_singularSet_iff]
  have h := mem_singularSet_iff.mp origin_singular_source
  exact ⟨h.1, fun j hj => h.2 j (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hj)⟩

/-- The same compact task admits a finite physically singular-centred,
original-tested resolution with descending native HS labels and canonical
native terminal windows. The produced physical tower is exactly the one
carrying the labels and the smooth endpoint. It cannot be conventional
original mark-one canonical. -/
theorem exists_mixed_compact_task_labelled_original_test_resolution :
    let K : Set X := {0,smoothPoint}
    ∃ (U : Opens X), K ⊆ U ∧
      ∃ (Z : CMfd.{0} 3) (T : BlowupTower (CMfd.of (n := 3) U) Z) (L : List (ℕ → ℕ)),
      let W := (Subtype.val : U → X) ⁻¹' source
      let P := original (A := CMfd.of (n := 3) U) W
      LabelledNativeTower 3 W [] ((Subtype.val : U → X) ⁻¹' K) T L ∧
      L.Pairwise (fun H H' => toLex H' < toLex H) ∧
      IsGeoTestTower P T ∧
      StageCentres (fun H D => D ⊆ singularSet (n := 3) (strictTransform 3 H.proj W)) T ∧
      IsClosedSubmanifold 3 (strictTransform 3 T.proj W) ∧
      ¬ IsCanonical P (inv.inv P) T := by
  intro K
  have hK : IsCompact K := isCompact_singleton.insert _
  have hDense : source ⊆ closure (source \ ⋃ B ∈ ([] : List (Set X)), B) := by
    simpa using (subset_closure : source ⊆ closure source)
  obtain ⟨U,hU,Z,T,L,hT,_⟩ :=
    exists_labelled_native_resolution_near_compact (by decide : 0 < 3)
      source_analytic [] isSNCDivisor_nil hDense K hK
  have hStage := hT.test_and_singular
  have hSmooth := hT.target_smooth
  refine ⟨U,hU,Z,T,L,hT,hT.descending,hStage.1,hStage.2,hSmooth,?_⟩
  intro hCan
  obtain ⟨z,hz,_⟩ := mixed_compact_task_singular_survivor_of_original_canonical U
    (hU (by simp [K])) (hU (by simp [K])) T hCan hStage.2
  obtain ⟨j,hj⟩ := hSmooth.2 z ((mem_singularSet_iff.mp hz).1)
  exact (mem_singularSet_iff.mp hz).2 j hj

end
end Hironaka.HironakaG8MixedCompactLabelledAlternative

/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms
import Hironaka.Resolution.HironakaSharpActualCurveBirthBoundaryOverlaps

/-!
# The entire chronological boundary of the same actual locally finite history

All original positions and actual exceptional births, including empty members,
are retained. Each limit subset is independently defined by an intersection of
actual finite-stage pullbacks. A given history is not scheduler existence.
Blueprint: `hironaka-actual-locally-finite-boundary-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical Function
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualLocallyFiniteBoundary
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
  HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
  HironakaSharpActualCurveBirthBoundaryOverlaps
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryComparison HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryFactors
  HironakaActualLocallyFiniteLimitStrictTransforms
variable {n : ℕ} {X Y Z : CMfd.{u} n}
attribute [local instance] limitChartedSpace

private theorem strict_empty {C : Set Y} (π : Z → Y) :
    geoStrictTransform π C ∅=∅ := by
  simp [geoStrictTransform]

private theorem strict_empty_centre {H : Set Y} (hH : IsClosed H) {π : Z → Y}
    (hπ : Continuous π) : geoStrictTransform π ∅ H=π ⁻¹' H := by
  simpa only [geoStrictTransform,sdiff_empty] using (hH.preimage hπ).closure_eq

private theorem readout_map_strict (E : List (Set Y)) (C : Set Y) (π : Z → Y) (k : ℕ) :
    boundaryReadout (E.map (geoStrictTransform π C)) k=
      geoStrictTransform π C (boundaryReadout E k) := by
  simpa only [boundaryReadout,strict_empty] using
    List.getD_map E (∅ : Set Y) (geoStrictTransform π C)

/-- Closedness retains every genuine finite ordered boundary position. -/
theorem isClosed_boundaryReadout (M : MarkedIdeal n X)
    (hE : ∀ H∈M.E,IsClosed H) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (k : ℕ),
      IsClosed (boundaryReadout (geoTransformAlong M T).E k) := by
  suffices h : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ∀ H∈(geoTransformAlong M T).E,IsClosed H by
    intro Y T k
    by_cases hk : k<(geoTransformAlong M T).E.length
    · rw [boundaryReadout,List.getD_eq_getElem _ _ hk]
      exact h T _ (List.getElem_mem hk)
    · rw [boundaryReadout,List.getD_eq_default _ _ (Nat.le_of_not_gt hk)]
      exact isClosed_empty
  intro Y T
  induction T with
  | refl => exact hE
  | @step Y Z T C π hπ ih =>
    intro H hH
    change H∈(geoTransformAlong M T).E.map (geoStrictTransform π C)++[π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hH|hH
    · obtain ⟨B,_hB,rfl⟩ := List.mem_map.mp hH
      exact isClosed_closure
    · rw [List.mem_singleton.mp hH]
      exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- An original slot is the genuine centre-relative strict transform, not a total pullback. -/
theorem boundaryReadout_old_slot (M : MarkedIdeal n X) (k : ℕ) (hk : k<M.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      boundaryReadout (geoTransformAlong M T).E k=strictAlong T (boundaryReadout M.E k) := by
  intro Y T
  induction T with
  | refl => rfl
  | @step Y Z T C π hπ ih =>
    have hle : k<((geoTransformAlong M T).E.map (geoStrictTransform π C)).length := by
      rw [List.length_map,length_E_geoTransformAlong]
      omega
    change boundaryReadout ((geoTransformAlong M T).E.map (geoStrictTransform π C)++[π ⁻¹' C]) k=_
    rw [boundaryReadout,List.getD_append _ _ ∅ k hle]
    change boundaryReadout ((geoTransformAlong M T).E.map (geoStrictTransform π C)) k=_
    rw [readout_map_strict,ih,strictAlong_step]

private theorem boundary_empty_tower (M : MarkedIdeal n X)
    (hE : ∀ H∈M.E,IsClosed H) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      ResolutionInvariantExt.IsEmptyTower T →
      (geoTransformAlong M T).E=M.E.map (T.proj ⁻¹' ·)++List.replicate T.length ∅ := by
  intro Y T
  induction T with
  | refl => intro _;simp
  | @step Y Z T C π hπ ih =>
    rintro ⟨hT,rfl⟩
    rw [geoTransformAlong_step,geoTransform_E,ih hT,List.map_append,List.map_map,List.map_replicate]
    have hm : M.E.map (geoStrictTransform π ∅ ∘ (T.proj ⁻¹' ·))=
        M.E.map ((T.proj ∘ π) ⁻¹' ·) := by
      apply List.map_congr_left
      intro H hH
      exact strict_empty_centre ((hE H hH).preimage T.contMDiff_proj.continuous)
        hπ.contMDiff.continuous
    rw [hm,strict_empty,preimage_empty]
    simp only [BlowupTower.length_step,BlowupTower.proj_step,List.replicate_succ',List.append_assoc]

/-- Every position, including all empty births, pulls back along a genuine empty tower. -/
theorem boundaryReadout_empty_tower (M : MarkedIdeal n X)
    (hE : ∀ H∈M.E,IsClosed H) (T : BlowupTower X Y)
    (hT : ResolutionInvariantExt.IsEmptyTower T) (k : ℕ) :
    boundaryReadout (geoTransformAlong M T).E k=T.proj ⁻¹' boundaryReadout M.E k := by
  rw [boundary_empty_tower M hE T hT,boundaryReadout_append_empty,boundaryReadout_map_preimage]

/-- Actual one-step equalities, including stage zero, fix the entire prefix length. -/
theorem stage_length (s : GrowingSeq X) (j : ℕ) : (s.stage j).2.length=j := by
  induction j with
  | zero => exact congrArg (fun Q : Σ Y : CMfd.{u} n,BlowupTower X Y => Q.2.length) s.zero
  | succ j ih =>
    obtain ⟨π,hπ,hstep⟩ := exists_step_map s j
    rw [hstep,BlowupTower.length_step,ih]

/-- The limit family is an actual intersection of all sufficiently late finite readouts. -/
def limitBoundaryMember (M : MarkedIdeal n X) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (k : ℕ) : Set (limitManifold s hLF) :=
  ⋂ r : ℕ,stageFactor s hLF (k+1+r) ⁻¹' boundaryReadout (geoTransformAlong M (s.stage (k+1+r)).2).E k


/-- Genuine restriction and the actual empty tail compare EVERY full boundary position. -/
theorem mem_boundary_stage_of_empty_tail (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hT : ∀ j,IsGeoTestTower M (s.stage j).2)
    (N r : ℕ) (U : Opens X)
    (hEmpty : ResolutionInvariantExt.IsEmptyTower
      (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)))
    (k : ℕ) (z : (s.stage (N+r)).1)
    (hz : (tailTower s N r).proj z∈openPreimage (s.stage N).2 U) :
    z∈boundaryReadout (geoTransformAlong M (s.stage (N+r)).2).E k ↔
      (tailTower s N r).proj z∈boundaryReadout (geoTransformAlong M (s.stage N).2).E k := by
  let A := geoTransformAlong M (s.stage N).2
  let W := openPreimage (s.stage N).2 U
  let R := tailTower s N r
  let q : openPreimage R W := ⟨z,hz⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (s.stage N).2 (hT N)
  have htestR : IsGeoTestTower A R := by
    apply ((isGeoTestTower_append_iff M (s.stage N).2 R).mp ?_).2
    rw [append_tailTower]
    exact hT (N+r)
  have hClosed : ∀ H∈(MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : W → (s.stage N).1) A).E,IsClosed H := by
    intro H hH
    change H∈A.E.map ((Subtype.val : W → (s.stage N).1) ⁻¹' ·) at hH
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hH
    exact (hwA.isSNCDivisor.1 B hB).preimage continuous_subtype_val
  have he := boundaryReadout_empty_tower
    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → (s.stage N).1) A)
    hClosed (restrict W R) hEmpty k
  change boundaryReadout (geoTransformAlong _ (restrict W R)).E k=
    (restrict W R).proj ⁻¹' boundaryReadout (A.E.map ((Subtype.val : W → (s.stage N).1) ⁻¹' ·)) k at he
  rw [boundaryReadout_map_preimage,
    boundaryReadout_restrict A hwA.isClosedSubmanifold_N hwA.isCoherent W R htestR k] at he
  have hi := Set.ext_iff.mp he q
  change z∈boundaryReadout (geoTransformAlong A R).E k ↔
    ((restrict W R).proj q).val∈boundaryReadout A.E k at hi
  rw [proj_restrict] at hi
  have ha : geoTransformAlong M (s.stage (N+r)).2=geoTransformAlong A R := by
    rw [←append_tailTower s N r,geoTransformAlong_append]
  rw [←ha] at hi
  exact hi

/-- The whole independently defined family equals the SAME actual finite prefix in a stable window. -/
theorem localInclusion_preimage_limitBoundaryMember (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) (x : X) (k : ℕ) :
    (actualHistoryLocalInclusion s hLF x) ⁻¹' limitBoundaryMember M s hLF k=
      (Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
        boundaryReadout (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).E k := by
  ext q
  let N := stableIndex s hLF x
  let U := stableWindow s hLF x
  let z := actualHistoryLocalInclusion s hLF x q
  have hEmpty (r : ℕ) : ResolutionInvariantExt.IsEmptyTower
      (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)) :=
    (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
      (centresAvoid_tailTower s N U (stableWindow_avoids s hLF x) r)
  have hTail (r : ℕ) : (tailTower s N r).proj (stageFactor s hLF (N+r) z)=q.val := by
    have hh := congrFun (stageFactor_tail s hLF N r) z
    change (tailTower s N r).proj (stageFactor s hLF (N+r) z)=stageFactor s hLF N z at hh
    exact hh.trans (stableFactor_local s hLF x q)
  constructor
  · intro hq
    have hJ := mem_iInter.mp hq N
    change stageFactor s hLF (k+1+N) z∈
      boundaryReadout (geoTransformAlong M (s.stage (k+1+N)).2).E k at hJ
    have hJ' : stageFactor s hLF (N+(k+1)) z∈
        boundaryReadout (geoTransformAlong M (s.stage (N+(k+1))).2).E k := by
      have hh := hJ
      rw [Nat.add_comm (k+1) N] at hh
      exact hh
    have h := (mem_boundary_stage_of_empty_tail M hM s hT N (k+1) U (hEmpty _) k
      (stageFactor s hLF (N+(k+1)) z) (by rw [hTail];exact q.property)).mp hJ'
    rwa [hTail] at h
  · intro hq
    apply mem_iInter.mpr
    intro r
    let J := k+1+r
    have hL : stageFactor s hLF (N+J) z∈
        boundaryReadout (geoTransformAlong M (s.stage (N+J)).2).E k :=
      (mem_boundary_stage_of_empty_tail M hM s hT N J U (hEmpty J) k
        (stageFactor s hLF (N+J) z) (by rw [hTail];exact q.property)).mpr (by rw [hTail];exact hq)
    have hL' : stageFactor s hLF (J+N) z∈
        boundaryReadout (geoTransformAlong M (s.stage (J+N)).2).E k := by
      have hh := hL
      rw [Nat.add_comm N J] at hh
      exact hh
    have hk : k<(geoTransformAlong M (s.stage J).2).E.length := by
      rw [length_E_geoTransformAlong,stage_length]
      dsimp [J]
      omega
    have hDown : (tailTower s J N).proj (stageFactor s hLF (J+N) z)∈
        boundaryReadout (geoTransformAlong M (s.stage J).2).E k := by
      apply strictAlong_subset_preimage (tailTower s J N)
        (isClosed_boundaryReadout M hM.isSNCDivisor.1 (s.stage J).2 k)
      rw [←boundaryReadout_old_slot (geoTransformAlong M (s.stage J).2) k hk,
        ←geoTransformAlong_append,append_tailTower]
      exact hL'
    have hf := congrFun (stageFactor_tail s hLF J N) z
    change (tailTower s J N).proj (stageFactor s hLF (J+N) z)=stageFactor s hLF J z at hf
    change stageFactor s hLF J z∈boundaryReadout (geoTransformAlong M (s.stage J).2).E k
    rwa [hf] at hDown

/-- Every actual boundary member is closed by its entire defining intersection. -/
theorem isClosed_limitBoundaryMember (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (k : ℕ) :
    IsClosed (limitBoundaryMember M s hLF k) :=
  isClosed_iInter fun r =>
    (isClosed_boundaryReadout M hM.isSNCDivisor.1 (s.stage (k+1+r)).2 k).preimage
      (stageFactor_contMDiff s hLF (k+1+r)).continuous

/-- The TRUE stable chart misses EVERY later chronological index, including empty births. -/
theorem locallyFinite_limitBoundaryMember (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) : LocallyFinite (limitBoundaryMember M s hLF) := by
  intro z
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let V := range (actualHistoryLocalInclusion s hLF x)
  let b := M.E.length+(s.stage (stableIndex s hLF x)).2.length
  refine ⟨V,(actualHistoryLocalInclusion_openEmbedding s hLF x).isOpen_range.mem_nhds ⟨q,rfl⟩,?_⟩
  apply (Finset.range b).finite_toSet.subset
  intro k hk
  rw [Finset.mem_coe,Finset.mem_range]
  by_contra hlate
  obtain ⟨p,hp,⟨w,rfl⟩⟩ := hk
  have hw := Set.ext_iff.mp (localInclusion_preimage_limitBoundaryMember M hM s hLF hT x k) w
  have hm := hw.mp hp
  rw [boundaryReadout_geoTransformAlong_eq_empty M _ k (Nat.le_of_not_gt hlate)] at hm
  exact hm


private theorem isComplexAnalyticSubset_boundaryReadout {Q : CMfd.{u} n}
    (E : List (Set Q)) (hE : NormalCrossings.IsSNCDivisor n E) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (boundaryReadout E k) := by
  by_cases hk : k<E.length
  · have he : boundaryReadout E k=E.get ⟨k,hk⟩ := by
      exact List.getD_eq_getElem E ∅ hk
    rw [he]
    apply AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    refine ⟨hE.1 _ (List.get_mem E _),fun x hx => ?_⟩
    obtain ⟨S,_hS,hcard,_hinj⟩ := hE.2 x
    have hn : 0<n := by
      have hle : (S ⟨k,hk⟩).card≤n := by simpa using Finset.card_le_univ (S ⟨k,hk⟩)
      have hone := hcard ⟨k,hk⟩ hx
      omega
    exact (MonomialPart.isClosedSubmanifold_get hn hE ⟨k,hk⟩).2 x hx
  · rw [boundaryReadout,List.getD_eq_default E ∅ (Nat.le_of_not_gt hk)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨isClosed_empty,fun _ h => False.elim h⟩

/-- Analyticity follows from the internally produced SAME-prefix analytic member on each true window. -/
theorem isComplexAnalyticSubset_limitBoundaryMember (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (limitBoundaryMember M s hLF k) := by
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro z
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let U := limitWindow s hLF (stableWindow s hLF x)
  let e := stableWindowDiffeomorph s hLF x
  refine ⟨U,?_,?_⟩
  · change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x q)∈stableWindow s hLF x
    rw [gluedProjection_local]
    exact q.property
  · have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM
      (s.stage (stableIndex s hLF x)).2 (hT _)
    have hA : IsComplexAnalyticSubset (n := n)
        ((Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
          boundaryReadout (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).E k) :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
        (isComplexAnalyticSubset_boundaryReadout _ hw.isSNCDivisor k) _
    have he : (Subtype.val : U → limitManifold s hLF) ⁻¹' limitBoundaryMember M s hLF k=
        e.symm ⁻¹' ((Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
          boundaryReadout (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).E k) := by
      ext v
      have hh := Set.ext_iff.mp (localInclusion_preimage_limitBoundaryMember M hM s hLF hT x k) (e.symm v)
      have heval : actualHistoryLocalInclusion s hLF x (e.symm v)=v.val :=
        congrArg Subtype.val (e.apply_symm_apply v)
      change v.val∈limitBoundaryMember M s hLF k ↔
        (e.symm v).val∈boundaryReadout (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).E k
      change actualHistoryLocalInclusion s hLF x (e.symm v)∈limitBoundaryMember M s hLF k ↔
        (e.symm v).val∈boundaryReadout (geoTransformAlong M (s.stage (stableIndex s hLF x)).2).E k at hh
      rwa [heval] at hh
    rw [he]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage e.symm.contMDiff hA


/-- The support of the WHOLE constructed boundary is itself an actual closed analytic subset. -/
theorem isComplexAnalyticSubset_limitBoundarySupport (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) :
    IsComplexAnalyticSubset (n := n) (⋃ k : ℕ,limitBoundaryMember M s hLF k) :=
  HironakaCurveAnalyticPredicates.isComplexAnalyticSubset_iUnion_of_locallyFinite _
    (locallyFinite_limitBoundaryMember M hM s hLF hT)
    (isComplexAnalyticSubset_limitBoundaryMember M hM s hLF hT)

/-- The standard locally finite indexed boundary convention, with original indices retained. -/
def IsLocallyFiniteSNCDivisor (n : ℕ) {Q : CMfd.{u} n} {ι : Type v}
    (D : ι → Set Q) : Prop :=
  LocallyFinite D ∧ (∀ i,IsClosed (D i)) ∧
    ∀ x : Q,∃ S : ι → Finset (Fin n),
      NormalCrossings.IsCoordinateFamilyAt n D S x ∧
      (∀ i,x∈D i → (S i).card=1) ∧ Set.InjOn S {i | x∈D i}

private theorem lt_length_of_mem_readout {Q : Type u} (E : List (Set Q))
    {k : ℕ} {x : Q} (hx : x∈boundaryReadout E k) : k<E.length := by
  by_contra hk
  rw [boundaryReadout,List.getD_eq_default E ∅ (Nat.le_of_not_gt hk)] at hx
  exact hx

private theorem readout_get {Q : Type u} (E : List (Set Q)) (i : Fin E.length) :
    boundaryReadout E i.val=E.get i := List.getD_eq_getElem E ∅ i.isLt

private theorem locallyFinite_readout {Q : Type u} [TopologicalSpace Q] (E : List (Set Q)) :
    LocallyFinite (boundaryReadout E) := by
  intro x
  refine ⟨univ,Filter.univ_mem,?_⟩
  apply (Finset.range E.length).finite_toSet.subset
  intro k hk
  obtain ⟨y,hy,_hyU⟩ := hk
  exact Finset.mem_range.mpr (lt_length_of_mem_readout E hy)

/-- The genuine finite List SNC API and its whole natural-number indexed extension coincide. -/
theorem isLocallyFiniteSNCDivisor_boundaryReadout_iff {Q : CMfd.{u} n} (E : List (Set Q)) :
    IsLocallyFiniteSNCDivisor n (boundaryReadout E) ↔ NormalCrossings.IsSNCDivisor n E := by
  constructor
  · rintro ⟨_hlf,hclosed,hcoords⟩
    refine ⟨?_,?_⟩
    · intro H hH
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      rw [←readout_get E i]
      exact hclosed i.val
    · intro x
      obtain ⟨S,hA,hcard,hinj⟩ := hcoords x
      refine ⟨fun i => S i.val,?_,?_,?_⟩
      · exact NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hA Fin.val
          (fun i => (readout_get E i).symm) (fun _ => rfl)
      · intro i hi
        exact hcard i.val ((readout_get E i).symm ▸ hi)
      · intro i hi j hj hij
        exact Fin.ext (hinj ((Set.ext_iff.mp (readout_get E i) x).mpr hi) ((Set.ext_iff.mp (readout_get E j) x).mpr hj) hij)
  · intro hE
    refine ⟨locallyFinite_readout E,fun k => (isComplexAnalyticSubset_boundaryReadout E hE k).isClosed,?_⟩
    intro x
    obtain ⟨S,⟨Φ,hsrc,hzero,hcoord⟩,hcard,hinj⟩ := hE.2 x
    let A : ℕ → Finset (Fin n) := fun k => if hk : k<E.length then S ⟨k,hk⟩ else ∅
    refine ⟨A,⟨Φ,hsrc,hzero,?_⟩,?_,?_⟩
    · intro k hk y hy hyΦ
      have hlen := lt_length_of_mem_readout E hk
      have he := readout_get E ⟨k,hlen⟩
      have hp := hcoord ⟨k,hlen⟩ ((Set.ext_iff.mp he x).mp hk) hy hyΦ
      simpa only [A,dif_pos hlen,←he] using hp
    · intro k hk
      have hlen := lt_length_of_mem_readout E hk
      change (if h : k<E.length then S ⟨k,h⟩ else ∅).card=1
      rw [dif_pos hlen]
      exact hcard ⟨k,hlen⟩ ((Set.ext_iff.mp (readout_get E ⟨k,hlen⟩) x).mp hk)
    · intro i hi j hj hij
      have hilen := lt_length_of_mem_readout E hi
      have hjlen := lt_length_of_mem_readout E hj
      have hEq : S ⟨i,hilen⟩=S ⟨j,hjlen⟩ := by simpa only [A,dif_pos hilen,dif_pos hjlen] using hij
      exact congrArg Fin.val (hinj ((Set.ext_iff.mp (readout_get E ⟨i,hilen⟩) x).mp hi)
        ((Set.ext_iff.mp (readout_get E ⟨j,hjlen⟩) x).mp hj) hEq)

private theorem coordinates_of_open_diffeomorph {Q P : CMfd.{u} n} {ι : Type v}
    (U : Opens Q) (e : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (D : ι → Set Q) (S : ι → Finset (Fin n)) (q : P)
    (h : NormalCrossings.IsCoordinateFamilyAt n (fun i => (fun p : P => (e p).val) ⁻¹' D i) S q) :
    NormalCrossings.IsCoordinateFamilyAt n D S (e q).val := by
  have hq : NormalCrossings.IsCoordinateFamilyAt n
      (fun i => (fun p : P => (e p).val) ⁻¹' D i) S (e.symm (e q)) := by
    rwa [e.symm_apply_apply]
  have hc := NormalCrossingsInvariance.isCoordinateFamilyAt_of_preimage
    e.symm.contMDiff (MarkedIdealTowerTransport.notMem_exceptionalLocus e.symm (e q))
    isOpen_univ (mem_univ (e q)) (fun _ _ _ => Iff.rfl) hq
  have heq : (fun i => e.symm ⁻¹' ((fun p : P => (e p).val) ⁻¹' D i))=
      fun i => (Subtype.val : U → Q) ⁻¹' D i := by
    funext i
    ext p
    simp only [mem_preimage,e.apply_symm_apply]
  change NormalCrossings.IsCoordinateFamilyAt n
    (fun i => e.symm ⁻¹' ((fun p : P => (e p).val) ⁻¹' D i)) S (e q) at hc
  rw [heq] at hc
  exact NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff.mp hc

/-- Original well-formedness and the SAME actual test prefixes produce the whole limit SNC family. -/
theorem isLocallyFiniteSNCDivisor_limitBoundaryMember (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j,IsGeoTestTower M (s.stage j).2) :
    IsLocallyFiniteSNCDivisor n (limitBoundaryMember M s hLF) := by
  refine ⟨locallyFinite_limitBoundaryMember M hM s hLF hT,
    isClosed_limitBoundaryMember M hM s hLF,?_⟩
  intro z
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let N := stableIndex s hLF x
  let E := (geoTransformAlong M (s.stage N).2).E
  let B : List (Set (localEndpoint s hLF x)) :=
    E.map ((Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹' ·)
  have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (s.stage N).2 (hT N)
  have hB : NormalCrossings.IsSNCDivisor n B :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val _) continuous_subtype_val hw.isSNCDivisor
  have hFamily : boundaryReadout B=fun k =>
      (actualHistoryLocalInclusion s hLF x) ⁻¹' limitBoundaryMember M s hLF k := by
    funext k
    rw [boundaryReadout_map_preimage]
    exact (localInclusion_preimage_limitBoundaryMember M hM s hLF hT x k).symm
  obtain ⟨S,hcoord,hcard,hinj⟩ := ((isLocallyFiniteSNCDivisor_boundaryReadout_iff B).mpr hB).2.2 q
  rw [hFamily] at hcoord hcard hinj
  refine ⟨S,?_,hcard,hinj⟩
  exact coordinates_of_open_diffeomorph (limitWindow s hLF (stableWindow s hLF x))
    (stableWindowDiffeomorph s hLF x) (limitBoundaryMember M s hLF) S q hcoord

end
end Hironaka.HironakaActualLocallyFiniteBoundary

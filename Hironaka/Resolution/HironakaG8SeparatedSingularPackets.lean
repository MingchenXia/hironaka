import Hironaka.Resolution.HironakaG8ClosedNativeTestGlobalization

/-! Compact windows isolated by locally finite disjoint compact supports. -/

open Set TopologicalSpace

namespace Hironaka.HironakaG8SeparatedSingularPackets

theorem exists_open_compact_support_window
    {X ι : Type*} [TopologicalSpace X] [T2Space X] {S K : Set X}
    (hS : IsClosed S) (hK : IsCompact K) (F : ι → Set X)
    (hF : ∀ i, IsCompact (F i)) (hLF : LocallyFinite F)
    (hSep : ∀ ⦃i j⦄, i ≠ j → Disjoint (F i) (F j))
    (hCover : S ⊆ ⋃ i, F i) :
    ∃ O : Opens X, K ⊆ O ∧ IsCompact (S ∩ O) := by
  classical
  let R : Set ι := {i | (F i ∩ K).Nonempty}
  have hR : R.Finite := hLF.finite_nonempty_inter_compact hK
  let : Fintype R := hR.fintype
  let G := ⋃ i : R, F i
  have hG : IsCompact G := isCompact_iUnion (fun i : R => hF i)
  let H := ⋃ i : {i // i ∉ R}, F i
  have hH : IsClosed H :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun i => (hF i).isClosed)
  let O : Opens X := ⟨Hᶜ, hH.isOpen_compl⟩
  refine ⟨O, ?_, ?_⟩
  · intro x hx hxO
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxO
    exact i.property ⟨x, hi, hx⟩
  have hEq : S ∩ (O : Set X) = S ∩ G := by
    ext x
    constructor
    · rintro ⟨hx, hxO⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hx)
      have hiR : i ∈ R := by
        by_contra h
        exact hxO (mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩)
      exact ⟨hx, mem_iUnion.mpr ⟨⟨i, hiR⟩, hi⟩⟩
    · rintro ⟨hx, hxG⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxG
      refine ⟨hx, ?_⟩
      intro hxH
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxH
      have hij : i.val ≠ j.val := fun e => j.property (e ▸ i.property)
      exact disjoint_left.mp (hSep hij) hi hj
  rw [hEq, inter_comm]
  exact hG.inter_right hS

/-- Such a packet cover cannot split a noncompact connected component
of a closed support between several packets. -/
theorem exists_packet_containing_preconnected
    {X ι : Type*} [TopologicalSpace X] [T2Space X] {S : Set X}
    (hConn : IsPreconnected S) (hS : S.Nonempty) (F : ι → Set X)
    (hF : ∀ i, IsCompact (F i)) (hLF : LocallyFinite F)
    (hSep : ∀ ⦃i j⦄, i ≠ j → Disjoint (F i) (F j))
    (hCover : S ⊆ ⋃ i, F i) :
    ∃ i, S ⊆ F i := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hx)
  let H := ⋃ j : {j // j ≠ i}, F j
  have hH : IsClosed H :=
    (hLF.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => (hF j).isClosed)
  have hd : Disjoint (F i) H := by
    refine disjoint_left.mpr ?_
    intro z hz hzH
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzH
    exact disjoint_left.mp (hSep j.property.symm) hz hj
  have hs : S ⊆ F i ∪ H := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hCover hz)
    by_cases h : j = i
    · exact Or.inl (h ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, h⟩, hj⟩)
  refine ⟨i, ?_⟩
  intro y hy
  by_contra hyF
  have hUnion : S ⊆ (F i)ᶜ ∪ Hᶜ := by
    intro z hz
    by_cases hzF : z ∈ F i
    · exact Or.inr (fun hzH => disjoint_left.mp hd hzF hzH)
    · exact Or.inl hzF
  obtain ⟨z, hz, hzF, hzH⟩ := hConn (F i)ᶜ Hᶜ
    (hF i).isClosed.isOpen_compl hH.isOpen_compl hUnion
    ⟨y, hy, hyF⟩ ⟨x, hx, fun hxH => disjoint_left.mp hd hi hxH⟩
  exact (hs hz).elim hzF hzH

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic NormalCrossings HironakaStageCenters
  HironakaG8FiniteNativeTestServing HironakaG8GlobalNativeTestAssembly
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaG8IntrinsicSingularBlockSchedule
  HironakaResolutionSpaceLocal HironakaG8LocalPureFinish NormalCrossingsInvariance
  HironakaAdmissibleSequence HomogenizedGlueingTower RestrictEmptyTower

/-- The isolated compact packets supply the original physical footprint
law at every tested prefix. The whole union of packets may be noncompact. -/
theorem hasNativeFootprintExtensions_of_separated_packets
    {n : ℕ} {X : CMfd.{0} (n+1)} {ι : Type*} (W : Set X) (E : List (Set X))
    (F : ι → Set X) (hF : ∀ i, IsCompact (F i)) (hLF : LocallyFinite F)
    (hSep : ∀ ⦃i j⦄, i ≠ j → Disjoint (F i) (F j))
    (hCover : singularSet (n := n+1) W ⊆ ⋃ i, F i) :
    HasNativeFootprintExtensions W E := by
  intro Y P hP K hK
  let U := strictTransform (n+1) P.proj W
  let M : MarkedIdeal (n+1) X := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩
  let B := (geoTransformAlong M P).E
  have hp := actual_singular_history_original_regular_protection W hP.analytic P
    (intrinsic_stage_native_history W P hP.singular)
  have hU := hp.2.2.2.1
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hP.analytic,hP.snc,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hP.snc⟩
  have hB : IsSNCDivisor (n+1) B :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM P hP.tested).isSNCDivisor
  have hD := HironakaG8DenseBoundaryRestart.strict_transform_dense_off_accumulated_boundary
    hP.analytic E hP.snc hP.dense P hP.tested hP.singular
  let FY (i : ι) := P.proj ⁻¹' F i
  obtain ⟨O, hKO, hFO⟩ := exists_open_compact_support_window
    (isClosed_singularSet hU.isClosed) (hp.2.2.1.isCompact_preimage hK) FY
    (fun i => hp.2.2.1.isCompact_preimage (hF i))
    (hLF.preimage_continuous P.contMDiff_proj.continuous)
    (fun {i j} h => (hSep h).preimage P.proj) (by
      intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover (hp.2.2.2.2.2.1 hy))
      exact mem_iUnion.mpr ⟨i,hi⟩)
  let G := singularSet (n := n+1) U ∩ (O : Set Y)
  let UO := (Subtype.val : O → Y) ⁻¹' U
  let EO := B.map ((Subtype.val : O → Y) ⁻¹' ·)
  have hUO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hU O
  have hEO := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hB
  have hDO := dense_complement_restrict U B hD O
  have hEq : singularSet (n := n+1) UO = (Subtype.val : O → Y) ⁻¹' G := by
    rw [show UO = (Subtype.val : O → Y) ⁻¹' U from rfl, singularSet_preimage_val]
    ext x
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hCap : IsCompact (singularSet (n := n+1) UO) := by
    rw [hEq]
    exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun x hx => ⟨⟨x,hx.2⟩,rfl⟩)).mpr hFO
  obtain ⟨Z,S,hS,hSmooth,_⟩ := global_native_test_of_compact_singular (X := CMfd.of (n := n+1) O) UO hUO EO hEO hDO hCap
  refine ⟨O,hKO,G,hFO,fun _ h => h.2,Z,S,hS,?_,?_⟩
  · rw [← hEq]
    let A := singularSet (n := n+1) UO
    let V : Opens O := ⟨Aᶜ,(isClosed_singularSet hUO.isClosed).isOpen_compl⟩
    have hAvoid := intrinsic_singular_history_avoids_regular_open hUO V
      disjoint_compl_right S hS.singular
    have h := centresOver_compl_of_centresAvoid V S hAvoid
    change CentresOver Aᶜᶜ S at h
    rwa [compl_compl] at h
  · refine disjoint_left.mpr ?_
    intro z _ hz
    obtain ⟨hzW,hzSing⟩ := mem_singularSet_iff.mp hz
    obtain ⟨k,hk⟩ := hSmooth.2 z hzW
    exact hzSing k hk

end Hironaka.HironakaG8SeparatedSingularPackets

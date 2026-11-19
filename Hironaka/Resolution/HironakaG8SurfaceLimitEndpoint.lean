import Hironaka.Resolution.HironakaG8SurfaceGlobalScheduler
import Hironaka.Resolution.HironakaActualLimitCarrierGeometry
import Hironaka.Resolution.HironakaActualSmoothBoundaryCleanup
import Hironaka.Resolution.HironakaG4CompactComponentLimit
set_option autoImplicit false
open Set Filter Classical TopologicalSpace Function
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SurfaceLimitEndpoint
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8IntrinsicSingularBlockSchedule
  HironakaG8SurfaceSingularPhase HironakaG8SurfaceGlobalScheduler HironakaActualSmoothBoundaryCleanup
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryFactors HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaActualLocallyFiniteHistoryOverlap HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq HomogenizedGlueingTower
  HironakaG4CompactComponentLimit HironakaActualLimitProtectedOpen HironakaAdmissibleSequence
attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- A literal suffix of a singular-centred tower has singular centres for the
actual current carrier. -/
theorem intrinsic_stage_tail {n : ℕ} {X Y Z : CMfd.{0} n}
    (W : Set X) (T : BlowupTower X Y) (S : BlowupTower Y Z)
    (h : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (T.append S)) :
    StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj (strictTransform n T.proj W))) S := by
  induction S with
  | refl => trivial
  | @step A B S C π hπ ih =>
    refine ⟨ih h.1,?_⟩
    have heq := StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj W
    rw [← BlowupTower.proj_append] at heq
    change C ⊆ singularSet (n := n) (strictTransform n S.proj (strictTransform n T.proj W))
    rw [← heq]
    exact h.2

/-- On any such physical history, iterated centre-relative strict transforms
coincide with the strict transform under the actual whole projection. -/
theorem intrinsic_strictAlong_eq {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (T : BlowupTower X Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    strictAlong T W = strictTransform n T.proj W := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hDense : W ⊆ closure (W ∩ (O : Set X)) := by
    change W ⊆ closure (W ∩ (singularSet (n := n) W)ᶜ)
    simpa only [Set.sdiff_eq] using HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hp := actual_singular_history_original_regular_protection W hW T (intrinsic_stage_native_history W T hStage)
  exact strictAlong_eq_library_of_avoid W hW.isClosed O hDense T hp.1
/-- Regularity over a base open persists through every later actual stage. -/
theorem intrinsic_stage_regular_later {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (s : GrowingSeq X)
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (N : ℕ) (U : Opens X)
    (hReg : Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
      ((s.stage N).2.proj ⁻¹' (U : Set X))) (r : ℕ) :
    Disjoint (singularSet (n := n) (strictTransform n (s.stage (N+r)).2.proj W))
      ((s.stage (N+r)).2.proj ⁻¹' (U : Set X)) := by
  let T := (s.stage N).2
  let R := tailTower s N r
  have hAppend : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (T.append R) := by
    rw [append_tailTower]
    exact hStage (N+r)
  have hTail := intrinsic_stage_tail W T R hAppend
  have hCurrent := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  have hp := intrinsic_singular_disjoint_persists hCurrent (T.proj ⁻¹' (U : Set X)) hReg R hTail
  rw [← StrictTransformComposition.strictTransform_comp T.contMDiff_proj R.contMDiff_proj W,
    ← BlowupTower.proj_append] at hp
  have heq := append_tailTower s N r
  rw [heq] at hp
  rw [← preimage_comp, ← BlowupTower.proj_append, heq] at hp
  exact hp

/-- Eventual finite-stage regularity on a base cover gives smoothness of the
independently defined physical limit strict transform. -/
theorem intrinsic_limit_strictTransform_smooth {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (hRegular : ∀ x : X, ∃ (U : Opens X) (N : ℕ), x ∈ U ∧
      Disjoint (singularSet (n := n) (strictTransform n (s.stage N).2.proj W))
        ((s.stage N).2.proj ⁻¹' (U : Set X))) :
    IsClosedSubmanifold n (limitStrictTransform s hLF W) := by
  refine ⟨isClosed_limitStrictTransform s hLF hW.isClosed,?_⟩
  intro z hz
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
  let N := stableIndex s hLF x
  let p := actualHistoryLocalInclusion s hLF x q
  let b := (s.stage N).2.proj q.val
  obtain ⟨U,j,hbU,hReg⟩ := hRegular b
  have hRegLater := intrinsic_stage_regular_later W hW s hStage j U hReg N
  let y := stageFactor s hLF (N+j) p
  have hBase : (s.stage (N+j)).2.proj y = b := by
    have hy := stageFactor_projection s hLF (N+j) p
    have hN := stageFactor_projection s hLF N p
    rw [stableFactor_local] at hN
    exact hy.trans hN.symm
  have hyU : (s.stage (N+j)).2.proj y ∈ U := hBase.symm ▸ hbU
  have hRegLater' : Disjoint (singularSet (n := n) (strictTransform n (s.stage (N+j)).2.proj W))
      ((s.stage (N+j)).2.proj ⁻¹' (U : Set X)) := by
    rw [Nat.add_comm j N] at hRegLater
    exact hRegLater
  have hyNot : y ∉ singularSet (n := n) (strictTransform n (s.stage (N+j)).2.proj W) :=
    fun hy => disjoint_left.mp hRegLater' hy hyU
  have hyAlong : y ∈ strictAlong (s.stage (N+j)).2 W := mem_iInter.mp hz (N+j)
  have heq := intrinsic_strictAlong_eq W hW (s.stage (N+j)).2 (hStage (N+j))
  have hyStrict : y ∈ strictTransform n (s.stage (N+j)).2.proj W := heq ▸ hyAlong
  obtain ⟨d,hd⟩ : ∃ d, RegularAtDim (n := n) (strictTransform n (s.stage (N+j)).2.proj W) y d := by
    by_contra h
    exact hyNot (mem_singularSet_iff.mpr ⟨hyStrict,fun d hd => h ⟨d,hd⟩⟩)
  let R := tailTower s N j
  have hTail : R.proj y = q.val := by
    have hh := congrFun (stageFactor_tail s hLF N j) p
    change R.proj y = stageFactor s hLF N p at hh
    rw [stableFactor_local] at hh
    exact hh
  have hAvoid := centresAvoid_tailTower s N (stableWindow s hLF x) (stableWindow_avoids s hLF x) j
  have hNoExc : y ∉ exceptionalLocus n R.proj := by
    apply EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid
      (openPreimage (s.stage N).2 (stableWindow s hLF x)) R hAvoid y
    change (s.stage N).2.proj (R.proj y) ∈ stableWindow s hLF x
    rw [hTail]
    exact q.property
  have hEq : strictTransform n (s.stage (N+j)).2.proj W =
      strictTransform n R.proj (strictAlong (s.stage N).2 W) := by
    rw [intrinsic_strictAlong_eq W hW (s.stage N).2 (hStage N)]
    rw [← StrictTransformComposition.strictTransform_comp (s.stage N).2.contMDiff_proj R.contMDiff_proj W,
      ← BlowupTower.proj_append, append_tailTower]
  rw [hEq] at hd
  have hClosed := (isComplexAnalyticSubset_strictAlong hW (s.stage N).2).isClosed
  have hOld := (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus R.contMDiff_proj hClosed hNoExc d).mp hd
  rw [hTail] at hOld
  exact ⟨d,(regularAtDim_limitStrictTransform_local_iff s hLF hW.isClosed x q d).mpr hOld⟩

/-- The recorded limit transform is the actual strict transform for the same
proper limit projection when the history is singular-centred. -/
theorem intrinsic_limit_strictTransform_eq_projection {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2)
    (hIso : IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ) :
    limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  let R : Set (limitManifold s hLF) := (gluedProjection s hLF) ⁻¹' (W \ singularSet (n := n) W)
  have hDense : W ⊆ closure (W \ singularSet (n := n) W) :=
    HironakaResolutionSpace.subset_closure_diff_singularSet hW
  have hLClosed := isClosed_limitStrictTransform s hLF hW.isClosed
  have hRinL : R ⊆ limitStrictTransform s hLF W := by
    intro z hz
    apply mem_iInter.mpr
    intro i
    let T := (s.stage i).2
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T (hStage i))
    have hBase := stageFactor_projection s hLF i z
    have hyO : T.proj (stageFactor s hLF i z) ∈ O := by
      change T.proj (stageFactor s hLF i z) ∉ singularSet (n := n) W
      rw [hBase]
      exact hz.2
    have hyW : T.proj (stageFactor s hLF i z) ∈ W := by rw [hBase]; exact hz.1
    have hy := (EmbeddedFromResolution.mem_strictTransform_iff_of_centresAvoid O T hp.1 hW.isClosed hyO).mpr hyW
    rw [intrinsic_strictAlong_eq W hW T (hStage i)]
    exact hy
  have hLinClosure : limitStrictTransform s hLF W ⊆ closure R := by
    intro z hz
    obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective s hLF z
    let N := stableIndex s hLF x
    let T := (s.stage N).2
    let A := strictTransform n T.proj W
    have hq : q.val ∈ A := by
      have hh := (Set.ext_iff.mp (localInclusion_preimage_limitStrictTransform s hLF hW.isClosed x) q).mp hz
      change q.val ∈ strictAlong T W at hh
      rwa [intrinsic_strictAlong_eq W hW T (hStage N)] at hh
    have hA := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hW.isClosed hDense
    have hQ : q ∈ closure ((Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹'
        (A \ T.proj ⁻¹' singularSet (n := n) W)) := by
      apply (openPreimage T (stableWindow s hLF x)).isOpen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_subset_closure_preimage
      exact hA hq
    apply map_mem_closure (localInclusion_contMDiff s hLF x).continuous hQ
    intro v hv
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x v) ∈ W \ singularSet (n := n) W
    rw [gluedProjection_local]
    exact ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hv.1,hv.2⟩
  have hLeq : limitStrictTransform s hLF W = closure R :=
    subset_antisymm hLinClosure (closure_minimal hRinL hLClosed)
  have hRinStrict : R ⊆ strictTransform n (gluedProjection s hLF) W := by
    intro z hz
    apply subset_closure
    refine ⟨hz.1,?_⟩
    exact fun he => disjoint_left.mp hIso.2 hz.2 he
  have hStrictInClosure : strictTransform n (gluedProjection s hLF) W ⊆ closure R := by
    have h := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff
      (gluedProjection_contMDiff s hLF) hW.isClosed hDense
    apply h.trans
    apply closure_mono
    intro z hz
    exact ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage
      (gluedProjection_contMDiff s hLF).continuous hW.isClosed hz.1,hz.2⟩
  exact hLeq.trans (subset_antisymm (closure_minimal hRinStrict isClosed_closure) hStrictInClosure)

/-- Every singular-centred locally finite history is an isomorphism over the
original regular open, for the same physical glued projection. -/
theorem intrinsic_limit_regular_open_iso {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s))
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) (s.stage i).2) :
    IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  have hOver : ∀ i, CentresOver (singularSet (n := n) W) (s.stage i).2 := by
    intro i
    let O : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
    have hp := actual_singular_history_original_regular_protection W hW (s.stage i).2
      (intrinsic_stage_native_history W (s.stage i).2 (hStage i))
    have h := centresOver_compl_of_centresAvoid O (s.stage i).2 hp.1
    change CentresOver ((singularSet (n := n) W)ᶜ)ᶜ (s.stage i).2 at h
    simpa only [compl_compl] using h
  have hImage := centreImage_subset_of_stage_support s (singularSet (n := n) W) hOver
  exact gluedProjection_isIsomorphismOver_compl_of_centreImages_subset s hLF _ hImage

/-- The internally scheduled surface history either terminates finitely or has
a proper holomorphic physical limit with smooth recorded strict transform. -/
theorem surface_singular_resolution_finite_or_proper_limit {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : NormalCrossings.IsSNCDivisor 2 E) :
    (∃ (Y : CMfd.{0} 2) (T : BlowupTower X Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) T ∧
      IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) T ∧
      IsClosedSubmanifold 2 (strictTransform 2 T.proj W) ∧
      IsIsomorphismOver 2 T.proj (singularSet (n := 2) W)ᶜ) ∨
    ∃ (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)),
      (∀ i, IsGeoTestTower (⟨univ,E,vanishingIdeal (n := 2) W,1⟩ : MarkedIdeal 2 X) (s.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj W)) (s.stage i).2) ∧
      IsClosedSubmanifold 2 (limitStrictTransform s hLF W) ∧
      limitStrictTransform s hLF W = strictTransform 2 (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver 2 (gluedProjection s hLF) (singularSet (n := 2) W)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞ (gluedProjection s hLF) := by
  obtain ⟨K,hK,U,hU,hCover,hResult⟩ := surface_exists_intrinsic_singular_service_schedule W hW E hE
  rcases hResult with hFinite | hInfinite
  · obtain ⟨a,hStable,hTest,hStage,hEmpty⟩ := hFinite
    let T := (HironakaExhaustionBlockLocalFiniteness.blockEndpoints (surfaceNext W hW K hK) a).2
    have hp := actual_singular_history_original_regular_protection W hW T
      (intrinsic_stage_native_history W T hStage)
    exact Or.inl ⟨_,T,hStage,hTest,hp.2.2.2.2.2.2.mp hEmpty,hp.2.1⟩
  · obtain ⟨s,hBoundary,hTest,hStage,hLF,hEmpty⟩ := hInfinite
    have hWindow := surface_scheduled_sequence_regular W hW K hK U hU s hBoundary
    have hReg : ∀ x : X, ∃ (V : Opens X) (N : ℕ), x ∈ V ∧
        Disjoint (singularSet (n := 2) (strictTransform 2 (s.stage N).2.proj W))
          ((s.stage N).2.proj ⁻¹' (V : Set X)) := by
      intro x
      obtain ⟨a,ha⟩ := hCover x
      obtain ⟨N,hN⟩ := hWindow a
      exact ⟨U a,N,ha,hN⟩
    have hIso := intrinsic_limit_regular_open_iso W hW s hLF hStage
    exact Or.inr ⟨s,hLF,hTest,hStage,intrinsic_limit_strictTransform_smooth W hW s hLF hStage hReg,
      intrinsic_limit_strictTransform_eq_projection W hW s hLF hStage hIso,
      gluedProjection_isProperMap s hLF,hIso,gluedProjection_contMDiff s hLF⟩

/-- A proper map that is an isomorphism off the original singular set is
surjective: that complement is dense. -/
theorem proper_regular_open_iso_surjective {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (π : Y → X) (hProper : IsProperMap π)
    (hIso : IsIsomorphismOver n π (singularSet (n := n) W)ᶜ) : Surjective π := by
  have hInterior : interior (singularSet (n := n) W) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxW : x ∈ interior W := interior_mono (singularSet_subset W) hx
    exact disjoint_left.mp (HironakaResolutionSpace.disjoint_interior_singularSet W) hxW (interior_subset hx)
  have hDense : Dense ((singularSet (n := n) W)ᶜ) := interior_eq_empty_iff_dense_compl.mp hInterior
  have hClosed : IsClosed (range π) := by
    simpa only [image_univ] using hProper.isClosedMap univ isClosed_univ
  have hSub : (singularSet (n := n) W)ᶜ ⊆ range π := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hIso.1.2.2 hx
    exact ⟨y,he⟩
  have hAll : univ ⊆ range π := by
    rw [← hDense.closure_eq]
    exact closure_minimal hSub hClosed
  intro x
  exact hAll (mem_univ x)

/-- A smooth strict transform and regular-open isomorphism identify the
whole exceptional locus with the preimage of the original singular locus. -/
theorem exceptionalLocus_eq_singular_preimage {n : ℕ} {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (π : Y → X)
    (hHolo : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (hIso : IsIsomorphismOver n π (singularSet (n := n) W)ᶜ)
    (hSmooth : IsClosedSubmanifold n (strictTransform n π W)) :
    exceptionalLocus n π = π ⁻¹' singularSet (n := n) W := by
  apply subset_antisymm
  · intro y hy
    by_contra h
    exact disjoint_left.mp hIso.2 h hy
  · exact preimage_singularSet_subset_exceptionalLocus hHolo hW hSmooth

/-- A complex-surface analytic set admits a proper holomorphic singular
resolution which is an isomorphism over its original regular locus. -/
theorem surface_proper_singular_resolution {X : CMfd.{0} 2}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := 2) W)
    (E : List (Set X)) (hE : NormalCrossings.IsSNCDivisor 2 E) :
    ∃ (Y : CMfd.{0} 2) (π : Y → X), IsProperMap π ∧ Surjective π ∧
      ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞ π ∧
      IsIsomorphismOver 2 π (singularSet (n := 2) W)ᶜ ∧
      IsClosedSubmanifold 2 (strictTransform 2 π W) ∧
      exceptionalLocus 2 π = π ⁻¹' singularSet (n := 2) W := by
  rcases surface_singular_resolution_finite_or_proper_limit W hW E hE with hFinite | hInfinite
  · obtain ⟨Y,T,hStage,hTest,hSmooth,hIso⟩ := hFinite
    exact ⟨Y,T.proj,HironakaLocalPrincipalization.isProperMap_proj T,
      proper_regular_open_iso_surjective W T.proj (HironakaLocalPrincipalization.isProperMap_proj T) hIso,
      T.contMDiff_proj,hIso,hSmooth,exceptionalLocus_eq_singular_preimage W hW.isClosed T.proj T.contMDiff_proj hIso hSmooth⟩
  · obtain ⟨s,hLF,hTest,hStage,hSmooth,hEq,hProper,hIso,hHolo⟩ := hInfinite
    let Y := CMfd.of (n := 2) (limitManifold s hLF)
    exact ⟨Y,gluedProjection s hLF,hProper,proper_regular_open_iso_surjective W _ hProper hIso,
      hHolo,hIso,hEq ▸ hSmooth,exceptionalLocus_eq_singular_preimage W hW.isClosed _ hHolo hIso (hEq ▸ hSmooth)⟩

/-- Analytic sets in ambient dimension at most one are already smooth. -/
theorem low_ambient_dimension_analytic_smooth {n : ℕ} (hn : n ≤ 1) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) : IsClosedSubmanifold n W := by
  have hEmpty : singularSet (n := n) W = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hA := HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hW
    obtain ⟨y,_,d,hy⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds hA hx univ_mem
    have hd := HironakaGeneralSingularCentreCodimension.regular_intrinsic_singular_centre_add_two_le
      hW subset_rfl hy
    omega
  refine ⟨hW.isClosed,?_⟩
  intro x hx
  by_contra h
  have hxS : x ∈ singularSet (n := n) W := mem_singularSet_iff.mpr ⟨hx,fun d hd => h ⟨d,hd⟩⟩
  rw [hEmpty] at hxS
  exact hxS

/-- Proper singular resolution in ambient dimensions zero, one and two. -/
theorem low_ambient_dimension_proper_singular_resolution {n : ℕ} (hn : n ≤ 2) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ (Y : CMfd.{0} n) (π : Y → X), IsProperMap π ∧ Surjective π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      exceptionalLocus n π = π ⁻¹' singularSet (n := n) W := by
  by_cases hn1 : n ≤ 1
  · refine ⟨X,id,isProperMap_id,surjective_id,contMDiff_id,?_,?_⟩
    · exact ⟨bijOn_id _,by rw [exceptionalLocus_id]; exact disjoint_empty _⟩
    · have hSmooth := low_ambient_dimension_analytic_smooth hn1 W hW
      have hIso : IsIsomorphismOver n (id : X → X) (singularSet (n := n) W)ᶜ :=
        ⟨bijOn_id _,by rw [exceptionalLocus_id]; exact disjoint_empty _⟩
      have hStrict : IsClosedSubmanifold n (strictTransform n (id : X → X) W) := by
        rw [HironakaG11PresTowerState.strictTransform_id hW.isClosed]
        exact hSmooth
      exact ⟨hStrict,exceptionalLocus_eq_singular_preimage W hW.isClosed id contMDiff_id hIso hStrict⟩
  · have hn2 : n = 2 := by omega
    subst n
    exact surface_proper_singular_resolution W hW [] NormalCrossings.isSNCDivisor_nil

end
end Hironaka.HironakaG8SurfaceLimitEndpoint

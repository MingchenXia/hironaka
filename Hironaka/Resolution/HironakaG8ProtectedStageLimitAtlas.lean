import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary

/-! The exact finite-stage atlas on arbitrary protected source opens. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ProtectedStageLimitAtlas
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryComparison
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryFactors HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaG8SurfaceLimitEndpoint HironakaStageCenters HironakaEmbeddedAnalytic
  HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong RestrictEmptyTower ResolutionInvariantSeq BlowupRestrictOpen

attribute [local instance] limitChartedSpace
variable {n : ℕ} {X : CMfd.{0} n}

/-- A chosen finite stage on a source open avoided by the later centres.
This is the literal restriction of the actual stage factor. -/
def protectedStageMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (k : ℕ) : limitWindow s hLF U → openPreimage (s.stage k).2 U :=
  fun z => ⟨stageFactor s hLF k z.val,by
    change (s.stage k).2.proj (stageFactor s hLF k z.val) ∈ U
    rw [stageFactor_projection]
    exact z.property⟩

theorem protectedStageMap_hol (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (protectedStageMap s hLF U k) :=
  contMDiff_opens_mk ((stageFactor_contMDiff s hLF k).comp contMDiff_subtype_val) _

/-- The restricted finite projection is the original physical limit
projection on the protected window. -/
theorem protectedStageMap_projection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (k : ℕ) (z : limitWindow s hLF U) :
    (s.stage k).2.proj (protectedStageMap s hLF U k z).val = gluedProjection s hLF z.val :=
  stageFactor_projection s hLF k z.val

private theorem strictAlong_of_protected_tail (s : GrowingSeq X)
    (k r : ℕ) (U : Opens X) {B : Set X} (hB : IsClosed B)
    (hAvoid : ∀ i, k ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)))
    (z : (s.stage (k+r)).1)
    (hz : (tailTower s k r).proj z ∈ openPreimage (s.stage k).2 U) :
    z ∈ strictAlong (s.stage (k+r)).2 B ↔
      (tailTower s k r).proj z ∈ strictAlong (s.stage k).2 B := by
  let W := openPreimage (s.stage k).2 U
  let A := strictAlong (s.stage k).2 B
  let q : openPreimage (tailTower s k r) W := ⟨z,hz⟩
  have hA : IsClosed A := isClosed_strictAlong (s.stage k).2 hB
  have hEmpty := (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s k U hAvoid r)
  have he := ContactEmptyPrefix.strictAlong_of_isEmptyTower
    (hA.preimage continuous_subtype_val) (restrict W (tailTower s k r)) hEmpty
  rw [strictAlong_restrict] at he
  have hi := (Set.ext_iff.mp he) q
  change z ∈ strictAlong (tailTower s k r) A ↔ ((restrict W (tailTower s k r)).proj q).val ∈ A at hi
  rw [proj_restrict] at hi
  change z ∈ strictAlong (tailTower s k r) (strictAlong (s.stage k).2 B) ↔ _ at hi
  rw [← strictAlong_append,append_tailTower] at hi
  exact hi

/-- On an arbitrary protected open, the exact finite prefix computes the
entire strict limit carrier, even when the chosen stage differs from
the individual atlas indices. This compares the independently defined
intersection over all actual finite stages. -/
theorem protectedStageMap_strictAlong (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (k : ℕ)
    (hAvoid : ∀ i, k ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)))
    {B : Set X} (hB : IsClosed B) (z : limitWindow s hLF U) :
    z.val ∈ limitStrictTransform s hLF B ↔
      (protectedStageMap s hLF U k z).val ∈ strictAlong (s.stage k).2 B := by
  constructor
  · intro hz
    exact mem_iInter.mp hz k
  · intro hz
    apply mem_iInter.mpr
    intro j
    let y := stageFactor s hLF (k+j) z.val
    have hQ : (tailTower s k j).proj y = (protectedStageMap s hLF U k z).val :=
      congrFun (stageFactor_tail s hLF k j) z.val
    have hyU : (tailTower s k j).proj y ∈ openPreimage (s.stage k).2 U := by
      rw [hQ]
      exact (protectedStageMap s hLF U k z).property
    have hy := (strictAlong_of_protected_tail s k j U hB hAvoid y hyU).mpr
      (hQ.symm ▸ hz)
    have hy' : stageFactor s hLF (j+k) z.val ∈ strictAlong (s.stage (j+k)).2 B := by
      rw [Nat.add_comm j k]
      exact hy
    have hDown : (tailTower s j k).proj (stageFactor s hLF (j+k) z.val) ∈
        strictAlong (s.stage j).2 B := by
      apply strictAlong_subset_preimage (tailTower s j k) (isClosed_strictAlong (s.stage j).2 hB)
      rw [← strictAlong_append,append_tailTower]
      exact hy'
    have hproj := congrFun (stageFactor_tail s hLF j k) z.val
    change (tailTower s j k).proj (stageFactor s hLF (j+k) z.val) = stageFactor s hLF j z.val at hproj
    rwa [hproj] at hDown

/-- With singular-centred stages, the protected atlas identifies the
intrinsic strict transform under the actual physical projection with
the strict transform of the chosen literal finite stage. -/
theorem protectedStageMap_strictTransform (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (U : Opens X) (k : ℕ)
    (hAvoid : ∀ i, k ≤ i → Disjoint (stepCentre s i) ((s.stage i).2.proj ⁻¹' (U : Set X)))
    (B : Set X) (hB : IsComplexAnalyticSubset (n := n) B)
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj B)) (s.stage i).2)
    (z : limitWindow s hLF U) :
    z.val ∈ strictTransform n (gluedProjection s hLF) B ↔
      (protectedStageMap s hLF U k z).val ∈ strictTransform n (s.stage k).2.proj B := by
  rw [← intrinsic_limit_strictTransform_eq_projection B hB s hLF hStage
    (intrinsic_limit_regular_open_iso B hB s hLF hStage),
    ← intrinsic_strictAlong_eq B hB (s.stage k).2 (hStage k)]
  exact protectedStageMap_strictAlong s hLF U k hAvoid hB.isClosed z


open MarkedIdeals MarkedIdeals.MarkedIdeal HironakaActualLocallyFiniteBoundary
  HironakaSharpActualCurveBirthBoundaryOverlaps

/-- Every readout position of the globally defined ordered boundary is the
exact finite readout through the same protected stage map. This includes
birth positions beyond the finite stage, whose readouts are empty there. -/
theorem protectedStageMap_boundary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j, IsGeoTestTower M (s.stage j).2)
    (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (k : ℕ) (z : limitWindow s hLF U) :
    z.val ∈ limitBoundaryMember M s hLF k ↔
      (protectedStageMap s hLF U N z).val ∈ boundaryReadout (geoTransformAlong M (s.stage N).2).E k := by
  have hEmpty (r : ℕ) : ResolutionInvariantExt.IsEmptyTower
      (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)) :=
    (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s N U hAvoid r)
  have hTail (r : ℕ) :
      (tailTower s N r).proj (stageFactor s hLF (N+r) z.val) = (protectedStageMap s hLF U N z).val :=
    congrFun (stageFactor_tail s hLF N r) z.val
  have hMap (r : ℕ) :
      (tailTower s N r).proj (stageFactor s hLF (N+r) z.val) ∈ openPreimage (s.stage N).2 U := by
    rw [hTail]
    exact (protectedStageMap s hLF U N z).property
  constructor
  · intro hq
    have hJ := mem_iInter.mp hq N
    change stageFactor s hLF (k+1+N) z.val ∈
      boundaryReadout (geoTransformAlong M (s.stage (k+1+N)).2).E k at hJ
    rw [Nat.add_comm (k+1) N] at hJ
    have h := (mem_boundary_stage_of_empty_tail M hM s hT N (k+1) U (hEmpty _) k
      (stageFactor s hLF (N+(k+1)) z.val) (hMap _)).mp hJ
    rwa [hTail] at h
  · intro hq
    apply mem_iInter.mpr
    intro r
    let J := k+1+r
    have hL : stageFactor s hLF (N+J) z.val ∈
        boundaryReadout (geoTransformAlong M (s.stage (N+J)).2).E k :=
      (mem_boundary_stage_of_empty_tail M hM s hT N J U (hEmpty J) k
        (stageFactor s hLF (N+J) z.val) (hMap J)).mpr (by rw [hTail];exact hq)
    have hL' : stageFactor s hLF (J+N) z.val ∈
        boundaryReadout (geoTransformAlong M (s.stage (J+N)).2).E k := by
      rw [Nat.add_comm J N]
      exact hL
    have hk : k < (geoTransformAlong M (s.stage J).2).E.length := by
      rw [length_E_geoTransformAlong,stage_length]
      dsimp [J]
      omega
    have hDown : (tailTower s J N).proj (stageFactor s hLF (J+N) z.val) ∈
        boundaryReadout (geoTransformAlong M (s.stage J).2).E k := by
      apply strictAlong_subset_preimage (tailTower s J N)
        (isClosed_boundaryReadout M hM.isSNCDivisor.1 (s.stage J).2 k)
      rw [← boundaryReadout_old_slot (geoTransformAlong M (s.stage J).2) k hk,
        ← geoTransformAlong_append,append_tailTower]
      exact hL'
    have hf := congrFun (stageFactor_tail s hLF J N) z.val
    change (tailTower s J N).proj (stageFactor s hLF (J+N) z.val) = stageFactor s hLF J z.val at hf
    change stageFactor s hLF J z.val ∈ boundaryReadout (geoTransformAlong M (s.stage J).2).E k
    rwa [hf] at hDown

/-- Later chronological births are genuinely absent on the protected
source open, with their index preserved in the global boundary family. -/
theorem protectedStageMap_later_boundary_empty (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ j, IsGeoTestTower M (s.stage j).2)
    (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (k : ℕ) (hk : M.E.length + N ≤ k) :
    (Subtype.val : limitWindow s hLF U → limitManifold s hLF) ⁻¹' limitBoundaryMember M s hLF k = ∅ := by
  have hl : (geoTransformAlong M (s.stage N).2).E.length ≤ k := by
    rw [length_E_geoTransformAlong,stage_length]
    exact hk
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hf := (protectedStageMap_boundary M hM s hLF hT U N hAvoid k z).mp hz
  rw [boundaryReadout,List.getD_eq_default _ _ hl] at hf
  exact hf


open BlowupTowerIsoTail HironakaOriginalEmptyHeadPrefix

/-- A later finite stage on a protected open maps biholomorphically to
the chosen stage, compatibly with the exact global stage factors. -/
theorem exists_protectedStage_transition (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (U : Opens X) (N J : ℕ) (hNJ : N ≤ J)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X))) :
    ∃ b : openPreimage (s.stage J).2 U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        openPreimage (s.stage N).2 U,
      ∀ z : limitWindow s hLF U, b (protectedStageMap s hLF U J z) = protectedStageMap s hLF U N z := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hNJ
  let W := openPreimage (s.stage N).2 U
  let T := tailTower s N r
  have hEmpty := (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s N U hAvoid r)
  obtain ⟨b,hb⟩ := exists_empty_tower_projection (restrict W T) hEmpty
  have hOpen : openPreimage T W = openPreimage (s.stage (N+r)).2 U := by
    rw [openPreimage_append,append_tailTower]
  let c := opensCongr (n := n) hOpen.symm
  refine ⟨c.trans b,fun z => Subtype.ext ?_⟩
  have hp := congrArg Subtype.val (hb (c (protectedStageMap s hLF U (N+r) z)))
  rw [proj_restrict] at hp
  change ((c.trans b) (protectedStageMap s hLF U (N+r) z)).val =
    T.proj (stageFactor s hLF (N+r) z.val) at hp
  exact hp.trans (congrFun (stageFactor_tail s hLF N r) z.val)

private theorem avoid_mono (s : GrowingSeq X) {U V : Opens X} (h : V ≤ U) {k : ℕ}
    (hU : ∀ j, k ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X))) :
    ∀ j, k ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (V : Set X)) :=
  fun j hj => (hU j hj).mono_right (preimage_mono h)

private theorem exists_protectedStage_pair (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (U : Opens X) (N J : ℕ)
    (hN : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (hJ : ∀ j, J ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X))) :
    ∃ b : openPreimage (s.stage J).2 U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        openPreimage (s.stage N).2 U,
      ∀ z : limitWindow s hLF U, b (protectedStageMap s hLF U J z) = protectedStageMap s hLF U N z := by
  obtain ⟨b,hb⟩ := exists_protectedStage_transition s hLF U N (max N J) (le_max_left _ _) hN
  obtain ⟨c,hc⟩ := exists_protectedStage_transition s hLF U J (max N J) (le_max_right _ _) hJ
  refine ⟨c.symm.trans b,fun z => ?_⟩
  change b (c.symm (protectedStageMap s hLF U J z)) = _
  rw [← hc,c.symm_apply_apply,hb]

/-- The chosen protected finite-stage factor is bijective on the entire
literal open of the glued limit. -/
theorem protectedStageMap_bijective (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X))) :
    Bijective (protectedStageMap s hLF U N) := by
  constructor
  · intro z₁ z₂ h
    let x := gluedProjection s hLF z₁.val
    let V := U ⊓ stableWindow s hLF x
    have h₁ : gluedProjection s hLF z₁.val ∈ stableWindow s hLF x :=
      point_mem_stableWindow s hLF x
    have h₂ : gluedProjection s hLF z₂.val ∈ stableWindow s hLF x := by
      rw [← protectedStageMap_projection s hLF U N z₂, ← h,
        protectedStageMap_projection]
      exact h₁
    let w₁ : limitWindow s hLF V := ⟨z₁.val,z₁.property,h₁⟩
    let w₂ : limitWindow s hLF V := ⟨z₂.val,z₂.property,h₂⟩
    let J := stableIndex s hLF x
    obtain ⟨b,hb⟩ := exists_protectedStage_pair s hLF V N J
      (avoid_mono s inf_le_left hAvoid) (avoid_mono s inf_le_right (stableWindow_avoids s hLF x))
    have hV : protectedStageMap s hLF V N w₁ = protectedStageMap s hLF V N w₂ :=
      Subtype.ext (congrArg (fun a : openPreimage (s.stage N).2 U => a.val) h)
    have hJ : protectedStageMap s hLF V J w₁ = protectedStageMap s hLF V J w₂ :=
      b.injective ((hb w₁).trans (hV.trans (hb w₂).symm))
    let a₁ : limitWindow s hLF (stableWindow s hLF x) := ⟨z₁.val,h₁⟩
    let a₂ : limitWindow s hLF (stableWindow s hLF x) := ⟨z₂.val,h₂⟩
    have hSquare : (stableWindowDiffeomorph s hLF x).symm a₁ =
        (stableWindowDiffeomorph s hLF x).symm a₂ :=
      Subtype.ext (congrArg (fun a : openPreimage (s.stage J).2 V => a.val) hJ)
    exact Subtype.ext (congrArg (fun a : limitWindow s hLF (stableWindow s hLF x) => a.val) ((stableWindowDiffeomorph s hLF x).symm.injective hSquare))
  · intro a
    obtain ⟨z,hz⟩ := stageFactor_surjective s hLF N a.val
    have hmem : gluedProjection s hLF z ∈ U := by
      rw [← stageFactor_projection s hLF N z,hz]
      exact a.property
    exact ⟨⟨z,hmem⟩,Subtype.ext hz⟩


set_option backward.isDefEq.respectTransparency false in
/-- On any source open protected after stage N, the actual stage factor
is a biholomorphism to that finite-stage open. The inverse is holomorphic
on its stable-window cover by the physical empty-tail comparisons. -/
def protectedStageDiffeomorph (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X))) :
    limitWindow s hLF U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      openPreimage (s.stage N).2 U := by
  let e := Equiv.ofBijective (protectedStageMap s hLF U N)
    (protectedStageMap_bijective s hLF U N hAvoid)
  refine ⟨e,protectedStageMap_hol s hLF U N,?_⟩
  intro a
  let x := (s.stage N).2.proj a.val
  let J := stableIndex s hLF x
  let U' := stableWindow s hLF x
  let V := U ⊓ U'
  let O : Opens (openPreimage (s.stage N).2 U) :=
    ⟨(fun y => (s.stage N).2.proj y.val) ⁻¹' (U' : Set X),
      U'.isOpen.preimage ((s.stage N).2.contMDiff_proj.continuous.comp continuous_subtype_val)⟩
  have ha : a ∈ O := point_mem_stableWindow s hLF x
  let i (y : O) : openPreimage (s.stage N).2 V := ⟨y.val.val,y.val.property,y.property⟩
  have hi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ i :=
    (ContMDiff.subtypeVal_comp_iff (openPreimage (s.stage N).2 V) i).mp
      ((contMDiff_subtype_val (U := openPreimage (s.stage N).2 U)).comp (contMDiff_subtype_val (U := O)))
  obtain ⟨b,hb⟩ := exists_protectedStage_pair s hLF V N J
    (avoid_mono s inf_le_left hAvoid) (avoid_mono s inf_le_right (stableWindow_avoids s hLF x))
  let l : openPreimage (s.stage J).2 V → localEndpoint s hLF x :=
    fun y => ⟨y.val,y.property.2⟩
  have hl : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ l :=
    (ContMDiff.subtypeVal_comp_iff (openPreimage (s.stage J).2 U') l).mp
      (contMDiff_subtype_val (U := openPreimage (s.stage J).2 V))
  let w (y : O) : limitWindow s hLF V := ⟨actualHistoryLocalInclusion s hLF x (l (b.symm (i y))), by
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x (l (b.symm (i y)))) ∈ V
    rw [gluedProjection_local]
    exact (b.symm (i y)).property⟩
  let g (y : O) : limitWindow s hLF U := ⟨(w y).val,(w y).property.1⟩
  have hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff (limitWindow s hLF U) g).mp
      ((localInclusion_contMDiff s hLF x).comp (hl.comp (b.symm.contMDiff.comp hi)))
  have hCompat (y : O) : protectedStageMap s hLF V J (w y) = b.symm (i y) :=
    Subtype.ext (stableFactor_local s hLF x (l (b.symm (i y))))
  have hEq : (fun y : O => e.symm y.val) = g := by
    funext y
    apply e.injective
    rw [e.apply_symm_apply]
    have hw := hb (w y)
    rw [hCompat,b.apply_symm_apply] at hw
    apply Subtype.ext
    exact congrArg (fun z : openPreimage (s.stage N).2 V => z.val) hw
  apply (contMDiffAt_subtype_iff (f := (e.symm : openPreimage (s.stage N).2 U → limitWindow s hLF U))
    (x := (⟨a,ha⟩ : O))).mp
  change ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (fun y : O => e.symm y.val) ⟨a,ha⟩
  rw [hEq]
  exact hg.contMDiffAt


@[simp] theorem protectedStageDiffeomorph_apply (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (U : Opens X) (N : ℕ)
    (hAvoid : ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)))
    (z : limitWindow s hLF U) :
    protectedStageDiffeomorph s hLF U N hAvoid z = protectedStageMap s hLF U N z := rfl


/-- The scheduler's empty-tail certificate gives exactly the pointwise
protection condition for the physical atlas. -/
theorem protected_centres_of_empty_tails (s : GrowingSeq X) (U : Opens X) (N : ℕ)
    (hEmpty : ∀ r, ResolutionInvariantExt.IsEmptyTower
      (restrict (openPreimage (s.stage N).2 U) (tailTower s N r))) :
    ∀ j, N ≤ j → Disjoint (stepCentre s j) ((s.stage j).2.proj ⁻¹' (U : Set X)) := by
  intro j hj
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  have he := (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mp (hEmpty (r+1))
  have hdisj : Disjoint (stepCentre s (N+r))
      ((tailTower s N r).proj ⁻¹' (openPreimage (s.stage N).2 U : Set (s.stage N).1)) := he.2
  change Disjoint (stepCentre s (N+r)) (((s.stage N).2.proj ∘ (tailTower s N r).proj) ⁻¹' (U : Set X))
    at hdisj
  rwa [← BlowupTower.proj_append,append_tailTower] at hdisj

/-- From the actual empty tails supplied by compact-footprint scheduling,
one finite atlas chart simultaneously computes the physical projection,
the physical strict transform, and every ordered boundary readout. -/
theorem exists_protected_atlas_of_empty_tails (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (N : ℕ)
    (hEmpty : ∀ r, ResolutionInvariantExt.IsEmptyTower
      (restrict (openPreimage (s.stage N).2 U) (tailTower s N r)))
    (B : Set X) (hB : IsComplexAnalyticSubset (n := n) B)
    (hStage : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj B)) (s.stage i).2)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hTest : ∀ j, M.IsGeoTestTower (s.stage j).2) :
    ∃ e : limitWindow s hLF U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage (s.stage N).2 U,
      (∀ z, (e z).val = stageFactor s hLF N z.val ∧
        (s.stage N).2.proj (e z).val = gluedProjection s hLF z.val) ∧
      (∀ z : limitWindow s hLF U,
        z.val ∈ strictTransform n (gluedProjection s hLF) B ↔
          (e z).val ∈ strictTransform n (s.stage N).2.proj B) ∧
      (∀ k (z : limitWindow s hLF U),
        z.val ∈ limitBoundaryMember M s hLF k ↔
          (e z).val ∈ boundaryReadout (geoTransformAlong M (s.stage N).2).E k) := by
  have h := protected_centres_of_empty_tails s U N hEmpty
  exact ⟨protectedStageDiffeomorph s hLF U N h, fun z => ⟨rfl,protectedStageMap_projection s hLF U N z⟩,
    protectedStageMap_strictTransform s hLF U N h B hB hStage,
    protectedStageMap_boundary M hM s hLF hTest U N h⟩

end
end Hironaka.HironakaG8ProtectedStageLimitAtlas

/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.MemberInterTowerAlongOriginalExact
import Hironaka.Resolution.HironakaNormalCrossingsJointBranchCharts
import Hironaka.Resolution.HironakaNormalCrossingsHighestSubcentreAdmissibility
import Hironaka.Resolution.HironakaBoundaryCoefficientStratumResolution

/-!
# The actual coefficient phase retains whole joint old and born histories

The SAME retained boundary is present in the phase input and in every genuine
local branch history. All branches come from the actual original joint chart.
No empty-boundary replacement or incoming local history is assumed.
Blueprint: `hironaka-boundary-coefficient-branch-histories-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaBoundaryCoefficientBranchHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterTowerAlong DropMembers
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsJointBranchCharts HironakaBoundaryCoefficientStratumResolution
  HironakaNormalCrossingsHighestSubcentreAdmissibility
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The literal whole old branch block precedes the SAME entire retained and
newly born boundary, without any testness premise or removed empty positions. -/
theorem entire_old_retained_boundary (M : MarkedIdeal n X) (B : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    (geoTransformAlong ({M with E:=B++M.E} : MarkedIdeal n X) T).E=
      B.map (strictAlong T) ++ (geoTransformAlong M T).E
  | _,.refl => by
    change B++M.E=B.map (fun A=>A)++M.E
    exact congrArg (fun L : List (Set X)=>L++M.E) (List.map_id B).symm
  | _,.step T C π hπ => by
    rw [geoTransformAlong_step,geoTransformAlong_step,geoTransform_E,geoTransform_E,
      entire_old_retained_boundary M B T,List.map_append,List.map_map,List.append_assoc]
    rfl

set_option maxHeartbeats 1000000 in
/-- Actual original testness and the true highest-stratum centres internally
supply joint branch histories retaining the ENTIRE original boundary. -/
theorem exists_highest_joint_branch_histories
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} T)
    {x : X} (hx : r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x) :
    ∃ (U : Opens X) (B : List (Set U)),x∈U ∧
      IsSNCDivisor n (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) ∧
      (Subtype.val : U→X) ⁻¹' H=(⋃ A∈B,A) ∧
      IsGeoTestTower (localBranchMarked U (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) univ I d)
        (restrict U T) ∧
      ∀ j : ℕ,
        let MU := MarkedIdeal.pullback (Subtype.val : U→X) (⟨univ,E,I,d⟩ : MarkedIdeal n X)
        let MB := localBranchMarked U (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) univ I d
        (geoTransformAlong MB (head (restrict U T) j)).IsWellFormed ∧
        (geoTransformAlong MB (head (restrict U T) j)).E=
          B.map (strictAlong (head (restrict U T) j)) ++
            (geoTransformAlong MU (head (restrict U T) j)).E := by
  let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  obtain ⟨U,B,hxU,hBE,hunion,hcontain⟩ := exists_highest_joint_branch_chart h hbound hx
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U→X) M
  let EU := E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)
  let MB := localBranchMarked U (B++EU) univ I d
  have hMB : MB.IsWellFormed := by
    have hNU : (Subtype.val : U→X) ⁻¹' (univ : Set X)=univ := preimage_univ
    change (⟨(Subtype.val : U→X) ⁻¹' univ,B++EU,
      GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U).IsWellFormed
    rw [hNU]
    exact ⟨isClosedSubmanifold_univ,
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,hBE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩
  have hTU : IsGeoTestTower MU (restrict U T) :=
    isGeoTestTower_restrict U isClosedSubmanifold_univ hI T hT
  have hTZU : CentresIn ((Subtype.val : U→X) ⁻¹' Z) (restrict U T) := by
    apply centresIn_restrict_of_centresIn_union U (A:=Z) (B:=∅) isClosed_empty (by simp) T
    simpa only [union_empty] using hTZ
  have hTMB : IsGeoTestTower MB (restrict U T) := by
    apply (isGeoTestTower_withE_iff_of_centresIn MB hMB (E':=EU)
      (S:=(Subtype.val : U→X) ⁻¹' Z)
      (fun A hA=>List.mem_append_right _ hA)
      (fun A hA hnot=>by
        rcases List.mem_append.mp hA with hOld|hRetained
        · exact hcontain A hOld
        · exact False.elim (hnot hRetained)) (restrict U T) hTZU).1.mp
    exact hTU
  refine ⟨U,B,hxU,hBE,hunion,hTMB,?_⟩
  intro j
  have hhead := ((isGeoTestTower_iff_head_tail MB (restrict U T) j).mp hTMB).1
  exact ⟨MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMB _ hhead,
    entire_old_retained_boundary MU B (head (restrict U T) j)⟩

/-- Original natural data supply the SAME whole-boundary stratum phase and
ALL its actual joint old/born histories, with no incoming phase certificate. -/
theorem exists_original_boundary_stratum_joint_histories
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ ∧
      ∀ x∈Z,∃ (U : Opens X) (B : List (Set U)),x∈U ∧
        IsSNCDivisor n (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) ∧
        (Subtype.val : U→X) ⁻¹' H=(⋃ A∈B,A) ∧
        IsGeoTestTower (localBranchMarked U (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) univ I d)
          (restrict U T) ∧
        ∀ j : ℕ,
          let MU := MarkedIdeal.pullback (Subtype.val : U→X) M
          let MB := localBranchMarked U (B++E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)) univ I d
          (geoTransformAlong MB (head (restrict U T) j)).IsWellFormed ∧
          (geoTransformAlong MB (head (restrict U T) j)).E=
            B.map (strictAlong (head (restrict U T) j)) ++
              (geoTransformAlong MU (head (restrict U T) j)).E := by
  dsimp only
  obtain ⟨Y,T,hres,hTM,hTZ,hclear⟩ :=
    exists_original_boundary_nc_coefficient_stratum_resolution I hI d hd hK h hr hbound
  exact ⟨Y,T,hres,hTM,hTZ,hclear,
    fun _ hx=>exists_highest_joint_branch_histories I hI d h hbound T hTM hTZ hx⟩

end
end Hironaka.HironakaBoundaryCoefficientBranchHistories

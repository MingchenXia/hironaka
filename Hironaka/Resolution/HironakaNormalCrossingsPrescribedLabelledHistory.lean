import Hironaka.Resolution.HironakaNormalCrossingsLabelledJointBranches
import Hironaka.Resolution.HironakaNormalCrossingsPermittedBranchHistory

/-!
# Actual prescribed joint histories retain every fixed original label group

The SAME real branch list from the original labelled chart is kept before all
actual global heads. Actual source-side testness and highest-cut containment
derive its entire joint test history and literal original-label transforms.
Blueprint: `hironaka-normal-crossings-prescribed-labelled-history-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaNormalCrossingsPrescribedLabelledHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen NormalCrossings GermIdealOrder CoefficientIdealRestriction
  DropMembers HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsLabelledBoundary
  HironakaNormalCrossingsLabelledJointBranches HironakaNormalCrossingsHighestSubcentreAdmissibility
  HironakaBoundaryCoefficientBranchHistories HironakaBoundaryCoefficientStratumResolution
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The same original finite position group survives actual strict transform. -/
theorem strictAlong_finset_union {ι : Type v} (P : BlowupTower X Y)
    (G : Finset ι) (A : ι → Set X) :
    strictAlong P (⋃ j∈G,A j)=⋃ j∈G,strictAlong P (A j) := by
  induction G using Finset.induction_on with
  | empty => simpa using StepOneEmptyPrefix.strictAlong_empty P
  | @insert j G hj ih =>
    have hX : (⋃ k∈insert j G,A k)=A j∪(⋃ k∈G,A k) := by ext x;simp
    have hY : (⋃ k∈insert j G,strictAlong P (A k))=
        strictAlong P (A j)∪(⋃ k∈G,strictAlong P (A k)) := by ext x;simp
    rw [hX,strictAlong_union,ih,hY]

private theorem joint_wellFormed (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    (E : List (Set X)) (U : Opens X) (B : List (Set U))
    (hBE : IsSNCDivisor n (B++E.map ((Subtype.val : U→X) ⁻¹' ·))) :
    (localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d).IsWellFormed := by
  have hNU : (Subtype.val : U→X) ⁻¹' (univ : Set X)=univ := preimage_univ
  change (⟨(Subtype.val : U→X) ⁻¹' univ,B++E.map ((Subtype.val : U→X) ⁻¹' ·),
    GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U).IsWellFormed
  rw [hNU]
  exact ⟨isClosedSubmanifold_univ,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,hBE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hBE⟩

/-- A prescribed actual SNC joint list becomes a genuine test boundary from
the original testness and real highest-carrier containment alone. -/
theorem prescribed_joint_test_history
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (E : List (Set X))
    (Z : Set X) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T) (hTZ : CentresIn Z T)
    (U : Opens X) (B : List (Set U))
    (hBE : IsSNCDivisor n (B++E.map ((Subtype.val : U→X) ⁻¹' ·)))
    (hcontain : ∀ A∈B,(Subtype.val : U→X) ⁻¹' Z⊆A) :
    IsGeoTestTower
      (localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d) (restrict U T) := by
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U→X) M
  let EU := E.map ((Subtype.val : U→X) ⁻¹' ·)
  let MB := localBranchMarked U (B++EU) univ I d
  have hMB : MB.IsWellFormed := joint_wellFormed I hI d E U B hBE
  have hTU : IsGeoTestTower MU (restrict U T) :=
    isGeoTestTower_restrict U isClosedSubmanifold_univ hI T hT
  have hTZU : CentresIn ((Subtype.val : U→X) ⁻¹' Z) (restrict U T) := by
    apply centresIn_restrict_of_centresIn_union U (A:=Z) (B:=∅) isClosed_empty (by simp) T
    simpa only [union_empty] using hTZ
  apply (isGeoTestTower_withE_iff_of_centresIn MB hMB (E':=EU)
    (S:=(Subtype.val : U→X) ⁻¹' Z)
    (fun A hA=>List.mem_append_right _ hA)
    (fun A hA hnot=>by
      rcases List.mem_append.mp hA with hOld|hRetained
      · exact hcontain A hOld
      · exact False.elim (hnot hRetained)) (restrict U T) hTZU).1.mp
  exact hTU

private theorem centresIn_head (Z : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn Z T →
      ∀ j : ℕ,CentresIn Z (head T j)
  | _,T,h,0 => by cases T <;> exact h
  | _,.refl,_,_+1 => trivial
  | _,.step T _ _ _,h,j+1 => centresIn_head Z T h.1 j

/-- ONE internally produced original chart and its SAME finite label groups
work for EVERY actual global head, with genuine entire-joint testness. -/
theorem exists_highest_labelled_joint_histories
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) {r : ℕ}
    (hbound : ∀ y : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y≤r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,E,I,d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn {y : X | r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y} T)
    {x : X} (hx : r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x) :
    ∃ (U : Opens X) (B : List (Set U)) (G : Fin L.length → Finset (Fin B.length)),
      x∈U ∧ IsSNCDivisor n (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      (∀ i j,i≠j → Disjoint (G i) (G j)) ∧
      (∀ i,(Subtype.val : U→X) ⁻¹' L.get i=⋃ k∈G i,B.get k) ∧
      IsGeoTestTower
        (localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d) (restrict U T) ∧
      ∀ j : ℕ,
        let Q:=head T j
        let V:=openPreimage Q U
        let P:=restrict U Q
        IsSNCDivisor n
          (B.map (strictAlong P)++(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) Q).E.map
            ((Subtype.val : V→(split T j).1) ⁻¹' ·)) ∧
        ∀ i,(Subtype.val : V→(split T j).1) ⁻¹' strictAlong Q (L.get i)=
          ⋃ k∈G i,strictAlong P (B.get k) := by
  obtain ⟨U,B,G,hxU,hBE,hG,hMember,_hUnion,hcontain⟩ :=
    exists_highest_labelled_joint_branch_chart h hE hbound hx
  let Z:={y : X | r≤branchMultiplicity
    (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y}
  have hJoint:=prescribed_joint_test_history I hI d E Z T hT hTZ U B hBE hcontain
  refine ⟨U,B,G,hxU,hBE,hG,hMember,hJoint,?_⟩
  intro j
  let Q:=head T j
  let V:=openPreimage Q U
  let P:=restrict U Q
  let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
  let MU:=MarkedIdeal.pullback (Subtype.val : U→X) M
  let MB:=localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d
  have hQ : IsGeoTestTower M Q:=((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hQZ : CentresIn Z Q:=centresIn_head Z T hTZ j
  have hQP : IsGeoTestTower MB P:=prescribed_joint_test_history I hI d E Z Q hQ hQZ U B hBE hcontain
  have hWF:=(MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (joint_wellFormed I hI d E U B hBE) P hQP).isSNCDivisor
  have hEntire : (geoTransformAlong MB P).E=
      B.map (strictAlong P)++(geoTransformAlong MU P).E:=entire_old_retained_boundary MU B P
  have hRecord:=geoTransformAlong_restrict U isClosedSubmanifold_univ hI Q hQ
  refine ⟨?_,?_⟩
  · rw [hEntire,hRecord] at hWF
    exact hWF
  · intro i
    rw [←strictAlong_restrict U Q (L.get i),hMember i]
    exact strictAlong_finset_union P (G i) B.get

/-- Original geometric and ideal data internally construct the SAME real
coefficient phase, with actual fixed-label-group histories as outputs. -/
theorem exists_original_labelled_phase_with_groups
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d)) {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ y : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y≤r) :
    let M : MarkedIdeal n X:=⟨univ,E,I,d⟩
    let Z:={y : X | r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y}
    let K:=withN (CoefficientIdeal.coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution K T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ ∧
      ∀ x∈Z,∃ (U : Opens X) (B : List (Set U)) (G : Fin L.length → Finset (Fin B.length)),
        x∈U ∧ IsSNCDivisor n (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
        (∀ i j,i≠j → Disjoint (G i) (G j)) ∧
        (∀ i,(Subtype.val : U→X) ⁻¹' L.get i=⋃ k∈G i,B.get k) ∧
        IsGeoTestTower
          (localBranchMarked U (B++E.map ((Subtype.val : U→X) ⁻¹' ·)) univ I d) (restrict U T) ∧
        ∀ j : ℕ,
          let Q:=head T j
          let V:=openPreimage Q U
          let P:=restrict U Q
          IsSNCDivisor n
            (B.map (strictAlong P)++(geoTransformAlong M Q).E.map
              ((Subtype.val : V→(split T j).1) ⁻¹' ·)) ∧
          ∀ i,(Subtype.val : V→(split T j).1) ⁻¹' strictAlong Q (L.get i)=
            ⋃ k∈G i,strictAlong P (B.get k) := by
  dsimp only
  obtain ⟨Y,T,hres,hT,hTZ,hclear⟩:=exists_original_boundary_nc_coefficient_stratum_resolution
    I hI d hd hK (boundaryAdapted_union_of_labelled h hE) hr hbound
  exact ⟨Y,T,hres,hT,hTZ,hclear,fun _ hx=>
    exists_highest_labelled_joint_histories I hI d h hE hbound T hT hTZ hx⟩

end
end Hironaka.HironakaNormalCrossingsPrescribedLabelledHistory

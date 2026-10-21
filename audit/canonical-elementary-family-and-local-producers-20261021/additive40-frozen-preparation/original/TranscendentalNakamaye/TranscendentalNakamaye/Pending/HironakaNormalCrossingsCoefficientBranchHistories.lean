import TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientRemainderPhase

/-!
# Genuine actual local old-NC branch histories of the coefficient phase

All local branch lists and their containment conditions are derived from the
ORIGINAL actual NC chart. Existing whole-history drop-member equivalence then
adds them to the SAME original marked test tower at every actual prefix.
Literal whole old/born list identities retain all chronology. This neither
identifies an old ordered invariant nor asserts the selected-zero phase.
Blueprint: `hironaka-normal-crossings-coefficient-branch-histories-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientBranchHistories
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  HomogenizedGlueingTower MemberInterTowerAlong DropMembers
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaStepOneZeroContactRemainderExtension CanonicalCentres
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestSubcentreAdmissibility
  HironakaNormalCrossingsCoefficientRemainderPhase
open ResolutionInvariantSpec (IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Whole literal old branch block and SAME chronological born block, even
without testness and with empty entries retained. -/
theorem entire_old_born_boundary (M : MarkedIdeal n X) (hE : M.E=[])
    (B : List (Set X)) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    (geoTransformAlong ({M with E:=B} : MarkedIdeal n X) T).E=
      B.map (strictAlong T) ++ (geoTransformAlong M T).E
  | _,.refl => by simp [hE,strictAlong]
  | _,.step T C π hπ => by
    rw [geoTransformAlong_step,geoTransformAlong_step,geoTransform_E,geoTransform_E,
      entire_old_born_boundary M hE B T,List.map_append,List.map_map,List.append_assoc]
    rfl

private theorem centresIn_restrict {S : Set X} (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn S T→
      CentresIn ((Subtype.val : U→X) ⁻¹' S) (restrict U T)
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hT => by
    refine ⟨centresIn_restrict U T hT.1,?_⟩
    intro p hp
    rw [strictAlong_restrict U T S]
    exact hT.2 hp

set_option maxHeartbeats 1000000 in
/-- Genuine local branch histories and ALL prefix geometry from actual
original testness and actual centres in the intrinsic highest stratum. -/
theorem exists_highest_stratum_local_branch_histories
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ)
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity hH x≤r)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ,[],I,d⟩ : MarkedIdeal n X) T)
    (hTZ : CentresIn {x : X | r≤branchMultiplicity hH x} T)
    {x : X} (hx : r≤branchMultiplicity hH x) :
    ∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
      (Subtype.val : U→X) ⁻¹' H=(⋃ A∈B,A) ∧
      IsGeoTestTower (localBranchMarked U B univ I d) (restrict U T) ∧
      ∀ j : ℕ,
        (geoTransformAlong (localBranchMarked U B univ I d) (head (restrict U T) j)).IsWellFormed ∧
        (geoTransformAlong (localBranchMarked U B univ I d) (head (restrict U T) j)).E=
          B.map (strictAlong (head (restrict U T) j)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X)
              (⟨univ,[],I,d⟩ : MarkedIdeal n X)) (head (restrict U T) j)).E := by
  let Z := {x : X | r≤branchMultiplicity hH x}
  obtain ⟨U,B,hxU,hB,hunion,hcontain⟩ := exists_highest_subcentre_branches
    (C:=Z) hH hbound subset_rfl hx
  let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U→X) M
  let MB := localBranchMarked U B univ I d
  have hMB : MB.IsWellFormed := by
    have hNU : (Subtype.val : U→X) ⁻¹' (univ : Set X)=univ := preimage_univ
    change (⟨(Subtype.val : U→X) ⁻¹' univ,B,
      GermIdeal.pullback (m:=n) (Subtype.val : U→X) I,d⟩ : MarkedIdeal n U).IsWellFormed
    rw [hNU]
    exact ⟨isClosedSubmanifold_univ,
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI,hB,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hB⟩
  have hTU : IsGeoTestTower MU (restrict U T) :=
    isGeoTestTower_restrict U isClosedSubmanifold_univ hI T hT
  have hTZU := centresIn_restrict U T hTZ
  have hTMB : IsGeoTestTower MB (restrict U T) := by
    apply (isGeoTestTower_withE_iff_of_centresIn MB hMB (E':=[])
      (S:=(Subtype.val : U→X) ⁻¹' Z) (by simp)
      (fun A hA _=>hcontain A hA) (restrict U T) hTZU).1.mp
    exact hTU
  refine ⟨U,B,hxU,hB,hunion,hTMB,?_⟩
  intro j
  have hhead := ((isGeoTestTower_iff_head_tail MB (restrict U T) j).mp hTMB).1
  exact ⟨MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMB _ hhead,
    entire_old_born_boundary MU rfl B (head (restrict U T) j)⟩

/-- SAME internally selected finite original coefficient phase, now with the
full actual local old-branch plus born-boundary test histories at EVERY prefix. -/
theorem exists_original_nc_coefficient_phase_branch_histories
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity hH x≤r) :
    let M : MarkedIdeal n X := ⟨univ,[],I,d⟩
    let Z := {x : X | r≤branchMultiplicity hH x}
    let L := withN (coeffMarked M) Z
    let A := contactRemainderMarked L 0
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical A ((canonicalInvariant n).inv A) T ∧ IsGeoResolution A T ∧
      IsGeoTestTower L T ∧ IsGeoTestTower M T ∧ CentresIn A.N T ∧ CentresIn Z T ∧
      (geoTransformAlong L T).cosupp=(geoTransformAlong M T).cosupp∩strictAlong T Z ∧
      (geoTransformAlong M T).cosupp∩strictAlong T A.N=∅ ∧
      ∀ x∈Z,∃ (U : Opens X) (B : List (Set U)),x∈U ∧ IsSNCDivisor n B ∧
        (Subtype.val : U→X) ⁻¹' H=(⋃ C∈B,C) ∧
        IsGeoTestTower (localBranchMarked U B univ I d) (restrict U T) ∧
        ∀ j : ℕ,
          (geoTransformAlong (localBranchMarked U B univ I d) (head (restrict U T) j)).IsWellFormed ∧
          (geoTransformAlong (localBranchMarked U B univ I d) (head (restrict U T) j)).E=
            B.map (strictAlong (head (restrict U T) j)) ++
              (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U→X) M)
                (head (restrict U T) j)).E := by
  dsimp only
  obtain ⟨Y,T,hcan,hres,hTL,hTM,hTR,hTZ,hcs,hclear⟩ :=
    exists_original_nc_coefficient_remainder_phase I hI d hd hK hH hbound
  exact ⟨Y,T,hcan,hres,hTL,hTM,hTR,hTZ,hcs,hclear,
    fun _ hx=>exists_highest_stratum_local_branch_histories I hI d hH hbound T hTM hTZ hx⟩

end
end TranscendentalNakamaye.Pending.HironakaNormalCrossingsCoefficientBranchHistories

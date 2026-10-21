/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsGlobalPhaseCarrier
import Hironaka.Resolution.HironakaNormalCrossingsOldBlockSuperlevels
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix

/-!
# A genuine old-count drop on a whole-cosupport neighbourhood

The SAME original-only phase has actual global high-cut control and an actual
open containing its ENTIRE current cosupport on which old count falls by one.
No repair is made outside the permitted locus; full iteration remains separate.
Blueprint: `hironaka-normal-crossings-permitted-count-drop-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsPermittedCountDrop
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MemberInterTowerAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings GermIdealOrder CoefficientIdeal CoefficientIdealRestriction
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsBiholomorphicMultiplicity
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSNCBlockCarrier
  HironakaNormalCrossingsGlobalPhaseCarrier HironakaNormalCrossingsOldBlockSuperlevels
  HironakaBoundaryCoefficientBranchHistories HironakaNormalCrossingsHighestSubcentreAdmissibility
  HironakaOriginalEmptyHeadPrefix RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem count_congr {A : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A]
    {H K : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hK : IsNormalCrossingsCarrier (n := n) K) (heq : H=K) (x : A) :
    branchMultiplicity hH x=branchMultiplicity hK x := by
  subst K
  rfl

private theorem strict_empty_tower {H : Set X} (hH : IsClosed H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsEmptyTower T→strictAlong T H=T.proj ⁻¹' H
  | _,.refl,_ => rfl
  | _,.step T C π hπ,hT => by
      obtain ⟨hT,rfl⟩ := hT
      rw [strictAlong_step,strict_empty_tower hH T hT]
      change closure (π ⁻¹' (T.proj ⁻¹' H\∅))=(T.proj ∘ π) ⁻¹' H
      rw [sdiff_empty,((hH.preimage T.contMDiff_proj.continuous).preimage hπ.contMDiff.continuous).closure_eq]
      rfl

/-- The true whole projection biholomorphism gives the intrinsic old count,
without a count or biholomorphism certificate as input. -/
theorem branchMultiplicity_empty_tower {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H)
    (T : BlowupTower X Y) (he : IsEmptyTower T)
    (hp : IsNormalCrossingsCarrier (n := n) (strictAlong T H)) (y : Y) :
    branchMultiplicity hp y=branchMultiplicity hH (T.proj y) := by
  obtain ⟨χ,hχ⟩ := exists_empty_tower_projection T he
  have hSet : strictAlong T H=χ ⁻¹' H := by
    rw [strict_empty_tower hH.1 T he]
    rw [show (χ : Y→X)=T.proj from funext hχ]
  have hpre : IsNormalCrossingsCarrier (n := n) (χ ⁻¹' H) := hSet ▸ hp
  exact (count_congr hp hpre hSet y).trans ((branchMultiplicity_diffeomorph χ hH hpre y).trans
    (congrArg (branchMultiplicity hH) (hχ y)))

private theorem strict_list_union (T : BlowupTower X Y) (B : List (Set X)) :
    strictAlong T (⋃ A∈B,A)=⋃ A∈B.map (strictAlong T),A := by
  have hc {A : Type u} (S : Set A) (L : List (Set A)) : (⋃ C∈S::L,C)=S∪(⋃ C∈L,C) := by
    ext z
    simp
  induction B with
  | nil => simpa using StepOneEmptyPrefix.strictAlong_empty T
  | cons A B ih => rw [hc,strictAlong_union,ih,List.map_cons,hc]

private theorem centresOver_of_centresIn {S : Set X} (hS : IsClosed S) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresIn S T→CentresOver S T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,hT =>
      ⟨centresOver_of_centresIn hS T hT.1,fun _ hp=>strictAlong_subset_preimage T hS (hT.2 hp)⟩

/-- Actual original data supply GLOBAL high-cut control for the SAME whole phase. -/
theorem exists_original_phase_high_cut_control
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
      ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
        {y | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y}⊆strictAlong T Z := by
  dsimp only
  let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
  let hNC := isNormalCrossingsCarrier_of_boundaryAdapted h
  let Z := {x : X | r≤branchMultiplicity hNC x}
  obtain ⟨Y,T,hres,hTM,hTZ,hclear,hFinal⟩ :=
    exists_original_phase_global_old_born_carrier I hI d hd hK h hr hbound
  let hNCf := isNormalCrossingsCarrier_of_boundaryAdapted hFinal
  have hZ : IsClosed Z := isClosed_branchMultiplicity_superlevel hNC r
  refine ⟨Y,T,hres,hTM,hTZ,hclear,hFinal,?_⟩
  intro y hy
  by_cases hx : T.proj y∈Z
  · obtain ⟨U,B,hxU,hBE,hUnion,hTB,_hPrefix⟩ :=
      exists_highest_joint_branch_histories I hI d h hbound T hTM hTZ hx
    let EU := E.map (fun A=>(Subtype.val : U→X) ⁻¹' A)
    let IU := GermIdeal.pullback (m:=n) (Subtype.val : U→X) I
    have hIU : IU.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
    have hTB' : IsGeoTestTower (⟨univ,B++EU,IU,d⟩ : MarkedIdeal n U) (restrict U T) := hTB
    obtain ⟨hCB,hControl⟩ := exists_current_old_carrier_superlevel_control B EU hBE IU hIU d (restrict U T) hTB'
    have hCurrentSet : (⋃ A∈B.map (strictAlong (restrict U T)),A)=
        (Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T H := by
      rw [←strict_list_union,←hUnion,strictAlong_restrict]
    let hTrace := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open (openPreimage T U) hFinal)
    have hCurrentCount (p : openPreimage T U) :
        branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p=branchMultiplicity hNCf p.val :=
      (count_congr _ hTrace hCurrentSet p).trans (branchMultiplicity_open (openPreimage T U) hNCf hTrace p)
    let hInitial := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B EU hBE)
    let hInitialTrace := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)
    have hInitialCount (p : U) : branchMultiplicity hInitial p=branchMultiplicity hNC p.val :=
      (count_congr hInitial hInitialTrace hUnion.symm p).trans (branchMultiplicity_open U hNC hInitialTrace p)
    have hCut : {p : U | r≤branchMultiplicity hInitial p}=(Subtype.val : U→X) ⁻¹' Z := by
      ext p
      change (r≤branchMultiplicity hInitial p)↔r≤branchMultiplicity hNC p.val
      rw [hInitialCount]
    let p : openPreimage T U := ⟨y,hxU⟩
    have hp : r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hCB) p := by
      rw [hCurrentCount]
      exact hy
    have hh := hControl r hp
    rw [hCut,strictAlong_restrict] at hh
    exact hh
  · let U : Opens X := ⟨Zᶜ,hZ.isOpen_compl⟩
    have he : IsEmptyTower (restrict U T) := isEmptyTower_restrict_of_centresOver U disjoint_compl_left T
      (centresOver_of_centresIn hZ T hTZ)
    let p : openPreimage T U := ⟨y,hx⟩
    let hInitial := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U h)
    let hTrace := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open (openPreimage T U) hFinal)
    have hLocal : IsNormalCrossingsCarrier (n := n)
        (strictAlong (restrict U T) ((Subtype.val : U→X) ⁻¹' H)) := by
      rw [strictAlong_restrict]
      exact hTrace
    have hCount : branchMultiplicity hNCf y=branchMultiplicity hNC (T.proj y) := by
      calc
        branchMultiplicity hNCf y=branchMultiplicity hTrace p := (branchMultiplicity_open (openPreimage T U) hNCf hTrace p).symm
        _=branchMultiplicity hLocal p := count_congr hTrace hLocal (strictAlong_restrict U T H).symm p
        _=branchMultiplicity hInitial ((restrict U T).proj p) := branchMultiplicity_empty_tower hInitial (restrict U T) he hLocal p
        _=branchMultiplicity hNC (((restrict U T).proj p).val) := branchMultiplicity_open U hNC hInitial _
        _=branchMultiplicity hNC (T.proj y) := by rw [proj_restrict]
    exact False.elim (hx (by change r≤branchMultiplicity hNC (T.proj y);rwa [←hCount]))

/-- The actual open complement of strict Z contains ALL current cosupport and
has old count at most r-1; high crossings elsewhere are preserved. -/
theorem exists_original_phase_permitted_count_drop
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
      ∃ hc : IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) (geoTransformAlong M T).E,
        ∃ U : Opens Y,(U : Set Y)=(strictAlong T Z)ᶜ ∧ (geoTransformAlong M T).cosupp⊆U ∧
          ∀ y : U,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U hc)) y≤r-1 := by
  dsimp only
  obtain ⟨Y,T,hres,hTM,hTZ,hclear,hc,hControl⟩ := exists_original_phase_high_cut_control I hI d hd hK h hr hbound
  let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let U : Opens Y := ⟨(strictAlong T Z)ᶜ,(isClosed_strictAlong T (isClosed_branchMultiplicity_superlevel _ _)).isOpen_compl⟩
  refine ⟨Y,T,hres,hTM,hTZ,hc,U,rfl,?_,?_⟩
  · intro y hy hz
    have hh : y∈(geoTransformAlong (⟨univ,E,I,d⟩ : MarkedIdeal n X) T).cosupp∩strictAlong T Z := ⟨hy,hz⟩
    rw [hclear] at hh
    exact hh
  · intro y
    have hn : ¬r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y.val := fun hy=>y.property (hControl hy)
    rw [branchMultiplicity_open U (isNormalCrossingsCarrier_of_boundaryAdapted hc)
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U hc)) y]
    omega

end
end Hironaka.HironakaNormalCrossingsPermittedCountDrop

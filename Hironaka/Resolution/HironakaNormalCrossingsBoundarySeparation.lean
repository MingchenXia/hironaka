/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.ExceptionalImageAvoidance
import Hironaka.Invariant.CentresOverAvoidance
import Hironaka.Blowup.BlowupStrictIdealControlled
import Hironaka.Resolution.HironakaNormalCrossingsBoundaryTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Resolution.HironakaLocalPrincipalization

/-! # Actual finite higher-stratum separation of an original NC carrier

The genuine higher highest stratum internally gives actual coordinate density,
so centre-relative and differential strict transforms agree at every performed
step. Bounded induction constructs an actual finite blowup tower, with literal
current differential strict carriers and literal accumulated old/new boundaries.
Every recorded centre is its whole attained original maximum of codimension at
least two; terminal original count is at most one. The entire terminal original
carrier is smooth and transverse to its actual SNC accumulated boundary, and
appending that carrier is genuinely SNC. The projection is an isomorphism on the
entire complement of the original carrier, without compactness or connectedness.

The arbitrary marked ideal parameter merely tracks the literal boundary through
geoTransformAlong. No marked-cosupport admissibility is asserted. The old ordered
colexicographic label tie-break is not compared with this geometric construction;
full canonical marked-ideal G9 remains open. Cartier count-one centre removal is
never used to erase the original carrier: the genuine tower stops at count one.
The two protected strict statement modules are not imported.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaNormalCrossingsBoundarySeparation
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  BlowupFlatCoordinates BlowupStrictSubmanifold NormalCrossings BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters RestrictEmptyTower

open Hironaka
noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual coordinate perturbations prove original density away from a higher highest stratum. -/
theorem subset_closure_sdiff_highest_of_two_le {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r) :
    H ⊆ closure (H \ {x | r ≤ branchMultiplicity hH x}) := by
  intro x hxH
  by_cases hx : r ≤ branchMultiplicity hH x
  · obtain ⟨Φ, hsrc, h0, hC, hHflat⟩ :=
      exists_highest_stratum_branch_adapted_coordinates hH hbound hx
    have hrn : r ≤ n := hx.trans (branchMultiplicity_le hH x)
    let i : Fin n := ⟨n-r, by omega⟩
    let j : Fin n := ⟨n-r+1, by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; dsimp [i,j] at this; omega
    have hi : n-r ≤ i.val := le_rfl
    have hj : n-r ≤ j.val := by dsimp [j]; omega
    have ht0 : (0 : ComplexModel n) ∈ Φ.target := by
      rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
    have hinv := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    rw [h0] at hinv
    have hcurve : Tendsto (fun t : ℂ => t • (EuclideanSpace.single j 1 : ComplexModel n))
        (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
      have hc : Continuous (fun t : ℂ => t • (EuclideanSpace.single j 1 : ComplexModel n)) :=
        continuous_id.smul continuous_const
      simpa using hc.tendsto (0 : ℂ)
    rw [mem_closure_iff_nhds]
    intro U hU
    have htarget : Φ.target ∈ 𝓝 (0 : ComplexModel n) := Φ.isOpen_target.mem_nhds ht0
    have hevT : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
        t • (EuclideanSpace.single j 1 : ComplexModel n) ∈ Φ.target :=
      mem_nhdsWithin_of_mem_nhds (hcurve htarget)
    have hevU : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
        (chartAt (ComplexModel n) x).symm
          (Φ.invFun (t • (EuclideanSpace.single j 1 : ComplexModel n))) ∈ U :=
      mem_nhdsWithin_of_mem_nhds ((hinv.comp hcurve) hU)
    have hev := hevT.and (hevU.and self_mem_nhdsWithin)
    obtain ⟨t, htT, htU, ht0⟩ := hev.exists
    obtain ⟨hdom, hcoord⟩ := flatInverse_mem Φ htT hsrc
    refine ⟨_, htU, (hHflat _ hdom).mpr ?_, ?_⟩
    · refine ⟨i, hi, ?_⟩
      change Φ.toFun (chartAt (ComplexModel n) x _) i = 0
      rw [hcoord]
      simp [hij]
    · intro hmem
      have hz := (hC _ hdom).mp hmem j hj
      rw [hcoord] at hz
      apply ht0
      simpa using hz
  · exact subset_closure ⟨hxH,hx⟩

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}

/-- The genuine higher highest-stratum step uses exactly the differential strict carrier. -/
theorem geoStrictTransform_highest_eq_strictTransform {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π) :
    geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H = strictTransform n π H :=
  BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ
    (subset_closure_sdiff_highest_of_two_le hH hr hbound)

/-- Actual count-one highest regularity gives the whole terminal original carrier. -/
theorem regularAtDim_of_branchMultiplicity_le_one {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ 1) {x : X} (hx : x ∈ H) :
    RegularAtDim (n := n) H x (n-1) := by
  have hC : {x | 1 ≤ branchMultiplicity hH x} = H := by
    ext x; exact branchMultiplicity_pos_iff hH x
  have hxC : 1 ≤ branchMultiplicity hH x := (branchMultiplicity_pos_iff hH x).mpr hx
  have hh := regularAtDim_highest_superlevel hH hbound hxC
  rwa [hC] at hh

/-- The actual whole original carrier is a closed smooth submanifold at count at most one. -/
theorem isClosedSubmanifold_of_branchMultiplicity_le_one {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ 1) : IsClosedSubmanifold n H :=
  ⟨hH.1, fun _ hx => ⟨n-1, regularAtDim_of_branchMultiplicity_le_one hH hbound hx⟩⟩

/-- At count at most one the actual common pair coordinates produce real transversality. -/
theorem isTransverse_of_boundaryAdapted_count_le_one {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E)
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    IsTransverse n H E := by
  intro x hx
  obtain ⟨Φ,S,B,hsrc,h0,hH,hB,hinj,hE⟩ := h.2.2 x
  have hc : S.card = 1 := by
    rw [← branchMultiplicity_eq_card (isNormalCrossingsCarrier_of_boundaryAdapted h) Φ h0 S hH]
    exact (hbound x).antisymm ((branchMultiplicity_pos_iff
      (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mpr hx)
  obtain ⟨j,hSj⟩ := Finset.card_eq_one.mp hc
  refine ⟨S,B,⟨Φ,hsrc,h0,?_⟩,fun i hi => ⟨(hB i hi).1,(hB i hi).2.symm⟩⟩
  rintro (_ | i) hi y hy hyΦ
  · change y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S
    rw [hH y ⟨hy,hyΦ⟩]
    simp [hSj,coordSubspace,flatCoord]
  · exact hE i hi y ⟨hy,hyΦ⟩

/-- The entire terminal carrier is a genuinely new singleton boundary coordinate. -/
theorem isSNCDivisor_append_original_of_count_le_one {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E)
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    IsSNCDivisor n (E ++ [H]) := by
  classical
  let E' := E.map (fun A => A) ++ [H]
  have hh : IsSNCDivisor n E' := by
    refine ⟨?_,fun x => ?_⟩
    · intro A hA
      rcases List.mem_append.mp hA with hA | hA
      · obtain ⟨A,hAE,rfl⟩ := List.mem_map.mp hA
        exact h.2.1 A hAE
      · rw [List.mem_singleton.mp hA]; exact h.1
    · obtain ⟨Φ,S,B,hsrc,h0,hH,hB,hinj,hE⟩ := h.2.2 x
      have hSone : x ∈ H → S.card = 1 := by
        intro hx
        rw [← branchMultiplicity_eq_card (isNormalCrossingsCarrier_of_boundaryAdapted h) Φ h0 S hH]
        exact (hbound x).antisymm ((branchMultiplicity_pos_iff
          (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mpr hx)
      let B' : Fin E'.length → Finset (Fin n) := fun i =>
        if hi : i.val < E.length then B ⟨i.val,hi⟩ else S
      refine ⟨B',⟨Φ,hsrc,h0,?_⟩,?_,?_⟩
      · intro i hi y hy hyΦ
        change x ∈ (E.map (fun A => A) ++ [H]).get i at hi
        change y ∈ (E.map (fun A => A) ++ [H]).get i ↔
          Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (B' i)
        rw [BlowupSNCTransform.get_map_append_singleton] at hi ⊢
        by_cases hiE : i.val < E.length
        · simp only [B',hiE,dif_pos] at hi ⊢
          exact hE _ hi y ⟨hy,hyΦ⟩
        · simp only [B',hiE] at hi ⊢
          obtain ⟨j,hSj⟩ := Finset.card_eq_one.mp (hSone hi)
          change y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S
          rw [hH y ⟨hy,hyΦ⟩]
          simp [hSj,coordSubspace,flatCoord]
      · intro i hi
        change x ∈ (E.map (fun A => A) ++ [H]).get i at hi
        rw [BlowupSNCTransform.get_map_append_singleton] at hi
        by_cases hiE : i.val < E.length
        · simp only [B',hiE,dif_pos] at hi ⊢
          exact (hB _ hi).1
        · simp only [B',hiE] at hi ⊢
          exact hSone hi
      · intro i hi i' hi' heq
        change x ∈ (E.map (fun A => A) ++ [H]).get i at hi
        change x ∈ (E.map (fun A => A) ++ [H]).get i' at hi'
        change B' i = B' i' at heq
        rw [BlowupSNCTransform.get_map_append_singleton] at hi hi'
        by_cases hiE : i.val < E.length
        · by_cases hi'E : i'.val < E.length
          · simp only [B',hiE,hi'E,dif_pos] at hi hi' heq
            have he := hinj hi hi' heq
            exact Fin.ext (congrArg (fun a : Fin E.length => a.val) he)
          · simp only [B',hiE,hi'E,dif_pos] at hi hi' heq
            have hdis := (hB _ hi).2
            rw [heq] at hdis
            have hempty := (Finset.disjoint_self_iff_empty S).mp hdis
            have hc := hSone hi'
            rw [hempty] at hc
            simp at hc
        · by_cases hi'E : i'.val < E.length
          · simp only [B',hiE,hi'E,dif_pos] at hi hi' heq
            have hdis := (hB _ hi').2
            rw [← heq] at hdis
            have hempty := (Finset.disjoint_self_iff_empty S).mp hdis
            have hc := hSone hi
            rw [hempty] at hc
            simp at hc
          · exact BlowupSNCTransform.eq_of_not_lt hiE hi'E
  simpa [E'] using hh

/-- An actual intrinsic higher centre, with real pair coordinates and attained maximum. -/
def IsHigherSeparationCentre (H : Set X) (E : List (Set X)) (C : Set X) : Prop :=
  ∃ h : IsBoundaryAdaptedCarrier (n := n) H E, ∃ r : ℕ,
    2 ≤ r ∧ (∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) ∧
    C = {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ∧ C.Nonempty

/-- A real higher original maximum internally supplies the exact differential strict step. -/
theorem exists_higher_boundary_blowup {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {b : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hnot : ¬ ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ b ∧
      (∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) ∧
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}.Nonempty ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
        (_ : IsComplexManifold n Y) (π : Y → X),
        IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π ∧
        ∃ h' : IsBoundaryAdaptedCarrier (n := n) (strictTransform n π H)
          (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
            [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]),
          ∀ z : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') z ≤ r-1 := by
  classical
  obtain ⟨x,hx⟩ := not_forall.mp hnot
  have hxH : x ∈ H := (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mp
    (by omega)
  obtain ⟨r,hr,hrn,hmax,hatt,-,-,-⟩ :=
    exists_highest_multiplicity_stratum (isNormalCrossingsCarrier_of_boundaryAdapted h) ⟨x,hxH⟩
  have hr2 : 2 ≤ r := by have := hmax x; omega
  have hrb : r ≤ b := by obtain ⟨y,hy⟩ := hatt; rw [← hy]; exact hbound y
  obtain ⟨Y,hYtop,hYchart,hYcm,π,hπ⟩ :=
    exists_highest_stratum_blowup (isNormalCrossingsCarrier_of_boundaryAdapted h) hr hmax
  have hgeo := geoStrictTransform_highest_eq_strictTransform
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hr2 hmax hπ
  have hex : ∃ hp : IsBoundaryAdaptedCarrier (n := n)
      (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H)
      (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]),
      ∀ z : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) z ≤ r-1 :=
    ⟨boundaryAdapted_strict_highest h hmax hπ, branchMultiplicity_boundary_strict_highest_le h hmax hπ⟩
  rw [hgeo] at hex
  obtain ⟨hp,hcount⟩ := hex
  refine ⟨r,hr2,hrb,hmax,?_,Y,hYtop,hYchart,hYcm,π,hπ,hp,hcount⟩
  obtain ⟨y,hy⟩ := hatt
  exact ⟨y,hy.ge⟩

/-- Every actual higher centre is contained in the real current original carrier. -/
theorem higherSeparationCentre_subset {H : Set X} {E : List (Set X)} {C : Set X}
    (hc : IsHigherSeparationCentre (n := n) H E C) : C ⊆ H := by
  obtain ⟨h,r,hr,hbound,rfl,hne⟩ := hc
  intro x hx
  change r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x at hx
  exact (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mp (by omega)

/-- Every recorded higher centre has actual smooth codimension at least two and actual boundary transversality. -/
theorem higherSeparationCentre_geometry {H : Set X} {E : List (Set X)} {C : Set X}
    (hc : IsHigherSeparationCentre (n := n) H E C) :
    IsSNCDivisor n E ∧ IsClosedSubmanifold n C ∧ IsTransverse n C E ∧
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ n ∧ ∀ x ∈ C, RegularAtDim (n := n) C x (n-r) := by
  obtain ⟨h,r,hr,hbound,rfl,hne⟩ := hc
  have hrn : r ≤ n := by
    obtain ⟨x,hx⟩ := hne
    exact hx.trans (branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  refine ⟨isSNCDivisor_of_boundaryAdapted h,
    isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound,
    ?_,r,hr,hrn,fun x hx => regularAtDim_highest_superlevel
      (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx⟩
  intro x hx
  obtain ⟨Φ,S,B,hsrc,h0,hH,hB,hinj,hE⟩ := h.2.2 x
  obtain ⟨-,hC⟩ := highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx Φ h0 S hH
  refine ⟨S,B,⟨Φ,hsrc,h0,?_⟩,fun i hi => ⟨(hB i hi).1,(hB i hi).2.symm⟩⟩
  rintro (_ | i) hi y hy hyΦ
  · exact hC y ⟨hy,hyΦ⟩
  · exact hE i hi y ⟨hy,hyΦ⟩

private theorem stageCentres_append_of_transport {A B D : CMfd.{u} n}
    (T : BlowupTower A B) (S : BlowupTower B D)
    (P : ∀ {V : CMfd.{u} n}, BlowupTower A V → Set V → Prop)
    (Q : ∀ {V : CMfd.{u} n}, BlowupTower B V → Set V → Prop)
    (hT : StageCentres P T) (hS : StageCentres Q S)
    (ht : ∀ {V : CMfd.{u} n} (R : BlowupTower B V) (C : Set V), Q R C → P (T.append R) C) :
    StageCentres P (T.append S) := by
  induction S with
  | refl => exact hT
  | step S C π hπ ih => exact ⟨ih hS.1,ht S C hS.2⟩

/-- Genuine finite separation, with internally produced higher centres at every actual prefix. -/
theorem exists_boundary_separation_tower_bound {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) {b : ℕ}
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    ∃ D : CMfd.{u} n, ∃ T : BlowupTower A D, T.length ≤ b-1 ∧
      (∃ hf : IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj H) (geoTransformAlong M T).E,
        ∀ z : D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hf) z ≤ 1) ∧
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T := by
  classical
  induction b generalizing A with
  | zero =>
      have hs : strictTransform n (id : A → A) H = H := by
        simp [strictTransform,exceptionalLocus_id,h.1.closure_eq]
      refine ⟨A,.refl,by simp,?_,trivial⟩
      simp only [BlowupTower.proj_refl,geoTransformAlong_refl,hs]
      exact ⟨h,fun x => (hbound x).trans (by omega)⟩
  | succ b ih =>
      by_cases hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1
      · have hs : strictTransform n (id : A → A) H = H := by
          simp [strictTransform,exceptionalLocus_id,h.1.closure_eq]
        refine ⟨A,.refl,by simp,?_,trivial⟩
        simp only [BlowupTower.proj_refl,geoTransformAlong_refl,hs]
        exact ⟨h,hone⟩
      · obtain ⟨r,hr,hrb,hmax,hne,Y,hYtop,hYchart,hYcm,π,hπ,hp,hcount⟩ :=
          exists_higher_boundary_blowup h hbound hone
        let B : CMfd.{u} n := CMfd.of (n := n) Y
        let C : Set A := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
        let T₀ : BlowupTower A B := .step .refl C π hπ
        let M' : MarkedIdeal n B := geoTransformAlong M T₀
        have hcount' : ∀ z : B, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) z ≤ b :=
          fun z => (hcount z).trans (by omega)
        obtain ⟨D,S,hlen,hfinal,hS⟩ := ih M' hp hcount'
        have hs₀ : T₀.proj = π := rfl
        have hstrict : ∀ {V : CMfd.{u} n} (R : BlowupTower B V),
            strictTransform n (T₀.append R).proj H = strictTransform n R.proj (strictTransform n π H) := by
          intro V R
          rw [BlowupTower.proj_append,hs₀]
          exact StrictTransformComposition.strictTransform_comp hπ.contMDiff R.contMDiff_proj H
        refine ⟨D,T₀.append S,?_,?_,?_⟩
        · rw [BlowupTower.length_append]
          have hlen₀ : T₀.length = 1 := rfl
          rw [hlen₀]
          omega
        · rw [hstrict S,geoTransformAlong_append]
          exact hfinal
        · apply stageCentres_append_of_transport T₀ S _ _ ?_ hS
          · intro V R C' hc
            rw [hstrict R,geoTransformAlong_append]
            exact hc
          · have hs : strictTransform n (id : A → A) H = H := by
              simp [strictTransform,exceptionalLocus_id,h.1.closure_eq]
            change True ∧ IsHigherSeparationCentre (n := n) (strictTransform n (id : A → A) H) M.E C
            rw [hs]
            exact ⟨trivial,h,r,hr,hmax,rfl,hne⟩

/-- Every actual recorded stage has SNC accumulated boundary, a genuine transverse
smooth centre of codimension at least two, and that centre lies in the current original carrier. -/
theorem stageGeometry_of_higherSeparationCentres {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A} :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      StageCentres (fun R C => IsSNCDivisor n (geoTransformAlong M R).E ∧
        C.Nonempty ∧ C ⊆ strictTransform n R.proj H ∧
        IsClosedSubmanifold n C ∧ IsTransverse n C (geoTransformAlong M R).E ∧
        ∃ r : ℕ, 2 ≤ r ∧ r ≤ n ∧ ∀ x ∈ C, RegularAtDim (n := n) C x (n-r)) T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hc => by
      refine ⟨stageGeometry_of_higherSeparationCentres M T hc.1,?_⟩
      obtain ⟨hS,hC,htrans,r,hr,hrn,hreg⟩ := higherSeparationCentre_geometry hc.2
      have hne : C.Nonempty := by obtain ⟨_,_,_,_,_,hne⟩ := hc.2; exact hne
      exact ⟨hS,hne,higherSeparationCentre_subset hc.2,hC,htrans,r,hr,hrn,hreg⟩

/-- Genuine higher separation centres all lie over the original closed carrier. -/
theorem centresOver_of_higherSeparationCentres {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A} (hH : IsClosed H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T → CentresOver H T
  | _,.refl,_ => trivial
  | _,.step T _C _π _hπ,hc =>
      ⟨centresOver_of_higherSeparationCentres M hH T hc.1,
        (higherSeparationCentre_subset hc.2).trans (EmbeddedFromResolution.strictTransform_subset_preimage hH T)⟩

/-- The actual finite separation projection is an isomorphism over the entire original complement. -/
theorem isIsomorphismOver_compl_of_higherSeparationCentres {A D : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A} (hH : IsClosed H) (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong M R).E C) T) :
    IsIsomorphismOver n T.proj Hᶜ := by
  let U : TopologicalSpace.Opens A := ⟨Hᶜ,hH.isOpen_compl⟩
  have hav := centresAvoid_of_centresOver U (F := H) (by exact disjoint_compl_left)
    T (centresOver_of_higherSeparationCentres M hH T hc)
  apply HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence
  simpa [U] using EmbeddedFromResolution.image_exceptionalLocus_subset_compl U T hav

/-- A real finite higher-stratum tower separates the whole original carrier from
itself while preserving the literal accumulated boundary at every stage. -/
theorem exists_boundary_separation_tower {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    ∃ D : CMfd.{u} n, ∃ T : BlowupTower A D, T.length ≤ n-1 ∧
      (∃ hf : IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj H) (geoTransformAlong M T).E,
        (∀ z : D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hf) z ≤ 1)) ∧
      IsClosedSubmanifold n (strictTransform n T.proj H) ∧
      IsTransverse n (strictTransform n T.proj H) (geoTransformAlong M T).E ∧
      IsSNCDivisor n ((geoTransformAlong M T).E ++ [strictTransform n T.proj H]) ∧
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T ∧
      CentresOver H T ∧ IsIsomorphismOver n T.proj Hᶜ := by
  obtain ⟨D,T,hlen,⟨hf,hcount⟩,hc⟩ := exists_boundary_separation_tower_bound M h
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  exact ⟨D,T,hlen,⟨hf,hcount⟩,
    isClosedSubmanifold_of_branchMultiplicity_le_one (isNormalCrossingsCarrier_of_boundaryAdapted hf) hcount,
    isTransverse_of_boundaryAdapted_count_le_one hf hcount,
    isSNCDivisor_append_original_of_count_le_one hf hcount,hc,
    centresOver_of_higherSeparationCentres M h.1 T hc,
    isIsomorphismOver_compl_of_higherSeparationCentres M h.1 T hc⟩

/-- An empty original carrier internally produces the genuine length-zero tower. -/
theorem exists_length_zero_separation_of_empty {A : CMfd.{u} n}
    (M : MarkedIdeal n A) (h : IsBoundaryAdaptedCarrier (n := n) (∅ : Set A) M.E) :
    ∃ D : CMfd.{u} n, ∃ T : BlowupTower A D, T.length = 0 ∧
      IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj ∅) (geoTransformAlong M T).E ∧
      IsIsomorphismOver n T.proj (Set.univ : Set A) := by
  have hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 0 := by
    intro x
    have hn : ¬ 0 < branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x := by
      intro hx
      exact (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mp hx
    omega
  obtain ⟨D,T,hlen,⟨hf,hcount⟩,hc⟩ := exists_boundary_separation_tower_bound M h hb
  refine ⟨D,T,by omega,hf,?_⟩
  simpa using isIsomorphismOver_compl_of_higherSeparationCentres M h.1 T hc

/-- Every actual NC original carrier internally produces an empty-boundary real
finite separation tower, without compactness or a supplied branch labelling. -/
theorem exists_normalCrossings_separation_tower {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∃ D : CMfd.{u} n, ∃ T : BlowupTower A D, T.length ≤ n-1 ∧
      IsClosedSubmanifold n (strictTransform n T.proj H) ∧
      IsTransverse n (strictTransform n T.proj H)
        (geoTransformAlong (⟨univ,[],vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n A) T).E ∧
      IsSNCDivisor n
        ((geoTransformAlong (⟨univ,[],vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n A) T).E ++
          [strictTransform n T.proj H]) ∧
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H)
        (geoTransformAlong (⟨univ,[],vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n A) R).E C) T ∧
      CentresOver H T ∧ IsIsomorphismOver n T.proj Hᶜ := by
  obtain ⟨D,T,hlen,hf,hsm,htrans,hSNC,hc,hcov,hiso⟩ := exists_boundary_separation_tower
    (⟨univ,[],vanishingIdeal (n := n) H,1⟩ : MarkedIdeal n A) (boundaryAdapted_nil hH)
  exact ⟨D,T,hlen,hsm,htrans,hSNC,hc,hcov,hiso⟩

end
end Hironaka.HironakaNormalCrossingsBoundarySeparation

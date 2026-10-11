/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsBiholomorphicMultiplicity
import Hironaka.Resolution.HironakaNormalCrossingsBoundarySeparation
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Resolution.HironakaBlowupComparisonCocycle

/-! # Actual finite geometric NC separation under arbitrary genuine blowup choices

Individual choices provide actual single blowups, with no finite tower,
termination or naturality certificate. The internally attained intrinsic
maximum, literal transformed pair and strict-original count decrease drive
an actual transparent bounded recursion. Every output records the genuinely
chosen first blowup and actual smaller tail. Simultaneous bounded induction
internally aligns the whole actual centres and constructs genuine stagewise
comparisons for arbitrary choices and actual original biholomorphisms.

Universal uniqueness gives the actual last-stage identity, inverse and triple
cocycle. Full differential strict originals and literal accumulated finite
boundaries correspond independently of marked ideal coherence or test-tower
admissibility. Internal genuine default choices give a natural finite
geometric separation, smooth terminal original, transverse SNC boundary,
codimension-at-least-two centres and an isomorphism over the original complement.

This is the intrinsic unordered geometric NC procedure. The old ordered
marked-ideal colexicographic label tie-break and additional marked-cosupport
admissibility remain separate, and full canonical marked-ideal G9 stays open.
Count-one Cartier centres are never blown up by this procedure. The two
protected strict statement modules are not imported.
-/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u
namespace Hironaka.HironakaNormalCrossingsSeparationChoiceComparison
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsBiholomorphicMultiplicity
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupStrictSubmanifold MarkedIdeals
  MarkedIdeals.MarkedIdeal HironakaStageCenters NormalCrossings RestrictEmptyTower

open Hironaka

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Any two holomorphic lifts of actual aligned blowups agree by their universal property. -/
theorem lift_eq_of_commuting {A' A B' B : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    {C' : Set A'} {C : Set A} {π' : B' → A'} {π : B → A}
    (hπ' : IsBlowupAlong n C' π') (hπ : IsBlowupAlong n C π)
    (hC : Φ ⁻¹' C = C') {f g : B' → B}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hcommf : ∀ z, π (f z) = Φ (π' z))
    (hcommg : ∀ z, π (g z) = Φ (π' z)) : f = g := by
  have htransport := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply hπ
  rw [hC] at htransport
  obtain ⟨e,-,hunique⟩ := BlowupUniqueness.existsUnique_comparison hπ' htransport
  have hf' : (Φ.symm ∘ π) ∘ f = π' := by
    funext z
    simp only [Function.comp_apply,hcommf,Φ.symm_apply_apply]
  have hg' : (Φ.symm ∘ π) ∘ g = π' := by
    funext z
    simp only [Function.comp_apply,hcommg,Φ.symm_apply_apply]
  exact (hunique f ⟨hf,hf'⟩).trans (hunique g ⟨hg,hg'⟩).symm

/-- Genuine aligned blowups internally produce their unique actual biholomorphic lift. -/
theorem exists_unique_lift {A' A B' B : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    {C' : Set A'} {C : Set A} {π' : B' → A'} {π : B → A}
    (hπ' : IsBlowupAlong n C' π') (hπ : IsBlowupAlong n C π)
    (hC : Φ ⁻¹' C = C') :
    ∃! χ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B,
      ∀ z, π (χ z) = Φ (π' z) := by
  have htransport := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply hπ
  rw [hC] at htransport
  obtain ⟨e,f,he,hf,hπe,hπf,hfe,hef⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hπ' htransport
  let χ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B :=
    ⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩
  have hcomm : ∀ z, π (χ z) = Φ (π' z) := by
    intro z
    change π (e z) = Φ (π' z)
    have ht := congrArg Φ (congrFun hπe z)
    simpa using ht
  refine ⟨χ,hcomm,?_⟩
  intro χ' hχ'
  exact Diffeomorph.ext (congrFun (lift_eq_of_commuting Φ hπ' hπ hC
    χ'.contMDiff χ.contMDiff hχ' hcomm))

/-- The whole geometric strict carrier follows the actual commuting square. -/
theorem geoStrictTransform_preimage_of_square {A' A B' B : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (χ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B)
    (π' : B' → A') (π : B → A) (C H : Set A)
    (hcomm : ∀ z, π (χ z) = Φ (π' z)) :
    geoStrictTransform π' (Φ ⁻¹' C) (Φ ⁻¹' H) = χ ⁻¹' geoStrictTransform π C H := by
  rw [← BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ π C H]
  unfold geoStrictTransform
  rw [← preimage_sdiff,← preimage_comp]
  congr 2
  exact funext fun z => (hcomm z).symm

/-- Literal accumulated boundary transport uses only actual sets, not marked admissibility. -/
theorem boundary_eq_of_towerIso {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsTowerIso Φ T' T χ) (M' : MarkedIdeal n A') (M : MarkedIdeal n A)
    (hE : M'.E = M.E.map (fun E => Φ ⁻¹' E)) :
    (geoTransformAlong M' T').E = (geoTransformAlong M T).E.map (fun E => χ ⁻¹' E) := by
  induction hi with
  | refl => exact hE
  | @step Y' Y Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    simp only [geoTransformAlong_step,geoTransform_E,List.map_append,List.map_singleton,List.map_map]
    rw [ih,hC.symm,List.map_map]
    congr 1
    · apply List.map_congr_left
      intro E hmem
      exact geoStrictTransform_preimage_of_square χ χ₁ π' π C E hcomm
    · congr 1
      ext z
      exact Iff.of_eq (congrArg (fun y => y ∈ C) (hcomm z).symm)

/-- Two genuine stagewise tower comparisons over a fixed base have the same last map. -/
theorem towerIso_unique_last {A' A D' D : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ ψ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ D}
    (hi : IsTowerIso Φ T' T χ) (hj : IsTowerIso Φ T' T ψ) : χ = ψ := by
  induction hi with
  | refl => exact hj.refl_inv.symm
  | @step Y' Y Z' Z T' T χ hi C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    obtain ⟨ψ₀,hψ₀,hcommψ,hCψ⟩ := hj.step_inv
    have he := ih hψ₀
    rw [← he] at hcommψ
    exact Diffeomorph.ext (congrFun (lift_eq_of_commuting χ hπ' hπ hC
      χ₁.contMDiff ψ.contMDiff hcomm hcommψ))

/-- Individual actual higher blowups, without a supplied tower or naturality property. -/
structure HigherBlowupChoices (n : ℕ) where
  choose {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (r : ℕ) (hr : 2 ≤ r)
    (hbound : ∀ x : A, branchMultiplicity hH x ≤ r) :
    Σ D : CMfd.{u} n, {π : D → A // IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π}

/-- Actual highest-stratum existence internally supplies individual genuine choices. -/
def defaultHigherBlowupChoices : HigherBlowupChoices.{u} n where
  choose hH r hr hbound := by
    have hex := exists_highest_stratum_blowup hH (by omega : 0 < r) hbound
    let Y := Classical.choose hex
    letI := Classical.choose (Classical.choose_spec hex)
    letI := Classical.choose (Classical.choose_spec (Classical.choose_spec hex))
    letI := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex)))
    have hp := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex)))
    exact ⟨CMfd.of (n := n) Y,Classical.choose hp,Classical.choose_spec hp⟩

private theorem exists_higher_maximum {A : CMfd.{u} n} {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {b : ℕ}
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hnot : ¬ ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ b ∧
      (∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) ∧
      {x | branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x = r}.Nonempty := by
  classical
  obtain ⟨x,hx⟩ := not_forall.mp hnot
  have hxH : x ∈ H := (branchMultiplicity_pos_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x).mp
    (by omega)
  obtain ⟨r,hr,hrn,hmax,hatt,-,-,-⟩ :=
    exists_highest_multiplicity_stratum (isNormalCrossingsCarrier_of_boundaryAdapted h) ⟨x,hxH⟩
  have hr2 : 2 ≤ r := by have := hmax x; omega
  have hrb : r ≤ b := by obtain ⟨y,hy⟩ := hatt; rw [← hy]; exact hbound y
  exact ⟨r,hr2,hrb,hmax,hatt⟩

/-- Data of the internally computed higher maximum and the chosen genuine first blowup. -/
structure HigherStep {A : CMfd.{u} n} {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) (b : ℕ) where
  r : ℕ
  hr : 2 ≤ r
  hrb : r ≤ b
  hmax : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r
  hatt : {x | branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x = r}.Nonempty
  D : CMfd.{u} n
  π : D → A
  hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π
  hp : IsBoundaryAdaptedCarrier (n := n) (strictTransform n π H)
    (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
      [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}])
  hcount : ∀ z : D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) z ≤ r-1

/-- This construction invokes the individual choice on the genuinely computed first centre. -/
def higherStep (β : HigherBlowupChoices.{u} n) {A : CMfd.{u} n} {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {b : ℕ}
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b)
    (hnot : ¬ ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    HigherStep h b := by
  let hex := exists_higher_maximum h hbound hnot
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  let data := β.choose (isNormalCrossingsCarrier_of_boundaryAdapted h) r hr.1 hr.2.2.1
  let π := data.2.val
  have hπ := data.2.property
  have hgeo := geoStrictTransform_highest_eq_strictTransform
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hr.1 hr.2.2.1 hπ
  have hx : ∃ hp : IsBoundaryAdaptedCarrier (n := n)
      (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H)
      (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]),
      ∀ z : data.1, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hp) z ≤ r-1 :=
    ⟨boundaryAdapted_strict_highest h hr.2.2.1 hπ,
      branchMultiplicity_boundary_strict_highest_le h hr.2.2.1 hπ⟩
  rw [hgeo] at hx
  exact ⟨r,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,data.1,π,hπ,Classical.choose hx,Classical.choose_spec hx⟩

/-- The recorded actual finite output carries conclusions derived internally by recursion. -/
structure SeparationOutput {A : CMfd.{u} n} (M : MarkedIdeal n A) (H : Set A) (b : ℕ) where
  D : CMfd.{u} n
  T : BlowupTower A D
  length_le : T.length ≤ b-1
  pair : IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj H) (geoTransformAlong M T).E
  count_le_one : ∀ z : D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted pair) z ≤ 1
  centres : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
    (strictTransform n R.proj H) (geoTransformAlong M R).E C) T

private def stopOutput {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (b : ℕ)
    (hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    SeparationOutput M H b := by
  have hs : strictTransform n (id : A → A) H = H := by
    simp [strictTransform,exceptionalLocus_id,h.1.closure_eq]
  refine ⟨A,.refl,by simp,?_,?_,trivial⟩
  · simpa only [BlowupTower.proj_refl,geoTransformAlong_refl,hs] using h
  · simpa only [BlowupTower.proj_refl,geoTransformAlong_refl,hs] using hone

private theorem stageCentres_append {A B D : CMfd.{u} n}
    (T : BlowupTower A B) (S : BlowupTower B D)
    (P : ∀ {V : CMfd.{u} n}, BlowupTower A V → Set V → Prop)
    (Q : ∀ {V : CMfd.{u} n}, BlowupTower B V → Set V → Prop)
    (hT : StageCentres P T) (hS : StageCentres Q S)
    (ht : ∀ {V : CMfd.{u} n} (R : BlowupTower B V) (C : Set V), Q R C → P (T.append R) C) :
    StageCentres P (T.append S) := by
  induction S with
  | refl => exact hT
  | step S C π hπ ih => exact ⟨ih hS.1,ht S C hS.2⟩

private def appendOutput {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (b : ℕ) (s : HigherStep h (b+1))
    (o : SeparationOutput
      (geoTransformAlong M (.step .refl _ s.π s.hπ)) (strictTransform n s.π H) b) :
    SeparationOutput M H (b+1) := by
  let T₀ : BlowupTower A s.D := .step .refl _ s.π s.hπ
  have hs₀ : T₀.proj = s.π := rfl
  have hstrict : ∀ {V : CMfd.{u} n} (R : BlowupTower s.D V),
      strictTransform n (T₀.append R).proj H = strictTransform n R.proj (strictTransform n s.π H) := by
    intro V R
    rw [BlowupTower.proj_append,hs₀]
    exact StrictTransformComposition.strictTransform_comp s.hπ.contMDiff R.contMDiff_proj H
  refine ⟨o.D,T₀.append o.T,?_,?_,?_,?_⟩
  · rw [BlowupTower.length_append]
    have ht : T₀.length = 1 := rfl
    have := o.length_le
    have := s.hr
    have := s.hrb
    rw [ht]
    omega
  · rw [hstrict,geoTransformAlong_append]
    exact o.pair
  · have hc := o.count_le_one
    simpa only [hstrict,geoTransformAlong_append] using hc
  · apply stageCentres_append T₀ o.T _ _ ?_ o.centres
    · intro V R C hc
      rw [hstrict,geoTransformAlong_append]
      exact hc
    · have hs : strictTransform n (id : A → A) H = H := by
        simp [strictTransform,exceptionalLocus_id,h.1.closure_eq]
      change True ∧ IsHigherSeparationCentre (n := n) (strictTransform n (id : A → A) H) M.E _
      rw [hs]
      refine ⟨trivial,h,s.r,s.hr,s.hmax,rfl,?_⟩
      obtain ⟨x,hx⟩ := s.hatt
      exact ⟨x,hx.ge⟩

/-- Real bounded recursion records the actual chosen first blowup and its actual smaller tail. -/
def separateWith (β : HigherBlowupChoices.{u} n) : (b : ℕ) →
    {A : CMfd.{u} n} → (M : MarkedIdeal n A) → {H : Set A} →
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) →
    (∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) →
    SeparationOutput M H b
  | 0,_,M,_,h,hbound => stopOutput M h 0 (fun x => (hbound x).trans (by omega))
  | b+1,_,M,H,h,hbound =>
    if hone : ∀ x, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1 then
      stopOutput M h (b+1) hone
    else
      let s := higherStep β h hbound hone
      let M' := geoTransformAlong M (.step .refl _ s.π s.hπ)
      let tail := separateWith β b M' s.hp (fun z => (s.hcount z).trans (by have := s.hrb; omega))
      appendOutput M h b s tail

private theorem strictTransform_diffeomorph {A' A : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsClosed H) : strictTransform n Φ H = Φ ⁻¹' H := by
  have he : exceptionalLocus n Φ = ∅ := by
    ext x
    simp only [mem_empty_iff_false,iff_false]
    exact MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply x
  simp only [strictTransform,he,sdiff_empty,(hH.preimage Φ.contMDiff.continuous).closure_eq]

/-- The entire differential strict original follows any genuine biholomorphic projection square. -/
theorem strictTransform_preimage_of_square {A' A B' B : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (χ : B' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B)
    {π' : B' → A'} {π : B → A}
    (hπ' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π')
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (H : Set A) (hH : IsClosed H) (hcomm : ∀ z, π (χ z) = Φ (π' z)) :
    strictTransform n π' (Φ ⁻¹' H) = χ ⁻¹' strictTransform n π H := by
  have hf : Φ ∘ π' = π ∘ χ := funext fun z => (hcomm z).symm
  calc
    strictTransform n π' (Φ ⁻¹' H) = strictTransform n (Φ ∘ π') H := by
      rw [StrictTransformComposition.strictTransform_comp Φ.contMDiff hπ',strictTransform_diffeomorph Φ hH]
    _ = strictTransform n (π ∘ χ) H := by rw [hf]
    _ = χ ⁻¹' strictTransform n π H := by
      rw [StrictTransformComposition.strictTransform_comp hπ χ.contMDiff]
      exact strictTransform_diffeomorph χ isClosed_closure

private theorem separateWith_stop_eq (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b+1)
    (hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    separateWith β (b+1) M h hb = stopOutput M h (b+1) hone := by
  rw [separateWith]
  exact dif_pos hone

private theorem separateWith_step_eq (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b+1)
    (hnot : ¬ ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1) :
    separateWith β (b+1) M h hb =
      let s := higherStep β h hb hnot
      let M' := geoTransformAlong M (.step .refl _ s.π s.hπ)
      appendOutput M h b s (separateWith β b M' s.hp
        (fun z => (s.hcount z).trans (by have := s.hrb; omega))) := by
  rw [separateWith]
  exact dif_neg hnot

/-- Arbitrary genuine individual choices internally produce stagewise comparisons of their finite procedures. -/
theorem separateWith_comparison (β' β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A' A : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M' : MarkedIdeal n A') (M : MarkedIdeal n A) {H' : Set A'} {H : Set A}
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hH : H' = Φ ⁻¹' H) (hE : M'.E = M.E.map (fun E => Φ ⁻¹' E))
    (hbound' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b)
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    ∃ χ : (separateWith β' b M' h' hbound').D
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (separateWith β b M h hbound).D,
      IsTowerIso Φ (separateWith β' b M' h' hbound').T (separateWith β b M h hbound).T χ := by
  induction b generalizing A' A with
  | zero =>
    subst H'
    exact ⟨Φ,IsTowerIso.refl⟩
  | succ b ih =>
    subst H'
    have hstop := branchMultiplicity_bound_diffeomorph_iff Φ
      (isNormalCrossingsCarrier_of_boundaryAdapted h) (isNormalCrossingsCarrier_of_boundaryAdapted h') 1
    by_cases hone : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ 1
    · have hone' := hstop.mpr hone
      rw [separateWith_stop_eq β' b M' h' hbound' hone',separateWith_stop_eq β b M h hbound hone]
      exact ⟨Φ,IsTowerIso.refl⟩
    · have hone' : ¬ ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ 1 :=
        fun hc => hone (hstop.mp hc)
      let s := higherStep β h hbound hone
      let s' := higherStep β' h' hbound' hone'
      have hrs : s'.r = s.r := by
        apply Nat.le_antisymm
        · obtain ⟨x,hx⟩ := s'.hatt
          have hc := s.hmax (Φ x)
          rw [← branchMultiplicity_diffeomorph Φ
            (isNormalCrossingsCarrier_of_boundaryAdapted h) (isNormalCrossingsCarrier_of_boundaryAdapted h')] at hc
          rw [hx] at hc
          exact hc
        · obtain ⟨x,hx⟩ := s.hatt
          have hc := s'.hmax (Φ.symm x)
          rw [branchMultiplicity_diffeomorph Φ
            (isNormalCrossingsCarrier_of_boundaryAdapted h) (isNormalCrossingsCarrier_of_boundaryAdapted h'),Φ.apply_symm_apply,hx] at hc
          exact hc
      have hC : Φ ⁻¹' {x | s.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} =
          {x | s'.r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x} := by
        ext x
        simp only [mem_preimage,mem_ofPred_eq,hrs,branchMultiplicity_diffeomorph Φ
          (isNormalCrossingsCarrier_of_boundaryAdapted h) (isNormalCrossingsCarrier_of_boundaryAdapted h')]
      obtain ⟨χ₀,hcomm,-⟩ := exists_unique_lift Φ s'.hπ s.hπ hC
      let T₀ : BlowupTower A s.D := .step .refl _ s.π s.hπ
      let T₀' : BlowupTower A' s'.D := .step .refl _ s'.π s'.hπ
      let N := geoTransformAlong M T₀
      let N' := geoTransformAlong M' T₀'
      have hi₀ : IsTowerIso Φ T₀' T₀ χ₀ := IsTowerIso.step IsTowerIso.refl s'.hπ s.hπ χ₀ hcomm hC
      have hH₀ : strictTransform n s'.π (Φ ⁻¹' H) = χ₀ ⁻¹' strictTransform n s.π H :=
        strictTransform_preimage_of_square Φ χ₀ s'.hπ.contMDiff s.hπ.contMDiff H h.1 hcomm
      have hE₀ : N'.E = N.E.map (fun E => χ₀ ⁻¹' E) := boundary_eq_of_towerIso hi₀ M' M hE
      have hb : ∀ z : s.D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted s.hp) z ≤ b :=
        fun z => (s.hcount z).trans (by have := s.hrb; omega)
      have hb' : ∀ z : s'.D, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted s'.hp) z ≤ b :=
        fun z => (s'.hcount z).trans (by have := s'.hrb; omega)
      obtain ⟨χ,hχ⟩ := ih χ₀ N' N s'.hp s.hp hH₀ hE₀ hb' hb
      rw [separateWith_step_eq β' b M' h' hbound' hone',separateWith_step_eq β b M h hbound hone]
      exact ⟨χ,hi₀.append hχ⟩

/-- The actual comparison also identifies the whole differential original and literal final boundary. -/
theorem separateWith_whole_dictionary (β' β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A' A : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M' : MarkedIdeal n A') (M : MarkedIdeal n A) {H' : Set A'} {H : Set A}
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hH : H' = Φ ⁻¹' H) (hE : M'.E = M.E.map (fun E => Φ ⁻¹' E))
    (hbound' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b)
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    let o' := separateWith β' b M' h' hbound'
    let o := separateWith β b M h hbound
    ∃ χ : o'.D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ o.D,
      IsTowerIso Φ o'.T o.T χ ∧ o'.T.length = o.T.length ∧
      strictTransform n o'.T.proj H' = χ ⁻¹' strictTransform n o.T.proj H ∧
      (geoTransformAlong M' o'.T).E = (geoTransformAlong M o.T).E.map (fun E => χ ⁻¹' E) := by
  obtain ⟨χ,hi⟩ := separateWith_comparison β' β b Φ M' M h' h hH hE hbound' hbound
  refine ⟨χ,hi,hi.length_eq,?_,boundary_eq_of_towerIso hi M' M hE⟩
  exact (congrArg (strictTransform n (separateWith β' b M' h' hbound').T.proj) hH).trans
    (strictTransform_preimage_of_square Φ χ (separateWith β' b M' h' hbound').T.contMDiff_proj
      (separateWith β b M h hbound).T.contMDiff_proj H h.1 (fun z => (hi.proj_comm z).symm))

/-- Genuine comparisons of three internally produced finite procedures obey the actual base-map cocycle. -/
theorem separateWith_comparison_cocycle (β'' β' β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A'' A' A : CMfd.{u} n}
    (Φ : A'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A')
    (Ψ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M'' : MarkedIdeal n A'') (M' : MarkedIdeal n A') (M : MarkedIdeal n A)
    {H'' : Set A''} {H' : Set A'} {H : Set A}
    (h'' : IsBoundaryAdaptedCarrier (n := n) H'' M''.E)
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hH₁ : H'' = Φ ⁻¹' H') (hE₁ : M''.E = M'.E.map (fun E => Φ ⁻¹' E))
    (hH₂ : H' = Ψ ⁻¹' H) (hE₂ : M'.E = M.E.map (fun E => Ψ ⁻¹' E))
    (hb'' : ∀ x : A'', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h'') x ≤ b)
    (hb' : ∀ x : A', branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') x ≤ b)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    let o'' := separateWith β'' b M'' h'' hb''
    let o' := separateWith β' b M' h' hb'
    let o := separateWith β b M h hb
    ∃ χ₁ : o''.D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ o'.D,
    ∃ χ₂ : o'.D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ o.D,
    ∃ χ₃ : o''.D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ o.D,
      IsTowerIso Φ o''.T o'.T χ₁ ∧ IsTowerIso Ψ o'.T o.T χ₂ ∧
      IsTowerIso (Φ.trans Ψ) o''.T o.T χ₃ ∧ χ₁.trans χ₂ = χ₃ := by
  have hH₃ : H'' = (Φ.trans Ψ) ⁻¹' H := by
    rw [hH₁,hH₂,Diffeomorph.coe_trans,preimage_comp]
  have hE₃ : M''.E = M.E.map (fun E => (Φ.trans Ψ) ⁻¹' E) := by
    rw [hE₁,hE₂,List.map_map]
    rfl
  obtain ⟨χ₁,h₁⟩ := separateWith_comparison β'' β' b Φ M'' M' h'' h' hH₁ hE₁ hb'' hb'
  obtain ⟨χ₂,h₂⟩ := separateWith_comparison β' β b Ψ M' M h' h hH₂ hE₂ hb' hb
  obtain ⟨χ₃,h₃⟩ := separateWith_comparison β'' β b (Φ.trans Ψ) M'' M h'' h hH₃ hE₃ hb'' hb
  exact ⟨χ₁,χ₂,χ₃,h₁,h₂,h₃,towerIso_unique_last (h₁.trans h₂) h₃⟩

/-- Every family of arbitrary actual individual choices has internally produced identity, inverse and triple comparisons. -/
theorem exists_choice_family_cocycle {I : Type*} (β : I → HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    let o := fun i => separateWith (β i) b M h hb
    ∃ χ : ∀ i j, (o i).D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (o j).D,
      (∀ i j, IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) (o i).T (o j).T (χ i j)) ∧
      (∀ i, χ i i = Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (o i).D ∞) ∧
      (∀ i j, (χ i j).symm = χ j i) ∧ ∀ i j k, (χ i j).trans (χ j k) = χ i k := by
  let o := fun i => separateWith (β i) b M h hb
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞
  have hE : M.E = M.E.map (fun E => Φ ⁻¹' E) := by simp [Φ]
  have he : ∀ i j, ∃ χ : (o i).D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (o j).D,
      IsTowerIso Φ (o i).T (o j).T χ := fun i j =>
    separateWith_comparison (β i) (β j) b Φ M M h h rfl hE hb hb
  choose χ hχ using he
  refine ⟨χ,hχ,?_,?_,?_⟩
  · intro i
    exact towerIso_unique_last (hχ i i) (IsTowerIso.refl_self (o i).T)
  · intro i j
    have hh := (hχ i j).symm
    have hp : Φ.symm = Φ := Diffeomorph.ext fun _ => rfl
    rw [hp] at hh
    exact towerIso_unique_last hh (hχ j i)
  · intro i j k
    have hh := (hχ i j).trans (hχ j k)
    have hp : Φ.trans Φ = Φ := Diffeomorph.ext fun _ => rfl
    rw [hp] at hh
    exact towerIso_unique_last hh (hχ i k)

/-- Every actual choice procedure has real smooth terminal original and literal accumulated SNC boundary. -/
theorem separateWith_geometry (β : HigherBlowupChoices.{u} n) (b : ℕ)
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hb : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ b) :
    let o := separateWith β b M h hb
    IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) (geoTransformAlong M o.T).E ∧
      IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      CentresOver H o.T ∧ IsIsomorphismOver n o.T.proj Hᶜ := by
  let o := separateWith β b M h hb
  exact ⟨isClosedSubmanifold_of_branchMultiplicity_le_one
      (isNormalCrossingsCarrier_of_boundaryAdapted o.pair) o.count_le_one,
    isTransverse_of_boundaryAdapted_count_le_one o.pair o.count_le_one,
    isSNCDivisor_append_original_of_count_le_one o.pair o.count_le_one,
    centresOver_of_higherSeparationCentres M h.1 o.T o.centres,
    isIsomorphismOver_compl_of_higherSeparationCentres M h.1 o.T o.centres⟩

/-- Internal actual choices yield a genuine finite geometric NC separation producer. -/
def naturalSeparation {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) : SeparationOutput M H n :=
  separateWith defaultHigherBlowupChoices n M h
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)

/-- Any arbitrary actual individual choice gives the same natural finite separation up to one unique genuine tower map. -/
theorem naturalSeparation_unique_comparison (β : HigherBlowupChoices.{u} n)
    {A' A : CMfd.{u} n}
    (Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
    (M' : MarkedIdeal n A') (M : MarkedIdeal n A) {H' : Set A'} {H : Set A}
    (h' : IsBoundaryAdaptedCarrier (n := n) H' M'.E)
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (hH : H' = Φ ⁻¹' H) (hE : M'.E = M.E.map (fun E => Φ ⁻¹' E)) :
    let o' := separateWith β n M' h' (fun x => branchMultiplicity_le
      (isNormalCrossingsCarrier_of_boundaryAdapted h') x)
    let o := naturalSeparation M h
    ∃! χ : o'.D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ o.D,
      IsTowerIso Φ o'.T o.T χ := by
  obtain ⟨χ,hi⟩ := separateWith_comparison β defaultHigherBlowupChoices n Φ M' M h' h hH hE
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h') x)
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  exact ⟨χ,hi,fun ψ hψ => towerIso_unique_last hψ hi⟩

/-- The internally natural separation has real terminal geometry and is an isomorphism over the whole original complement. -/
theorem naturalSeparation_geometry {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    let o := naturalSeparation M h
    o.T.length ≤ n-1 ∧ IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) (geoTransformAlong M o.T).E ∧
      IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      StageCentres (fun R C => IsSNCDivisor n (geoTransformAlong M R).E ∧
        C.Nonempty ∧ C ⊆ strictTransform n R.proj H ∧
        IsClosedSubmanifold n C ∧ IsTransverse n C (geoTransformAlong M R).E ∧
        ∃ r : ℕ, 2 ≤ r ∧ r ≤ n ∧ ∀ x ∈ C, RegularAtDim (n := n) C x (n-r)) o.T ∧
      CentresOver H o.T ∧ IsIsomorphismOver n o.T.proj Hᶜ := by
  let o := naturalSeparation M h
  obtain ⟨hsm,htrans,hsnc,hcover,hiso⟩ := separateWith_geometry defaultHigherBlowupChoices n M h
    (fun x => branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
  exact ⟨o.length_le,hsm,htrans,hsnc,
    stageGeometry_of_higherSeparationCentres M o.T o.centres,hcover,hiso⟩

end
end Hironaka.HironakaNormalCrossingsSeparationChoiceComparison

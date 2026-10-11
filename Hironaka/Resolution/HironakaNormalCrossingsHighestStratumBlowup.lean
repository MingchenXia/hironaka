/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsMultiplicityStrata
import Hironaka.Blowup.BlowupExistence
import Hironaka.Resolution.EmbeddedFromResolution

set_option autoImplicit false

/-!
# The genuine blowup of the intrinsic highest original branch stratum

Actual simultaneous branch coordinates, the real monomial chart inverse and
finite local union closure produce an actual normal-crossing strict carrier
whose original branch count decreases globally. The exceptional coordinate
is distinct from each surviving original branch. No compactness or global
original branch labels are inputs. Accumulated boundary compatibility and
additional marked-ideal cosupport containment remain separate obligations.
Blueprint: `hironaka-normal-crossings-highest-stratum-blowup-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsHighestStratumBlowup

open Hironaka.BlowupSequences BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  BlowupSNCTransform BlowupLocalSurjectivity BlowupMonomialCharts BlowupStrictSubmanifold
  RegularAtDimTransport RegularPatchPullback SimultaneousNormalCrossings

open Hironaka
noncomputable section

variable {n : ℕ}

private def permuteCoordinates {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n) :
    LocalHolomorphicEquivAt (n := n) p := by
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ
  exact
    { source := Φ.source
      target := L.symm ⁻¹' Φ.target
      isOpen_source := Φ.isOpen_source
      isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
      center_mem_source := Φ.center_mem_source
      toFun := fun z => L (Φ.toFun z)
      invFun := fun z => Φ.invFun (L.symm z)
      toFun_holomorphic := L.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn.comp
        Φ.toFun_holomorphic (fun _ _ => mem_univ _)
      invFun_holomorphic := Φ.invFun_holomorphic.comp
        L.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn
        (fun _ hz => hz)
      mapsTo_toFun := fun z hz => by
        change L.symm (L (Φ.toFun z)) ∈ Φ.target
        rw [L.symm_apply_apply]; exact Φ.mapsTo_toFun hz
      mapsTo_invFun := fun z hz => Φ.mapsTo_invFun hz
      left_inv := fun z hz => by
        rw [L.symm_apply_apply]; exact Φ.left_inv z hz
      right_inv := fun z hz => by
        rw [Φ.right_inv _ hz]; exact L.apply_symm_apply z }

private theorem permuteCoordinates_apply {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) (σ : Fin n ≃ Fin n)
    (z : ComplexModel n) (i : Fin n) : (permuteCoordinates Φ σ).toFun z (σ i) = Φ.toFun z i := by
  simp [permuteCoordinates, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The original highest-count chart internally produces coordinates adapted
to the whole centre and every original branch. -/
theorem exists_highest_stratum_branch_adapted_coordinates {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r) {x : X}
    (hx : r ≤ branchMultiplicity hH x) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ,
        (r ≤ branchMultiplicity hH y ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈
          complexCoordinatePlane n (n - r))) ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i : Fin n, n - r ≤ i.1 ∧ flatCoord Φ i y = 0) := by
  classical
  obtain ⟨Ψ, hsrc, hΨ0, S, hΨH⟩ := hH.2 x
  obtain ⟨hcard, hflatC⟩ := highest_superlevel_flattening hH hbound hx Ψ hΨ0 S hΨH
  obtain ⟨σ, hσ⟩ := exists_perm_nested (X := S) (Y := S) (Subset.refl _)
  have hσ' : ∀ i, n - r ≤ (σ i).1 ↔ i ∈ S := by
    intro i; rw [← hcard]; exact (hσ i).1
  let Φ := permuteCoordinates Ψ σ
  refine ⟨Φ, hsrc, ?_, ?_, ?_⟩
  · change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ) (Ψ.toFun _) = 0
    rw [hΨ0, map_zero]
  · intro y hy
    rw [hflatC y hy]
    constructor
    · intro hy i hi
      obtain ⟨j, rfl⟩ := σ.surjective i
      rw [permuteCoordinates_apply]
      exact hy j ((hσ' j).mp hi)
    · intro hy i hi
      change Ψ.toFun (chartAt (ComplexModel n) x y) i = 0
      rw [← permuteCoordinates_apply Ψ σ _ i]
      exact hy (σ i) ((hσ' i).mpr hi)
  · intro y hy
    rw [hΨH y hy]
    constructor
    · rintro ⟨i, hiS, hi0⟩
      refine ⟨σ i, (hσ' i).mpr hiS, ?_⟩
      change (permuteCoordinates Ψ σ).toFun _ (σ i) = 0
      rw [permuteCoordinates_apply]; exact hi0
    · rintro ⟨i, hi, hi0⟩
      obtain ⟨j, rfl⟩ := σ.surjective i
      refine ⟨j, (hσ' j).mp hi, ?_⟩
      change (permuteCoordinates Ψ σ).toFun _ (σ j) = 0 at hi0
      rwa [permuteCoordinates_apply] at hi0

/-- Positive intrinsic highest strata have genuinely empty interior. -/
theorem interior_highest_superlevel_eq_empty {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r) :
    interior {x | r ≤ branchMultiplicity hH x} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxC : r ≤ branchMultiplicity hH x :=
    interior_subset (s := {x : X | r ≤ branchMultiplicity hH x}) hx
  have hxr := regularAtDim_highest_superlevel hH hbound hxC
  have hxn : RegularAtDim (n := n) {x | r ≤ branchMultiplicity hH x} x n :=
    EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  have heq := RegularPointDimension.eq_of_regularAtDim hxn hxr
  have hle : r ≤ n := hxC.trans (branchMultiplicity_le hH x)
  omega

/-- The closed smooth intrinsic positive highest stratum internally admits an actual blowup. -/
theorem exists_highest_stratum_blowup {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X),
      IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π :=
  BlowupExistence.exists_isBlowupAlong _ (isClosedSubmanifold_highest_superlevel hH hbound)
    (interior_highest_superlevel_eq_empty hH hr hbound)

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X} {C : Set X}

private theorem mem_closure_iff_of_eventually_iff {A B : Set Y} {y : Y}
    (heq : ∀ᶠ z in 𝓝 y, z ∈ A ↔ z ∈ B) : y ∈ closure A ↔ y ∈ closure B := by
  rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
  exact frequently_congr heq

/-- The entire original carrier's strict closure is calculated from its real
finite local branch union; the pivot branch disappears from the actual chart. -/
theorem mem_strict_carrier_iff_of_actual_chart {H : Set X}
    (hπ : IsBlowupAlong n C π) {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) {k : ℕ}
    (hflatC : ∀ y ∈ flatDomain Φ,
      y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)
    (hflatH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i : Fin n, k ≤ i.1 ∧ flatCoord Φ i y = 0)
    {j : Fin n} (hj : k ≤ j.1) {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z)
    (hWeq : ∀ z ∈ O, π z ∈ flatDomain Φ ∧
      monomial k j (W z) = Φ.toFun (chartAt (ComplexModel n) x (π z)))
    (hℓ : ∀ ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
      π ∘ ℓ = monomialChart Φ k j → ∀ z ∈ O, ∀ hw : W z ∈ monomialDomain Φ k j,
        ℓ (LiftedOpen.mk _ (W z) hw) = z)
    {z : Y} (hz : z ∈ O) :
    z ∈ geoStrictTransform π C H ↔ ∃ i : Fin n, k ≤ i.1 ∧ i ≠ j ∧ W z i = 0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => k ≤ i.1)
  let A : S → Set X := fun i => {x' | flatCoord Φ i x' = 0}
  let V := ⋃ i : S, A i
  have heq : z ∈ geoStrictTransform π C H ↔ z ∈ geoStrictTransform π C V := by
    apply mem_closure_iff_of_eventually_iff
    have hdom := hπ.contMDiff.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_flatDomain Φ).mem_nhds (hWeq z hz).1)
    filter_upwards [hdom] with u hu
    change (π u ∈ H ∧ π u ∉ C) ↔ (π u ∈ V ∧ π u ∉ C)
    rw [hflatH (π u) hu]
    have hV : π u ∈ V ↔ ∃ i : Fin n, k ≤ i.1 ∧ flatCoord Φ i (π u) = 0 := by
      simp [V, A, S]
    rw [hV]
  have hUnion : geoStrictTransform π C V = ⋃ i : S, geoStrictTransform π C (A i) := by
    simp only [V, geoStrictTransform, iUnion_sdiff, preimage_iUnion, closure_iUnion_of_finite]
  rw [heq, hUnion, mem_iUnion]
  have hbranch : ∀ i : S, z ∈ geoStrictTransform π C (A i) ↔ i.1 ≠ j ∧ W z i = 0 := by
    intro i
    have h := mem_geoStrictTransform_iff_of_chart hπ hsrc
      (fun hy hyΦ => hflatC _ ⟨hy, hyΦ⟩)
      (A := A i) (T := {i.1})
      (fun hy hyΦ => by simp [A, flatCoord, NormalCrossings.coordSubspace])
      hj hO hWs hWeq hℓ hz
    simpa [NormalCrossings.coordSubspace, eq_comm] using h
  simp_rw [hbranch]
  constructor
  · rintro ⟨i, hij, hi0⟩
    exact ⟨i, (Finset.mem_filter.mp i.2).2, hij, hi0⟩
  · rintro ⟨i, hi, hij, hi0⟩
    exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩, hij, hi0⟩

/-- Every actual point above the intrinsic centre has a genuine centred strict
original NC chart with fewer branches and a separate exceptional coordinate. -/
theorem exists_strict_carrier_coordinates_over_highest {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π)
    {z : Y} (hz : r ≤ branchMultiplicity hH (π z)) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (S : Finset (Fin n)) (j : Fin n),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧ S.card ≤ r - 1 ∧ j ∉ S ∧
      (∀ u ∈ flatDomain Θ, u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H ↔
        ∃ i ∈ S, flatCoord Θ i u = 0) ∧
      (∀ u ∈ flatDomain Θ, r ≤ branchMultiplicity hH (π u) ↔ flatCoord Θ j u = 0) := by
  classical
  obtain ⟨Φ, hsrc, hΦ0, hflatC, hflatH⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hz
  let k := n - r
  let T := Finset.univ.filter (fun i : Fin n => k ≤ i.1)
  have hflatT : ∀ u ∈ flatDomain Φ, u ∈ H ↔ ∃ i ∈ T, flatCoord Φ i u = 0 := by
    simpa [T, k] using hflatH
  have hcardT : T.card = r := by
    rw [← branchMultiplicity_eq_card hH Φ hΦ0 T hflatT]
    exact (hbound (π z)).antisymm hz
  have hflatC' : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) u ∈ Φ.source →
      (r ≤ branchMultiplicity hH u ↔ Φ.toFun (chartAt (ComplexModel n) (π z) u) ∈
        complexCoordinatePlane n k) := fun {u} hu huΦ => hflatC u ⟨hu, huΦ⟩
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hsrc hflatC' (mem_flatDomain_self Φ)
  have hWmem : ∀ u ∈ O, W u ∈ monomialDomain Φ k j := by
    intro u hu
    change monomial k j (W u) ∈ Φ.target
    rw [(hWeq u hu).2]
    exact Φ.mapsTo_toFun (hWeq u hu).1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hsrc hflatC' hj
  have hWinj := injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO
  have hcentre : ∀ u ∈ O, r ≤ branchMultiplicity hH (π u) ↔ W u j = 0 := by
    intro u hu
    rw [hflatC' (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hzj : W z j = 0 := (hcentre z hzO).mp hz
  have hstrict : ∀ u ∈ O,
      u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H ↔
        ∃ i : Fin n, k ≤ i.1 ∧ i ≠ j ∧ W u i = 0 :=
    fun u hu => mem_strict_carrier_iff_of_actual_chart hπ Φ hsrc hflatC hflatH hj hO hWs hWeq hℓ hu
  have hne : ∀ᶠ u in 𝓝 z, ∀ i : Fin n, W z i ≠ 0 → W u i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : W z i = 0
    · exact Eventually.of_forall fun _ h => False.elim (h hi)
    · have hc : ContinuousAt (fun u => W u i) z :=
        (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt.comp (hWs z hzO).continuousAt
      filter_upwards [hc.eventually (isOpen_ne.mem_nhds hi)] with u hu
      exact fun _ => hu
  have hdom : ∀ᶠ u in 𝓝 z, u ∈ O := hO.mem_nhds hzO
  obtain ⟨O', hOsub, hO'o, hzO'⟩ := mem_nhds_iff.mp (hdom.and hne)
  obtain ⟨Θ, hΘsrc, hΘ0, hΘ⟩ := exists_recentred_coords hO'o
    (fun u hu => hWs u (hOsub hu).1) hzO' hWinj
  let S := (T.erase j).filter (fun i => W z i = 0)
  have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  refine ⟨Θ, S, j, hΘsrc, hΘ0, ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le (T.erase j) _).trans_eq
      ((Finset.card_erase_of_mem hjT).trans (congrArg (· - 1) hcardT))
  · simp [S]
  · intro u hu
    obtain ⟨huO', heq⟩ := hΘ hu.1 hu.2
    have huO := (hOsub huO').1
    rw [hstrict u huO]
    constructor
    · rintro ⟨i, hi, hij, hi0⟩
      have hzi : W z i = 0 := by
        by_contra hzi
        exact (hOsub huO').2 i hzi hi0
      refine ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hij, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩, hzi⟩, ?_⟩
      have heqi := congrArg (fun w : ComplexModel n => w i) heq
      change flatCoord Θ i u = W u i - W z i at heqi
      rw [heqi, hi0, hzi, sub_self]
    · rintro ⟨i, hiS, hi0⟩
      obtain ⟨hiE, hzi⟩ := Finset.mem_filter.mp hiS
      obtain ⟨hij, hiT⟩ := Finset.mem_erase.mp hiE
      refine ⟨i, (Finset.mem_filter.mp hiT).2, hij, ?_⟩
      have heqi := congrArg (fun w : ComplexModel n => w i) heq
      change flatCoord Θ i u = W u i - W z i at heqi
      rwa [hi0, hzi, sub_zero, eq_comm] at heqi
  · intro u hu
    obtain ⟨huO', heq⟩ := hΘ hu.1 hu.2
    rw [hcentre u (hOsub huO').1]
    have heqj := congrArg (fun w : ComplexModel n => w j) heq
    change flatCoord Θ j u = W u j - W z j at heqj
    rw [hzj, sub_zero] at heqj
    rw [heqj]

private theorem exists_strict_carrier_coordinates_off_highest {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π)
    {z : Y} (hz : ¬ r ≤ branchMultiplicity hH (π z)) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (S : Finset (Fin n)),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      S.card = branchMultiplicity hH (π z) ∧
      (∀ u ∈ flatDomain Θ, u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H ↔
        ∃ i ∈ S, flatCoord Θ i u = 0) := by
  obtain ⟨Φ, -, hΦ0, S, hΦH⟩ := hH.2 (π z)
  obtain ⟨Θ, hΘsrc, hΘ0, hΘ⟩ := MonomialResolution.exists_chart_comp hπ hz Φ hΦ0
  refine ⟨Θ, S, hΘsrc, hΘ0, (branchMultiplicity_eq_card hH Φ hΦ0 S hΦH).symm, ?_⟩
  intro u hu
  obtain ⟨huC, huΦ, heq⟩ := hΘ hu.1 hu.2
  rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH.1 huC, hΦH (π u) huΦ]
  have hi : ∀ i : Fin n, flatCoord Θ i u = flatCoord Φ i (π u) :=
    fun i => congrArg (fun w : ComplexModel n => w i) heq
  simp_rw [← hi]

/-- The entire strict original carrier remains genuinely normal crossings
under the blowup of its intrinsic highest stratum. -/
theorem isNormalCrossingsCarrier_strict_highest {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π) :
    IsNormalCrossingsCarrier (n := n) (geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H) := by
  refine ⟨isClosed_closure, fun z => ?_⟩
  by_cases hz : r ≤ branchMultiplicity hH (π z)
  · obtain ⟨Θ, S, -, hsrc, h0, -, -, hflat, -⟩ :=
      exists_strict_carrier_coordinates_over_highest hH hbound hπ hz
    exact ⟨Θ, hsrc, h0, S, hflat⟩
  · obtain ⟨Θ, S, hsrc, h0, -, hflat⟩ := exists_strict_carrier_coordinates_off_highest hH hπ hz
    exact ⟨Θ, hsrc, h0, S, hflat⟩

/-- The internally produced strict-carrier count is globally at most r-1. -/
theorem branchMultiplicity_strict_highest_le {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π) (z : Y) :
    branchMultiplicity (isNormalCrossingsCarrier_strict_highest hH hbound hπ) z ≤ r - 1 := by
  by_cases hz : r ≤ branchMultiplicity hH (π z)
  · obtain ⟨Θ, S, -, -, h0, hcard, -, hflat, -⟩ :=
      exists_strict_carrier_coordinates_over_highest hH hbound hπ hz
    rw [branchMultiplicity_eq_card (isNormalCrossingsCarrier_strict_highest hH hbound hπ) Θ h0 S hflat]
    exact hcard
  · obtain ⟨Θ, S, -, h0, hcard, hflat⟩ := exists_strict_carrier_coordinates_off_highest hH hπ hz
    rw [branchMultiplicity_eq_card (isNormalCrossingsCarrier_strict_highest hH hbound hπ) Θ h0 S hflat,
      hcard]
    omega

/-- The actual carrier internally produces an attained positive maximum, its
genuine blowup and the globally smaller actual strict-original NC value. -/
theorem exists_highest_stratum_blowup_strict_count_decrease {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hne : H.Nonempty) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ (∀ x : X, branchMultiplicity hH x ≤ r) ∧
      {x | r ≤ branchMultiplicity hH x}.Nonempty ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
        (_ : IsComplexManifold n Y) (π : Y → X),
        IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π ∧
        ∃ hH' : IsNormalCrossingsCarrier (n := n)
          (geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H),
          ∀ z : Y, branchMultiplicity hH' z ≤ r - 1 := by
  obtain ⟨r, hr, hrn, hbound, hmax, -, -, -⟩ := exists_highest_multiplicity_stratum hH hne
  obtain ⟨Y, hYtop, hYchart, hYcm, π, hπ⟩ := exists_highest_stratum_blowup hH hr hbound
  refine ⟨r, hr, hrn, hbound, ?_, Y, hYtop, hYchart, hYcm, π, hπ,
    isNormalCrossingsCarrier_strict_highest hH hbound hπ, ?_⟩
  · obtain ⟨x, hx⟩ := hmax
    exact ⟨x, hx.ge⟩
  · exact branchMultiplicity_strict_highest_le hH hbound hπ

end
end Hironaka.HironakaNormalCrossingsHighestStratumBlowup

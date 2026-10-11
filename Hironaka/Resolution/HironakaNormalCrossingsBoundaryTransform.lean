/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsHighestStratumBlowup

set_option autoImplicit false

/-!
# Actual original normal-crossing carrier with accumulated boundary

Real common coordinates for the entire original carrier and old boundary
produce simultaneous highest-centre coordinates. Genuine monomial lift
inverses and whole finite-union strict closure produce the whole transformed
pair, old strict boundary plus the actual new exceptional member, and a
globally smaller original branch count. Additional marked-ideal cosupport
and the old ordered invariant tie-break remain separate obligations.
Blueprint: `hironaka-normal-crossings-boundary-transform-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsBoundaryTransform

open Hironaka.BlowupSequences BlowupFlatCoordinates NormalCrossings
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup BlowupSNCTransform BlowupLocalSurjectivity
  BlowupMonomialCharts BlowupStrictSubmanifold RegularAtDimTransport RegularPatchPullback
  SimultaneousNormalCrossings

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

/-- Actual common original-carrier and boundary coordinates, with no global original labels. -/
def IsBoundaryAdaptedCarrier (H : Set X) (E : List (Set X)) : Prop :=
  IsClosed H ∧ (∀ A ∈ E, IsClosed A) ∧ ∀ x : X,
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)) (B : Fin E.length → Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) ∧
      (∀ i, x ∈ E.get i → (B i).card = 1 ∧ Disjoint S (B i)) ∧
      Set.InjOn B {i | x ∈ E.get i} ∧
      ∀ i, x ∈ E.get i → ∀ y ∈ flatDomain Φ,
        y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (B i)

omit [IsComplexManifold n X] in
/-- Forgetting real common boundary equations gives the actual NC carrier. -/
theorem isNormalCrossingsCarrier_of_boundaryAdapted {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) : IsNormalCrossingsCarrier (n := n) H := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨Φ, S, -, hsrc, h0, hH, -, -, -⟩ := h.2.2 x
  exact ⟨Φ, hsrc, h0, S, hH⟩

omit [IsComplexManifold n X] in
/-- The same genuine common coordinates produce the actual SNC boundary. -/
theorem isSNCDivisor_of_boundaryAdapted {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) : IsSNCDivisor n E := by
  refine ⟨h.2.1, fun x => ?_⟩
  obtain ⟨Φ, S, B, hsrc, h0, -, hcard, hinj, hE⟩ := h.2.2 x
  exact ⟨B, ⟨Φ, hsrc, h0, fun i hi y hy hyΦ => hE i hi y ⟨hy, hyΦ⟩⟩,
    fun i hi => (hcard i hi).1, hinj⟩

omit [IsComplexManifold n X] in
/-- Every actual original NC carrier internally supplies the empty boundary pair. -/
theorem boundaryAdapted_nil {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsBoundaryAdaptedCarrier (n := n) H [] := by
  refine ⟨hH.1, fun _ h => False.elim (List.not_mem_nil h), fun x => ?_⟩
  obtain ⟨Φ, hsrc, h0, S, hH⟩ := hH.2 x
  exact ⟨Φ, S, Fin.elim0, hsrc, h0, hH, fun i => i.elim0,
    fun i => i.elim0, fun i => i.elim0⟩

/-- The whole intrinsic highest stratum has actual NC coordinates with the old boundary. -/
theorem hasNormalCrossings_highest_boundary {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    HasNormalCrossings n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} E := by
  intro x hx
  obtain ⟨Φ, S, B, hsrc, h0, hH, hcard, -, hE⟩ := h.2.2 x
  obtain ⟨-, hC⟩ := highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx Φ h0 S hH
  refine ⟨S, B, ⟨Φ, hsrc, h0, ?_⟩, fun i hi => (hcard i hi).1⟩
  rintro (_ | i) hi y hy hyΦ
  · exact hC y ⟨hy, hyΦ⟩
  · exact hE i hi y ⟨hy, hyΦ⟩

/-- Joint actual coordinates put the original maximum centre last and every
through old boundary coordinate in the disjoint tangential block. -/
theorem exists_highest_joint_coordinates {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {x : X} (hx : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (B : Fin E.length → Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ,
        (r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) y ↔
          Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n (n-r))) ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i : Fin n, n-r ≤ i.1 ∧ flatCoord Φ i y = 0) ∧
      (∀ i, x ∈ E.get i → (B i).card = 1 ∧ ∀ j ∈ B i, j.1 < n-r) ∧
      Set.InjOn B {i | x ∈ E.get i} ∧
      ∀ i, x ∈ E.get i → ∀ y ∈ flatDomain Φ,
        y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (B i) := by
  classical
  obtain ⟨Ψ, S, A, hsrc, h0, hH, hA, hinj, hE⟩ := h.2.2 x
  obtain ⟨hcard, hflatC⟩ := highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx Ψ h0 S hH
  obtain ⟨σ, hσ⟩ := exists_perm_nested (X := S) (Y := S) (Subset.refl _)
  have hσ' : ∀ i, n-r ≤ (σ i).1 ↔ i ∈ S := by
    intro i; rw [← hcard]; exact (hσ i).1
  let Φ := permuteCoordinates Ψ σ
  let B := fun i => (A i).image σ
  have htransport : ∀ (T : Finset (Fin n)) (w : ComplexModel n),
      (permuteCoordinates Ψ σ).toFun w ∈ coordSubspace (T.image σ) ↔
      Ψ.toFun w ∈ coordSubspace T := by
    intro T w
    constructor
    · intro hh j hj
      have hz := hh (σ j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      rwa [permuteCoordinates_apply] at hz
    · intro hh j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [permuteCoordinates_apply]
      exact hh i hi
  refine ⟨Φ, B, hsrc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ) (Ψ.toFun _) = 0
    rw [h0, map_zero]
  · intro y hy
    rw [hflatC y hy]
    constructor
    · intro hh i hi
      obtain ⟨j, rfl⟩ := σ.surjective i
      rw [permuteCoordinates_apply]
      exact hh j ((hσ' j).mp hi)
    · intro hh i hi
      change Ψ.toFun (chartAt (ComplexModel n) x y) i = 0
      rw [← permuteCoordinates_apply Ψ σ _ i]
      exact hh (σ i) ((hσ' i).mpr hi)
  · intro y hy
    rw [hH y hy]
    constructor
    · rintro ⟨i, hi, hi0⟩
      refine ⟨σ i, (hσ' i).mpr hi, ?_⟩
      change (permuteCoordinates Ψ σ).toFun _ (σ i) = 0
      rw [permuteCoordinates_apply]; exact hi0
    · rintro ⟨i, hi, hi0⟩
      obtain ⟨j, rfl⟩ := σ.surjective i
      refine ⟨j, (hσ' j).mp hi, ?_⟩
      change (permuteCoordinates Ψ σ).toFun _ (σ j) = 0 at hi0
      rwa [permuteCoordinates_apply] at hi0
  · intro i hi
    refine ⟨(Finset.card_image_of_injective _ σ.injective).trans (hA i hi).1, ?_⟩
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    have haS : a ∉ S := fun haS => (Finset.disjoint_left.mp (hA i hi).2) haS ha
    have hlt := (hσ' a).not.mpr haS
    omega
  · intro i hi j hj hij
    apply hinj hi hj
    ext a
    have he := congrArg (fun T : Finset (Fin n) => σ a ∈ T) hij
    simpa [B, σ.injective.eq_iff] using he
  · intro i hi y hy
    change y ∈ E.get i ↔ (permuteCoordinates Ψ σ).toFun _ ∈ coordSubspace ((A i).image σ)
    rw [htransport]
    exact hE i hi y hy

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}

/-- The true monomial inverse jointly produces every strict original branch,
every through strict old boundary and the new exceptional coordinate. -/
theorem exists_joint_coordinates_over_highest {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    {z : Y} (hz : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (π z)) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (S : Finset (Fin n))
      (B : Fin (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).length → Finset (Fin n)),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧ S.card ≤ r-1 ∧
      (∀ u ∈ flatDomain Θ,
        u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H ↔
        ∃ i ∈ S, flatCoord Θ i u = 0) ∧
      (∀ i, z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i →
        (B i).card = 1 ∧ Disjoint S (B i)) ∧
      Set.InjOn B {i | z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i} ∧
      ∀ i, z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i →
        ∀ u ∈ flatDomain Θ,
          u ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
            [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i ↔
          Θ.toFun (chartAt (ComplexModel n) z u) ∈ coordSubspace (B i) := by
  classical
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  obtain ⟨Φ, B, hsrc, hΦ0, hflatC, hflatH, hB, hBinj, hBE⟩ :=
    exists_highest_joint_coordinates h hbound hz
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
  let C : Set X := {x | r ≤ branchMultiplicity hH x}
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let B' : Fin E'.length → Finset (Fin n) := fun i =>
    if hi : i.val < E.length then B ⟨i.val, hi⟩ else {j}
  have hthrough : ∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i :=
    fun i hi => geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (h.2.1 _ (List.get_mem _ _)) hi
  have hHu : ∀ i, π z ∈ E.get i → ∀ u ∈ O,
      u ∈ geoStrictTransform π C (E.get i) ↔ W u ∈ coordSubspace (B i) := by
    intro i hi u hu
    have hjB : j ∉ B i := fun hjB => by
      have hlt := (hB i hi).2 j hjB
      omega
    have hh := mem_geoStrictTransform_iff_of_chart hπ hsrc hflatC'
      (fun hy hyΦ => hBE i hi _ ⟨hy, hyΦ⟩) hj hO hWs hWeq hℓ hu
    exact hh.trans (and_iff_right hjB)
  have hSnormal : ∀ a ∈ S, k ≤ a.val := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2).2
  have hjS : j ∉ S := by simp [S]
  refine ⟨Θ, S, B', hΘsrc, hΘ0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le (T.erase j) _).trans_eq
      ((Finset.card_erase_of_mem hjT).trans (congrArg (· - 1) hcardT))
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
  · intro i hi
    rw [get_map_append_singleton] at hi
    by_cases hiE : i.val < E.length
    · simp only [hiE, dif_pos] at hi
      simp only [B', hiE, dif_pos]
      refine ⟨(hB _ (hthrough _ hi)).1, Finset.disjoint_left.mpr ?_⟩
      intro a haS haB
      have hlt := (hB _ (hthrough _ hi)).2 a haB
      have hge := hSnormal a haS
      omega
    · simp only [B', hiE]
      exact ⟨Finset.card_singleton _, Finset.disjoint_singleton_right.mpr hjS⟩
  · intro i hi i' hi' heq
    change B' i = B' i' at heq
    change z ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i at hi
    change z ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i' at hi'
    rw [get_map_append_singleton] at hi hi'
    by_cases hiE : i.val < E.length
    · by_cases hi'E : i'.val < E.length
      · simp only [hiE, hi'E, dif_pos] at hi hi'
        simp only [B', hiE, hi'E, dif_pos] at heq
        have he := hBinj (hthrough _ hi) (hthrough _ hi') heq
        exact Fin.ext (congrArg (fun a : Fin E.length => a.val) he)
      · simp only [B', hiE, hi'E, dif_pos] at heq
        have hjB : j ∈ B ⟨i.val, hiE⟩ := by rw [heq]; simp
        have hlt := (hB _ (hthrough _ (by simpa [hiE] using hi))).2 j hjB
        omega
    · by_cases hi'E : i'.val < E.length
      · simp only [B', hiE, hi'E, dif_pos] at heq
        have hjB : j ∈ B ⟨i'.val, hi'E⟩ := by rw [← heq]; simp
        have hlt := (hB _ (hthrough _ (by simpa [hi'E] using hi'))).2 j hjB
        omega
      · exact eq_of_not_lt hiE hi'E
  · intro i hi u hu
    obtain ⟨huO', heq⟩ := hΘ hu.1 hu.2
    change Θ.toFun (chartAt (ComplexModel n) z u) = W u - W z at heq
    rw [get_map_append_singleton] at hi ⊢
    by_cases hiE : i.val < E.length
    · simp only [B', hiE, dif_pos] at hi ⊢
      have hbase := hthrough _ hi
      have hWz := (hHu _ hbase z hzO).mp hi
      rw [hHu _ hbase u (hOsub huO').1, heq, sub_mem_coordSubspace_iff hWz]
    · simp only [B', hiE]
      change r ≤ branchMultiplicity hH (π u) ↔
        Θ.toFun (chartAt (ComplexModel n) z u) ∈ coordSubspace {j}
      rw [hcentre u (hOsub huO').1, heq, mem_coordSubspace_singleton,
        PiLp.sub_apply, hzj, sub_zero]

private theorem exists_joint_coordinates_off_highest {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    {z : Y} (hz : ¬ r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (π z)) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (S : Finset (Fin n))
      (B : Fin (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).length → Finset (Fin n)),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      (∀ u ∈ flatDomain Θ,
        u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H ↔
        ∃ i ∈ S, flatCoord Θ i u = 0) ∧
      (∀ i, z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i →
        (B i).card = 1 ∧ Disjoint S (B i)) ∧
      Set.InjOn B {i | z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i} ∧
      ∀ i, z ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i →
        ∀ u ∈ flatDomain Θ,
          u ∈ (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
            [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]).get i ↔
          Θ.toFun (chartAt (ComplexModel n) z u) ∈ coordSubspace (B i) := by
  classical
  let C : Set X := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  obtain ⟨Φ, S, B, hsrc, h0, hH, hB, hinj, hE⟩ := h.2.2 (π z)
  obtain ⟨Θ, hΘsrc, hΘ0, hΘ⟩ := MonomialResolution.exists_chart_comp hπ hz Φ h0
  let B' : Fin E'.length → Finset (Fin n) := fun i =>
    if hi : i.val < E.length then B ⟨i.val, hi⟩ else ∅
  have hthrough : ∀ i, z ∈ geoStrictTransform π C (E.get i) ↔ π z ∈ E.get i :=
    fun i => mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
      (h.2.1 _ (List.get_mem _ _)) hz
  refine ⟨Θ, S, B', hΘsrc, hΘ0, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨huC, huΦ, heq⟩ := hΘ hu.1 hu.2
    rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous h.1 huC,
      hH (π u) huΦ]
    have hi : ∀ i : Fin n, flatCoord Θ i u = flatCoord Φ i (π u) :=
      fun i => congrArg (fun w : ComplexModel n => w i) heq
    simp_rw [← hi]
  · intro i hi
    rw [get_map_append_singleton] at hi
    by_cases hiE : i.val < E.length
    · simp only [hiE, dif_pos] at hi
      simpa only [B', hiE, dif_pos] using hB _ ((hthrough _).mp hi)
    · simp only [hiE] at hi
      exact False.elim (hz hi)
  · intro i hi i' hi' heq
    change z ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i at hi
    change z ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i' at hi'
    rw [get_map_append_singleton] at hi hi'
    by_cases hiE : i.val < E.length
    · by_cases hi'E : i'.val < E.length
      · simp only [hiE, hi'E, dif_pos] at hi hi'
        change B' i = B' i' at heq
        simp only [B', hiE, hi'E, dif_pos] at heq
        have he := hinj ((hthrough _).mp hi) ((hthrough _).mp hi') heq
        exact Fin.ext (congrArg (fun a : Fin E.length => a.val) he)
      · simp only [hi'E] at hi'
        exact False.elim (hz hi')
    · simp only [hiE] at hi
      exact False.elim (hz hi)
  · intro i hi u hu
    rw [get_map_append_singleton] at hi ⊢
    by_cases hiE : i.val < E.length
    · simp only [B', hiE, dif_pos] at hi ⊢
      obtain ⟨huC, huΦ, heq⟩ := hΘ hu.1 hu.2
      change Θ.toFun (chartAt (ComplexModel n) z u) =
        Φ.toFun (chartAt (ComplexModel n) (π z) (π u)) at heq
      rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
        (h.2.1 _ (List.get_mem _ _)) huC, hE _ ((hthrough _).mp hi) (π u) huΦ, heq]
    · simp only [hiE] at hi
      exact False.elim (hz hi)

/-- The complete transformed pair is produced on the entire actual blowup. -/
theorem boundaryAdapted_strict_highest {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π) :
    IsBoundaryAdaptedCarrier (n := n)
      (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H)
      (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]) := by
  refine ⟨isClosed_closure, ?_, fun z => ?_⟩
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨A, -, rfl⟩ := List.mem_map.mp hA
      exact isClosed_closure
    · rw [List.mem_singleton.mp hA]
      exact (isClosed_branchMultiplicity_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) r).preimage
        hπ.contMDiff.continuous
  · by_cases hz : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (π z)
    · obtain ⟨Θ, S, B, hsrc, h0, -, hH, hB, hinj, hE⟩ :=
        exists_joint_coordinates_over_highest h hbound hπ hz
      exact ⟨Θ, S, B, hsrc, h0, hH, hB, hinj, hE⟩
    · exact exists_joint_coordinates_off_highest h hπ hz

/-- The actual accumulated boundary, including the new exceptional member, is SNC. -/
theorem isSNCDivisor_strict_highest_boundary {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π) :
    IsSNCDivisor n
      (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
        [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]) :=
  isSNCDivisor_of_boundaryAdapted (boundaryAdapted_strict_highest h hbound hπ)

/-- The internally produced whole pair has genuinely smaller intrinsic original count. -/
theorem branchMultiplicity_boundary_strict_highest_le {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    (z : Y) :
    branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted
      (boundaryAdapted_strict_highest h hbound hπ)) z ≤ r-1 := by
  exact branchMultiplicity_strict_highest_le (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hπ z

/-- The actual pair internally supplies its positive maximum, genuine blowup,
whole transformed original/boundary pair and globally decreased original count. -/
theorem exists_highest_boundary_blowup_count_decrease {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) (hne : H.Nonempty) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧
      (∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) ∧
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}.Nonempty ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
        (_ : IsComplexManifold n Y) (π : Y → X),
        IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π ∧
        ∃ h' : IsBoundaryAdaptedCarrier (n := n)
          (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} H)
          (E.map (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) ++
            [π ⁻¹' {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}]),
          ∀ z : Y, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h') z ≤ r-1 := by
  obtain ⟨r, hr, hrn, hbound, hmax, -, -, -⟩ :=
    exists_highest_multiplicity_stratum (isNormalCrossingsCarrier_of_boundaryAdapted h) hne
  obtain ⟨Y, hYtop, hYchart, hYcm, π, hπ⟩ :=
    exists_highest_stratum_blowup (isNormalCrossingsCarrier_of_boundaryAdapted h) hr hbound
  refine ⟨r, hr, hrn, hbound, ?_, Y, hYtop, hYchart, hYcm, π, hπ,
    boundaryAdapted_strict_highest h hbound hπ, ?_⟩
  · obtain ⟨x, hx⟩ := hmax
    exact ⟨x, hx.ge⟩
  · exact branchMultiplicity_boundary_strict_highest_le h hbound hπ

end
end Hironaka.HironakaNormalCrossingsBoundaryTransform

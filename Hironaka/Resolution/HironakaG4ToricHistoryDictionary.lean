import Hironaka.Resolution.HironakaG4ToricFreePivot

/-!
# Exact strict-transform coordinates in an uncentred toric chart

The local toric chart retains its original coordinates, so the coordinate
locus description can be propagated without recentering.  The reverse
inclusion uses a nonzero perturbation of the pivot inside the actual chart.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ToricHistoryDictionary

noncomputable section

open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling
  HironakaG34ToricCharts HironakaG4ToricCharacterSections BlowupSNCTransform

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C A : Set X} {π : Y → X} {y₀ : X}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- The geometric strict transform is the coordinate locus when the pivot
is free and is empty in this chart when the pivot belongs to the mask. -/
theorem mem_geoStrictTransform_iff_flatMap
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (S : Finset (Fin n))
    (hflatA : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ coordSubspace S))
    {j : Fin n} (hj : k ≤ j.val) {z : Y}
    (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hcoords : ∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Φ ∧
      monomial k j (flatMap Ψ u) = flatMap Φ (π u))
    {u : Y} (hu : u ∈ flatDomain Ψ) :
    u ∈ geoStrictTransform π C A ↔ j ∉ S ∧ flatMap Ψ u ∈ coordSubspace S := by
  have hraw : ∀ v ∈ flatDomain Ψ, v ∈ π ⁻¹' (A \ C) →
      j ∉ S ∧ flatMap Ψ v ∈ coordSubspace S := by
    intro v hv hvpre
    obtain ⟨hdom, hmon⟩ := hcoords v hv
    have hAcoords := (hflatA hdom.1 hdom.2).mp hvpre.1
    change flatMap Φ (π v) ∈ coordSubspace S at hAcoords
    rw [← hmon] at hAcoords
    have hpivot : flatMap Ψ v j ≠ 0 := by
      intro hpivot
      apply hvpre.2
      apply (hflatC hdom.1 hdom.2).mpr
      change flatMap Φ (π v) ∈ complexCoordinatePlane n k
      rw [← hmon, monomial_mem_plane_iff hj]
      exact hpivot
    exact (monomial_mem_coordSubspace_iff hpivot).mp hAcoords
  constructor
  · intro hcl
    let l : Filter Y := 𝓝[π ⁻¹' (A \ C)] u
    have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hlim : Tendsto (flatMap Ψ) l (𝓝 (flatMap Ψ u)) :=
      ((continuousOn_flatMap Ψ).continuousAt ((isOpen_flatDomain Ψ).mem_nhds hu)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hsource : ∀ᶠ v in l, v ∈ flatDomain Ψ :=
      nhdsWithin_le_nhds ((isOpen_flatDomain Ψ).mem_nhds hu)
    have hzero : ∀ᶠ v in l, flatMap Ψ v ∈ coordSubspace S := by
      filter_upwards [hsource, self_mem_nhdsWithin] with v hv hvpre
      exact (hraw v hv hvpre).2
    have hjfree : j ∉ S := by
      obtain ⟨v, hv, hvpre⟩ :=
        mem_closure_iff_nhds.mp hcl (flatDomain Ψ) ((isOpen_flatDomain Ψ).mem_nhds hu)
      exact (hraw v hv hvpre).1
    exact ⟨hjfree, (isClosed_coordSubspace S).mem_of_tendsto hlim hzero⟩
  · rintro ⟨hjfree, hWu⟩
    by_cases hWj : flatMap Ψ u j = 0
    · rw [geoStrictTransform, mem_closure_iff_nhds]
      intro U hU
      set e_j : ComplexModel n := EuclideanSpace.single j 1 with he_j
      have hcurve : Tendsto (fun t : ℂ => flatMap Ψ u + t • e_j) (𝓝 0) (𝓝 (flatMap Ψ u)) := by
        have : Continuous (fun t : ℂ => flatMap Ψ u + t • e_j) := continuous_const.add
          (continuous_id.smul continuous_const)
        simpa using this.tendsto 0
      have htarget : Ψ.target ∈ 𝓝 (flatMap Ψ u) := Ψ.isOpen_target.mem_nhds (Ψ.mapsTo_toFun hu.2)
      have hinv := tendsto_flatInverse Ψ hu
      have hevU : ∀ᶠ v in 𝓝 (flatMap Ψ u),
          (chartAt (ComplexModel n) z).symm (Ψ.invFun v) ∈ U := hinv.eventually hU
      have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
          flatMap Ψ u + t • e_j ∈ Ψ.target ∧
          (chartAt (ComplexModel n) z).symm (Ψ.invFun (flatMap Ψ u + t • e_j)) ∈ U ∧
          flatMap Ψ u j + t ≠ 0 := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hcurve htarget),
          mem_nhdsWithin_of_mem_nhds (hcurve hevU), self_mem_nhdsWithin] with t ht htU htne
        exact ⟨ht, htU, by simpa [hWj] using htne⟩
      obtain ⟨t, ht, htU, htne⟩ := hev.exists
      let v := (chartAt (ComplexModel n) z).symm (Ψ.invFun (flatMap Ψ u + t • e_j))
      have hv := flatInverse_mem Ψ ht hΨsrc
      have hvdom : v ∈ flatDomain Ψ := hv.1
      have hvcoord : flatMap Ψ v = flatMap Ψ u + t • e_j := hv.2
      have hvS : flatMap Ψ v ∈ coordSubspace S := by
        rw [hvcoord]
        intro i hi
        have hij : i ≠ j := fun h => hjfree (h ▸ hi)
        simp [he_j, hWu i hi, hij]
      have hvj : flatMap Ψ v j ≠ 0 := by
        rw [hvcoord]
        simpa [he_j] using htne
      obtain ⟨hdom, hmon⟩ := hcoords v hvdom
      refine ⟨v, htU, ?_, ?_⟩
      · apply (hflatA hdom.1 hdom.2).mpr
        change flatMap Φ (π v) ∈ coordSubspace S
        rw [← hmon]
        exact monomial_mem_coordSubspace hvS
      · intro hvC
        have h := (hflatC hdom.1 hdom.2).mp hvC
        change flatMap Φ (π v) ∈ complexCoordinatePlane n k at h
        rw [← hmon, monomial_mem_plane_iff hj] at h
        exact hvj h
  
    · apply subset_closure
      obtain ⟨hdom, hmon⟩ := hcoords u hu
      refine ⟨?_, ?_⟩
      · apply (hflatA hdom.1 hdom.2).mpr
        change flatMap Φ (π u) ∈ coordSubspace S
        rw [← hmon]
        exact monomial_mem_coordSubspace hWu
      · intro huC
        have h := (hflatC hdom.1 hdom.2).mp huC
        change flatMap Φ (π u) ∈ complexCoordinatePlane n k at h
        rw [← hmon, monomial_mem_plane_iff hj] at h
        exact hWj h

/-- All tracked coordinate loci and the new exceptional divisor have their
literal strict-transform equations in the same actual chart. -/
theorem strict_family_and_exceptional_coordinates
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {ι : Type*} (D : ι → Set X) (S : ι → Finset (Fin n))
    (hflatD : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ coordSubspace (S i)))
    {j : Fin n} (hj : k ≤ j.val) {z : Y}
    (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hcoords : ∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Φ ∧
      monomial k j (flatMap Ψ u) = flatMap Φ (π u)) :
    ∀ u ∈ flatDomain Ψ,
      (∀ i, u ∈ geoStrictTransform π C (D i) ↔
        j ∉ S i ∧ flatMap Ψ u ∈ coordSubspace (S i)) ∧
      (π u ∈ C ↔ flatMap Ψ u j = 0) := by
  intro u hu
  refine ⟨fun i => mem_geoStrictTransform_iff_flatMap hflatC (S i) (hflatD i) hj Ψ hΨsrc hcoords hu, ?_⟩
  obtain ⟨hdom, hmon⟩ := hcoords u hu
  rw [hflatC hdom.1 hdom.2]
  change flatMap Φ (π u) ∈ complexCoordinatePlane n k ↔ _
  rw [← hmon, monomial_mem_plane_iff hj]

end
end Hironaka.HironakaG4ToricHistoryDictionary

import Hironaka.Resolution.HironakaG4ToricCharacterSections

/-!
# Retaining the actual free pivot and character section in a toric blowup chart

The coordinate-subspace strict-transform calculation already exists in
`BlowupSNCTransform.mem_geoStrictTransform_iff_of_chart`. Its forward
closure argument uses only the qualified projection equations, rather than
the inverse-lift fields erased by `exists_toric_chart_of_blowup`. Here that
argument is extracted for the actual returned toric chart; it receives no
separate mathematical credit. The strengthened consumer retains its literal
pivot/chart/action together with the explicit transported partial section.

No native tangent or alternative flattening is selected. The chosen monomial
chart itself is qualified by strict-carrier membership, and no future-history
or equivariant-protection package is assumed. Starting Gamma action/section
and the complete lower-tail induction remain to be constructed.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ToricFreePivot

noncomputable section

open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling
  HironakaG34ToricCharts HironakaG4ToricCharacterSections BlowupSNCTransform

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C N : Set X} {π : Y → X} {y₀ : X}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- Strict-carrier membership qualifies the actual toric chart's pivot,
so its literal monomial character change transports the primitive section. -/
theorem exists_toric_chart_with_partial_realization (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (S : Finset (Fin n))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ coordSubspace S))
    {z : Y} (hz : π z ∈ flatDomain Φ) (hzN : z ∈ geoStrictTransform π C N)
    {A : Type*} {F : Filter A} {act : A → X → X} {act' : A → Y → Y}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2))
    (hcont : ∀ᶠ p in F ×ˢ 𝓝 z, ContinuousAt (act' p.1) p.2)
    (s : (Fin n → ℂ) → A) (hs : Tendsto s (𝓝 1) F)
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (s b) i = b i) :
    ∃ j : Fin n, k ≤ j.val ∧ j ∉ S ∧
      ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
        Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
        (∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Φ ∧
          monomial k j (flatMap Ψ u) = flatMap Φ (π u)) ∧
        ActsDiagonallyNear F act' (fun a => chartVec (μ a) k j) Ψ z ∧
        (∀ u ∈ flatDomain Ψ, u ∈ geoStrictTransform π C N →
          flatMap Ψ u ∈ coordSubspace S) ∧
        Tendsto (fun b => s (inverseChartVec b k j)) (𝓝 1) F ∧
        ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S,
          chartVec (μ (s (inverseChartVec b k j))) k j i = b i := by
  obtain ⟨j, hj, Ψ, hΨsrc, hcoords, hdiag'⟩ :=
    exists_toric_chart_of_blowup hπ hΦsrc hflatC hz hμ hdiag hcomm hcont
  have hraw : ∀ u ∈ flatDomain Ψ, u ∈ π ⁻¹' (N \ C) →
      j ∉ S ∧ flatMap Ψ u ∈ coordSubspace S := by
    intro u hu hpre
    obtain ⟨hdom, hmon⟩ := hcoords u hu
    have hNcoords := (hflatN hdom.1 hdom.2).mp hpre.1
    change flatMap Φ (π u) ∈ coordSubspace S at hNcoords
    rw [← hmon] at hNcoords
    have hpivot : flatMap Ψ u j ≠ 0 := by
      intro hpivot
      apply hpre.2
      apply (hflatC hdom.1 hdom.2).mpr
      change flatMap Φ (π u) ∈ complexCoordinatePlane n k
      rw [← hmon, monomial_mem_plane_iff hj]
      exact hpivot
    exact (monomial_mem_coordSubspace_iff hpivot).mp hNcoords
  have hzΨ : z ∈ flatDomain Ψ := mem_flatDomain_self Ψ
  obtain ⟨u, hu, hpre⟩ :=
    mem_closure_iff_nhds.mp hzN (flatDomain Ψ) ((isOpen_flatDomain Ψ).mem_nhds hzΨ)
  have hjfree : j ∉ S := (hraw u hu hpre).1
  have hstrict : ∀ u ∈ flatDomain Ψ, u ∈ geoStrictTransform π C N →
      flatMap Ψ u ∈ coordSubspace S := by
    intro u hu huN
    let l : Filter Y := 𝓝[π ⁻¹' (N \ C)] u
    have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp huN
    have hlim : Tendsto (flatMap Ψ) l (𝓝 (flatMap Ψ u)) :=
      ((continuousOn_flatMap Ψ).continuousAt ((isOpen_flatDomain Ψ).mem_nhds hu)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hsource : ∀ᶠ v in l, v ∈ flatDomain Ψ :=
      nhdsWithin_le_nhds ((isOpen_flatDomain Ψ).mem_nhds hu)
    have hzero : ∀ᶠ v in l, flatMap Ψ v ∈ coordSubspace S := by
      filter_upwards [hsource, self_mem_nhdsWithin] with v hv hvpre
      exact (hraw v hv hvpre).2
    exact (isClosed_coordSubspace S).mem_of_tendsto hlim hzero
  obtain ⟨hsection, hsectionRealize⟩ :=
    partial_realization_after_chartVec S k j hjfree s hs hrealize
  exact ⟨j, hj, hjfree, Ψ, hΨsrc, hcoords, hdiag', hstrict, hsection, hsectionRealize⟩

end

end Hironaka.HironakaG4ToricFreePivot

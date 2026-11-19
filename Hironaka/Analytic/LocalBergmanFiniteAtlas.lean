import Hironaka.Analytic.DemaillyAnalyticType
import Hironaka.Analytic.PotentialTheory.GlobalPotentialsBasic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.QuasiEquisingularBergmanAtlas


open DemaillyAnalyticType

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- One actual coordinate neighbourhood carrying the finite local Bergman data
at a fixed exponent.  The domain is retained with its smooth local potential,
so it can subsequently participate in a global gluing construction. -/
structure LocalBergmanPatch (θ : SmoothRealForm n M 2) (u : M → EReal) (m : ℕ) where
  chart : ComplexChart n M
  domain : TopologicalSpace.Opens (ComplexModel n)
  domain_le_target : (domain : Set (ComplexModel n)) ⊆ chart.val.target
  potential : ComplexModel n → ℝ
  localPotential : IsSmoothLocalPotential θ chart domain potential
  plurisubharmonic :
    PlurisubharmonicOn (fun z => chartFunction u chart z + (potential z : EReal)) domain
  N : ℕ
  generator : Fin N → ComplexModel n → ℂ
  generator_analytic : ∀ l, AnalyticOnNhd ℂ (generator l) domain
  generator_weighted : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ l, WeightedL2On (fun z => chartFunction u chart z + (potential z : EReal)) m
      (generator l) domain volume
  domination : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y ∈ domain,
    EReal.exp ((m : EReal) *
      (chartFunction u chart y + (potential y : EReal))) ≤
      C * ∑ l, ENNReal.ofReal (‖generator l y‖ ^ 2)
  analyticType : ∀ y ∈ domain,
    HasAnalyticSingularityTypeAt
      (fun x => (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog generator x) y

namespace LocalBergmanPatch

variable {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}

def corrected (D : LocalBergmanPatch θ u m) : ComplexModel n → EReal :=
  fun z => chartFunction u D.chart z + (D.potential z : EReal)

def source (D : LocalBergmanPatch θ u m) : TopologicalSpace.Opens M :=
  ⟨D.chart.val.source ∩ D.chart.val ⁻¹' D.domain,
    D.chart.val.isOpen_inter_preimage D.domain.isOpen⟩

@[simp] theorem mem_source (D : LocalBergmanPatch θ u m) {x : M} :
    x ∈ D.source ↔ x ∈ D.chart.val.source ∧ D.chart.val x ∈ D.domain := Iff.rfl

theorem source_subset (D : LocalBergmanPatch θ u m) :
    (D.source : Set M) ⊆ D.chart.val.source := inter_subset_left

theorem map_source (D : LocalBergmanPatch θ u m) {x : M} (hx : x ∈ D.source) :
    D.chart.val x ∈ D.domain := hx.2

end LocalBergmanPatch

/-- A finite cover by actual local Bergman patches for one exponent. -/
structure FiniteLocalBergmanAtlas (θ : SmoothRealForm n M 2) (u : M → EReal) (m : ℕ) where
  count : ℕ
  patch : Fin count → LocalBergmanPatch θ u m
  covers : ∀ x : M, ∃ i, x ∈ (patch i).source

/-- Local theta-PSH data and Demailly's finite weighted generators furnish one
Bergman patch around every point. -/
theorem exists_localBergmanPatch_containing
    {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (m : ℕ) (hm : 0 < m) (x : M) :
    ∃ D : LocalBergmanPatch θ u m, x ∈ D.source := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu.1 e (e.val x) hz
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨O, hO, hzO, hOW, N, g, C, hC, hg, hL2, hdom, htype⟩ :=
    exists_weightedL2_generators_with_analyticSingularityType W
      (fun z => chartFunction u e z + (ρ z : EReal)) hρ.1 hpsh (e.val x) hzW m hm
  refine ⟨{
    chart := e
    domain := ⟨O, hO⟩
    domain_le_target := hOW.trans hρ.2.1
    potential := ρ
    localPotential := hρ.mono hO hOW
    plurisubharmonic := hpsh.mono hOW
    N := N
    generator := g
    generator_analytic := hg
    generator_weighted := hL2
    domination := ⟨C, hC, hdom⟩
    analyticType := htype }, ?_⟩
  exact ⟨hx, hzO⟩

/-- Compactness extracts finitely many concrete coordinate patches, each with
finite Bergman generators, from the pointwise local construction. -/
theorem nonempty_finiteLocalBergmanAtlas [CompactSpace M]
    {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (m : ℕ) (hm : 0 < m) :
    Nonempty (FiniteLocalBergmanAtlas θ u m) := by
  classical
  have hcover : (univ : Set M) ⊆ ⋃ D : LocalBergmanPatch θ u m, (D.source : Set M) := by
    intro x _
    obtain ⟨D, hx⟩ := exists_localBergmanPatch_containing hu m hm x
    exact mem_iUnion.mpr ⟨D, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun D : LocalBergmanPatch θ u m => (D.source : Set M))
    (fun D => D.source.isOpen) hcover
  refine ⟨{
    count := s.card
    patch := fun i => (s.equivFin.symm i).val
    covers := ?_ }⟩
  intro x
  obtain ⟨D, hDx⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hD, hx⟩ := mem_iUnion.mp hDx
  refine ⟨s.equivFin ⟨D, hD⟩, ?_⟩
  change x ∈ (((s.equivFin.symm (s.equivFin ⟨D, hD⟩)).val).source : Set M)
  rw [Equiv.symm_apply_apply]
  exact hx

end

end Hironaka.QuasiEquisingularBergmanAtlas

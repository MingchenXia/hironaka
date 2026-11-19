import Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank
import Hironaka.Analytic.FibreDimensionLowerBound

/-!
# Native Remmert, item 5.4: fibres are not too small (lane G10R3)

Setting of `HironakaG10MwRemmertRegular`: `Y` a second-countable native reduced complex space,
`φ : Y ⟶ ofClosedAnalytic C hC`, `g = pointMap φ : Y → M`.

* `NativeLocDimGE Y A y q`: in EVERY local embedding `(Ω, C)` of `Y` through `y`, the trace of `A` in `Ω` has
  local dimension `≥ q` at the point over `y` (`AnalyticDimensionBasics.LocDimGE`).
* `nativeLocDimGE_fibre` (**the fibre-dimension lower bound**, Demailly II.8.2): if `Y` has pure dimension `d` and
  the native rank of `φ` is `≤ r` everywhere on `Reg_d(Y)`, then every fibre `g⁻¹(g y)` has native local
  dimension `≥ d - r` at `y`.

Proof: in a local embedding take an ambient lift `G : W → M` of `g` (`HironakaG10RkNativeRank.exists_lift`); on
the manifold `W` the carrier is pure of dimension `d` and, by the chart bridge, `G` has rank `≤ r` at its regular
points; apply the manifold theorem `FibreDimensionLowerBound.locDimGE_fibre`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Set TopologicalSpace Topology Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10RkFibreDim

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  RankDegeneracy AnalyticDimensionBasics HironakaG10MwRemmertRegular HironakaG10RkNativeRank

noncomputable section

/-- **Native local dimension `≥ q`**: in every local embedding through `y`, the trace of `A` in the ambient space
has local dimension at least `q` at the point over `y`. -/
def NativeLocDimGE (Y : SourceReducedComplexSpace) (A : Set Y.obj.left) (y : Y.obj.left) (q : ℕ) : Prop :=
  ∀ (e : LocalEmbedding Y) (c : e.carrier), e.toPoint c = y →
    LocDimGE (n := e.dim) (HironakaG10EpNativeDim.trace e A) c.val q

variable {Y : SourceReducedComplexSpace} {d k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {C : Set M}
  {hC : IsComplexAnalyticSubset (n := k) C}

theorem NativeLocDimGE.mono {A B : Set Y.obj.left} {y : Y.obj.left} {q : ℕ}
    (h : NativeLocDimGE Y A y q) (hAB : A ⊆ B) (hB : Y.IsAnalyticSubset B) : NativeLocDimGE Y B y q :=
  fun e c hc => DimensionMonotone.LocDimGE.mono
    (HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hB e)
    (HironakaG10EpNativeDim.trace_mono e hAB) (h e c hc)

/-- **The fibre-dimension lower bound** (item 5.4; Demailly II.8.2).  If `Y` has pure dimension `d` and the
native rank of `φ` is at most `r` on `Reg_d(Y)`, then for every `y` the fibre `g⁻¹(g y)` has native local
dimension at least `d - r` at `y`. -/
theorem nativeLocDimGE_fibre [SecondCountableTopology Y.obj.left] (φ : Y ⟶ ofClosedAnalytic C hC)
    (hY : NativePureDim Y d) {r : ℕ} (hr : ∀ y, nativeRankAt d φ y ≤ r) (y : Y.obj.left) :
    NativeLocDimGE Y (pointMap φ ⁻¹' {pointMap φ y}) y (d - r) := by
  intro e c hcy
  obtain ⟨W, hcW, G, hG, hGl⟩ := exists_lift φ e c
  set A' : Set W := (↑) ⁻¹' e.carrier with hA'
  have hA'a : IsComplexAnalyticSubset (n := e.dim) A' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic W
  have hpure : IsPureDim (n := e.dim) A' d := by
    intro z j hz
    have hzC : (z : e.ambient) ∈ e.carrier := hz.2.1
    exact hY _ j ((regularAtDim_carrier_restrict_iff e W ⟨z.val, hzC⟩ z.property j).mp hz)
  have hrank : ∀ z, RegularAtDim (n := e.dim) A' z d → rankAt (n := e.dim) (n' := k) G A' z ≤ r := by
    intro z hz
    have hzC : (z : e.ambient) ∈ e.carrier := hz.2.1
    have hreg : e.toPoint ⟨z.val, hzC⟩ ∈ regLocus Y d :=
      (regularAtDim_carrier_restrict_iff e W ⟨z.val, hzC⟩ z.property d).mp hz
    have hb := nativeRankAt_eq_rankAt_lift φ e ⟨z.val, hzC⟩ hreg W z.property G hG hGl
    rw [← hb]
    exact hr _
  have hcA' : (⟨c.val, hcW⟩ : W) ∈ A' := c.property
  have hfib := FibreDimensionLowerBound.locDimGE_fibre hA'a hpure hG hrank hcA'
  have hset : A' ∩ G ⁻¹' {G ⟨c.val, hcW⟩} =
      ((↑) ⁻¹' HironakaG10EpNativeDim.trace e (pointMap φ ⁻¹' {pointMap φ y}) : Set W) := by
    ext z
    have hGc : G ⟨c.val, hcW⟩ = pointMap φ y := by rw [hGl c hcW, hcy]
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hGc]
    constructor
    · rintro ⟨hzC, hzG⟩
      refine (HironakaG10EpNativeDim.mem_trace e _ ⟨z.val, hzC⟩).mpr ?_
      change pointMap φ (e.toPoint ⟨z.val, hzC⟩) = pointMap φ y
      rw [← hGl ⟨z.val, hzC⟩ z.property]
      exact hzG
    · intro hz
      have hzC : (z : e.ambient) ∈ e.carrier := HironakaG10EpNativeDim.trace_subset_carrier e _ hz
      refine ⟨hzC, ?_⟩
      have h := (HironakaG10EpNativeDim.mem_trace e _ ⟨z.val, hzC⟩).mp hz
      rw [show G z = G ⟨(⟨z.val, hzC⟩ : e.carrier).val, z.property⟩ from rfl, hGl]
      exact h
  rw [hset] at hfib
  exact AnalyticSubsetOpens.locDimGE_preimage_val_iff.mp hfib

end

end Hironaka.Analytic.Unibranch.HironakaG10RkFibreDim

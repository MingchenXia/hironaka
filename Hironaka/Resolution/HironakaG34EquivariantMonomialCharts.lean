import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Resolution.HironakaG34CoordinateScaling

/-!
# Lifted diagonal maps in the monomial charts of a blow-up (brick (d1))

Lane G34 (run 0080, round 11).  Blueprint: `hironaka-g34-resume-equivariant-monomial-charts.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §9.1 item 4, §9.2 (d1).

Let `π : Z → M` be the blow-up along `C`, flattened near `y₀` by `Φ ∘ e` onto `ℂᵏ × 0`, and let `ℓⱼ` lift the `j`-th
monomial chart `γⱼ = e⁻¹ ∘ Φ⁻¹ ∘ σⱼ` (`π ∘ ℓⱼ = γⱼ`).  Let `g` be a map of `M` which near `γⱼ(w₀)` acts DIAGONALLY in the
coordinates `Φ ∘ e` (`(Φ ∘ e)(g p) = a · (Φ ∘ e)(p)`), and `g'` a map of `Z`, continuous at `ℓⱼ(w₀)`, lifting `g` near
`ℓⱼ(w₀)` (`π ∘ g' = g ∘ π`).  Then

  `g' (ℓⱼ w₀) = ℓⱼ (chartScale a k j w₀)`        (`monomialLift_comm_of_diagonal`),

i.e. in the monomial chart the lift acts diagonally, by `a` on the coordinates of `C` and the pivot `wⱼ` and by the ratios
`aᵢ / aⱼ` on the other normal coordinates.  Proof: both sides of the identity, as functions of `w` near `w₀`, are
continuous and lift `g ∘ γⱼ = γⱼ ∘ chartScale` (`monomial_chartScale`); where `wⱼ ≠ 0` their image is off the centre, where
`π` is injective (`BlowupIsomorphismOff`); and `{wⱼ ≠ 0}` is dense.  No universal property, no group structure and no
continuity of the map in a parameter are used (the held `exists_diagonal_history_lift_chart` is the global special case
on the entire model).

## Main results

* `mem_closure_coord_ne_zero`;
* **`monomialLift_comm_of_diagonal`**.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34EquivariantMonomialCharts
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  HironakaNormalCrossingsDiagonalLiftOrbits HironakaG34CoordinateScaling

variable {n : ℕ}

/-- Points with a nonzero `j`-th coordinate are dense in `ℂⁿ`. -/
theorem mem_closure_coord_ne_zero (j : Fin n) (z : ComplexModel n) :
    z ∈ closure {z : ComplexModel n | z j ≠ 0} := by
  by_cases hz : z j = 0
  · rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨z + EuclideanSpace.single j ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · show (z + EuclideanSpace.single j ((ε / 2 : ℝ) : ℂ)) j ≠ 0
      have hzj : (z + EuclideanSpace.single j ((ε / 2 : ℝ) : ℂ)) j = ((ε / 2 : ℝ) : ℂ) := by
        simp [hz]
      rw [hzj]
      exact Complex.ofReal_ne_zero.mpr (half_pos hε).ne'
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, PiLp.norm_single]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  · exact subset_closure hz

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M} {y₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}

theorem flatMap_monomialChart (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (v : LiftedOpen.{u} (monomialDomain Φ k j)) :
    flatMap Φ (monomialChart Φ k j v) = monomial k j (LiftedOpen.toModel _ v) := by
  ext i
  exact flatCoord_monomialChart hΦsrc v i

/-- **Lifted diagonal maps act diagonally in the monomial charts.** -/
theorem monomialLift_comm_of_diagonal (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hj : k ≤ j.1) {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Z} (hℓ : Continuous ℓ)
    (hℓπ : π ∘ ℓ = monomialChart Φ k j) {g : M → M} {g' : Z → Z} {a : Fin n → ℂ} (haj : a j ≠ 0)
    (w₀ : LiftedOpen.{u} (monomialDomain Φ k j)) (hg' : ContinuousAt g' (ℓ w₀))
    (hcomm : ∀ᶠ z in 𝓝 (ℓ w₀), π (g' z) = g (π z))
    (hdiag : ∀ᶠ p in 𝓝 (monomialChart Φ k j w₀),
      g p ∈ flatDomain Φ ∧ flatMap Φ (g p) = diagonal a (flatMap Φ p))
    (hw₀ : chartScale a k j (LiftedOpen.toModel _ w₀) ∈ monomialDomain Φ k j) :
    g' (ℓ w₀) = ℓ (LiftedOpen.mk _ _ hw₀) := by
  classical
  let L : ComplexModel n → Z := fun z => if h : z ∈ (monomialDomain Φ k j) then ℓ (LiftedOpen.mk (monomialDomain Φ k j) z h) else ℓ w₀
  have hL : ∀ v : LiftedOpen.{u} (monomialDomain Φ k j), L (LiftedOpen.toModel (monomialDomain Φ k j) v) = ℓ v := by
    intro v
    simp only [L, dif_pos (LiftedOpen.toModel_mem (monomialDomain Φ k j) v), LiftedOpen.mk_toModel]
  have hLmk : ∀ z (hz : z ∈ (monomialDomain Φ k j)), L z = ℓ (LiftedOpen.mk (monomialDomain Φ k j) z hz) := fun z hz => by
    simp only [L, dif_pos hz]
  have hLcont : ∀ z ∈ (monomialDomain Φ k j), ContinuousAt L z := by
    intro z hz
    have h1 : ContinuousAt (L ∘ LiftedOpen.toModel (monomialDomain Φ k j)) (LiftedOpen.mk (monomialDomain Φ k j) z hz) := by
      have : L ∘ LiftedOpen.toModel (monomialDomain Φ k j) = ℓ := funext hL
      rw [this]
      exact hℓ.continuousAt
    exact ((LiftedOpen.isOpenEmbedding_toModel (monomialDomain Φ k j)).continuousAt_iff.mp h1)
  have hLπ : ∀ z (hz : z ∈ (monomialDomain Φ k j)), π (L z) = monomialChart Φ k j (LiftedOpen.mk (monomialDomain Φ k j) z hz) := by
    intro z hz
    rw [hLmk z hz]
    exact congrFun hℓπ _
  set z₀ := LiftedOpen.toModel (monomialDomain Φ k j) w₀ with hz₀
  have hz₀D : z₀ ∈ (monomialDomain Φ k j) := LiftedOpen.toModel_mem (monomialDomain Φ k j) w₀
  have hLz₀ : L z₀ = ℓ w₀ := hL w₀
  have hscont : Continuous (chartScale a k j) := (contDiff_diagonal _).continuous
  have hf₁ : ContinuousAt (fun z => g' (L z)) z₀ :=
    ContinuousAt.comp_of_eq hg' (hLcont z₀ hz₀D) hLz₀
  have hf₂ : ContinuousAt (fun z => L (chartScale a k j z)) z₀ :=
    (hLcont _ hw₀).comp hscont.continuousAt
  have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ (monomialDomain Φ k j) := (monomialDomain Φ k j).isOpen.mem_nhds hz₀D
  have h2 : ∀ᶠ z in 𝓝 z₀, chartScale a k j z ∈ (monomialDomain Φ k j) :=
    hscont.continuousAt.preimage_mem_nhds ((monomialDomain Φ k j).isOpen.mem_nhds hw₀)
  have hLt : Tendsto L (𝓝 z₀) (𝓝 (ℓ w₀)) := by
    have := (hLcont z₀ hz₀D).tendsto
    rwa [hLz₀] at this
  have h3 : ∀ᶠ z in 𝓝 z₀, π (g' (L z)) = g (π (L z)) := hLt.eventually hcomm
  have hπLt : Tendsto (fun z => π (L z)) (𝓝 z₀) (𝓝 (monomialChart Φ k j w₀)) := by
    have h := (hπ.contMDiff.continuous.tendsto (ℓ w₀)).comp hLt
    have he : π (ℓ w₀) = monomialChart Φ k j w₀ := congrFun hℓπ w₀
    rw [he] at h
    exact h
  have h4 : ∀ᶠ z in 𝓝 z₀, g (π (L z)) ∈ flatDomain Φ ∧
      flatMap Φ (g (π (L z))) = diagonal a (flatMap Φ (π (L z))) := hπLt.eventually hdiag
  have hinj := (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.injOn
  have heq : ∀ᶠ z in 𝓝[{z : ComplexModel n | z j ≠ 0}] z₀,
      g' (L z) = L (chartScale a k j z) := by
    filter_upwards [nhdsWithin_le_nhds (h1.and (h2.and (h3.and h4))), self_mem_nhdsWithin] with
      z ⟨hzD, hzs, hc, hdg⟩ hzj
    have e1 := hLπ z hzD
    have e2 := hLπ _ hzs
    have hB : π (L (chartScale a k j z)) ∈ flatDomain Φ := by
      rw [e2]; exact monomialChart_mem_flatDomain hΦsrc _
    have hfl : flatMap Φ (g (π (L z))) = flatMap Φ (π (L (chartScale a k j z))) := by
      rw [hdg.2, e1, e2, flatMap_monomialChart hΦsrc, flatMap_monomialChart hΦsrc,
        LiftedOpen.toModel_mk, LiftedOpen.toModel_mk, monomial_chartScale a haj]
    have hgeq : g (π (L z)) = π (L (chartScale a k j z)) := by
      rw [← flatInverse_flat Φ hdg.1, ← flatInverse_flat Φ hB]
      exact congrArg (fun u => (chartAt (ComplexModel n) y₀).symm (Φ.invFun u)) hfl
    have hnotC : π (L (chartScale a k j z)) ∉ C := by
      intro hC
      have hmem := (hflat hB.1 hB.2).1 hC
      have hjz := hmem j hj
      change flatMap Φ (π (L (chartScale a k j z))) j = 0 at hjz
      rw [e2, flatMap_monomialChart hΦsrc, LiftedOpen.toModel_mk] at hjz
      simp only [monomial_apply, ne_eq, not_true_eq_false, and_false, if_false, chartScale,
        diagonal_apply] at hjz
      exact hzj ((mul_eq_zero.mp hjz).resolve_left haj)
    refine hinj (show π (g' (L z)) ∈ Cᶜ by rw [hc, hgeq]; exact hnotC) hnotC ?_
    rw [hc, hgeq]
  have : (𝓝[{z : ComplexModel n | z j ≠ 0}] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_coord_ne_zero j z₀)
  have hlim := tendsto_nhds_unique_of_eventuallyEq (hf₁.tendsto.mono_left nhdsWithin_le_nhds)
    (hf₂.tendsto.mono_left nhdsWithin_le_nhds) heq
  rw [hLz₀, hLmk _ hw₀] at hlim
  exact hlim

end
end Hironaka.HironakaG34EquivariantMonomialCharts

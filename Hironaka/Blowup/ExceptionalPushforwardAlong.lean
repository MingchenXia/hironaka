/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ExceptionalIdealPushforward
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Blowup.NestedFlattening
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The blowup calculus along a submanifold: the chart retraction and `π_* 𝒪(-KD)` along `N'`

The blowup half of the calculus along a submanifold `N ≠ M` (`hir:along-calculus`). Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`) §2.2 and the monomial charts of `le:inclusions`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`) §3 (marked ideals `(M, N, E, 𝓘, d)`, the transform restricted to `N'`).

Let `π : Y → X` be the blowup along `C`, `N ⊇ C` a closed submanifold and
`N' = closure (π⁻¹(N \ C))` its strict transform.  At a point `z ∈ N'` over `C`:

* `exists_chartRetraction`: in nested flattening coordinates `Φ` at `π z` (`C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`) the
  flat retraction `r = φ ∘ P ∘ ψ` of `X` onto `N` (`P` = `planeRetract k_N`; `ψ = flatMap Φ`, `φ = flatInv Φ`,
  `GiraudAlong` API) lifts through the monomial chart `σⱼ` containing `z` (necessarily `j < k_N`) to `r' = ℓⱼ ∘ P ∘
  W`, a holomorphic map near `z` with `r' z = z`, values in `N'`, and `π ∘ r' = r ∘ π`. The key identity is `σⱼ ∘ P
  = P ∘ σⱼ` for `j < k_N` (`monomial_planeRetract`); that `ℓⱼ` maps the plane into `N'` is
  `lift_mem_geoStrictTransform`.
* `mem_idealPow_vanishingIdeal_along_of_pullback`: if `f ∘ π` agrees on `N'` near `z` with a germ of
  `𝒪(-D)^K`, then `f` agrees on `N` near `π z` with a germ of `𝓘_C^K` (the along-`N'` form of
  `π_* 𝒪(-KD) = 𝓘_C^K`).  Proof: `f♭ = f ∘ r` has `f♭ ∘ π = (f ∘ π) ∘ r'` near `z`; `r'` maps
  `𝒪(-D)^K` into itself (`comp_mem_idealPow`, `comp_mem_exceptionalDivisor`) and `N'` near `z` into
  `N'`, so `f♭ ∘ π ∈ 𝒪(-D)^K` at `z`, and `ExceptionalIdealPushforward` gives `f♭ ∈ 𝓘_C^K`; and
  `f♭ = f` on `N`.
* `geoStrictTransform_inter_eq`: `(H ∩ N)' = H' ∩ N'` for a member `H` of a simple normal crossings
  divisor transverse to `N`, the centre `C ⊆ N` having normal crossings with it.

For a marked ideal `(M, N, E, 𝔞, d)` (`N` a closed submanifold, `𝔞` coherent, `C ⊆ cosupp`) with
transformed ideal `𝔞' = 𝓘_D^{-d} π^*𝔞|_{N'}` (`MarkedIdeal.geoTransform`):

* `restrictLe_pullback_geoTransform`: `π^*𝔞|_{N'} ⊆ (𝒪(-dD) · 𝔞')|_{N'}` (the restricted form of
  `π^*𝔞 = 𝒪(-dD) σ^c(𝔞, d)`);
* clause 1 of `bcalc:controlled-not-exceptional` along `N'`
  (`mem_cosupport_succ_of_geoTransform_le`, `exists_not_isInSpanOnAt_exceptionalDivisor`): if every
  germ of `𝔞'` at `z ∈ D ∩ N'` is, on `N'`, a combination of germs of `𝒪(-D)`, then
  `ord_{π z}(𝔞|_N) ≥ d + 1`;
* clause 2 along `N'` (`frequently_le_vanishingIdeal_of_geoTransform_le`,
  `exists_not_mem_vanishingIdeal_of_geoTransform`), for a closed `A ⊆ N` (e.g. `A = H ∩ N`): if
  `𝔞' ⊆ 𝓘_{A'}` at `z ∈ A'`, then `𝔞 ⊆ 𝓘_A` at points of `A \ C` arbitrarily close to `π z`;
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExceptionalPushforwardAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
open Hironaka.BlowupFlatCoordinates
open Hironaka.BlowupMonomialCharts
open Hironaka.BlowupLocalSurjectivity
open Hironaka.BlowupExceptionalDivisor
open Hironaka.BlowupStrictSubmanifold
open Hironaka.BlowupSNCTransform
open Hironaka.NormalCrossings
open Hironaka.HadamardBridgeAlong
open Hironaka.GiraudAlong
open Hironaka.GlueingTrivialAction
open Hironaka.RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ}

/-! ### The monomial map commutes with the retraction onto a plane containing its index -/

/-- **`σⱼ ∘ P = P ∘ σⱼ`** for the retraction `P` onto `ℂᵐ × 0` when `j < m`. -/
theorem monomial_planeRetract {k m : ℕ} {j : Fin n} (hjm : j.1 < m) (v : ComplexModel n) :
    monomial k j (planeRetract m v) = planeRetract m (monomial k j v) := by
  ext i
  simp only [monomial_apply, planeRetract_apply]
  by_cases hi : i.1 < m <;> by_cases hc : k ≤ i.1 ∧ i ≠ j <;> simp [hi, hc, hjm]

/-! ### Holomorphy of the flat coordinates -/

section Flat

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {x : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- The flat coordinates `ψ = Φ ∘ e` are holomorphic on the flat domain. -/
theorem mdifferentiableAt_flatMap {y : M} (hy : y ∈ flatDomain Φ) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (flatMap Φ) y := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.toFun
      (chartAt (ComplexModel n) x y) :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).mdifferentiableAt
  exact h1.comp y (mdifferentiableAt_chart hy.1)

/-- Their inverse `φ = e⁻¹ ∘ Φ⁻¹` is holomorphic on the target. -/
theorem mdifferentiableAt_flatInv (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    {w : ComplexModel n} (hw : w ∈ Φ.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (flatInv Φ) w := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Φ.invFun w :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).mdifferentiableAt
  exact (mdifferentiableAt_chart_symm (hΦsrc (Φ.mapsTo_invFun hw))).comp w h1

end Flat

/-! ### The lifted chart maps a coordinate subspace into the strict transform -/

section Lift

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}
  {y₀ : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- The flat coordinates of a point of the `j`-th monomial chart. -/
theorem flatMap_monomialChart (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    {j : Fin n} (p : LiftedOpen.{u} (monomialDomain Φ k j)) :
    Φ.toFun (chartAt (ComplexModel n) y₀ (monomialChart Φ k j p)) =
      monomial k j (LiftedOpen.toModel _ p) := by
  have hmon : monomial k j (LiftedOpen.toModel _ p) ∈ Φ.target := LiftedOpen.toModel_mem _ p
  rw [monomialChart, (chartAt (ComplexModel n) y₀).right_inv (hΦsrc (Φ.mapsTo_invFun hmon)),
    Φ.right_inv _ hmon]

/-- **The lift of a monomial chart maps a coordinate subspace into the strict transform.**  Let `Φ`
flatten `C` onto `ℂᵏ × 0` and `A` onto `L_T`, `j ≥ k` with `j ∉ T`, and `ℓ` the lift of the
`j`-th monomial chart.  Then `ℓ q ∈ closure (π⁻¹(A \ C))` for every `q` with coordinates in `L_T`
(over `A \ C` when `q_j ≠ 0`, a limit of such points along `q + t e_j` otherwise). -/
theorem lift_mem_geoStrictTransform
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {A : Set X} {T : Finset (Fin n)}
    (hflatA : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ coordSubspace T))
    {j : Fin n} (hj : k ≤ j.1) (hjT : j ∉ T)
    {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y}
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓπ : π ∘ ℓ = monomialChart Φ k j)
    {q : LiftedOpen.{u} (monomialDomain Φ k j)} (hq : LiftedOpen.toModel _ q ∈ coordSubspace T) :
    ℓ q ∈ geoStrictTransform π C A := by
  -- off `w_j = 0` the lifted point lies over `A \ C`
  have key : ∀ q' : LiftedOpen.{u} (monomialDomain Φ k j),
      LiftedOpen.toModel _ q' ∈ coordSubspace T → LiftedOpen.toModel _ q' j ≠ 0 →
        ℓ q' ∈ π ⁻¹' (A \ C) := by
    intro q' hq'T hq'j
    have hπq : π (ℓ q') = monomialChart Φ k j q' := congrFun hℓπ q'
    have hsrc : π (ℓ q') ∈ flatDomain Φ := by
      rw [hπq]; exact monomialChart_mem_flatDomain hΦsrc q'
    have hcoord : Φ.toFun (chartAt (ComplexModel n) y₀ (π (ℓ q'))) =
        monomial k j (LiftedOpen.toModel _ q') := by
      rw [hπq]; exact flatMap_monomialChart hΦsrc q'
    refine ⟨(hflatA hsrc.1 hsrc.2).mpr ?_, fun hC => hq'j ?_⟩
    · rw [hcoord]; exact monomial_mem_coordSubspace hq'T
    · have h := (hflatC hsrc.1 hsrc.2).mp hC
      rw [hcoord, monomial_mem_plane_iff hj] at h
      exact h
  by_cases hqj : LiftedOpen.toModel _ q j = 0
  · rw [geoStrictTransform, mem_closure_iff_nhds]
    intro U hU
    have hpre : ℓ ⁻¹' U ∈ 𝓝 q := hℓs.continuous.continuousAt.preimage_mem_nhds hU
    have himg : LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∈ 𝓝 (LiftedOpen.toModel _ q) := by
      have := (LiftedOpen.isOpenEmbedding_toModel (S := monomialDomain Φ k j)).map_nhds_eq q
      rw [← this]
      exact image_mem_map hpre
    set e_j : ComplexModel n := EuclideanSpace.single j 1 with he_j
    have hcurve : Tendsto (fun t : ℂ => LiftedOpen.toModel _ q + t • e_j) (𝓝 0)
        (𝓝 (LiftedOpen.toModel _ q)) := by
      have : Continuous (fun t : ℂ => LiftedOpen.toModel _ q + t • e_j) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using this.tendsto 0
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
        LiftedOpen.toModel _ q + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∧ t ≠ 0 :=
      (show ∀ᶠ t in 𝓝[≠] (0 : ℂ), LiftedOpen.toModel _ q + t • e_j ∈
          LiftedOpen.toModel _ '' (ℓ ⁻¹' U) from
        mem_nhdsWithin_of_mem_nhds (hcurve himg)).and self_mem_nhdsWithin
    obtain ⟨t, ⟨q', hq'U, hq't⟩, ht0⟩ := hev.exists
    refine ⟨ℓ q', hq'U, key q' ?_ ?_⟩
    · rw [hq't]
      intro i hi
      have hij : i ≠ j := fun h => hjT (h ▸ hi)
      simp [he_j, hq i hi, hij]
    · rw [hq't]
      simp [he_j, hqj, ht0]
  · exact subset_closure (key q hq hqj)

end Lift

/-! ### Strict transforms of the traces of the members on `N` -/

section Trace

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- `L_{S ∪ T} = L_S ∩ L_T`. -/
theorem coordSubspace_union (S T : Finset (Fin n)) :
    coordSubspace (S ∪ T) = coordSubspace S ∩ coordSubspace T := by
  ext w
  simp only [coordSubspace, Finset.mem_union, mem_ofPred_eq, mem_inter_iff]
  exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩,
    fun h j hj => hj.elim (h.1 j) (h.2 j)⟩

/-- **`(H ∩ N)' = H' ∩ N'`**: for a member `H` of a simple normal crossings divisor `E` transverse
to a closed set `N ⊇ C`, the centre `C` having only normal crossings with `E`, the strict
transform of the trace `H ∩ N` is the trace on `N'` of the strict transform `H'`.  (Off `π⁻¹ C`
the blowup is biholomorphic; over `C`, in adapted coordinates and a monomial chart, all three
strict transforms are coordinate subspaces, `bcalc:snc-chart`.) -/
theorem geoStrictTransform_inter_eq (hπ : IsBlowupAlong n C π) {N : Set X} (hNc : IsClosed N)
    (hCN : C ⊆ N) {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hnc : HasNormalCrossings n C E) (i : Fin E.length) :
    geoStrictTransform π C (E.get i ∩ N) =
      geoStrictTransform π C (E.get i) ∩ geoStrictTransform π C N := by
  classical
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hHc : IsClosed (E.get i) := hE.1 _ (List.get_mem _ _)
  refine Subset.antisymm (subset_inter
    (closure_mono (preimage_mono (sdiff_subset_sdiff_left inter_subset_left)))
    (closure_mono (preimage_mono (sdiff_subset_sdiff_left inter_subset_right)))) ?_
  rintro z ⟨hzH, hzN⟩
  have hzH' : π z ∈ E.get i := geoStrictTransform_subset_preimage hπc hHc hzH
  have hzN' : π z ∈ N := geoStrictTransform_subset_preimage hπc hNc hzN
  by_cases hzC : π z ∈ C
  · have hn : 0 < n := SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hzC
    obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ :=
      SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn hCN hE hT hnc hzC
    have hx' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
    have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
      fun hy hyΦ => (hflat hy hyΦ).1
    set TN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => kN ≤ t.1 with hTN
    have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace TN) :=
      fun hy hyΦ => by
        rw [hTN, coordSubspace_eq_complexCoordinatePlane]; exact (hflat hy hyΦ).2.1
    have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
      fun hy hyΦ => by rw [mem_coordSubspace_singleton]; exact (hflat hy hyΦ).2.2 i hzH'
    have hflatHN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ E.get i ∩ N ↔
            Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace ({s i} ∪ TN)) :=
      fun hy hyΦ => by
        rw [coordSubspace_union]; exact and_congr (hflatH hy hyΦ) (hflatN hy hyΦ)
    obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
      exists_monomialLocalInverse hπ hΦt hflatC hx'
    obtain ⟨hjH, hWH⟩ :=
      (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH hj hO hWs hWeq hℓ hzO).mp hzH
    obtain ⟨hjN, hWN⟩ :=
      (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN hj hO hWs hWeq hℓ hzO).mp hzN
    refine (mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatHN hj hO hWs hWeq hℓ
      hzO).mpr ⟨?_, ?_⟩
    · rw [Finset.mem_union]
      rintro (h | h)
      exacts [hjH h, hjN h]
    · rw [coordSubspace_union]
      exact ⟨hWH, hWN⟩
  · exact subset_closure ⟨⟨hzH', hzN'⟩, hzC⟩

end Trace

/-! ### The chart retraction -/

section Retraction

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The chart retraction** (the blowup half of the normal form `𝔞♭ = r^*(𝔞|_N)` of
`hir:along-calculus`).  Let `π` be the blowup along `C`, `N ⊇ C` a closed submanifold and `z` a
point of the strict transform `N'` over `C`.  There are a holomorphic retraction `r` of a
neighbourhood of `π z` onto `N` (`r y ∈ N`, `r = id` on `N`) and a holomorphic map `r'` near `z`
with `r' z = z`, values in `N'`, and `π ∘ r' = r ∘ π` near `z`.  (In nested flattening coordinates
`r = φ ∘ P ∘ ψ`, and `r' = ℓⱼ ∘ P ∘ W` in the monomial chart through `z`.) -/
theorem exists_chartRetraction (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N) :
    ∃ (r : X → X) (r' : Y → Y),
      (∀ᶠ y in 𝓝 (π z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r y) ∧
      (∀ᶠ y in 𝓝 (π z), r y ∈ N) ∧ (∀ᶠ y in 𝓝 (π z), y ∈ N → r y = y) ∧
      (∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r' w) ∧
      r' z = z ∧ (∀ᶠ w in 𝓝 z, r' w ∈ geoStrictTransform π C N) ∧
      (∀ᶠ w in 𝓝 z, π (r' w) = r (π w)) := by
  classical
  obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
  obtain ⟨kN, hkN⟩ := hN.2 (π z) (hCN hzC)
  have hkCN : kC ≤ kN := le_of_regularAtDim_subset hkC hkN hCN
  obtain ⟨Φ, hΦsrc, hΦx, hflat⟩ := NestedFlattening.exists_nested_flattening hkCN hkC hkN hCN
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => (hflat hy hyΦ).2
  set TN : Finset (Fin n) := Finset.univ.filter fun t : Fin n => kN ≤ t.1 with hTN
  have hflatN' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace TN) :=
    fun hy hyΦ => by rw [hTN, coordSubspace_eq_complexCoordinatePlane]; exact hflatN hy hyΦ
  have hx' : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflatC hx'
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflatC hj
  obtain ⟨hjT, hWzT⟩ :=
    (mem_geoStrictTransform_iff_of_chart hπ hΦsrc hflatC hflatN' hj hO hWs hWeq hℓ hzO).mp hzN
  have hjN : j.1 < kN := by
    by_contra h
    exact hjT (by simp only [hTN, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hWzN : W z ∈ complexCoordinatePlane n kN := by
    rw [← coordSubspace_eq_complexCoordinatePlane]; exact hWzT
  have hw₀ : W z ∈ monomialDomain Φ kC j := by
    show monomial kC j (W z) ∈ Φ.target
    rw [(hWeq z hzO).2]; exact Φ.mapsTo_toFun (hWeq z hzO).1.2
  have hℓz : ℓ (LiftedOpen.mk _ (W z) hw₀) = z := hℓ ℓ hℓs hℓπ z hzO hw₀
  set P := planeRetract (n := n) kN with hP
  have hPWz : P (W z) = W z := planeRetract_of_mem hWzN
  -- near `π z`: the flat domain, and `P ψ` in the target
  have hψ0 : flatMap Φ (π z) = 0 := hΦx
  have hψc : ContinuousAt (fun y => P (flatMap Φ y)) (π z) :=
    P.continuous.continuousAt.comp (mdifferentiableAt_flatMap hx').continuousAt
  have hT0 : (0 : ComplexModel n) ∈ Φ.target := zero_mem_target hΦx
  have hnearX : ∀ᶠ y in 𝓝 (π z), y ∈ flatDomain Φ ∧ P (flatMap Φ y) ∈ Φ.target := by
    refine ((isOpen_flatDomain Φ).eventually_mem hx').and ?_
    have h := hψc.preimage_mem_nhds (Φ.isOpen_target.mem_nhds (by
      show P (flatMap Φ (π z)) ∈ Φ.target
      rw [hψ0, map_zero]; exact hT0))
    exact h
  -- near `z`: the chart domain, and `P W` in the monomial domain
  have hWc : ContinuousAt (fun w => P (W w)) z :=
    P.continuous.continuousAt.comp (hWs z hzO).continuousAt
  have hnearY : ∀ᶠ w in 𝓝 z, w ∈ O ∧ P (W w) ∈ monomialDomain Φ kC j := by
    refine (hO.eventually_mem hzO).and ?_
    exact hWc.preimage_mem_nhds ((monomialDomain Φ kC j).isOpen.mem_nhds (by
      show P (W z) ∈ monomialDomain Φ kC j
      rw [hPWz]; exact hw₀))
  refine ⟨fun y => flatInv Φ (P (flatMap Φ y)), fun w => extendLifted ℓ hw₀ (P (W w)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `r` is holomorphic
    filter_upwards [hnearX] with y hy
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (fun y => P (flatMap Φ y)) y :=
      P.differentiableAt.mdifferentiableAt.comp y (mdifferentiableAt_flatMap hy.1)
    exact MDifferentiableAt.comp (g := flatInv Φ) y (mdifferentiableAt_flatInv hΦsrc hy.2) h2
  · -- `r` takes values in `N`
    filter_upwards [hnearX] with y hy
    exact flatInv_mem hΦsrc hflatN hy.2 (planeRetract_mem kN _)
  · -- `r` fixes `N`
    filter_upwards [hnearX] with y hy hyN
    show flatInv Φ (P (flatMap Φ y)) = y
    rw [planeRetract_of_mem ((mem_iff_flatMap_mem hflatN hy.1).mp hyN), flatInv_flatMap hy.1]
  · -- `r'` is holomorphic
    filter_upwards [hnearY] with w hw
    exact (mdifferentiableAt_extendLifted hℓs hw₀ hw.2).comp w
      (P.differentiableAt.mdifferentiableAt.comp w ((hWs w hw.1).mdifferentiableAt (by simp)))
  · -- `r' z = z`
    show extendLifted ℓ hw₀ (P (W z)) = z
    rw [hPWz, extendLifted_of_mem ℓ hw₀ hw₀, hℓz]
  · -- `r'` takes values in `N'`
    filter_upwards [hnearY] with w hw
    show extendLifted ℓ hw₀ (P (W w)) ∈ geoStrictTransform π C N
    rw [extendLifted_of_mem ℓ hw₀ hw.2]
    refine lift_mem_geoStrictTransform hΦsrc hflatC hflatN' hj hjT hℓs hℓπ ?_
    rw [LiftedOpen.toModel_mk, hTN, coordSubspace_eq_complexCoordinatePlane]
    exact planeRetract_mem kN _
  · -- `π ∘ r' = r ∘ π`
    filter_upwards [hnearY] with w hw
    show π (extendLifted ℓ hw₀ (P (W w))) = flatInv Φ (P (flatMap Φ (π w)))
    rw [extendLifted_of_mem ℓ hw₀ hw.2]
    have h1 : π (ℓ (LiftedOpen.mk _ (P (W w)) hw.2)) =
        monomialChart Φ kC j (LiftedOpen.mk _ (P (W w)) hw.2) := congrFun hℓπ _
    rw [h1]
    show flatInv Φ (monomial kC j (LiftedOpen.toModel _ (LiftedOpen.mk _ (P (W w)) hw.2))) = _
    rw [LiftedOpen.toModel_mk, hP, monomial_planeRetract hjN]
    congr 2
    exact (hWeq w hw.1).2

end Retraction

/-! ### Powers of an ideal under a map fixing the point -/

section Powers

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Powers pass under a holomorphic map fixing the point** that maps the ideal into itself: if
`ρ z = z`, `ρ` is holomorphic near `z` and `q ∘ ρ ∈ 𝔩` at `z` for every `q ∈ 𝔩` at `z`, then
`g ∘ ρ ∈ 𝔩^K` at `z` for every `g ∈ 𝔩^K` at `z`. -/
theorem comp_mem_idealPow {𝔩 : GermIdeal n M} {ρ : M → M} {z : M} (hρz : ρ z = z)
    (hρ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ρ w)
    (h𝔩 : ∀ q, 𝔩.mem z q → 𝔩.mem z (q ∘ ρ)) :
    ∀ (K : ℕ) {g : M → ℂ}, (idealPow 𝔩 K).mem z g → (idealPow 𝔩 K).mem z (g ∘ ρ)
  | 0, g, hg => HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact hg)
  | K + 1, g, hg => by
    obtain ⟨hghol, N, s, a, hs, ha, hsum⟩ := mem_idealPow_succ_iff.mp hg
    have hρt : Tendsto ρ (𝓝 z) (𝓝 z) := by
      have h := hρ.self_of_nhds.continuousAt
      rwa [ContinuousAt, hρz] at h
    refine mem_idealPow_succ_iff.mpr
      ⟨HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact hghol), N,
        fun i => s i ∘ ρ, fun i => a i ∘ ρ, fun i => ?_,
        fun i => HadamardBridge.holomorphicAt_comp_map hρ (by rw [hρz]; exact ha i), ?_⟩
    · obtain ⟨p, q, hp, hq, hpq⟩ := hs i
      exact ⟨p ∘ ρ, q ∘ ρ, comp_mem_idealPow hρz hρ h𝔩 K hp, h𝔩 q hq, by
        show s i ∘ ρ = _
        rw [hpq]; rfl⟩
    · filter_upwards [hρt.eventually hsum] with w hw
      simpa using hw

end Powers

/-! ### The exceptional ideal under the chart retraction -/

section Exceptional

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`𝒪(-D)` is stable under a lift of a retraction fixing `C`**: if `r` is holomorphic near
`π z`, fixes the points of `C` near `π z`, and `π ∘ r' = r ∘ π` near `z` with `r' z = z`, then
`q ∘ r' ∈ 𝒪(-D)` at `z` for every `q ∈ 𝒪(-D)` at `z`. -/
theorem comp_mem_exceptionalDivisor (hπ : IsBlowupAlong n C π) {z : Y} {r : X → X} {r' : Y → Y}
    (hr : ∀ᶠ y in 𝓝 (π z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r y)
    (hrC : ∀ᶠ y in 𝓝 (π z), y ∈ C → r y = y) (hzC : π z ∈ C)
    (hr' : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r' w)
    (hr'z : r' z = z) (hcomm : ∀ᶠ w in 𝓝 z, π (r' w) = r (π w)) (q : Y → ℂ)
    (hq : (exceptionalDivisor hπ).ideal.mem z q) :
    (exceptionalDivisor hπ).ideal.mem z (q ∘ r') := by
  have hrz : r (π z) = π z := hrC.self_of_nhds hzC
  obtain ⟨hqhol, N, s, a, hs, ha, hsum⟩ := GermIdeal.mem_pullback_iff.mp hq
  choose b hb hbs using hs
  have hr't : Tendsto r' (𝓝 z) (𝓝 z) := by
    have h := hr'.self_of_nhds.continuousAt
    rwa [ContinuousAt, hr'z] at h
  have hrt : Tendsto r (𝓝 (π z)) (𝓝 (π z)) := by
    have h := hr.self_of_nhds.continuousAt
    rwa [ContinuousAt, hrz] at h
  -- the generators `b ∘ r` stay in `𝓘_C`
  have hbr : ∀ i, (vanishingIdeal (n := n) C).mem (π z) (b i ∘ r) := by
    intro i
    refine ⟨HadamardBridge.holomorphicAt_comp_map hr (by rw [hrz]; exact (hb i).1), ?_⟩
    filter_upwards [hrC, hrt.eventually (hb i).2] with y hy1 hy2 hyC
    have hry : r y = y := hy1 hyC
    show b i (r y) = 0
    exact hy2 (by rw [hry]; exact hyC)
  refine GermIdeal.mem_pullback_iff.mpr ⟨HadamardBridge.holomorphicAt_comp_map hr'
    (by rw [hr'z]; exact hqhol), N, fun i => (b i ∘ r) ∘ π, fun i => a i ∘ r',
    fun i => ⟨b i ∘ r, hbr i, rfl⟩,
    fun i => HadamardBridge.holomorphicAt_comp_map hr' (by rw [hr'z]; exact ha i), ?_⟩
  filter_upwards [hr't.eventually hsum, hcomm] with w hw hcw
  show q (r' w) = ∑ i, a i (r' w) * b i (r (π w))
  rw [hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbs i]
  simp [Function.comp_apply, hcw]

end Exceptional

/-! ### `π_* 𝒪(-KD) = 𝓘_C^K` along `N'` -/

section Pushforward

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **`π_* 𝒪(-KD) = 𝓘_C^K` along the strict transform of a submanifold**: let `N ⊇ C` be a closed
submanifold, `z ∈ N'` a point over `C`, and `f` holomorphic at `π z`.  If `f ∘ π` agrees on `N'`
near `z` with a holomorphic combination of germs of `𝒪(-D)^K` at `z`, then `f` agrees on `N` near
`π z` with a combination of germs of `𝓘_C^K` at `π z`. -/
theorem mem_idealPow_vanishingIdeal_along_of_pullback (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C)
    (hzN : z ∈ geoStrictTransform π C N) {f : X → ℂ} (hf : HolomorphicAt n f (π z)) {K : ℕ}
    (hK : IsInSpanOnAt (n := n) (geoStrictTransform π C N)
      ((idealPow (exceptionalDivisor hπ).ideal K).mem z) z (f ∘ π)) :
    IsInSpanOnAt (n := n) N ((idealPow (vanishingIdeal (n := n) C) K).mem (π z)) (π z) f := by
  obtain ⟨r, r', hr, -, hrfix, hr', hr'z, hr'N, hcomm⟩ :=
    exists_chartRetraction hπ hN hCN hzC hzN
  have hrz : r (π z) = π z := hrfix.self_of_nhds (hCN hzC)
  have hrC : ∀ᶠ y in 𝓝 (π z), y ∈ C → r y = y := by
    filter_upwards [hrfix] with y hy hyC
    exact hy (hCN hyC)
  have hr't : Tendsto r' (𝓝 z) (𝓝 z) := by
    have h := hr'.self_of_nhds.continuousAt
    rwa [ContinuousAt, hr'z] at h
  obtain ⟨M₀, s, a, hs, ha, hsum⟩ := hK
  -- `f♭ = f ∘ r`
  have hfr : HolomorphicAt n (f ∘ r) (π z) :=
    HadamardBridge.holomorphicAt_comp_map hr (by rw [hrz]; exact hf)
  have hfrπ : HolomorphicAt n ((f ∘ r) ∘ π) z := by
    have hπd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
      Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
    exact HadamardBridge.holomorphicAt_comp_map hπd hfr
  -- `f♭ ∘ π = (f ∘ π) ∘ r'` is a combination of the germs `sᵢ ∘ r'` of `𝒪(-D)^K`
  have hmem : (idealPow (exceptionalDivisor hπ).ideal K).mem z ((f ∘ r) ∘ π) := by
    refine GermIdealOrder.mem_idealPow_of_isInSpanAt ⟨hfrπ, M₀, fun i => s i ∘ r',
      fun i => a i ∘ r', fun i => ?_, fun i => HadamardBridge.holomorphicAt_comp_map hr'
        (by rw [hr'z]; exact ha i), ?_⟩
    · exact comp_mem_idealPow hr'z hr'
        (comp_mem_exceptionalDivisor hπ hr hrC hzC hr' hr'z hcomm) K (hs i)
    · filter_upwards [hcomm, hr'N, hr't.eventually hsum] with w hw1 hw2 hw3
      show f (r (π w)) = ∑ i, a i (r' w) * s i (r' w)
      rw [← hw1]
      exact hw3 hw2
  have hmemC := ExceptionalIdealPushforward.mem_idealPow_vanishingIdeal_of_pullback_mem hπ hzC hfr
    hmem
  refine ⟨1, fun _ => f ∘ r, fun _ => fun _ => 1, fun _ => hmemC,
    fun _ => holomorphicAt_const 1, ?_⟩
  filter_upwards [hrfix] with y hy hyN
  simp [hy hyN]

end Pushforward

/-! ### The transform of a marked ideal at the points of `D ∩ N'` -/

section MarkedIdeal

open MarkedIdeals MarkedIdeals.MarkedIdeal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- A product `p q` with `p ∈ 𝔩^d` and `q|_W` in the span of `𝔩|_W` has `(p q)|_W` in the span of
`𝔩^{d+1}|_W`. -/
theorem isInSpanOnAt_mul_idealPow_succ {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔩 : GermIdeal n M} {W : Set M}
    {z : M} {d : ℕ}
    {p q : M → ℂ} (hp : (idealPow 𝔩 d).mem z p) (hq : IsInSpanOnAt (n := n) W (𝔩.mem z) z q)
    (h𝔩 : ∀ t, 𝔩.mem z t → HolomorphicAt n t z) :
    IsInSpanOnAt (n := n) W ((idealPow 𝔩 (d + 1)).mem z) z (p * q) := by
  obtain ⟨K, t, b, ht, hb, hsum⟩ := hq
  have hphol : HolomorphicAt n p z := holomorphicAt_of_mem_idealPow hp
  refine ⟨K, fun k w => p w * t k w, b, fun k => OrderTaylor.mul_mem_idealPow_succ hp (ht k)
    (hphol.mul (h𝔩 _ (ht k))), hb, ?_⟩
  filter_upwards [hsum] with w hw hwW
  show p w * q w = ∑ k, b k w * (p w * t k w)
  rw [hw hwW, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **`π^*𝔞 = 𝒪(-dD) · 𝔞'` restricted to `N'`** (the along-`N'` form of the bridge consumer
`π^*𝔞 = 𝒪(-dD) σ^c(𝔞, d)`): for a marked ideal `(M, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞`
coherent and `C ⊆ cosupp`, every germ of `π^*𝔞` agrees on `N'` with a combination of germs of
`𝒪(-dD) · 𝔞'`, `𝔞'` the transformed ideal.  (This is the first half of
`MarkedIdealOperationsAlong.MarkedIdeal.restrictLe_pullback_geoTransform`, which assumes an
admissible centre; here only `C ⊆ cosupp` is used.) -/
theorem restrictLe_pullback_geoTransform (hπ : IsBlowupAlong n C π) {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hsub : C ⊆ 𝔪.cosupp) :
    RestrictedIdealWeight.RestrictLe (geoStrictTransform π C 𝔪.N)
      (GermIdeal.pullback (m := n) π 𝔪.ideal)
      ((idealPow (exceptionalDivisor hπ).ideal 𝔪.d).mul (𝔪.geoTransform C π).ideal) := by
  have hCN : C ⊆ 𝔪.N := hsub.trans 𝔪.cosupp_subset_N
  have hπc : Continuous π := hπ.contMDiff.continuous
  have h1 : RestrictedIdealWeight.RestrictLe 𝔪.N 𝔪.ideal
      (idealPow (vanishingIdeal (n := n) C) 𝔪.d) :=
    restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hπ.1 hCN hsub
  have h2 := restrictLe_pullback (M' := Y) hπ.contMDiff
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) h1
  rw [pullback_idealPow_vanishingIdeal hπ] at h2
  have h3 : RestrictedIdealWeight.RestrictLe (geoStrictTransform π C 𝔪.N)
      (GermIdeal.pullback (m := n) π 𝔪.ideal) (idealPow (exceptionalDivisor hπ).ideal 𝔪.d) := by
    intro w hw g hg
    obtain ⟨K, t, b, ht, hb, hsum⟩ :=
      h2 w (geoStrictTransform_subset_preimage hπc hN.1 hw) g hg
    refine ⟨K, t, b, ht, hb, ?_⟩
    filter_upwards [hsum] with w' hw' hw'N
    exact hw' (geoStrictTransform_subset_preimage hπc hN.1 hw'N)
  exact RestrictedIdealQuotient.restrictLe_mul_colon
    (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff h𝔞)
    (isInvertibleAlong_geoStrictTransform hπ 𝔪.N 𝔪.d) h3

/-- **Clause 1 of `bcalc:controlled-not-exceptional` along `N'`**: for a marked ideal
`(M, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent and `C ⊆ cosupp`, if at a point
`z ∈ N'` over `C` every germ of the transformed ideal `𝔞' = 𝓘_D^{-d} π^*𝔞|_{N'}` agrees on `N'`
with a combination of germs of `𝒪(-D)`, then `ord_{π z}(𝔞|_N) ≥ d + 1`. -/
theorem mem_cosupport_succ_of_geoTransform_le (hπ : IsBlowupAlong n C π) {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hsub : C ⊆ 𝔪.cosupp) {z : Y}
    (hzC : π z ∈ C) (hzN : z ∈ geoStrictTransform π C 𝔪.N)
    (hle : ∀ g, (𝔪.geoTransform C π).ideal.mem z g →
      IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
        ((exceptionalDivisor hπ).ideal.mem z) z g) :
    π z ∈ cosupport n 𝔪.N 𝔪.ideal (𝔪.d + 1) := by
  have hCN : C ⊆ 𝔪.N := hsub.trans 𝔪.cosupp_subset_N
  have h4 := restrictLe_pullback_geoTransform hπ hN h𝔞 hsub
  have hlhol : ∀ t, (exceptionalDivisor hπ).ideal.mem z t → HolomorphicAt n t z :=
    fun t ht => (GermIdeal.mem_pullback_iff.mp ht).1
  refine ⟨hCN hzC, fun a ha => ?_⟩
  have hahol : HolomorphicAt n a (π z) :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha
  have hπd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπ : HolomorphicAt n (a ∘ π) z := HadamardBridge.holomorphicAt_comp_map hπd hahol
  have hpa : (GermIdeal.pullback (m := n) π 𝔪.ideal).mem z (a ∘ π) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨a, ha, rfl⟩ haπ
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
  -- `(a ∘ π)|_{N'}` is in the span of `𝒪(-(d+1)D)|_{N'}`
  have h6 : IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
      ((idealPow (exceptionalDivisor hπ).ideal (𝔪.d + 1)).mem z) z (a ∘ π) := by
    refine IsInSpanOnAt.trans (fun s hs => ?_) (h4 z hzN (a ∘ π) hpa)
    refine IsInSpanOnAt.trans (fun s' hs' => ?_) (IsInSpanAt.restrict
      (InvertibleIdealQuotient.mem_mul_iff.mp hs))
    obtain ⟨p, q, hp, hq, rfl⟩ := hs'
    exact isInSpanOnAt_mul_idealPow_succ hp (hle q hq) hlhol
  -- push forward along `N'`
  obtain ⟨K, t, c, ht, hc, hsum⟩ :=
    mem_idealPow_vanishingIdeal_along_of_pullback hπ hN hCN hzC hzN hahol h6
  have hCx : ∀ g, (vanishingIdeal (n := n) C).mem (π z) g → (pointIdeal n (π z)).mem (π z) g :=
    fun g hg => ⟨hg.1, Eventually.of_forall fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact hg.2.self_of_nhds hzC⟩
  refine ⟨fun y => ∑ k, c k y * t k y, ?_, hsum⟩
  refine OrderTaylor.mem_idealPow_sum Finset.univ fun k _ => ?_
  exact mul_mem_idealPow (hc k)
    (ExceptionalIdealPushforward.mem_idealPow_of_mem_at hCx (𝔪.d + 1) (ht k))

/-- **Clause 1 along `N'`, contrapositive**: where `ord_{π z}(𝔞|_N) = d`, some germ of the
transformed ideal at `z ∈ D ∩ N'` is, restricted to `N'`, outside `𝒪(-D)|_{N'}`. -/
theorem exists_not_isInSpanOnAt_exceptionalDivisor (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hsub : C ⊆ 𝔪.cosupp) {z : Y} (hzC : π z ∈ C) (hzN : z ∈ geoStrictTransform π C 𝔪.N)
    (hord : π z ∉ cosupport n 𝔪.N 𝔪.ideal (𝔪.d + 1)) :
    ∃ g, (𝔪.geoTransform C π).ideal.mem z g ∧
      ¬ IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
        ((exceptionalDivisor hπ).ideal.mem z) z g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hord (mem_cosupport_succ_of_geoTransform_le hπ hN h𝔞 hsub hzC hzN h)

/-- **Clause 2 of `bcalc:controlled-not-exceptional` along `N'`**: for a marked ideal
`(M, N, E, 𝔞, d)` as above and a closed set `A ⊆ N` (e.g. `A = H ∩ N` for a member `H`), if at a
point `z` of the strict transform `A'` every germ of the transformed ideal `𝔞'` vanishes on `A'`
near `z`, then arbitrarily close to `π z` there are points `y ∈ A \ C` at which every germ of `𝔞`
vanishes on `A` near `y`.  Proof: as for `N = M`, with `π^*𝔞 = 𝒪(-dD) 𝔞'` restricted to `N'`
(`restrictLe_pullback_geoTransform`) at the points of `π⁻¹(A \ C) ⊆ N'`. -/
theorem frequently_le_vanishingIdeal_of_geoTransform_le (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hsub : C ⊆ 𝔪.cosupp) {A : Set X} (hAN : A ⊆ 𝔪.N) {z : Y}
    (hzA : z ∈ geoStrictTransform π C A)
    (hle : ∀ g, (𝔪.geoTransform C π).ideal.mem z g →
      (vanishingIdeal (n := n) (geoStrictTransform π C A)).mem z g) :
    ∃ᶠ y in 𝓝 (π z), y ∈ A \ C ∧ ∀ a, 𝔪.ideal.mem y a → (vanishingIdeal (n := n) A).mem y a := by
  have hCN : C ⊆ 𝔪.N := hsub.trans 𝔪.cosupp_subset_N
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hσc : (𝔪.geoTransform C π).ideal.IsCoherent :=
    isCoherent_geoTransform_ideal h𝔞 hN hπ hCN
      (restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hπ.1 hCN hsub)
  have hev := ExceptionalIdealPushforward.eventually_le_vanishingIdeal_of_isCoherent hσc hle
  have hfreq : ∃ᶠ z' in 𝓝 z, z' ∈ π ⁻¹' (A \ C) := mem_closure_iff_frequently.mp hzA
  have h4 := restrictLe_pullback_geoTransform hπ hN h𝔞 hsub
  have hAN' : geoStrictTransform π C A ⊆ geoStrictTransform π C 𝔪.N :=
    closure_mono (preimage_mono (sdiff_subset_sdiff_left hAN))
  obtain ⟨sec, hsec, hπsec, hsecπ⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  refine (hπc.tendsto z).frequently ((hfreq.and_eventually hev).mono fun z' ⟨hz'AC, hz'le⟩ => ?_)
  refine ⟨hz'AC, fun a ha => ?_⟩
  have hahol : HolomorphicAt n a (π z') :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha
  have hπd : ∀ᶠ w in 𝓝 z', MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπ : HolomorphicAt n (a ∘ π) z' := HadamardBridge.holomorphicAt_comp_map hπd hahol
  have h1 : (GermIdeal.pullback (m := n) π 𝔪.ideal).mem z' (a ∘ π) :=
    BlowupDerivativeIdeal.comp_mem_pullback ha haπ (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  have hz'N : z' ∈ geoStrictTransform π C 𝔪.N :=
    subset_closure ⟨hAN hz'AC.1, hz'AC.2⟩
  -- `a ∘ π` vanishes on `A'` near `z'`
  have hvanish : ∀ᶠ w in 𝓝 z', w ∈ geoStrictTransform π C A → (a ∘ π) w = 0 := by
    obtain ⟨K, u, c, hu, -, hsum⟩ := h4 z' hz'N (a ∘ π) h1
    have huv : ∀ k, ∀ᶠ w in 𝓝 z', w ∈ geoStrictTransform π C A → u k w = 0 := by
      intro k
      obtain ⟨-, L, v, e, hv, -, hvsum⟩ := InvertibleIdealQuotient.mem_mul_iff.mp (hu k)
      choose p q hp hq hpq using hv
      have hqv : ∀ l, ∀ᶠ w in 𝓝 z', w ∈ geoStrictTransform π C A → q l w = 0 :=
        fun l => (hz'le _ (hq l)).2
      filter_upwards [hvsum, eventually_all.mpr hqv] with w hw hwq hwA
      rw [hw]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hpq l]
      simp [hwq l hwA]
    filter_upwards [hsum, eventually_all.mpr huv] with w hw hwu hwA
    rw [hw (hAN' hwA)]
    exact Finset.sum_eq_zero fun k _ => by simp [hwu k hwA]
  -- carry the vanishing down along the section of `π` over `X \ C`
  have hz'C : π z' ∈ Cᶜ := hz'AC.2
  have hcont : Tendsto sec (𝓝 ⟨π z', hz'C⟩) (𝓝 z') := by
    have h := hsec.continuous.continuousAt (x := ⟨π z', hz'C⟩)
    rwa [ContinuousAt, hsecπ z' hz'C] at h
  have h2 := hcont.eventually hvanish
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h2
  refine ⟨hahol, ?_⟩
  filter_upwards [h2, hπ.1.1.isOpen_compl.mem_nhds hz'C] with y hy hyC hyA
  have hsy : π (sec ⟨y, hyC⟩) = y := congrFun hπsec ⟨y, hyC⟩
  have hmem : sec ⟨y, hyC⟩ ∈ geoStrictTransform π C A :=
    subset_closure (show π (sec ⟨y, hyC⟩) ∈ A \ C by rw [hsy]; exact ⟨hyA, hyC⟩)
  have := hy ⟨y, hyC⟩ rfl hmem
  simpa [Function.comp_apply, hsy] using this

/-- **Clause 2 along `N'`, contrapositive**: if near `π z` the ideal `𝔞` vanishes on `A` near no
point of `A \ C`, then at a point `z` of `A'` some germ of the transformed ideal `𝔞'` does not
vanish on `A'` near `z`. -/
theorem exists_not_mem_vanishingIdeal_of_geoTransform (hπ : IsBlowupAlong n C π)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hsub : C ⊆ 𝔪.cosupp) {A : Set X} (hAN : A ⊆ 𝔪.N) {z : Y}
    (hzA : z ∈ geoStrictTransform π C A)
    (hnot : ∀ᶠ y in 𝓝 (π z), y ∈ A \ C →
      ∃ a, 𝔪.ideal.mem y a ∧ ¬ (vanishingIdeal (n := n) A).mem y a) :
    ∃ g, (𝔪.geoTransform C π).ideal.mem z g ∧
      ¬ (vanishingIdeal (n := n) (geoStrictTransform π C A)).mem z g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨y, hy, hyle⟩ :=
    ((frequently_le_vanishingIdeal_of_geoTransform_le hπ hN h𝔞 hsub hAN hzA h).and_eventually
      hnot).exists
  obtain ⟨a, ha, hna⟩ := hyle hy.1
  exact hna (hy.2 a ha)

end MarkedIdeal

end

end Hironaka.ExceptionalPushforwardAlong

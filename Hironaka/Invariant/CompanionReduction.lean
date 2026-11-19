import Hironaka.Analytic.GermOrderProduct
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Blowup.BlowupDerivativeIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reduction to maximal order: the companion ideal along multiple test blow-ups

Blueprint `hir:companion-reduction` (`blueprint/src/hironaka.tex`, Hironaka phase H4, Step 2a of the resolution
algorithm).  Sources: Włodarczyk 2005, Proposition `pr:resol`, Step 2a; Bierstone--Milman 2008 §5, Step II.B and
Remark 5.2.

Let `𝔞 = 𝔟 𝔠` on `M` (`N = M`), with a common `E`, coherent `𝔟, 𝔠`, a mark `d ≥ 1` and `o ≥ 1` such that
`ord_x 𝔟 ≤ o` at every point of `cosupp(𝔞, d)`.  The **companion ideal** is `(𝔟, o) + (𝔠, d - o)` if `o < d` and
`(𝔟, o)` if `o ≥ d`.  The abstract factorization stands for the monomial / nonmonomial decomposition
`𝔞 = 𝓜(𝔞) 𝓝(𝔞)` (`𝔟 = 𝓝`, `𝔠 = 𝓜`), which is not needed here.

## Main results

* one blowup along an admissible centre (`N = M`, coherent ideal):
  `mem_cosupp_of_mem_cosupp_geoTransform` (the cosupport of the transform lies over the cosupport) and
  `notMem_cosupport_succ_geoTransform` (`ord_{π z} 𝔟 ≤ o` gives `ord_z 𝔟' ≤ o` for the transform `𝔟' = σ^c(𝔟, o)`),
  both from TN23's `le:inclusions` (`BlowupDerivativeIdeal.controlledTransform_iterDerivIdeal_le`);
* `cosupp_add_eq_inter_cosupp_mul`: under the order bound, `cosupp((𝔟, o) + (𝔠, d')) = cosupp(𝔟, o) ∩ cosupp(𝔟𝔠, o + d')`
  (`GermOrderProduct.mem_cosupport_of_mem_cosupport_mul`);
* `reduction_add` (case `o < d`): every multiple test blow-up `T` of `(𝔟, o) + (𝔠, d')` is one of `(𝔟, o)`, of `(𝔠, d')` and of
  the product `(𝔟𝔠, o + d')`, the order bound persists along `T`, and `cosupp` of the companion's transform is
  `cosupp(𝔟_T, o) ∩ cosupp((𝔟𝔠)_T, o + d')`;
* `reduction_le` (case `o ≥ d`): every multiple test blow-up of `(𝔟, o)` is one of `(𝔞, d)` for every `𝔞 ⊆ 𝔟`, the inclusion of
  the transforms persists, and `cosupp(𝔟_T, o) ⊆ cosupp(𝔞_T, d)`;
* `companion`, `companion_reduction`, `companion_resolution`: the packaged statement of `hir:companion-reduction` -- along every
  multiple test blow-up `T` of the companion ideal, `T` is one of `(𝔟𝔠, d)` and of `(𝔟, o)`, the bound `ord 𝔟_T ≤ o` persists
  on `cosupp((𝔟𝔠)_T, d)`, the companion's cosupport is `cosupp(𝔟_T, o) ∩ cosupp((𝔟𝔠)_T, d)`; after a resolution of the companion,
  `ord 𝔟_T < o` on `cosupp((𝔟𝔠)_T, d)`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CompanionReduction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.DerivativeIdeal Hironaka.OrderTaylor
  Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor
  Hironaka.InvertibleIdealQuotient Hironaka.BlowupTowers
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealOperationsTransform
  Hironaka.MarkedIdealOperationsTransform.MarkedIdeal
  Hironaka.GermOrderProduct

noncomputable section

/-! ### Ideal-level facts for one blowup -/

section OneBlowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- A germ of a coherent ideal times a holomorphic germ is a germ of the ideal. -/
theorem mul_mem_of_isCoherent {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] {J : GermIdeal n Z} (hJ : J.IsCoherent) {y : Z} {c g : Z → ℂ}
    (hc : HolomorphicAt n c y) (hg : J.mem y g) : J.mem y (fun p => c p * g p) :=
  GermIdealTotalTransform.mem_of_isInSpanAt_mem hJ
    (RelativePrincipalizationSpan.IsInSpanAt.mul_left hc
      (isInSpanAt_self hg (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg)))

/-- `π^*𝔟 ⊆ σ^c(𝔟, μ)` for a coherent `𝔟`: a pulled-back germ divides by nothing. -/
theorem pullback_le_controlledTransform (hπ : IsBlowupAlong n C π) {𝔟 : GermIdeal n X}
    (h𝔟 : 𝔟.IsCoherent) (μ : ℕ) :
    (GermIdeal.pullback (m := n) π 𝔟).Le (controlledTransform hπ 𝔟 μ) := by
  have hcoh := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff h𝔟
  intro y f hf
  refine ⟨RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hf, fun g hg => ?_⟩
  exact mul_mem_of_isCoherent hcoh (holomorphicAt_of_mem_idealPow hg) hf

/-- `g ∘ π` is a germ of `π^*𝔟` at `z` for a germ `g` of the coherent `𝔟` at `π z`. -/
theorem comp_mem_pullback' (hπ : IsBlowupAlong n C π) {𝔟 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) {z : Y}
    {g : X → ℂ} (hg : 𝔟.mem (π z) g) : (GermIdeal.pullback (m := n) π 𝔟).mem z (g ∘ π) := by
  have hgh : HolomorphicAt n g (π z) := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  have hcomp : HolomorphicAt n (g ∘ π) z :=
    hgh.comp_contMDiff (Eventually.of_forall fun q => hπ.contMDiff q)
  exact BlowupDerivativeIdeal.comp_mem_pullback (c := fun _ => 1) hg hcomp (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp)

/-- Outside the zero locus of a coherent ideal: a germ nonvanishing at the point. -/
theorem exists_mem_ne_zero_of_notMem_zeroLocus {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] {J : GermIdeal n Z} {y : Z}
    (hy : y ∉ J.zeroLocus) : ∃ g, J.mem y g ∧ g y ≠ 0 := by
  by_contra! h
  exact hy h

/-- **The cosupport of the controlled transform lies over the cosupport** (`N = M`): if `𝔞 ⊆ 𝓘_C^d`, `d ≥ 1`, and
`π z ∉ cosupp(𝔞, d)`, then `z ∉ cosupp(σ^c(𝔞, d), d)` (Włodarczyk `le:inclusions` with `r = d - 1`). -/
theorem notMem_cosupport_controlledTransform (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) {d : ℕ} (hd : 1 ≤ d) (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) d)) {z : Y}
    (hz : π z ∉ cosupport n univ 𝔞 d) : z ∉ cosupport n univ (controlledTransform hπ 𝔞 d) d := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hct := isCoherent_controlledTransform hπ h𝔞 hle
  have hcthol : ∀ x g, (controlledTransform hπ 𝔞 d).mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hct hg
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol] at hz
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hcthol]
  obtain ⟨g, hg, hgne⟩ := exists_mem_ne_zero_of_notMem_zeroLocus hz
  have hDcoh := isCoherent_iterDerivIdeal h𝔞 j
  have h1 : (controlledTransform hπ (iterDerivIdeal 𝔞 j) 1).mem z (g ∘ π) :=
    pullback_le_controlledTransform hπ hDcoh 1 z _ (comp_mem_pullback' hπ hDcoh hg)
  have hle' : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) (1 + j)) := by
    rw [Nat.add_comm]; exact hle
  have h2 := BlowupDerivativeIdeal.controlledTransform_iterDerivIdeal_le hπ h𝔞 j 1 hle' z _ h1
  rw [show 1 + j = j + 1 by omega] at h2
  exact fun hz' => hgne (hz' _ h2)

/-- **The order bound passes to the transform** (`N = M`): if `𝔟 ⊆ 𝓘_C^o` and `ord_{π z} 𝔟 ≤ o` (i.e.
`π z ∉ cosupp(𝔟, o + 1)`), then `ord_z σ^c(𝔟, o) ≤ o` (Villamayor; Włodarczyk `le:inclusions` with `r = o`). -/
theorem notMem_cosupport_succ_controlledTransform (hπ : IsBlowupAlong n C π) {𝔟 : GermIdeal n X}
    (h𝔟 : 𝔟.IsCoherent) {o : ℕ} (hle : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) o)) {z : Y}
    (hz : π z ∉ cosupport n univ 𝔟 (o + 1)) :
    z ∉ cosupport n univ (controlledTransform hπ 𝔟 o) (o + 1) := by
  have hhol : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  have hct := isCoherent_controlledTransform hπ h𝔟 hle
  have hcthol : ∀ x g, (controlledTransform hπ 𝔟 o).mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hct hg
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol] at hz
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hcthol]
  obtain ⟨g, hg, hgne⟩ := exists_mem_ne_zero_of_notMem_zeroLocus hz
  have hDcoh := isCoherent_iterDerivIdeal h𝔟 o
  have h1 : (controlledTransform hπ (iterDerivIdeal 𝔟 o) 0).mem z (g ∘ π) :=
    pullback_le_controlledTransform hπ hDcoh 0 z _ (comp_mem_pullback' hπ hDcoh hg)
  have hle' : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) (0 + o)) := by
    rw [Nat.zero_add]; exact hle
  have h2 := BlowupDerivativeIdeal.controlledTransform_iterDerivIdeal_le hπ h𝔟 o 0 hle' z _ h1
  rw [Nat.zero_add] at h2
  exact fun hz' => hgne (hz' _ h2)

/-- **Monotonicity of controlled transforms**: `𝔞 ⊆ 𝔟` and `d ≤ o` give `σ^c(𝔞, d) ⊆ σ^c(𝔟, o)`. -/
theorem controlledTransform_le_controlledTransform (hπ : IsBlowupAlong n C π) {𝔞 𝔟 : GermIdeal n X}
    (h : 𝔞.Le 𝔟) {d o : ℕ} (hdo : d ≤ o) :
    (controlledTransform hπ 𝔞 d).Le (controlledTransform hπ 𝔟 o) := by
  intro z f hf
  refine ⟨hf.1, fun g hg => ?_⟩
  have hDhol : ∀ y ℓ, (exceptionalDivisor hπ).ideal.mem y ℓ → HolomorphicAt n ℓ y := fun _ _ hℓ =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (BlowupExceptionalDivisor.isCoherent_ideal _) hℓ
  have hg' := idealPow_le_of_le hDhol hdo z g hg
  exact GermIdealPullbackCalculus.pullback_le_pullback h z _ (hf.2 g hg')

end OneBlowup

/-! ### Marked ideals with `N = M`: one admissible blowup -/

section Marked

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The cosupport of the transform lies over the cosupport** (`N = M`, coherent ideal, mark `≥ 1`, admissible
centre). -/
theorem mem_cosupp_of_mem_cosupp_geoTransform {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : z ∈ (𝔪.geoTransform C π).cosupp) : π z ∈ 𝔪.cosupp := by
  have hle := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN h𝔞 hC
  by_contra hπz
  rw [MarkedIdeal.cosupp, hN] at hπz
  have hz' : z ∈ cosupport n univ (controlledTransform hπ 𝔪.ideal 𝔪.d) 𝔪.d := by
    have h := hz
    rw [MarkedIdeal.cosupp, geoTransform_N_eq_univ hN hπ, geoTransform_ideal_eq_controlledTransform hN h𝔞 hπ,
      geoTransform_d] at h
    exact h
  exact notMem_cosupport_controlledTransform hπ h𝔞 hd hle hπz hz'

/-- **The order bound passes to the transform of a marked ideal** (`N = M`, coherent ideal, admissible centre):
`ord_{π z} ≤ d` gives `ord_z ≤ d` for the transform. -/
theorem notMem_cosupport_succ_geoTransform {𝔫 : MarkedIdeal n X} (hN : 𝔫.N = univ)
    (h𝔟 : 𝔫.ideal.IsCoherent) (hC : 𝔫.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∉ cosupport n univ 𝔫.ideal (𝔫.d + 1)) :
    z ∉ cosupport n univ (𝔫.geoTransform C π).ideal (𝔫.d + 1) := by
  rw [geoTransform_ideal_eq_controlledTransform hN h𝔟 hπ]
  exact notMem_cosupport_succ_controlledTransform hπ h𝔟
    (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN h𝔟 hC) hz

/-- **The cosupport of the companion sum** (`N = M`): if `ord_x 𝔫 ≤ 𝔫.d` at every point of the cosupport of the product,
then `cosupp(𝔫 + 𝔪') = cosupp 𝔫 ∩ cosupp(𝔫 · 𝔪')`. -/
theorem cosupp_add_eq_inter_cosupp_mul {𝔫 𝔪' : MarkedIdeal n X} (h : IsAmbientPair 𝔫 𝔪')
    (ho : 1 ≤ 𝔫.d) (hm : 1 ≤ 𝔪'.d)
    (hbound : ∀ x ∈ (mul 𝔫 𝔪').cosupp, x ∉ cosupport n univ 𝔫.ideal (𝔫.d + 1)) :
    (add 𝔫 𝔪').cosupp = 𝔫.cosupp ∩ (mul 𝔫 𝔪').cosupp := by
  rw [cosupp_add h.N₁ h.N₂ h.coh₁ h.coh₂ ho hm]
  have hhol₁ : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.coh₁ hg
  have hhol₂ : ∀ x g, 𝔪'.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.coh₂ hg
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, inter_cosupp_subset_cosupp_mul (h.N₁.trans h.N₂.symm) ⟨h₁, h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    have hx : x ∈ cosupport n univ (𝔫.ideal.mul 𝔪'.ideal) (𝔫.d + 𝔪'.d) := by
      have h₂' := h₂
      simp only [MarkedIdeal.cosupp, mul, h.N₁] at h₂'
      exact h₂'
    have := mem_cosupport_of_mem_cosupport_mul hhol₁ hhol₂ (Nat.le_add_right 𝔫.d 𝔪'.d) hx
      (hbound x h₂)
    rw [Nat.add_sub_cancel_left] at this
    rw [MarkedIdeal.cosupp, h.N₂]
    exact this

end Marked

/-! ### Along multiple test blow-ups -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Reduction to maximal order, case `o < d`** (Włodarczyk Step 2a; BM08 Step II.B): let `𝔫 = (𝔟, o)` and
`𝔪' = (𝔠, d')` be an ambient pair with marks `≥ 1` such that `ord_x 𝔟 ≤ o` on `cosupp(𝔟𝔠, o + d')`.  Every multiple test
blow-up `T` of the companion `𝔫 + 𝔪'` is one of `𝔫`, of `𝔪'` and of `𝔫 · 𝔪'`; the bound persists along `T`; and
`cosupp (𝔫 + 𝔪')_T = cosupp 𝔫_T ∩ cosupp (𝔫 · 𝔪')_T`. -/
theorem reduction_add (𝔫 𝔪' : MarkedIdeal n X) (h : IsAmbientPair 𝔫 𝔪') (ho : 1 ≤ 𝔫.d) (hm : 1 ≤ 𝔪'.d)
    (hbound : ∀ x ∈ (mul 𝔫 𝔪').cosupp, x ∉ cosupport n univ 𝔫.ideal (𝔫.d + 1)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (add 𝔫 𝔪') T →
      IsGeoTestTower 𝔫 T ∧ IsGeoTestTower 𝔪' T ∧ IsGeoTestTower (mul 𝔫 𝔪') T ∧
      (∀ z ∈ (geoTransformAlong (mul 𝔫 𝔪') T).cosupp,
        z ∉ cosupport n univ (geoTransformAlong 𝔫 T).ideal (𝔫.d + 1)) ∧
      (geoTransformAlong (add 𝔫 𝔪') T).cosupp =
        (geoTransformAlong 𝔫 T).cosupp ∩ (geoTransformAlong (mul 𝔫 𝔪') T).cosupp
  | _, .refl, _ => ⟨trivial, trivial, trivial, hbound, cosupp_add_eq_inter_cosupp_mul h ho hm hbound⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hiff, hEq⟩ := geoTransformAlong_add 𝔫 𝔪' h ho hm (.step T C π hπ)
      obtain ⟨h𝔫T', h𝔪T'⟩ := hiff.mp hT
      obtain ⟨heqT', hpairT'⟩ := hEq h𝔫T' h𝔪T'
      obtain ⟨hmulT', hmulEqT', -⟩ := geoTransformAlong_mul 𝔫 𝔪' h (.step T C π hπ) h𝔫T' h𝔪T'
      obtain ⟨h𝔫T, hC𝔫⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp h𝔫T'
      obtain ⟨h𝔪T, hC𝔪⟩ := (isGeoTestTower_step_iff 𝔪' T C π hπ).mp h𝔪T'
      have hTadd : IsGeoTestTower (add 𝔫 𝔪') T :=
        ((geoTransformAlong_add 𝔫 𝔪' h ho hm T).1).mpr ⟨h𝔫T, h𝔪T⟩
      obtain ⟨-, -, -, hboundT, -⟩ := reduction_add 𝔫 𝔪' h ho hm hbound T hTadd
      obtain ⟨-, hmulEqT, hpairT⟩ := geoTransformAlong_mul 𝔫 𝔪' h T h𝔫T h𝔪T
      -- the bound at the new stage
      have hboundT' : ∀ z ∈ (geoTransformAlong (mul 𝔫 𝔪') (.step T C π hπ)).cosupp,
          z ∉ cosupport n univ (geoTransformAlong 𝔫 (.step T C π hπ)).ideal (𝔫.d + 1) := by
        intro z hz
        set P := mul (geoTransformAlong 𝔫 T) (geoTransformAlong 𝔪' T) with hP
        have hPN : P.N = univ := hpairT.N₁
        have hPcoh : P.ideal.IsCoherent := isCoherent_mul hpairT.coh₁ hpairT.coh₂
        have hPd : 1 ≤ P.d := by
          show 1 ≤ (geoTransformAlong 𝔫 T).d + (geoTransformAlong 𝔪' T).d
          rw [d_geoTransformAlong]; omega
        have hPC : P.IsAdmissibleCentre C :=
          IsAdmissibleCentre.mul (hpairT.N₁.trans hpairT.N₂.symm) hC𝔫 hC𝔪
        have hz' : z ∈ (P.geoTransform C π).cosupp := by
          rw [geoTransformAlong_step, hmulEqT] at hz
          exact hz
        have hπz : π z ∈ (geoTransformAlong (mul 𝔫 𝔪') T).cosupp := by
          rw [hmulEqT]
          exact mem_cosupp_of_mem_cosupp_geoTransform hPN hPcoh hPd hPC hπ hz'
        have hb := hboundT (π z) hπz
        rw [← d_geoTransformAlong 𝔫 T] at hb ⊢
        rw [geoTransformAlong_step]
        exact notMem_cosupport_succ_geoTransform hpairT.N₁ hpairT.coh₁ hC𝔫 hπ hb
      refine ⟨h𝔫T', h𝔪T', hmulT', hboundT', ?_⟩
      rw [heqT', hmulEqT']
      have hd₁ : 1 ≤ (geoTransformAlong 𝔫 (.step T C π hπ)).d := by rw [d_geoTransformAlong]; exact ho
      have hd₂ : 1 ≤ (geoTransformAlong 𝔪' (.step T C π hπ)).d := by rw [d_geoTransformAlong]; exact hm
      refine cosupp_add_eq_inter_cosupp_mul hpairT' hd₁ hd₂ ?_
      rw [← hmulEqT']
      intro x hx
      have := hboundT' x hx
      rw [d_geoTransformAlong]
      exact this

/-- **Reduction to maximal order, case `o ≥ d`**: if `𝔞 ⊆ 𝔟` and `d ≤ o` (same `E`, `N = M`, coherent), every multiple
test blow-up of `(𝔟, o)` is one of `(𝔞, d)`, along it `𝔞_T ⊆ 𝔟_T`, and `cosupp(𝔟_T, o) ⊆ cosupp(𝔞_T, d)`. -/
theorem reduction_le (𝔫 𝔪 : MarkedIdeal n X) (hN𝔫 : 𝔫.N = univ) (hN𝔪 : 𝔪.N = univ) (hE : 𝔫.E = 𝔪.E)
    (h𝔫 : 𝔫.ideal.IsCoherent) (h𝔪 : 𝔪.ideal.IsCoherent) (hle : 𝔪.ideal.Le 𝔫.ideal) (hdo : 𝔪.d ≤ 𝔫.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔫 T →
      IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).N = univ ∧ (geoTransformAlong 𝔫 T).N = univ ∧
      (geoTransformAlong 𝔫 T).E = (geoTransformAlong 𝔪 T).E ∧
      (geoTransformAlong 𝔫 T).ideal.IsCoherent ∧ (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      (geoTransformAlong 𝔪 T).ideal.Le (geoTransformAlong 𝔫 T).ideal ∧
      (geoTransformAlong 𝔫 T).cosupp ⊆ (geoTransformAlong 𝔪 T).cosupp
  | _, .refl, _ => by
      refine ⟨trivial, hN𝔪, hN𝔫, hE, h𝔫, h𝔪, hle, ?_⟩
      show 𝔫.cosupp ⊆ 𝔪.cosupp
      intro x hx
      refine ⟨by rw [hN𝔪]; exact mem_univ x, fun g hg => ?_⟩
      have h1 := hx.2 g (hle x g hg)
      rw [hN𝔫] at h1
      rw [hN𝔪]
      exact h1.mono hdo
  | _, .step T C π hπ, hT => by
      obtain ⟨hT𝔫, hC⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp hT
      obtain ⟨hT𝔪, hN𝔪T, hN𝔫T, hET, hcoh𝔫T, hcoh𝔪T, hleT, hsubT⟩ :=
        reduction_le 𝔫 𝔪 hN𝔫 hN𝔪 hE h𝔫 h𝔪 hle hdo T hT𝔫
      set 𝔫T := geoTransformAlong 𝔫 T
      set 𝔪T := geoTransformAlong 𝔪 T
      have hC𝔪 : 𝔪T.IsAdmissibleCentre C := ⟨hC.1, hC.2.1.trans hsubT, by rw [← hET]; exact hC.2.2⟩
      have hle𝔫 := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN𝔫T hcoh𝔫T hC
      have hle𝔪 := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN𝔪T hcoh𝔪T hC𝔪
      have hd𝔪𝔫 : 𝔪T.d ≤ 𝔫T.d := by
        simp only [𝔫T, 𝔪T, d_geoTransformAlong]; exact hdo
      have hideal𝔫 : (𝔫T.geoTransform C π).ideal = controlledTransform hπ 𝔫T.ideal 𝔫T.d :=
        geoTransform_ideal_eq_controlledTransform hN𝔫T hcoh𝔫T hπ
      have hideal𝔪 : (𝔪T.geoTransform C π).ideal = controlledTransform hπ 𝔪T.ideal 𝔪T.d :=
        geoTransform_ideal_eq_controlledTransform hN𝔪T hcoh𝔪T hπ
      have hleT' : (𝔪T.geoTransform C π).ideal.Le (𝔫T.geoTransform C π).ideal := by
        rw [hideal𝔫, hideal𝔪]
        exact controlledTransform_le_controlledTransform hπ hleT hd𝔪𝔫
      have hN𝔫' := geoTransform_N_eq_univ hN𝔫T hπ (𝔪 := 𝔫T) (C := C)
      have hN𝔪' := geoTransform_N_eq_univ hN𝔪T hπ (𝔪 := 𝔪T) (C := C)
      refine ⟨(isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hT𝔪, hC𝔪⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [geoTransformAlong_step]; exact hN𝔪'
      · rw [geoTransformAlong_step]; exact hN𝔫'
      · rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E, hET]
      · rw [geoTransformAlong_step, hideal𝔫]; exact isCoherent_controlledTransform hπ hcoh𝔫T hle𝔫
      · rw [geoTransformAlong_step, hideal𝔪]; exact isCoherent_controlledTransform hπ hcoh𝔪T hle𝔪
      · rw [geoTransformAlong_step, geoTransformAlong_step]; exact hleT'
      · rw [geoTransformAlong_step, geoTransformAlong_step]
        intro x hx
        refine ⟨by rw [hN𝔪']; exact mem_univ x, fun g hg => ?_⟩
        have h1 := hx.2 g (hleT' x g hg)
        rw [hN𝔫'] at h1
        rw [hN𝔪']
        simp only [geoTransform_d] at h1 ⊢
        exact h1.mono hd𝔪𝔫

/-- **The bound persists along multiple test blow-ups of `(𝔞, d)`** (`N = M`, coherent): if `ord_x 𝔟 ≤ o` at every point of
`cosupp(𝔞, d)` and `T` is a multiple test blow-up of both `(𝔟, o)` and `(𝔞, d)`, then `ord_z 𝔟_T ≤ o` at every point of
`cosupp(𝔞_T, d)`. -/
theorem bound_along (𝔫 𝔪 : MarkedIdeal n X) (hN𝔫 : 𝔫.N = univ) (hN𝔪 : 𝔪.N = univ) (h𝔫 : 𝔫.ideal.IsCoherent)
    (h𝔪 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n univ 𝔫.ideal (𝔫.d + 1)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔫 T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔫 T).N = univ ∧ (geoTransformAlong 𝔪 T).N = univ ∧
      (geoTransformAlong 𝔫 T).ideal.IsCoherent ∧ (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, z ∉ cosupport n univ (geoTransformAlong 𝔫 T).ideal (𝔫.d + 1)
  | _, .refl, _, _ => ⟨hN𝔫, hN𝔪, h𝔫, h𝔪, hbound⟩
  | _, .step T C π hπ, hT𝔫', hT𝔪' => by
      obtain ⟨hT𝔫, hC𝔫⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp hT𝔫'
      obtain ⟨hT𝔪, hC𝔪⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT𝔪'
      obtain ⟨hN𝔫T, hN𝔪T, hcoh𝔫T, hcoh𝔪T, hbT⟩ := bound_along 𝔫 𝔪 hN𝔫 hN𝔪 h𝔫 h𝔪 hd hbound T hT𝔫 hT𝔪
      have hle𝔫 := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN𝔫T hcoh𝔫T hC𝔫
      have hle𝔪 := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN𝔪T hcoh𝔪T hC𝔪
      have hdT : 1 ≤ (geoTransformAlong 𝔪 T).d := by rw [d_geoTransformAlong]; exact hd
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [geoTransformAlong_step]; exact geoTransform_N_eq_univ hN𝔫T hπ
      · rw [geoTransformAlong_step]; exact geoTransform_N_eq_univ hN𝔪T hπ
      · rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hN𝔫T hcoh𝔫T hπ]
        exact isCoherent_controlledTransform hπ hcoh𝔫T hle𝔫
      · rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hN𝔪T hcoh𝔪T hπ]
        exact isCoherent_controlledTransform hπ hcoh𝔪T hle𝔪
      · intro z hz
        rw [geoTransformAlong_step] at hz
        have hπz := mem_cosupp_of_mem_cosupp_geoTransform hN𝔪T hcoh𝔪T hdT hC𝔪 hπ hz
        have hb := hbT (π z) hπz
        rw [← d_geoTransformAlong 𝔫 T] at hb ⊢
        rw [geoTransformAlong_step]
        exact notMem_cosupport_succ_geoTransform hN𝔫T hcoh𝔫T hC𝔫 hπ hb

/-! ### The companion ideal -/

/-- **The companion ideal** of the factorization `𝔞 = 𝔟 𝔠` (`N = M`; Włodarczyk Step 2a, BM08 Step II.B):
`(𝔟, o) + (𝔠, d - o)` if `o < d`, and `(𝔟, o)` if `o ≥ d`. -/
def companion (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) (o d : ℕ) : MarkedIdeal n X :=
  if o < d then add ⟨univ, E, 𝔟, o⟩ ⟨univ, E, 𝔠, d - o⟩ else ⟨univ, E, 𝔟, o⟩

/-- `(𝔟, o) · (𝔠, d - o) = (𝔟𝔠, d)` for `o ≤ d`. -/
theorem mul_eq_of_le (E : List (Set X)) (𝔟 𝔠 : GermIdeal n X) {o d : ℕ} (hod : o ≤ d) :
    mul (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨univ, E, 𝔠, d - o⟩ = ⟨univ, E, 𝔟.mul 𝔠, d⟩ :=
  ext_of rfl rfl rfl (by show o + (d - o) = d; omega)

/-- **Reduction to maximal order** (`hir:companion-reduction`; Włodarczyk Step 2a, BM08 Step II.B): let `𝔟, 𝔠` be coherent,
`d, o ≥ 1`, and `ord_x 𝔟 ≤ o` at every point of `cosupp(𝔟𝔠, d)` (`N = M`, common `E`).  Every multiple test blow-up `T` of the
companion ideal is one of `(𝔟𝔠, d)` and of `(𝔟, o)`; along it `ord 𝔟_T ≤ o` on `cosupp((𝔟𝔠)_T, d)`, and the cosupport of the
companion's transform is `cosupp(𝔟_T, o) ∩ cosupp((𝔟𝔠)_T, d)`. -/
theorem companion_reduction (E : List (Set X)) {𝔟 𝔠 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent)
    {o d : ℕ} (ho : 1 ≤ o) (hd : 1 ≤ d)
    (hbound : ∀ x ∈ cosupport n univ (𝔟.mul 𝔠) d, x ∉ cosupport n univ 𝔟 (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (companion E 𝔟 𝔠 o d) T) :
    IsGeoTestTower (⟨univ, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T ∧
      IsGeoTestTower (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T ∧
      (∀ z ∈ (geoTransformAlong (⟨univ, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T).cosupp,
        z ∉ cosupport n univ (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal (o + 1)) ∧
      (geoTransformAlong (companion E 𝔟 𝔠 o d) T).cosupp =
        (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).cosupp ∩
          (geoTransformAlong (⟨univ, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T).cosupp := by
  by_cases hod : o < d
  · have hc : companion E 𝔟 𝔠 o d = add ⟨univ, E, 𝔟, o⟩ ⟨univ, E, 𝔠, d - o⟩ := if_pos hod
    have hpair : IsAmbientPair (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨univ, E, 𝔠, d - o⟩ :=
      ⟨rfl, rfl, rfl, h𝔟, h𝔠⟩
    have hmul := mul_eq_of_le E 𝔟 𝔠 hod.le
    have hb : ∀ x ∈ (mul (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨univ, E, 𝔠, d - o⟩).cosupp,
        x ∉ cosupport n univ (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X).ideal
          ((⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X).d + 1) := by
      rw [hmul]; exact hbound
    rw [hc] at hT ⊢
    obtain ⟨h1, -, h3, h4, h5⟩ := reduction_add _ _ hpair ho (by show 1 ≤ d - o; omega) hb T hT
    rw [hmul] at h3 h4 h5
    exact ⟨h3, h1, h4, h5⟩
  · have hc : companion E 𝔟 𝔠 o d = ⟨univ, E, 𝔟, o⟩ := if_neg hod
    rw [hc] at hT ⊢
    have hle : (𝔟.mul 𝔠).Le 𝔟 := GermIdealPullbackCalculus.mul_le_left h𝔟
      (fun hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg)
    have hdo : d ≤ o := le_of_not_gt hod
    have hcoh : (𝔟.mul 𝔠).IsCoherent := isCoherent_mul h𝔟 h𝔠
    obtain ⟨hT𝔪, -, -, -, -, -, -, hsub⟩ :=
      reduction_le (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨univ, E, 𝔟.mul 𝔠, d⟩ rfl rfl rfl h𝔟 hcoh hle hdo T hT
    obtain ⟨-, -, -, -, hb⟩ :=
      bound_along (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) ⟨univ, E, 𝔟.mul 𝔠, d⟩ rfl rfl h𝔟 hcoh hd hbound T hT hT𝔪
    exact ⟨hT𝔪, hT, hb, (inter_eq_left.mpr hsub).symm⟩

/-- **After a resolution of the companion ideal the order of `𝔟` has dropped** (`hir:companion-reduction`, last clause):
`T` is a multiple test blow-up of `(𝔟𝔠, d)` and `ord_z 𝔟_T < o` at every point of `cosupp((𝔟𝔠)_T, d)`. -/
theorem companion_resolution (E : List (Set X)) {𝔟 𝔠 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent)
    {o d : ℕ} (ho : 1 ≤ o) (hd : 1 ≤ d)
    (hbound : ∀ x ∈ cosupport n univ (𝔟.mul 𝔠) d, x ∉ cosupport n univ 𝔟 (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoResolution (companion E 𝔟 𝔠 o d) T) :
    IsGeoTestTower (⟨univ, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T ∧
      ∀ z ∈ (geoTransformAlong (⟨univ, E, 𝔟.mul 𝔠, d⟩ : MarkedIdeal n X) T).cosupp,
        z ∉ (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).cosupp := by
  obtain ⟨h1, -, -, h4⟩ := companion_reduction E h𝔟 h𝔠 ho hd hbound T hT.1
  refine ⟨h1, fun z hz hz' => ?_⟩
  have h2 := hT.2
  rw [h4] at h2
  exact (eq_empty_iff_forall_notMem.mp h2) z ⟨hz', hz⟩

end Tower

/-! ### The companion ideal is of maximal order -/

section MaximalOrder

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A coherent ideal with a germ nonvanishing at `x` contains the unit germ at `x`. -/
theorem one_mem_of_apply_ne_zero {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ}
    (hg : 𝔞.mem x g) (hgx : g x ≠ 0) : 𝔞.mem x (fun _ => 1) := by
  have hgh : HolomorphicAt n g x := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞
    (HolomorphicIdealSheaves.isInSpanAt_of_eq_mul hg (holomorphicAt_const 1)
      (RelativePrincipalizationSpan.holomorphicAt_inv hgh hgx) ?_)
  filter_upwards [hgh.continuousAt.eventually (isOpen_ne.mem_nhds hgx)] with y hy
  exact (inv_mul_cancel₀ hy).symm

/-- **Maximal order from orders**: if `ord_x 𝔞 ≤ μ` at every point (`x ∉ cosupp(𝔞, μ + 1)`), then `(𝔞, μ)` is of maximal
order in TN23's sense (`𝓓^μ 𝔞 = 𝒪`). -/
theorem isMaximalOrder_of_forall_notMem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (h : ∀ x, x ∉ cosupport n univ 𝔞 (μ + 1)) : MaximalContact.IsMaximalOrder 𝔞 μ := by
  intro x
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hx := h x
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol] at hx
  obtain ⟨g, hg, hgx⟩ := exists_mem_ne_zero_of_notMem_zeroLocus hx
  exact one_mem_of_apply_ne_zero (isCoherent_iterDerivIdeal h𝔞 μ) hg hgx

/-- Powers of a holomorphic germ are holomorphic. -/
theorem holomorphicAt_pow_of {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x) :
    ∀ k : ℕ, HolomorphicAt n (fun p => g p ^ k) x
  | 0 => by simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | k + 1 => by
    have h := (holomorphicAt_pow_of hg k).mul hg
    simpa [pow_succ] using h

/-- `g ∉ 𝔪_x^{o+1}` gives `g^k ∉ 𝔪_x^{k o + 1}` (orders add, `GermOrderProduct.mul_notMem_idealPow`). -/
theorem pow_notMem_idealPow {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x) {o : ℕ}
    (hgo : ¬ (idealPow (pointIdeal n x) (o + 1)).mem x g) :
    ∀ k : ℕ, ¬ (idealPow (pointIdeal n x) (k * o + 1)).mem x (fun p => g p ^ k)
  | 0 => by
    intro h
    have h1 : (idealPow (pointIdeal n x) 1).mem x (fun _ => (1 : ℂ)) :=
      mem_idealPow_congr (by simpa using h) (Eventually.of_forall fun _ => rfl)
    have := apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl h1
    simp at this
  | k + 1 => by
    intro h
    have hk := holomorphicAt_pow_of hg k
    have hne := GermOrderProduct.mul_notMem_idealPow (f := fun p => g p ^ k) hk hg
      (pow_notMem_idealPow hg hgo k) hgo
    refine hne (mem_idealPow_congr (by rwa [show k * o + o + 1 = (k + 1) * o + 1 by ring]) ?_)
    exact Eventually.of_forall fun p => pow_succ (g p) k

/-- A germ outside `cosupp(𝔞, q)` (`N = M`) has a germ of `𝔞` outside `𝔪_x^q`. -/
theorem exists_notMem_idealPow_of_notMem_cosupport {𝔞 : GermIdeal n M} {x : M} {q : ℕ}
    (hx : x ∉ cosupport n univ 𝔞 q) : ∃ g, 𝔞.mem x g ∧ ¬ (idealPow (pointIdeal n x) q).mem x g := by
  by_contra! hall
  exact hx ⟨mem_univ x, fun g hg => vanishesToOrderOn_of_mem (hall g hg)⟩

/-- If all products of germs of `𝔟` and `𝔠` at `x` lie in `𝔪_x^q`, so does every germ of `𝔟𝔠`. -/
theorem mem_idealPow_of_mem_mul {𝔟 𝔠 : GermIdeal n M} {x : M} {q : ℕ}
    (hprod : ∀ a b, 𝔟.mem x a → 𝔠.mem x b → (idealPow (pointIdeal n x) q).mem x (a * b)) {h : M → ℂ}
    (hh : (𝔟.mul 𝔠).mem x h) : (idealPow (pointIdeal n x) q).mem x h :=
  mem_idealPow_of_isInSpanAt (IsInSpanAt.mono
    (fun _s ⟨a, b, ha, hb, hs⟩ => hs ▸ hprod a b ha hb) (IdealOrderArithmetic.mem_mul_iff.mp hh))

end MaximalOrder

section CompanionMaximalOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The companion ideal is of maximal order** (`hir:companion-basic` for an abstract factorization; Włodarczyk
Definition of the companion ideal, BM08 Step II.B): if `ord_x 𝔟 ≤ o` at every point of `cosupp(𝔟𝔠, d)`, then
`(𝔟, o) + (𝔠, d - o)` (`o < d`), resp. `(𝔟, o)` (`o ≥ d`), has order at most its mark at every point. -/
theorem companion_isMaximalOrder (E : List (Set X)) {𝔟 𝔠 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent)
    (h𝔠 : 𝔠.IsCoherent) {o d : ℕ}
    (hbound : ∀ x ∈ cosupport n univ (𝔟.mul 𝔠) d, x ∉ cosupport n univ 𝔟 (o + 1)) :
    MaximalContact.IsMaximalOrder (companion E 𝔟 𝔠 o d).ideal (companion E 𝔟 𝔠 o d).d := by
  have hhol𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  have hhol𝔠 : ∀ x g, 𝔠.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg
  have hpt : ∀ (x : X) y g, (pointIdeal n x).mem y g → HolomorphicAt n g y := fun _ _ _ hg =>
    holomorphicAt_of_mem_pointIdeal hg
  by_cases hod : o < d
  · have hc : companion E 𝔟 𝔠 o d = add ⟨univ, E, 𝔟, o⟩ ⟨univ, E, 𝔠, d - o⟩ := if_pos hod
    rw [hc]
    show MaximalContact.IsMaximalOrder (RestrictedIdealExtension.sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)) (o * (d - o))
    have hcoh : (RestrictedIdealExtension.sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)).IsCoherent :=
      RestrictedIdealExtension.isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow h𝔟 _)
        (GermIdealPullbackCalculus.isCoherent_idealPow h𝔠 _)
    refine isMaximalOrder_of_forall_notMem hcoh fun x hx => ?_
    suffices h : ∃ h, (RestrictedIdealExtension.sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o)).mem x h ∧
        ¬ (idealPow (pointIdeal n x) (o * (d - o) + 1)).mem x h by
      obtain ⟨h, hh, hno⟩ := h
      exact hno (mem_idealPow_of_vanishesToOrderOn_univ (hx.2 h hh))
    by_cases hxb : x ∈ cosupport n univ 𝔟 (o + 1)
    · have hxa : x ∉ cosupport n univ (𝔟.mul 𝔠) d := fun h => hbound x h hxb
      obtain ⟨h0, hh0, hno0⟩ := exists_notMem_idealPow_of_notMem_cosupport hxa
      obtain ⟨f, hf, hfno⟩ : ∃ f, 𝔠.mem x f ∧ ¬ (idealPow (pointIdeal n x) ((d - o - 1) + 1)).mem x f := by
        by_contra! hall
        apply hno0
        refine mem_idealPow_of_mem_mul (fun a b ha hb => ?_) hh0
        have h1 : (idealPow (pointIdeal n x) (o + 1)).mem x a :=
          mem_idealPow_of_vanishesToOrderOn_univ (hxb.2 a ha)
        have h3 := mul_mem_idealPow_add (hpt x) h1 (hall b hb)
        exact idealPow_le_of_le (hpt x) (show d ≤ (o + 1) + ((d - o - 1) + 1) by omega) x _ h3
      refine ⟨fun p => f p ^ o, ?_, fun hmem => ?_⟩
      · exact IdealOrderArithmetic.le_sumIdeal_right' (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) x _
          (OrderMultiplicativity.pow_mem_idealPow hf (hhol𝔠 x f hf) o)
      · refine pow_notMem_idealPow (hhol𝔠 x f hf) hfno o ?_
        refine idealPow_le_of_le (hpt x) ?_ x _ hmem
        exact Nat.add_le_add_right (Nat.mul_le_mul_left o (Nat.sub_le _ _)) 1
    · obtain ⟨g, hg, hgno⟩ := exists_notMem_idealPow_of_notMem_cosupport hxb
      refine ⟨fun p => g p ^ (d - o), ?_, ?_⟩
      · exact IdealOrderArithmetic.le_sumIdeal_left' (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) x _
          (OrderMultiplicativity.pow_mem_idealPow hg (hhol𝔟 x g hg) (d - o))
      · have := pow_notMem_idealPow (hhol𝔟 x g hg) hgno (d - o)
        rwa [show (d - o) * o + 1 = o * (d - o) + 1 by ring] at this
  · have hc : companion E 𝔟 𝔠 o d = ⟨univ, E, 𝔟, o⟩ := if_neg hod
    rw [hc]
    show MaximalContact.IsMaximalOrder 𝔟 o
    refine isMaximalOrder_of_forall_notMem h𝔟 fun x hxb => ?_
    by_cases hxa : x ∈ cosupport n univ (𝔟.mul 𝔠) d
    · exact hbound x hxa hxb
    · obtain ⟨h0, hh0, hno0⟩ := exists_notMem_idealPow_of_notMem_cosupport hxa
      apply hno0
      refine mem_idealPow_of_mem_mul (fun a b ha hb => ?_) hh0
      have h1 : (idealPow (pointIdeal n x) (o + 1)).mem x a :=
        mem_idealPow_of_vanishesToOrderOn_univ (hxb.2 a ha)
      have h1' := idealPow_le_of_le (hpt x) (show d ≤ o + 1 by omega) x a h1
      exact mem_idealPow_congr (mul_mem_idealPow (hhol𝔠 x b hb) h1')
        (Eventually.of_forall fun z => mul_comm _ _)

end CompanionMaximalOrder

end

end Hironaka.CompanionReduction

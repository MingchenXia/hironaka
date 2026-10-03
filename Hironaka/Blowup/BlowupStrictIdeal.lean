/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Coherence.FiniteGeneratorIdealDescent
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealProducts
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Blowup.NestedFlattening
import Hironaka.Blowup.RegularPatchPullback
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ideal of the strict transform of a submanifold through the centre

Sources: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), §2 (the transform of a marked ideal `(M, N, E,
𝓘, d)` under a blowup of `M` with centre `C ⊆ N`); Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.2 (controlled
transforms; the lemma `𝓘 ⊆ 𝓘_C^μ`) and Lemma `le:Gi` (the controlled transform of a hypersurface of maximal contact
is its strict transform).

Let `π : Y → X` be the blowup along `C` with exceptional divisor `D`, and `N ⊇ C` a closed
submanifold.  With `N' = closure (π⁻¹ (N \ C))` (`BlowupStrictSubmanifold.geoStrictTransform`):

* `pullback_vanishingIdeal_eq_mul` -- **`π^*𝓘_N = 𝒪_Y(-D) · 𝓘_{N'}`**;
* `isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold` -- `N'` is a closed
  submanifold (no constant dimension needed);

Proof of the ideal identity, stalk by stalk at `z ∈ Y`.
* `π z ∉ C`: `π` has a holomorphic section over `X \ C` (`BlowupIsomorphismOff`), so
  `π^*𝓘_N = 𝓘_{π⁻¹N}` at `z`, `N' = π⁻¹N` near `z`, and `𝒪_Y(-D)` contains `1` at `z`.
* `π z ∈ C`: nested flattening coordinates `Φ` for `C ⊆ N` at `π z` (`C = ℂ^{k_C} × 0`,
  `N = ℂ^{k_N} × 0`) and a monomial chart `j ≥ k_C` with local inverse `W` near `z`
  (`σ_j ∘ W = Φ ∘ e ∘ π`).  By Hadamard in the coordinates `Φ`, `π^*𝓘_A` is generated near `z` by
  the `σ_j(W)_i`, `i ≥ k_A` (`A = C, N`); so `𝒪_Y(-D) = (W_j)`, and `π^*𝓘_N = (W_j W_i, i ≥ k_N)`
  if `j < k_N`, `= (W_j)` if `j ≥ k_N`.  On the other side `N' = W⁻¹(ℂ^{k_N} × 0)` near `z` if
  `j < k_N` (then Hadamard in the coordinates `W`, a local biholomorphism, gives
  `𝓘_{N'} = (W_i, i ≥ k_N)`), and `N'` misses a neighbourhood of `z` if `j ≥ k_N`
  (`𝓘_{N'} = 𝒪`).  The product of the presentations is the presentation of `π^*𝓘_N`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupStrictIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection NestedFlattening BlowupStrictSubmanifold BlowupExceptionalDivisor BlowupControlledTransform IdealWeightPowers IdealWeightProducts IdealWeightComparison InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealPullbackCalculus VanishingIdealCoherent Hironaka.RegularPatchPullback

noncomputable section

variable {n : ℕ}

/-! ### Spans, vanishing ideals and pullbacks -/

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The zero germ lies in every span. -/
theorem isInSpanAt_zero {S : (M → ℂ) → Prop} {x : M} :
    IsInSpanAt (n := n) S x (fun _ => 0) :=
  ⟨holomorphicAt_const 0, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
    Eventually.of_forall fun _ => by simp⟩

/-- `𝓘_A` absorbs holomorphic combinations of its members. -/
theorem mem_vanishingIdeal_of_isInSpanAt' {A : Set M} {S : (M → ℂ) → Prop} {y : M}
    (hS : ∀ s, S s → (vanishingIdeal (n := n) A).mem y s) {f : M → ℂ}
    (hf : IsInSpanAt (n := n) S y f) : (vanishingIdeal (n := n) A).mem y f := by
  obtain ⟨hfhol, K, s, a, hs, -, hsum⟩ := hf
  refine ⟨hfhol, ?_⟩
  have hzero : ∀ᶠ y' in 𝓝 y, ∀ i, y' ∈ A → s i y' = 0 :=
    eventually_all.mpr fun i => (hS _ (hs i)).2
  filter_upwards [hsum, hzero] with y' h1 h2 hy'A
  rw [h1]
  exact Finset.sum_eq_zero fun i _ => by rw [h2 i hy'A, mul_zero]

/-- The vanishing ideal at `y` only depends on the germ of the set at `y`. -/
theorem vanishingIdeal_mem_congr {A B : Set M} {y : M} (hAB : ∀ᶠ y' in 𝓝 y, (y' ∈ A ↔ y' ∈ B))
    (g : M → ℂ) : (vanishingIdeal (n := n) A).mem y g ↔ (vanishingIdeal (n := n) B).mem y g := by
  constructor
  · rintro ⟨hg, hgA⟩
    refine ⟨hg, ?_⟩
    filter_upwards [hgA, hAB] with y' h1 h2 hB
    exact h1 (h2.mpr hB)
  · rintro ⟨hg, hgB⟩
    refine ⟨hg, ?_⟩
    filter_upwards [hgB, hAB] with y' h1 h2 hA
    exact h1 (h2.mp hA)

/-- On an open set missing `A`, the ideal of `A` is the unit ideal, generated by `1`. -/
theorem vanishingIdeal_mem_iff_of_disjoint {A U : Set M} (hU : IsOpen U) (hAU : ∀ y ∈ U, y ∉ A)
    {y : M} (hy : y ∈ U) (g : M → ℂ) :
    (vanishingIdeal (n := n) A).mem y g ↔
      IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => (fun _ => (1 : ℂ) : M → ℂ)) y g := by
  constructor
  · rintro ⟨hg, -⟩
    exact isInSpanAt_of_eq_mul ⟨0, rfl⟩ hg hg (Eventually.of_forall fun _ => by simp)
  · intro hg
    refine ⟨hg.holomorphicAt, ?_⟩
    filter_upwards [hU.mem_nhds hy] with y' hy' hA
    exact absurd hA (hAU y' hy')

/-- A holomorphic map `W` into `ℂⁿ` on an open set has holomorphic coordinates there. -/
theorem holomorphicAt_coord {O : Set M} (hO : IsOpen O) {W : M → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') (i : Fin n)
    {z : M} (hz : z ∈ O) : HolomorphicAt n (fun y => W y i) z := by
  filter_upwards [hO.mem_nhds hz] with y hy
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun y => W y i) y :=
    ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff.contMDiff.contMDiffAt).comp y
      (hWs y hy)
  exact h1.mdifferentiableAt (by simp)

theorem mdifferentiableOn_coord {O : Set M} (hO : IsOpen O) {W : M → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') (i : Fin n) :
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (fun y => W y i) O := fun _ hy =>
  (holomorphicAt_coord hO hWs i hy).mdifferentiableAt.mdifferentiableWithinAt

end General

section Pullback

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **`f^*𝓘_A ⊆ 𝓘_{f⁻¹A}`** for a continuous `f`. -/
theorem pullback_vanishingIdeal_le {f : Y → X} (hf : Continuous f) (A : Set X) :
    (GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) A)).Le
      (vanishingIdeal (n := n) (f ⁻¹' A)) := by
  intro y g hg
  obtain ⟨hgh, K, s, a, hs, -, hsum⟩ := hg
  refine ⟨hgh, ?_⟩
  have hzero : ∀ i, ∀ᶠ y' in 𝓝 y, f y' ∈ A → s i y' = 0 := by
    intro i
    obtain ⟨b, hb, hsb⟩ := hs i
    filter_upwards [hf.continuousAt.eventually hb.2] with y' hy' hA
    rw [hsb]
    exact hy' hA
  filter_upwards [hsum, eventually_all.mpr hzero] with y' h1 h2 hA
  rw [h1]
  exact Finset.sum_eq_zero fun i _ => by rw [h2 i hA, mul_zero]

variable {C : Set X} {π : Y → X}

/-- **Off the centre, `π^*𝓘_A ⊇ 𝓘_{π⁻¹A}`**: `π` has a holomorphic section over `X \ C`. -/
theorem mem_pullback_vanishingIdeal_of_notMem (hπ : IsBlowupAlong n C π) (A : Set X) {y : Y}
    (hy : π y ∉ C) {g : Y → ℂ} (hg : (vanishingIdeal (n := n) (π ⁻¹' A)).mem y g) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) A)).mem y g := by
  obtain ⟨σ, hσ, hσπ, hσsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hσx : σ ⟨π y, hy⟩ = y := hσsec y hy
  have hav : ∀ x' : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X),
      extendOpens _ (g ∘ σ) x'.1 = g (σ x') := fun x' => extendOpens_val _ (g ∘ σ) x'
  have hgs : HolomorphicAt n (g ∘ σ) ⟨π y, hy⟩ := by
    refine HolomorphicAt.comp_contMDiff (by rw [hσx]; exact hg.1) ?_
    exact Eventually.of_forall fun x' => hσ x'
  have ha_hol : HolomorphicAt n (extendOpens _ (g ∘ σ)) (π y) :=
    (holomorphicAt_iff_extendOpens _).mp hgs
  have ha_mem : (vanishingIdeal (n := n) A).mem (π y) (extendOpens _ (g ∘ σ)) := by
    refine ⟨ha_hol, ?_⟩
    show ∀ᶠ x' in 𝓝 (⟨π y, hy⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X)).1,
      x' ∈ A → extendOpens _ (g ∘ σ) x' = 0
    rw [eventually_nhds_val_iff]
    have hcont : ContinuousAt σ ⟨π y, hy⟩ := hσ.continuous.continuousAt
    have h2 : ∀ᶠ x' in 𝓝 (⟨π y, hy⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X)),
        σ x' ∈ π ⁻¹' A → g (σ x') = 0 :=
      hcont.eventually (p := fun y' => y' ∈ π ⁻¹' A → g y' = 0) (by rw [hσx]; exact hg.2)
    filter_upwards [h2] with x' hx' hxA
    rw [hav x']
    refine hx' ?_
    show π (σ x') ∈ A
    rw [show π (σ x') = x'.1 from congrFun hσπ x']
    exact hxA
  refine GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul (s := extendOpens _ (g ∘ σ) ∘ π)
    ⟨_, ha_mem, rfl⟩ hg.1 (holomorphicAt_const 1) ?_)
  have hopen : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  filter_upwards [hopen.mem_nhds hy] with y' hy'
  show g y' = 1 * extendOpens _ (g ∘ σ) (π y')
  have h1 : extendOpens _ (g ∘ σ) (π y') = g y' := by
    have := hav ⟨π y', hy'⟩
    rw [hσsec y' hy'] at this
    exact this
  rw [h1, one_mul]

/-- **Off the centre, `π^*𝓘_A = 𝓘_{π⁻¹A}`.** -/
theorem mem_pullback_vanishingIdeal_iff_of_notMem (hπ : IsBlowupAlong n C π) (A : Set X)
    {y : Y} (hy : π y ∉ C) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) A)).mem y g ↔
      (vanishingIdeal (n := n) (π ⁻¹' A)).mem y g :=
  ⟨fun h => pullback_vanishingIdeal_le hπ.contMDiff.continuous A y g h,
    mem_pullback_vanishingIdeal_of_notMem hπ A hy⟩

/-- Off the exceptional divisor, `𝒪_Y(-D)` contains `1`, so multiplying by it changes nothing. -/
theorem mem_mul_vanishingIdeal_iff_of_notMem (hπ : IsBlowupAlong n C π) (A : Set Y) {y : Y}
    (hy : π y ∉ C) (g : Y → ℂ) :
    ((exceptionalDivisor hπ).ideal.mul (vanishingIdeal (n := n) A)).mem y g ↔
      (vanishingIdeal (n := n) A).mem y g := by
  have hDhol : ∀ {p : Y → ℂ}, (exceptionalDivisor hπ).ideal.mem y p → HolomorphicAt n p y :=
    fun hp => GermIdeal.IsInvertible.holomorphicAt_mem (exceptionalDivisor hπ).isInvertible hp
  constructor
  · intro hg
    refine mem_vanishingIdeal_of_isInSpanAt' ?_ (InvertibleIdealQuotient.mem_mul_iff.mp hg)
    rintro t ⟨p, q, hp, hq, rfl⟩
    refine ⟨(hDhol hp).mul hq.1, ?_⟩
    filter_upwards [hq.2] with y' hy' hA
    show p y' * q y' = 0
    rw [hy' hA, mul_zero]
  · intro hg
    have h1C : (vanishingIdeal (n := n) C).mem (π y) (fun _ => 1) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hy] with x hx hxC
      exact absurd hxC hx
    have h1D : (exceptionalDivisor hπ).ideal.mem y (fun _ => 1) := by
      rw [exceptionalDivisor_ideal]
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul (s := (fun _ : X => (1 : ℂ)) ∘ π)
        ⟨fun _ => 1, h1C, rfl⟩ (holomorphicAt_const 1) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
    refine InvertibleIdealQuotient.mem_mul_iff.mpr (isInSpanAt_of_eq_mul ⟨fun _ => 1, g, h1D, hg, rfl⟩ hg.1
      (holomorphicAt_const 1) (Eventually.of_forall fun y' => by simp))

end Pullback

/-! ### Monomial charts: pulled-back flat coordinates generate pullbacks -/

section Chart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}
  {y₀ : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)}
  {k : ℕ} {j : Fin n} {O : Set Y} {W : Y → ComplexModel n}

/-- The pulled-back flat coordinates `σ_j(W)_i` with `i ≥ m`, and `0` for `i < m`. -/
def pulledCoords (k : ℕ) (j : Fin n) (W : Y → ComplexModel n) (m : ℕ) : Fin n → Y → ℂ :=
  fun i => if m ≤ i.1 then fun y => monomial k j (W y) i else fun _ => 0

theorem holomorphicAt_pulledCoords (hO : IsOpen O)
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') (m : ℕ)
    (i : Fin n) {z : Y} (hz : z ∈ O) : HolomorphicAt n (pulledCoords k j W m i) z := by
  unfold pulledCoords
  split_ifs
  · simp only [monomial_apply]
    split_ifs
    · exact (holomorphicAt_coord hO hWs i hz).mul (holomorphicAt_coord hO hWs j hz)
    · exact holomorphicAt_coord hO hWs i hz
  · exact holomorphicAt_const 0

/-- **On a monomial chart, the pullback of the ideal of a flattened set `A = ℂ^m × 0` is generated
by the pulled-back flat coordinates** `σ_j(W)_i`, `i ≥ m` (Hadamard in the coordinates `Φ`). -/
theorem mem_pullback_vanishingIdeal_iff_pulledCoords
    (hπs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {A : Set X} {m : ℕ}
    (hflatA : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n m))
    (hO : IsOpen O)
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWeq : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧
      monomial k j (W z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z')))
    {z : Y} (hz : z ∈ O) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) A)).mem z g ↔
      IsInSpanAt (n := n) (· ∈ range (pulledCoords k j W m)) z g := by
  have hπat : ∀ {y : Y}, ∀ᶠ y' in 𝓝 y,
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y' :=
    fun {_} => Eventually.of_forall fun y' => hπs y'
  -- on `O`, the flat coordinates pulled back by `π` are the `σ_j(W)_i`
  have hcoord : ∀ y ∈ O, ∀ i, flatCoord Φ i (π y) = monomial k j (W y) i := fun y hy i => by
    simp only [flatCoord]
    rw [← (hWeq y hy).2]
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro t ⟨a, ha, rfl⟩
    obtain ⟨b, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflatA (hWeq z hz).1 ha
    refine ⟨ha.1.comp_contMDiff hπat, n, pulledCoords k j W m, fun i => b i ∘ π,
      fun i => ⟨i, rfl⟩, fun i => (hbh i).comp_contMDiff hπat, ?_⟩
    filter_upwards [hπs.continuous.continuousAt.eventually hbeq, hO.mem_nhds hz] with y hy hyO
    simp only [Function.comp_apply, hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold pulledCoords
    split_ifs with hi
    · rw [hcoord y hyO i]
    · simp [hb0 i (by omega)]
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ hg)
    rintro t ⟨i, rfl⟩
    by_cases hi : m ≤ i.1
    · refine isInSpanAt_of_eq_mul ⟨flatCoord Φ i, flatCoord_mem_vanishingIdeal Φ hflatA hi
        (hWeq z hz).1, rfl⟩ (holomorphicAt_pulledCoords hO hWs m i hz) (holomorphicAt_const 1) ?_
      filter_upwards [hO.mem_nhds hz] with y hy
      simp only [pulledCoords, hi, if_true, Function.comp_apply, one_mul, hcoord y hy i]
    · have : pulledCoords k j W m i = fun _ => 0 := by simp [pulledCoords, hi]
      rw [this]
      exact isInSpanAt_zero

/-- The pulled-back flat coordinates of the centre (`m = k`) span the same ideal as `W_j`. -/
theorem isInSpanAt_pulledCoords_centre_iff (hj : k ≤ j.1) (hO : IsOpen O)
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    {z : Y} (hz : z ∈ O) (g : Y → ℂ) :
    IsInSpanAt (n := n) (· ∈ range (pulledCoords k j W k)) z g ↔
      IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => fun y => W y j) z g := by
  have hWj := holomorphicAt_coord hO hWs j hz
  refine FiniteGeneratorIdealDescent.isInSpanAt_iff_of_generators_mutually_in_span
    (f := fun _ : Fin 1 => fun y => W y j) (g := pulledCoords k j W k) (fun i => ?_) (fun _ => ?_) g
  rotate_left
  · refine isInSpanAt_of_eq_mul ⟨j, rfl⟩ hWj (holomorphicAt_const 1) ?_
    refine Eventually.of_forall fun y => ?_
    simp [pulledCoords, hj, monomial_apply]
  · by_cases hi : k ≤ i.1
    · by_cases hij : i = j
      · subst hij
        refine isInSpanAt_of_eq_mul ⟨0, rfl⟩ (holomorphicAt_pulledCoords hO hWs k i hz)
          (holomorphicAt_const 1) (Eventually.of_forall fun y => ?_)
        simp [pulledCoords, hi, monomial_apply]
      · refine isInSpanAt_of_eq_mul ⟨0, rfl⟩ (holomorphicAt_pulledCoords hO hWs k i hz)
          (holomorphicAt_coord hO hWs i hz) (Eventually.of_forall fun y => ?_)
        simp [pulledCoords, hi, monomial_apply, hij]
    · have : pulledCoords k j W k i = fun _ => 0 := by simp [pulledCoords, hi]
      rw [this]
      exact isInSpanAt_zero

/-- **The exceptional divisor has the local equation `W_j` on a monomial chart.** -/
theorem exceptionalDivisor_mem_iff_of_chart {C : Set X} (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    (hj : k ≤ j.1) (hO : IsOpen O)
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWeq : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧
      monomial k j (W z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z')))
    {z : Y} (hz : z ∈ O) (g : Y → ℂ) :
    (exceptionalDivisor hπ).ideal.mem z g ↔
      IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => fun y => W y j) z g := by
  rw [exceptionalDivisor_ideal, mem_pullback_vanishingIdeal_iff_pulledCoords hπ.contMDiff hΦsrc
    hflatC hO hWs hWeq hz, isInSpanAt_pulledCoords_centre_iff hj hO hWs hz]

end Chart

/-! ### Hadamard's lemma in the coordinates of a local inverse -/

section Hadamard

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The coordinates `W_i` with `i ≥ m`, and `0` for `i < m`. -/
def planeCoords (W : Y → ComplexModel n) (m : ℕ) : Fin n → Y → ℂ :=
  fun i => if m ≤ i.1 then fun y => W y i else fun _ => 0

theorem mdifferentiableOn_planeCoords {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') (m : ℕ)
    (i : Fin n) : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (planeCoords W m i) O := by
  unfold planeCoords
  split_ifs
  · exact mdifferentiableOn_coord hO hWs i
  · exact mdifferentiableOn_const

/-- **Hadamard's lemma in the coordinates `W`.**  Let `W` be holomorphic on the open set `O`, with
injective differential (in a chart) at `z ∈ O`, and let `A ∩ O = W⁻¹(ℂ^m × 0) ∩ O` with
`W z ∈ ℂ^m × 0`.  Near `z` the ideal `𝓘_A` is generated by the coordinates `W_i`, `i ≥ m`. -/
theorem exists_vanishingIdeal_mem_iff_planeCoords {O : Set Y} (hO : IsOpen O)
    {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    {z : Y} (hzO : z ∈ O)
    (hFinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)))
    {m : ℕ} (hWz : W z ∈ complexCoordinatePlane n m) {A : Set Y}
    (hA : ∀ y ∈ O, (y ∈ A ↔ W y ∈ complexCoordinatePlane n m)) :
    ∃ U : Set Y, IsOpen U ∧ z ∈ U ∧ U ⊆ O ∧ ∀ y ∈ U, ∀ g : Y → ℂ,
      (vanishingIdeal (n := n) A).mem y g ↔
        IsInSpanAt (n := n) (· ∈ range (planeCoords W m)) y g := by
  set ez := chartAt (ComplexModel n) z with hez
  set F : ComplexModel n → ComplexModel n := fun ζ => W (ez.symm ζ) with hF
  set Nset : Set (ComplexModel n) := ez.target ∩ ez.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := ez.continuousOn_symm.isOpen_inter_preimage ez.open_target hO
  have hzN : ez z ∈ Nset :=
    ⟨ez.map_source (mem_chart_source _ z), by
      show ez.symm (ez z) ∈ O
      rw [ez.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ F Nset := by
    intro ζ hζ
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) hζ.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (ez.symm ζ) :=
      (hWs _ hζ.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)).differentiableWithinAt
  obtain ⟨Θ, hΘN, hΘF, -⟩ := Hironaka.exists_localHolomorphicEquivAt hNo hzN hFd hFinj
  set Φ' : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z) :=
    subConst Θ (W z) with hΦ'
  have hΦ'src : Φ'.source ⊆ (chartAt (ComplexModel n) z).target := fun ζ hζ => (hΘN hζ).1
  have hΦ'fun : ∀ {y : Y}, y ∈ ez.source → ez y ∈ Φ'.source →
      Φ'.toFun (ez y) = W y - W z := fun {y} hy _ => by
    show Θ.toFun (ez y) - W z = W y - W z
    rw [hΘF]
    show W (ez.symm (ez y)) - W z = W y - W z
    rw [ez.left_inv hy]
  have hyO : ∀ {y : Y}, y ∈ ez.source → ez y ∈ Φ'.source → y ∈ O := fun {y} hy hyΦ => by
    have h : ez.symm (ez y) ∈ O := (hΘN hyΦ).2
    rwa [ez.left_inv hy] at h
  have hflat' : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Φ'.source →
        (y ∈ A ↔ Φ'.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n m) :=
    fun {y} hy hyΦ => by
      rw [hΦ'fun hy hyΦ, sub_mem_plane_iff hWz]
      exact hA y (hyO hy hyΦ)
  refine ⟨flatDomain Φ', isOpen_flatDomain Φ', mem_flatDomain_self Φ',
    fun y hy => hyO hy.1 hy.2, fun y hy g => ?_⟩
  have hyO' : y ∈ O := hyO hy.1 hy.2
  constructor
  · intro hg
    obtain ⟨b, hb0, hbh, hbeq⟩ := exists_eq_sum_flatCoord Φ' hΦ'src hflat' hy hg
    refine ⟨hg.1, n, planeCoords W m, b, fun i => ⟨i, rfl⟩, hbh, ?_⟩
    filter_upwards [hbeq, (isOpen_flatDomain Φ').mem_nhds hy] with y' h1 h2
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold planeCoords
    split_ifs with hi
    · simp only [flatCoord]
      rw [hΦ'fun h2.1 h2.2, PiLp.sub_apply, hWz i hi, sub_zero]
    · simp [hb0 i (by omega)]
  · intro hg
    refine mem_vanishingIdeal_of_isInSpanAt' ?_ hg
    rintro t ⟨i, rfl⟩
    by_cases hi : m ≤ i.1
    · simp only [planeCoords, hi, if_true]
      refine ⟨holomorphicAt_coord hO hWs i hyO', ?_⟩
      filter_upwards [hO.mem_nhds hyO'] with y' hy' hA'
      exact (hA y' hy').mp hA' i hi
    · simp only [planeCoords, hi, if_false]
      exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩

end Hadamard

/-! ### The ideal of the strict transform -/

section Strict

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The strict transform of a closed submanifold through the centre is a closed submanifold**
(no constant dimension needed: the dimension is read off at each point). -/
theorem isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold (hπ : IsBlowupAlong n C π)
    {N : Set X} (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) :
    IsClosedSubmanifold n (geoStrictTransform π C N) := by
  refine ⟨isClosed_closure, fun z hz => ?_⟩
  by_cases hzC : π z ∈ C
  · obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
    obtain ⟨kN, hkN⟩ := hN.2 (π z) (hCN hzC)
    exact ⟨kN, regularAtDim_geoStrictTransform_of_mem hπ (le_of_regularAtDim_subset hkC hkN hCN)
      hkC hkN hCN hz⟩
  · obtain ⟨k, hk⟩ := hN.2 (π z)
      (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz)
    exact ⟨k, regularAtDim_geoStrictTransform_of_notMem hπ hN.1 hzC hk⟩

/-- The two sides of the ideal identity agree at a point off the exceptional divisor. -/
theorem mem_pullback_iff_mem_mul_of_notMem (hπ : IsBlowupAlong n C π) {N : Set X}
    (hNc : IsClosed N) {z : Y} (hzC : π z ∉ C) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) N)).mem z g ↔
      ((exceptionalDivisor hπ).ideal.mul
        (vanishingIdeal (n := n) (geoStrictTransform π C N))).mem z g := by
  rw [mem_mul_vanishingIdeal_iff_of_notMem hπ _ hzC, mem_pullback_vanishingIdeal_iff_of_notMem hπ
    N hzC]
  refine vanishingIdeal_mem_congr ?_ g
  have hopen : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  filter_upwards [hopen.mem_nhds hzC] with y hy
  exact (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNc hy).symm

/-- The two sides of the ideal identity agree at a point of the exceptional divisor. -/
theorem mem_pullback_iff_mem_mul_of_mem (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) {z : Y} (hzC : π z ∈ C) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) N)).mem z g ↔
      ((exceptionalDivisor hπ).ideal.mul
        (vanishingIdeal (n := n) (geoStrictTransform π C N))).mem z g := by
  classical
  obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
  obtain ⟨kN, hkN⟩ := hN.2 (π z) (hCN hzC)
  have hk : kC ≤ kN := le_of_regularAtDim_subset hkC hkN hCN
  obtain ⟨Φ, hΦt, -, hflat⟩ := exists_nested_flattening hk hkC hkN hCN
  have hz' : π z ∈ flatDomain Φ :=
    ⟨mem_chart_source _ (π z), by
      show chartAt (ComplexModel n) (π z) (π z) ∈ Φ.source
      exact Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kN) :=
    fun hy hyΦ => (hflat hy hyΦ).2
  -- the strict transform on the chart (`BlowupStrictSubmanifold`)
  obtain ⟨j', hj', O', hO', hzO', W', hW's, hW'mem, hℓ', hiff⟩ :=
    exists_local_geoStrictTransform hπ hΦt hflatC hflatN hz'
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj'
  -- the defining equation of the chart, recovered from the lift
  have hW'eq : ∀ z' ∈ O', π z' ∈ flatDomain Φ ∧
      monomial kC j' (W' z') = Φ.toFun (chartAt (ComplexModel n) (π z) (π z')) := by
    intro z' hz''
    have hℓz := hℓ' ℓ hℓs hℓπ z' hz'' (hW'mem z' hz'')
    have hπz : π z' = monomialChart Φ kC j' (LiftedOpen.mk _ (W' z') (hW'mem z' hz'')) :=
      calc π z' = π (ℓ (LiftedOpen.mk _ (W' z') (hW'mem z' hz''))) := by rw [hℓz]
        _ = _ := congrFun hℓπ _
    have hmon : monomial kC j' (W' z') ∈ Φ.target := hW'mem z' hz''
    refine ⟨?_, ?_⟩
    · rw [hπz]; exact monomialChart_mem_flatDomain hΦt _
    · rw [hπz]
      simp only [monomialChart, LiftedOpen.toModel_mk]
      rw [(chartAt (ComplexModel n) (π z)).right_inv (hΦt (Φ.mapsTo_invFun hmon)),
        Φ.right_inv _ hmon]
  -- presentations on the chart
  have hD : ∀ y ∈ O', ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔
      IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => fun y => W' y j') y g :=
    fun y hy g => exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj' hO' hW's hW'eq hy g
  have hDdiff : ∀ i : Fin 1, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      ((fun _ : Fin 1 => fun y => W' y j') i) O' := fun _ => mdifferentiableOn_coord hO' hW's j'
  have hPN : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) N)).mem z g ↔
      IsInSpanAt (n := n) (· ∈ range (pulledCoords kC j' W' kN)) z g :=
    mem_pullback_vanishingIdeal_iff_pulledCoords hπ.contMDiff hΦt hflatN hO' hW's hW'eq hzO' g
  rw [hPN]
  have hWj := holomorphicAt_coord hO' hW's j' hzO'
  by_cases hjN : j'.1 < kN
  · -- `N'` is the plane `W'⁻¹(ℂ^{k_N} × 0)` near `z`
    -- injectivity of the differential of `W'` at `z`
    have hFinj : Function.Injective (fderiv ℂ (fun ζ => W' ((chartAt (ComplexModel n) z).symm ζ))
        (chartAt (ComplexModel n) z z)) := by
      set ez := chartAt (ComplexModel n) z with hez
      have hdiff : DifferentiableAt ℂ (fun ζ => W' (ez.symm ζ)) (ez z) := by
        have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
          (chart_mem_atlas (ComplexModel n) z) (ez.map_source (mem_chart_source _ z))
        have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W'
            (ez.symm (ez z)) := by
          rw [ez.left_inv (mem_chart_source _ z)]
          exact (hW's _ hzO').mdifferentiableAt (by simp)
        exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
      refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
      by_contra hv0
      apply fderiv_monomialInverse_ne_zero hO' hW's hW'mem hℓs (hℓ' ℓ hℓs hℓπ) hzO' hv0
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact hv
    by_cases hzN' : z ∈ geoStrictTransform π C N
    · have hWz : W' z ∈ complexCoordinatePlane n kN := ((hiff z hzO').mp hzN').2
      obtain ⟨U, hU, hzU, hUO, hUgen⟩ := exists_vanishingIdeal_mem_iff_planeCoords hO' hW's hzO'
        hFinj hWz (A := geoStrictTransform π C N) (fun y hy => by
          rw [hiff y hy]; exact ⟨fun h => h.2, fun h => ⟨hjN, h⟩⟩)
      rw [mem_mul_iff_isInSpanAt_mulFamily hU (fun i => (hDdiff i).mono hUO)
        (fun i => (mdifferentiableOn_planeCoords hO' hW's kN i).mono hUO)
        (fun y hy => hD y (hUO hy)) hUgen hzU g]
      refine FiniteGeneratorIdealDescent.isInSpanAt_iff_of_generators_mutually_in_span
        (f := mulFamily (fun _ : Fin 1 => fun y => W' y j') (planeCoords W' kN))
        (g := pulledCoords kC j' W' kN) (fun i => ?_) (fun q => ?_) g
      · -- `σ_j(W)_i = W_j · W_i` (or `0`) is a product generator
        refine isInSpanAt_of_eq_mul ⟨finProdFinEquiv (0, i), rfl⟩
          (holomorphicAt_pulledCoords hO' hW's kN i hzO') (holomorphicAt_const 1)
          (Eventually.of_forall fun y => ?_)
        simp only [mulFamily_apply]
        simp only [pulledCoords, planeCoords]
        split_ifs with hi
        · have hij : i ≠ j' := fun h => by rw [h] at hi; omega
          simp only [monomial_apply, show kC ≤ i.1 by omega, ne_eq, hij, not_false_eq_true,
            and_self, if_true]
          ring
        · simp
      · -- a product generator `W_j · W_i` (or `0`) is a pulled-back coordinate
        set i := (finProdFinEquiv.symm q).2 with hidef
        have hq : mulFamily (fun _ : Fin 1 => fun y => W' y j') (planeCoords W' kN) q =
            pulledCoords kC j' W' kN i := by
          funext y
          simp only [mulFamily, pulledCoords, planeCoords, ← hidef]
          split_ifs with hi
          · have hij : i ≠ j' := fun h => by rw [h] at hi; omega
            simp only [monomial_apply, show kC ≤ i.1 by omega, ne_eq, hij, not_false_eq_true,
              and_self, if_true]
            ring
          · simp
        rw [hq]
        exact isInSpanAt_of_eq_mul ⟨i, rfl⟩ (holomorphicAt_pulledCoords hO' hW's kN i hzO')
          (holomorphicAt_const 1) (Eventually.of_forall fun y => by simp)
    · -- `z ∉ N'`: near `z`, `N'` is empty
      have hNc : IsClosed (geoStrictTransform π C N) := isClosed_closure
      set U := O' ∩ (geoStrictTransform π C N)ᶜ with hUdef
      have hU : IsOpen U := hO'.inter hNc.isOpen_compl
      have hzU : z ∈ U := ⟨hzO', hzN'⟩
      rw [mem_mul_iff_isInSpanAt_mulFamily hU (fun i => (hDdiff i).mono inter_subset_left)
        (fun _ => mdifferentiableOn_const) (fun y hy => hD y hy.1)
        (fun y hy => vanishingIdeal_mem_iff_of_disjoint hU (fun y' hy' => hy'.2) hy) hzU g]
      -- here `W_j` divides every `σ_j(W)_i` with `i ≥ k_N`, and `W'(z) ∉ ℂ^{k_N} × 0`
      have hWz : W' z ∉ complexCoordinatePlane n kN := fun h => hzN' ((hiff z hzO').mpr ⟨hjN, h⟩)
      obtain ⟨i₀, hi₀, hWi₀⟩ : ∃ i : Fin n, kN ≤ i.1 ∧ W' z i ≠ 0 := by
        simpa [complexCoordinatePlane] using hWz
      have hi₀j : i₀ ≠ j' := fun h => by rw [h] at hi₀; omega
      refine FiniteGeneratorIdealDescent.isInSpanAt_iff_of_generators_mutually_in_span
        (f := mulFamily (fun _ : Fin 1 => fun y => W' y j') (fun _ : Fin 1 => fun _ => (1 : ℂ)))
        (g := pulledCoords kC j' W' kN) (fun i => ?_) (fun q => ?_) g
      · -- `σ_j(W)_i = W_i · W_j`, a multiple of `W_j · 1`
        by_cases hi : kN ≤ i.1
        · have hij : i ≠ j' := fun h => by rw [h] at hi; omega
          refine isInSpanAt_of_eq_mul ⟨finProdFinEquiv (0, 0), rfl⟩
            (holomorphicAt_pulledCoords hO' hW's kN i hzO') (holomorphicAt_coord hO' hW's i hzO')
            (Eventually.of_forall fun y => ?_)
          simp only [mulFamily_apply]
          simp only [pulledCoords, hi, if_true, monomial_apply, show kC ≤ i.1 by omega, ne_eq,
            hij, not_false_eq_true, and_self, mul_one]
        · have : pulledCoords kC j' W' kN i = fun _ => 0 := by simp [pulledCoords, hi]
          rw [this]
          exact isInSpanAt_zero
      · -- `W_j · 1 = σ_j(W)_{i₀} / W_{i₀}` near `z`
        have hq : mulFamily (fun _ : Fin 1 => fun y => W' y j')
            (fun _ : Fin 1 => fun _ => (1 : ℂ)) q = fun y => W' y j' := by
          funext y; simp [mulFamily]
        rw [hq]
        have hWi₀h := holomorphicAt_coord hO' hW's i₀ hzO'
        refine isInSpanAt_of_eq_mul ⟨i₀, rfl⟩ hWj
          (BlowupFlatCoordinates.HolomorphicAt.inv hWi₀h hWi₀) ?_
        filter_upwards [hWi₀h.continuousAt.eventually (isOpen_ne.mem_nhds hWi₀)] with y hy
        simp only [pulledCoords, hi₀, if_true, monomial_apply, show kC ≤ i₀.1 by omega, ne_eq,
          hi₀j, not_false_eq_true, and_self]
        field_simp
  · -- `j ≥ k_N`: `N'` misses the chart, and `π^*𝓘_N = (W_j)`
    have hU : ∀ y ∈ O', y ∉ geoStrictTransform π C N := fun y hy h =>
      hjN ((hiff y hy).mp h).1
    rw [mem_mul_iff_isInSpanAt_mulFamily hO' hDdiff (fun _ => mdifferentiableOn_const)
      hD (fun y hy => vanishingIdeal_mem_iff_of_disjoint hO' hU hy) hzO' g]
    have hjN' : kN ≤ j'.1 := not_lt.mp hjN
    refine FiniteGeneratorIdealDescent.isInSpanAt_iff_of_generators_mutually_in_span
      (f := mulFamily (fun _ : Fin 1 => fun y => W' y j') (fun _ : Fin 1 => fun _ => (1 : ℂ)))
      (g := pulledCoords kC j' W' kN) (fun i => ?_) (fun q => ?_) g
    · by_cases hi : kN ≤ i.1
      · by_cases hij : i = j'
        · subst hij
          refine isInSpanAt_of_eq_mul ⟨finProdFinEquiv (0, 0), rfl⟩
            (holomorphicAt_pulledCoords hO' hW's kN i hzO') (holomorphicAt_const 1)
            (Eventually.of_forall fun y => ?_)
          simp only [mulFamily_apply]
          simp [pulledCoords, hi, monomial_apply]
        · refine isInSpanAt_of_eq_mul ⟨finProdFinEquiv (0, 0), rfl⟩
            (holomorphicAt_pulledCoords hO' hW's kN i hzO') (holomorphicAt_coord hO' hW's i hzO')
            (Eventually.of_forall fun y => ?_)
          simp only [mulFamily_apply]
          simp only [pulledCoords, hi, if_true, monomial_apply, show kC ≤ i.1 by omega, ne_eq,
            hij, not_false_eq_true, and_self, mul_one]
      · have : pulledCoords kC j' W' kN i = fun _ => 0 := by simp [pulledCoords, hi]
        rw [this]
        exact isInSpanAt_zero
    · have hq : mulFamily (fun _ : Fin 1 => fun y => W' y j')
          (fun _ : Fin 1 => fun _ => (1 : ℂ)) q = pulledCoords kC j' W' kN j' := by
        funext y; simp [mulFamily, pulledCoords, hjN', monomial_apply]
      rw [hq]
      exact isInSpanAt_of_eq_mul ⟨j', rfl⟩ (holomorphicAt_pulledCoords hO' hW's kN j' hzO')
        (holomorphicAt_const 1) (Eventually.of_forall fun y => by simp)

/-- **`π^*𝓘_N = 𝒪_Y(-D) · 𝓘_{N'}`** for a closed submanifold `N` containing the centre, with
`N' = closure (π⁻¹(N \ C))` its strict transform and `D` the exceptional divisor. -/
theorem pullback_vanishingIdeal_eq_mul (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) :
    GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) N) =
      (exceptionalDivisor hπ).ideal.mul (vanishingIdeal (n := n) (geoStrictTransform π C N)) := by
  refine GermIdeal.ext (funext fun z => funext fun g => propext ?_)
  by_cases hzC : π z ∈ C
  · exact mem_pullback_iff_mem_mul_of_mem hπ hN hCN hzC g
  · exact mem_pullback_iff_mem_mul_of_notMem hπ hN.1 hzC g

/-- `𝒪_Y(-D)^1 = 𝒪_Y(-D)`. -/
theorem idealPow_one_exceptionalDivisor (hπ : IsBlowupAlong n C π) :
    idealPow (exceptionalDivisor hπ).ideal 1 = (exceptionalDivisor hπ).ideal := by
  show (idealPow (exceptionalDivisor hπ).ideal 0).mul (exceptionalDivisor hπ).ideal = _
  rw [idealPow_zero, unitIdeal_mul (isCoherent_ideal _)]

/-! ### Comparison with the library's strict transform -/

/-- The geometric strict transform of the centre itself is empty. -/
@[simp] theorem geoStrictTransform_self : geoStrictTransform π C C = ∅ := by
  simp [geoStrictTransform]

end Strict

end

end Hironaka.BlowupStrictIdeal

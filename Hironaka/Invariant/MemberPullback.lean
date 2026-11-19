import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Blowup.SimultaneousNormalCrossings

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The pullback of the ideal of a member of a normal crossings divisor along a blowup

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 and the monomial charts of the proof of
`le: inclusions` ("`u_i' = u_i / u_m` for `i < m`, `u_i' = u_i` for `i ≥ m`"); Bierstone--Milman
2008, Definition 2.2 and §3 (monomial marked ideals).  Blueprint `bcalc:hyperplane-ideal`,
`bcalc:member-pullback` (chapter `blowup-calculus.tex`).  Input of the H4 design nodes
`hir:monomial-blowup` and `hir:nonmonomial-transform` (`hironaka.tex`).

Let `π : Y → X` be the blowup along `C`, `D = π⁻¹ C`, `E` a simple normal crossings divisor such
that `C` has normal crossings with `E`, `H` a member of `E` and `H' = closure (π⁻¹ (H \ C))`.  At
every `z ∈ Y`:

* `mem_pullback_member_iff_of_subset` (`C ⊆ H` near `π z`): `π^*𝓘_H = 𝒪_Y(-D) · 𝓘_{H'}` at `z`;
* `mem_pullback_member_iff_of_not_subset` (`C ⊄ H` near `π z`): `π^*𝓘_H = 𝓘_{H'}` at `z`.

Proof, at a point `z` over `x ∈ C ∩ H`: adapted coordinates `Φ` at `x`
(`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`, `N = X`) in which `C = ℂ^k × 0`
and `H = {w_t = 0}`; `C ⊆ H` near `x` exactly when `t ≥ k`.  In a monomial chart `j ≥ k` with local
inverse `W` (`σ_j ∘ W = Φ ∘ e ∘ π`), `𝓘_H = (Φ_t)` (`vanishingIdeal_mem_iff_flatCoord`) pulls back
to `(σ_j(W)_t)`, which is `(W_t)` if `t < k`, `(W_t W_j)` if `t ≥ k`, `t ≠ j`, and `(W_j)` if
`t = j`; `𝒪(-D) = (W_j)`; and `𝓘_{H'} = (W_t)` if `t ≠ j` (`W_t` has multiplicity one, the
differential of `W` being injective), `= 𝒪` if `t = j` (`H'` misses the chart).

The second identity is false for members of higher codimension (`A = {z₁ = z₃ = 0}`,
`C = {z₁ = z₂ = 0}`: in the chart `z₁ = w₁` the pullback is `(w₁, w₃)` but `A'` misses the chart),
so everything here is about hypersurfaces.

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MemberPullback

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupExceptionalDivisor
  BlowupStrictSubmanifold BlowupStrictIdeal BlowupSNCTransform NormalCrossings
  SimultaneousNormalCrossings RelativePrincipalizationSpan DerivativeIdeal

noncomputable section

variable {n : ℕ}

/-! ### Principal ideals -/

section Principal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Generators that agree near the point span the same germs. -/
theorem isInSpanAt_eq_congr {x : M} {h h' : M → ℂ} (hhh' : h =ᶠ[𝓝 x] h') (g : M → ℂ) :
    IsInSpanAt (n := n) (· = h) x g ↔ IsInSpanAt (n := n) (· = h') x g := by
  constructor
  · intro hg
    obtain ⟨hgh, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    refine isInSpanAt_eq_iff.mpr ⟨hgh, a, ha, ?_⟩
    filter_upwards [heq, hhh'] with y h1 h2
    rw [h1, h2]
  · intro hg
    obtain ⟨hgh, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    refine isInSpanAt_eq_iff.mpr ⟨hgh, a, ha, ?_⟩
    filter_upwards [heq, hhh'] with y h1 h2
    rw [h1, h2]

/-- **Products of principal ideals**: if `𝔞 = (p)` and `𝔟 = (q)` at `x`, then `𝔞 𝔟 = (p q)` at
`x`. -/
theorem mul_mem_iff_of_generators {𝔞 𝔟 : GermIdeal n M} {x : M} {p q : M → ℂ}
    (hp : ∀ g, 𝔞.mem x g ↔ IsInSpanAt (n := n) (· = p) x g)
    (hq : ∀ g, 𝔟.mem x g ↔ IsInSpanAt (n := n) (· = q) x g)
    (hph : HolomorphicAt n p x) (hqh : HolomorphicAt n q x) (g : M → ℂ) :
    (𝔞.mul 𝔟).mem x g ↔ IsInSpanAt (n := n) (· = fun y => p y * q y) x g := by
  show IsInSpanAt (n := n) (fun s => ∃ a b, 𝔞.mem x a ∧ 𝔟.mem x b ∧ s = a * b) x g ↔ _
  constructor
  · intro hg
    refine IsInSpanAt.of_forall_eq_mul ?_ hg
    rintro s ⟨a, b, ha, hb, rfl⟩
    obtain ⟨-, c, hc, hac⟩ := isInSpanAt_eq_iff.mp ((hp a).mp ha)
    obtain ⟨-, d, hd, hbd⟩ := isInSpanAt_eq_iff.mp ((hq b).mp hb)
    refine ⟨fun y => c y * d y, hc.mul hd, ?_⟩
    filter_upwards [hac, hbd] with y h1 h2
    simp only [Pi.mul_apply, h1, h2]
    ring
  · intro hg
    refine IsInSpanAt.trans (fun s hs => ?_) hg
    subst hs
    exact isInSpanAt_of_eq_mul ⟨p, q, (hp p).mpr (isInSpanAt_of_eq_mul rfl hph
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)), (hq q).mpr
      (isInSpanAt_of_eq_mul rfl hqh (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)),
      rfl⟩ (hph.mul hqh) (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)

/-- A unit generates every holomorphic germ. -/
theorem isInSpanAt_one_iff {x : M} (g : M → ℂ) :
    IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) x g ↔ HolomorphicAt n g x := by
  refine ⟨fun hg => hg.1, fun hg => isInSpanAt_of_eq_mul rfl hg hg
    (Eventually.of_forall fun _ => by simp)⟩

end Principal

/-! ### Pullbacks of principal ideals -/

section Pullback

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The pullback of a principal ideal is principal**: if `𝔞 = (h)` at `f z`, then `f^*𝔞 = (h ∘ f)`
at `z`. -/
theorem pullback_mem_iff_of_generator {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {𝔞 : GermIdeal n X}
    {h : X → ℂ} {z : Y} (hh : HolomorphicAt n h (f z))
    (hgen : ∀ g, 𝔞.mem (f z) g ↔ IsInSpanAt (n := n) (· = h) (f z) g) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) f 𝔞).mem z g ↔ IsInSpanAt (n := n) (· = h ∘ f) z g := by
  have hfat : ∀ᶠ y in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
    Eventually.of_forall fun y => hf y
  constructor
  · intro hg
    refine IsInSpanAt.of_forall_eq_mul ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨a, ha, rfl⟩
    obtain ⟨-, c, hc, hac⟩ := isInSpanAt_eq_iff.mp ((hgen a).mp ha)
    refine ⟨c ∘ f, hc.comp_contMDiff hfat, ?_⟩
    filter_upwards [hf.continuous.continuousAt.eventually hac] with y hy
    exact hy
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans (fun s hs => ?_) hg)
    subst hs
    exact isInSpanAt_of_eq_mul ⟨h, (hgen h).mpr (isInSpanAt_of_eq_mul rfl hh
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)), rfl⟩
      (hh.comp_contMDiff hfat) (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)

end Pullback

/-! ### Coordinate hyperplanes -/

section Hyperplane

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {y₀ : M}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))

/-- The differential of a local biholomorphism is injective. -/
theorem injective_fderiv_toFun {p : ComplexModel n} (hp : p ∈ Φ.source) :
    Function.Injective (fderiv ℂ Φ.toFun p) := by
  have hd : DifferentiableAt ℂ Φ.toFun p :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hp)
  have hdi : DifferentiableAt ℂ Φ.invFun (Φ.toFun p) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hp))
  have hcomp : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w))
      ((fderiv ℂ Φ.invFun (Φ.toFun p)).comp (fderiv ℂ Φ.toFun p)) p :=
    hdi.hasFDerivAt.comp p hd.hasFDerivAt
  have hid : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w)) (ContinuousLinearMap.id ℂ _) p := by
    refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
    filter_upwards [Φ.isOpen_source.mem_nhds hp] with w hw
    exact Φ.left_inv w hw
  have heq := hcomp.unique hid
  intro v w hvw
  have := congrArg (fun L => L v) heq
  have h2 := congrArg (fun L => L w) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2, hvw]

/-- **A flat coordinate has a nonvanishing partial derivative** at every point of the flat
domain. -/
theorem exists_chartDeriv_flatCoord_ne_zero (t : Fin n) {y : M} (hy : y ∈ flatDomain Φ) :
    ∃ v : ComplexModel n, chartDeriv (complexChartAt (n := n) y₀) v (flatCoord Φ t) y ≠ 0 := by
  have hpΦ : chartAt (ComplexModel n) y₀ y ∈ Φ.source := hy.2
  have hpt : chartAt (ComplexModel n) y₀ y ∈ (chartAt (ComplexModel n) y₀).target :=
    (chartAt (ComplexModel n) y₀).map_source hy.1
  have hsurj : Function.Surjective (fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y)) :=
    LinearMap.injective_iff_surjective
      (f := ((fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y) : ComplexModel n →L[ℂ]
        ComplexModel n) : ComplexModel n →ₗ[ℂ] ComplexModel n)) |>.mp
      (injective_fderiv_toFun Φ hpΦ)
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single t 1)
  refine ⟨v, ?_⟩
  have hd : DifferentiableAt ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hpΦ)
  have heq : (flatCoord Φ t ∘ (chartAt (ComplexModel n) y₀).symm)
      =ᶠ[𝓝 (chartAt (ComplexModel n) y₀ y)] fun w => Φ.toFun w t := by
    filter_upwards [(chartAt (ComplexModel n) y₀).open_target.mem_nhds hpt] with w hw
    simp only [Function.comp_apply, flatCoord]
    rw [(chartAt (ComplexModel n) y₀).right_inv hw]
  have hderiv : HasFDerivAt (fun w => Φ.toFun w t)
      ((EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ Φ.toFun (chartAt (ComplexModel n) y₀ y))) (chartAt (ComplexModel n) y₀ y) :=
    (EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hd.hasFDerivAt
  unfold chartDeriv
  show fderiv ℂ (flatCoord Φ t ∘ (chartAt (ComplexModel n) y₀).symm)
      (chartAt (ComplexModel n) y₀ y) v ≠ 0
  rw [heq.fderiv_eq, hderiv.fderiv]
  simp [hv]

/-- **Hadamard for a coordinate hyperplane**: if `A = {Φ_t = 0}` on the flat domain of `Φ`, then
at every point of the flat domain `𝓘_A` is generated by the flat coordinate `Φ_t`. -/
theorem vanishingIdeal_mem_iff_flatCoord {A : Set M} {t : Fin n}
    (hflatA : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) t = 0))
    {y : M} (hy : y ∈ flatDomain Φ) (g : M → ℂ) :
    (vanishingIdeal (n := n) A).mem y g ↔ IsInSpanAt (n := n) (· = flatCoord Φ t) y g := by
  rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff (isOpen_flatDomain Φ)
    (fun y' hy' => holomorphicAt_flatCoord Φ t hy')
    (fun y' hy' _ => let ⟨v, hv⟩ := exists_chartDeriv_flatCoord_ne_zero Φ t hy'
      ⟨complexChartAt (n := n) y₀, v, hy'.1, hv⟩) hy g]
  refine vanishingIdeal_mem_congr ?_ g
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hy] with y' hy'
  exact ⟨fun h => ⟨(hflatA hy'.1 hy'.2).mp h, hy'⟩, fun h => (hflatA hy'.1 hy'.2).mpr h.1⟩

end Hyperplane

/-! ### Members of a normal crossings divisor -/

section Member

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- A span over a single-element range is a span over the element. -/
theorem isInSpanAt_range_one_iff {x : Y} (f g : Y → ℂ) :
    IsInSpanAt (n := n) (· ∈ range fun _ : Fin 1 => f) x g ↔ IsInSpanAt (n := n) (· = f) x g :=
  ⟨IsInSpanAt.mono fun _ ⟨_, hs⟩ => hs.symm, IsInSpanAt.mono fun _ hs => ⟨0, hs.symm⟩⟩

/-- **The coordinates of a map with injective differential have multiplicity one.** -/
theorem exists_chartDeriv_coord_ne_zero {O : Set Y} {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z') {u : Y}
    (hu : u ∈ O)
    (hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)))
    (t : Fin n) :
    ∃ v : ComplexModel n, chartDeriv (complexChartAt (n := n) u) v (fun y => W y t) u ≠ 0 := by
  have hdiff : DifferentiableAt ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
      (chartAt (ComplexModel n) u u) := by
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) u)
      ((chartAt (ComplexModel n) u).map_source (mem_chart_source _ u))
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W
        ((chartAt (ComplexModel n) u).symm (chartAt (ComplexModel n) u u)) := by
      rw [(chartAt (ComplexModel n) u).left_inv (mem_chart_source _ u)]
      exact (hWs _ hu).mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
  have hsurj : Function.Surjective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
      (chartAt (ComplexModel n) u u)) :=
    LinearMap.injective_iff_surjective
      (f := ((fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
        (chartAt (ComplexModel n) u u) : ComplexModel n →L[ℂ] ComplexModel n) :
          ComplexModel n →ₗ[ℂ] ComplexModel n)) |>.mp hinj
  obtain ⟨v, hv⟩ := hsurj (EuclideanSpace.single t 1)
  refine ⟨v, ?_⟩
  have hderiv : HasFDerivAt (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ) t)
      ((EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ))
          (chartAt (ComplexModel n) u u))) (chartAt (ComplexModel n) u u) :=
    (EuclideanSpace.proj t : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hdiff.hasFDerivAt
  unfold chartDeriv
  show fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ) t)
      (chartAt (ComplexModel n) u u) v ≠ 0
  rw [hderiv.fderiv]
  simp [hv]

/-- **Generators over a point of `C ∩ H` in a monomial chart.**  At `z` with `π z ∈ C ∩ H`
(`H = E.get i`), there are adapted indices `k ≤ j` and `t` and a local inverse `W` of a monomial
chart such that `C ⊆ H` near `π z` exactly when `k ≤ t`, and at `z`: `π^*𝓘_H = (σ_j(W)_t)`,
`𝒪(-D) = (W_j)`, and `𝓘_{H'} = (W_t)` if `t ≠ j`, `= 𝒪` if `t = j`. -/
theorem exists_chart_generators (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (i : Fin E.length) {z : Y}
    (hzC : π z ∈ C) (hzH : π z ∈ E.get i) :
    ∃ (k : ℕ) (t j : Fin n) (W : Y → ComplexModel n), k ≤ j.1 ∧
      ((∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) ↔ k ≤ t.1) ∧
      HolomorphicAt n (fun y => W y t) z ∧ HolomorphicAt n (fun y => W y j) z ∧
      (∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem z g ↔
        IsInSpanAt (n := n) (· = fun y => monomial k j (W y) t) z g) ∧
      (∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔
        IsInSpanAt (n := n) (· = fun y => W y j) z g) ∧
      (∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem z g ↔
        IsInSpanAt (n := n) (· = if t = j then (fun _ => (1 : ℂ)) else fun y => W y t) z g) := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨kC, kN, Φ, s, hΦt, -, -, hflat⟩ := isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE
    (isTransverse_univ_of_isSNCDivisor hE) hnc hzC
  set t := s i with ht
  have hz' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) t = 0) :=
    fun hy hyΦ => (hflat hy hyΦ).2.2 i hzH
  have hflatH' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {t}) :=
    fun hy hyΦ => by rw [mem_coordSubspace_singleton]; exact hflatH hy hyΦ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz'' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz'').2]; exact Φ.mapsTo_toFun (hWeq z' hz'').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  have hFinj : ∀ u ∈ O, Function.Injective (fderiv ℂ
      (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)) :=
    fun u hu => injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hu
  refine ⟨kC, t, j, W, hj, ?_, holomorphicAt_coord hO hWs t hzO, holomorphicAt_coord hO hWs j hzO,
    ?_, ?_, ?_⟩
  · -- `C ⊆ H` near `π z` iff the coordinate of `H` is not a free coordinate of `C`
    constructor
    · intro hCH
      by_contra hlt
      push Not at hlt
      have hpt : Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) ∈ Φ.target :=
        Φ.mapsTo_toFun hz'.2
      have hpC := (hflatC hz'.1 hz'.2).mp hzC
      have hpH := (hflatH hz'.1 hz'.2).mp hzH
      -- the curve `ε ↦ e⁻¹ Φ⁻¹ (Φ (e x) + ε e_t)` runs inside `C` and leaves `H`
      have hwc : Continuous fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ) := by fun_prop
      have htend : Tendsto (fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ)) (𝓝 0)
          (𝓝 (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)))) := by
        simpa using hwc.tendsto 0
      have hinv : Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z))) =
          chartAt (ComplexModel n) (π z) (π z) := Φ.left_inv _ hz'.2
      have hψ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ε • EuclideanSpace.single t (1 : ℂ)))) (𝓝 0) (𝓝 (π z)) := by
        have h1 : ContinuousAt Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z))) :=
          Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
        have h2 : ContinuousAt (chartAt (ComplexModel n) (π z)).symm
            (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)))) := by
          rw [hinv]
          exact (chartAt (ComplexModel n) (π z)).continuousAt_symm
            ((chartAt (ComplexModel n) (π z)).map_source hz'.1)
        have h3 := (h2.comp h1).tendsto.comp htend
        simpa [Function.comp_def, hinv, (chartAt (ComplexModel n) (π z)).left_inv hz'.1] using h3
      have hwt : ∀ᶠ ε in 𝓝 (0 : ℂ), Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
          ε • EuclideanSpace.single t (1 : ℂ) ∈ Φ.target := by
        exact htend (Φ.isOpen_target.mem_nhds hpt)
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((hψ.eventually hCH).and hwt)
      have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
        rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      obtain ⟨hCHε, hwtε⟩ := hball hε
      have hsrc := Φ.mapsTo_invFun hwtε
      have htgt := hΦt hsrc
      have hys := (chartAt (ComplexModel n) (π z)).map_target htgt
      have hey := (chartAt (ComplexModel n) (π z)).right_inv htgt
      have hyΦ : chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ)))) ∈ Φ.source := by
        rw [hey]; exact hsrc
      have hΦy : Φ.toFun (chartAt (ComplexModel n) (π z) ((chartAt (ComplexModel n) (π z)).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ))))) =
          Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) +
            ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ) := by
        rw [hey]; exact Φ.right_inv _ hwtε
      have hyC := (hflatC hys hyΦ).mpr (by
        rw [hΦy]
        intro l hl
        have hlt' : l ≠ t := fun h => by rw [h] at hl; omega
        simp [hpC l hl, hlt'])
      have hyH := (hflatH hys hyΦ).mp (hCHε hyC)
      rw [hΦy] at hyH
      simp [hpH] at hyH
      linarith
    · intro hkt
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hz'] with y hy hyC
      refine (hflatH hy.1 hy.2).mpr ?_
      exact (hflatC hy.1 hy.2).mp hyC t hkt
  · intro g
    rw [pullback_mem_iff_of_generator hπ.contMDiff (holomorphicAt_flatCoord Φ t hz')
      (vanishingIdeal_mem_iff_flatCoord Φ hflatH hz') g]
    refine isInSpanAt_eq_congr ?_ g
    filter_upwards [hO.mem_nhds hzO] with y hy
    simp only [Function.comp_apply, flatCoord]
    rw [← (hWeq y hy).2]
  · intro g
    rw [exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj hO hWs hWeq hzO g,
      isInSpanAt_range_one_iff]
  · intro g
    have hHu : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ j ∉ ({t} : Finset (Fin n)) ∧
        W u ∈ coordSubspace {t}) := fun u hu =>
      mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatH' hj hO hWs hWeq hℓ hu
    by_cases htj : t = j
    · rw [if_pos htj, vanishingIdeal_mem_iff_of_disjoint hO (fun u hu hH => ((hHu u hu).mp hH).1
        (by simp [htj])) hzO g, isInSpanAt_range_one_iff]
    · rw [if_neg htj]
      have hHu' : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ W u t = 0) := fun u hu => by
        rw [hHu u hu, mem_coordSubspace_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by simp [Ne.symm htj], h⟩⟩
      rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hO
        (fun u hu => holomorphicAt_coord hO hWs t hu)
        (fun u hu _ => let ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hu (hFinj u hu) t
          ⟨complexChartAt (n := n) u, v, mem_complexChartAt_source u, hv⟩) hzO g]
      refine vanishingIdeal_mem_congr ?_ g
      filter_upwards [hO.mem_nhds hzO] with u hu
      exact ⟨fun h => ⟨(hHu' u hu).mp h, hu⟩, fun h => (hHu' u hu).mpr h.1⟩

/-- **`π^*𝓘_H = 𝒪_Y(-D) · 𝓘_{H'}` where the centre lies in the member** `H = E.get i` near `π z`
(`E` SNC, `C` with normal crossings with `E`). -/
theorem mem_pullback_member_iff_of_subset (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (i : Fin E.length) {z : Y}
    (hCH : ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem z g ↔
      ((exceptionalDivisor hπ).ideal.mul
        (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i)))).mem z g := by
  by_cases hzC : π z ∈ C
  · have hzH : π z ∈ E.get i := hCH.self_of_nhds hzC
    obtain ⟨k, t, j, W, -, hdich, hWt, hWj, hpb, hD, hH'⟩ :=
      exists_chart_generators hπ hE hnc i hzC hzH
    have hkt : k ≤ t.1 := hdich.mp hCH
    have hq : HolomorphicAt n (if t = j then (fun _ => (1 : ℂ)) else fun y => W y t) z := by
      split_ifs
      · exact holomorphicAt_const 1
      · exact hWt
    rw [hpb, mul_mem_iff_of_generators hD hH' hWj hq]
    have hfun : (fun y => monomial k j (W y) t) =
        fun y => W y j * (if t = j then (fun _ => (1 : ℂ)) else fun y => W y t) y := by
      funext y
      by_cases htj : t = j
      · subst htj
        simp
      · simp [monomial_apply, hkt, htj, mul_comm]
    rw [hfun]
  · exact mem_pullback_iff_mem_mul_of_notMem hπ (hE.1 _ (List.get_mem _ _)) hzC g

/-- **`π^*𝓘_H = 𝓘_{H'}` where the centre does not lie in the member** `H = E.get i` near `π z`
(`E` SNC, `C` with normal crossings with `E`). -/
theorem mem_pullback_member_iff_of_not_subset (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) (i : Fin E.length) {z : Y}
    (hCH : ¬ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))).mem z g ↔
      (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem z g := by
  have hHc : IsClosed (E.get i) := hE.1 _ (List.get_mem _ _)
  have hzC : π z ∈ C := by
    by_contra hzC
    exact hCH (by
      filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hzC] with y hy hyC
      exact absurd hyC hy)
  by_cases hzH : π z ∈ E.get i
  · obtain ⟨k, t, j, W, hkj, hdich, hWt, -, hpb, -, hH'⟩ :=
      exists_chart_generators hπ hE hnc i hzC hzH
    have hkt : ¬ k ≤ t.1 := fun h => hCH (hdich.mpr h)
    have htj : t ≠ j := fun h => hkt (h ▸ hkj)
    rw [hpb, hH', if_neg htj]
    refine isInSpanAt_eq_congr (Eventually.of_forall fun y => ?_) g
    simp [monomial_apply, hkt]
  · -- both ideals are the unit ideal at `z`
    have hgen : ∀ g', (vanishingIdeal (n := n) (E.get i)).mem (π z) g' ↔
        IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) (π z) g' := fun g' => by
      rw [vanishingIdeal_mem_iff_of_disjoint hHc.isOpen_compl (fun y hy => hy) hzH g',
        isInSpanAt_range_one_iff]
    rw [pullback_mem_iff_of_generator hπ.contMDiff (holomorphicAt_const 1) hgen g]
    have hopen : IsOpen (π ⁻¹' (E.get i)ᶜ) := hHc.isOpen_compl.preimage hπ.contMDiff.continuous
    rw [vanishingIdeal_mem_iff_of_disjoint hopen (fun y hy hyH' =>
      hy (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHc hyH')) hzH g,
      isInSpanAt_range_one_iff]
    rfl

end Member

end

end Hironaka.MemberPullback

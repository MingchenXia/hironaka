import Hironaka.Analytic.ChartPartition
import Hironaka.Analytic.ManifoldTubePositivity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A collar cut-off on a compact set, with a one-sided `ddᶜ` bound

`Hironaka.ChartPartition.exists_chartSmooth_bump` produces a chart-smooth bump
equal to one near *one* point.  The collar construction of CT22 Lemma 4.3,
Step 3 needs the version on a whole compact set: given `K ⊆ W` with `K`
compact and `W` open, a chart-smooth `ρ` with

* `-1 ≤ ρ ≤ 0`,
* `ρ = 0` on an open neighbourhood of `K`,
* `ρ = -1` off `W`,

together with a constant `C > 0` such that `ddᶜρ ≥ -Cω`.

The blueprint (`ana:collar-cutoff`) reaches this by a *regularized* maximum of
finitely many point bumps.  That is not needed: with `h₁, …, h_r` the point
bumps, the function
\[
  \rho = -\prod_{i}(1-h_i)
\]
is already chart-smooth, because a finite product of chart-smooth functions is
chart-smooth chart by chart.  It vanishes wherever some `h_i` equals one — hence
on the open set covering `K` — and equals `-1` wherever every `h_i` vanishes,
hence off `W`.  No smoothing step and no numerical gap enter.

The `ddᶜ` bound is the Kähler domination `gnpp:kahler-domination` applied to the
single closed real `(1,1)`-form `ddᶜρ`, bundled by
`Hironaka.ManifoldTubePositivity.ddcClosedForm`.  Only the LOWER bound is used
downstream: in the collar construction the local branch is `ψ + sρ`, whose
background is `θ - s ddᶜρ`, and enlarging that background by the semipositive
form `s ddᶜρ + (Λ/2)ω` is what the gap pays for.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.CompactCollarCutoff

open Hironaka.PositiveClasses
open Hironaka.ChartPartition
open Hironaka.ManifoldTubePositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite product of chart-smooth functions is chart-smooth. -/
theorem chartSmooth_prod {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ChartSmooth (n := n) (f i)) :
    ChartSmooth (n := n) fun y => ∏ i ∈ s, f i y := fun e =>
  contDiffOn_prod fun i hi => hf i hi e

/-- **The collar cut-off on a compact set.**  `K ⊆ W` with `K` compact and `W`
open carry a chart-smooth `ρ` with values in `[-1,0]`, vanishing on an open
neighbourhood of `K` and equal to `-1` off `W`. -/
theorem exists_chartSmooth_collar {K W : Set M} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) :
    ∃ ρ : M → ℝ, ChartSmooth (n := n) ρ ∧ (∀ y, -1 ≤ ρ y) ∧ (∀ y, ρ y ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ K ⊆ N ∧ ∀ y ∈ N, ρ y = 0) ∧
      ∀ y ∉ W, ρ y = -1 := by
  classical
  -- a chart-smooth bump at every point of `K`, supported in `W`
  have hbump : ∀ x ∈ K, ∃ h : M → ℝ, ChartSmooth (n := n) h ∧ (∀ y, 0 ≤ h y) ∧
      (∀ y, h y ≤ 1) ∧ tsupport h ⊆ W ∧ ∀ᶠ y in 𝓝 x, h y = 1 := by
    intro x hx
    obtain ⟨h, hsm, h0, h1, hsupp, -, hone⟩ :=
      exists_chartSmooth_bump (n := n) x ⟨W, hW⟩ (hKW hx)
    exact ⟨h, hsm, h0, h1, hsupp, hone⟩
  choose! h hsm h0 h1 hsupp hone using hbump
  -- the open sets where a bump is identically one
  set N : M → Set M := fun x => interior {y | h x y = 1} with hNdef
  have hNopen (x : M) : IsOpen (N x) := isOpen_interior
  have hxN : ∀ x ∈ K, x ∈ N x := fun x hx => mem_interior_iff_mem_nhds.2 (hone x hx)
  obtain ⟨t, htK, htfin, htcover⟩ :=
    hK.elim_finite_subcover_image (c := N) (fun x _ => hNopen x)
      fun x hx => mem_biUnion hx (hxN x hx)
  set s : Finset M := htfin.toFinset with hsdef
  have hst : ∀ x ∈ s, x ∈ K := fun x hx => htK (htfin.mem_toFinset.mp hx)
  refine ⟨fun y => -∏ x ∈ s, (1 - h x y), ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact ((chartSmooth_prod (n := n) (M := M) (f := fun x y => 1 - h x y) s fun x hx => fun e' =>
      contDiffOn_const.sub (hsm x (hst x hx) e')) e).neg
  · intro y
    have : (∏ x ∈ s, (1 - h x y)) ≤ 1 :=
      Finset.prod_le_one (fun x hx => by linarith [h1 x (hst x hx) y])
        (fun x hx => by linarith [h0 x (hst x hx) y])
    linarith
  · intro y
    have : (0 : ℝ) ≤ ∏ x ∈ s, (1 - h x y) :=
      Finset.prod_nonneg fun x hx => by linarith [h1 x (hst x hx) y]
    linarith
  · refine ⟨⋃ x ∈ s, N x, isOpen_biUnion fun x _ => hNopen x, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (htcover hy)
      exact mem_biUnion (htfin.mem_toFinset.mpr hx) hyx
    · intro y hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
      have hxy' : y ∈ {z : M | h x z = 1} := interior_subset hyx
      have hxy : h x y = 1 := hxy'
      have : (∏ x' ∈ s, (1 - h x' y)) = 0 :=
        Finset.prod_eq_zero hx (by rw [hxy]; ring)
      show -∏ x' ∈ s, (1 - h x' y) = 0
      rw [this, neg_zero]
  · intro y hy
    have hzero : ∀ x ∈ s, h x y = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hc => hy (hsupp x (hst x hx) hc)
    have : (∏ x ∈ s, (1 - h x y)) = 1 := by
      refine Finset.prod_eq_one fun x hx => ?_
      rw [hzero x hx]; ring
    show -∏ x ∈ s, (1 - h x y) = -1
    rw [this]

variable [CompactSpace M]

/-- **The collar cut-off together with its `ddᶜ` lower bound.**  On a compact
Kähler manifold the cut-off of `exists_chartSmooth_collar` satisfies
`ddᶜρ + Cω ≥ 0` for some `C > 0`; this is Kähler domination applied to the
closed real `(1,1)`-form `ddᶜρ`. -/
theorem exists_chartSmooth_collar_ddc_lower (omega : KahlerBackground n M)
    {K W : Set M} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (ρ : M → ℝ) (hρ : ChartSmooth (n := n) ρ),
      (∀ y, -1 ≤ ρ y) ∧ (∀ y, ρ y ≤ 0) ∧
      (∃ N : Set M, IsOpen N ∧ K ⊆ N ∧ ∀ y ∈ N, ρ y = 0) ∧
      (∀ y ∉ W, ρ y = -1) ∧
      ∃ C : ℝ, 0 < C ∧ (ddcClosedForm ρ hρ + C • omega.form).val.IsSemipositive := by
  obtain ⟨ρ, hρ, hlow, hup, hnbhd, hoff⟩ := exists_chartSmooth_collar (n := n) hK hW hKW
  obtain ⟨C, hC, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (ddcClosedForm ρ hρ)
  exact ⟨ρ, hρ, hlow, hup, hnbhd, hoff, C, hC, hsemi⟩

end

end Hironaka.CompactCollarCutoff

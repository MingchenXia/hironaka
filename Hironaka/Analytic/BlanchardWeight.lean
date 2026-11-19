import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Analytic.ChartPartition

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Blanchard weight of a smooth centre

Let `C` be a closed complex submanifold of a compact complex manifold `M`.  Cover `C` by
flattening charts `Φ_p` (`C = {ζ_i = 0, i ≥ k_p}`) and `M \ C` by itself, and take a
chart-smooth partition of unity `χ_a` subordinate to this cover (`BlanchardData`,
`exists_blanchardData`).  The **Blanchard weight** is
`U(y) = ∑_a χ_a(y) N_a(y)`, `N_a = ∑_{i ≥ k_p} |ζ^p_i|²` if `χ_a` lives in the chart of `p`, and
`N_a = 1` if it lives off `C`.

* `weight_eq_zero_of_mem`, `weight_pos_of_notMem`: `U` vanishes exactly on `C`;
* `chartSmooth_weight`: `U` is smooth.

On a blowup `π : Z → M` along `C`, `U ∘ π = |h|² U'` locally with `U' > 0`, and
`ddᶜ log U'` is the curvature form that makes `π^* ω + ε ddᶜ log U'` Kähler.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlanchardWeight

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n) in
/-- Flattening charts along `C` and a subordinate partition of unity. -/
structure BlanchardData (C : Set M) where
  kdim : C → ℕ
  flat : (p : C) → LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.1 p.1)
  flat_src : ∀ p, (flat p).source ⊆ (chartAt (ComplexModel n) p.1).target
  flat_eq : ∀ (p : C) {y : M}, y ∈ (chartAt (ComplexModel n) p.1).source →
    chartAt (ComplexModel n) p.1 y ∈ (flat p).source →
      (y ∈ C ↔ (flat p).toFun (chartAt (ComplexModel n) p.1 y) ∈
        complexCoordinatePlane n (kdim p))
  m : ℕ
  χ : Fin m → M → ℝ
  center : Fin m → Option C
  smooth : ∀ a, ChartSmooth (n := n) (χ a)
  nonneg : ∀ a y, 0 ≤ χ a y
  sum_one : ∀ y, ∑ a, χ a y = 1
  supp_none : ∀ a, center a = none → tsupport (χ a) ⊆ Cᶜ
  supp_some : ∀ a p, center a = some p → tsupport (χ a) ⊆ flatDomain (flat p)

theorem exists_blanchardData [CompactSpace M] {C : Set M} (hC : IsClosedSubmanifold n C) :
    Nonempty (BlanchardData n C) := by
  classical
  choose kdim hreg using fun p : C => hC.2 p.1 p.2
  choose Φ hsrc _ hflat using fun p : C => (hreg p).2.2
  set S : Option C → TopologicalSpace.Opens M := fun o => match o with
    | none => ⟨Cᶜ, hC.1.isOpen_compl⟩
    | some p => ⟨flatDomain (Φ p), isOpen_flatDomain _⟩ with hS
  have hcover : ∀ y, ∃ o, y ∈ S o := fun y => by
    by_cases hy : y ∈ C
    · exact ⟨some ⟨y, hy⟩, mem_flatDomain_self (Φ ⟨y, hy⟩)⟩
    · exact ⟨none, hy⟩
  obtain ⟨m, χ, idx, hs, hnn, hsupp, -, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  exact ⟨⟨kdim, Φ, hsrc, fun p => hflat p, m, χ, idx, hs, hnn, hsum,
    fun a h => by have := hsupp a; rw [h] at this; exact this,
    fun a p h => by have := hsupp a; rw [h] at this; exact this⟩⟩

namespace BlanchardData

variable {C : Set M} (D : BlanchardData n C)

/-- The normal part `N_a`. -/
def normalWeight (a : Fin D.m) (y : M) : ℝ :=
  match D.center a with
  | none => 1
  | some p => ∑ i : Fin n,
      if D.kdim p ≤ i.1 then Complex.normSq (flatCoord (D.flat p) i y) else 0

/-- **The Blanchard weight** `U = ∑_a χ_a N_a`. -/
def weight (y : M) : ℝ := ∑ a, D.χ a y * D.normalWeight a y

theorem normalWeight_nonneg (a : Fin D.m) (y : M) : 0 ≤ D.normalWeight a y := by
  unfold normalWeight
  split
  · exact zero_le_one
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]

theorem weight_nonneg (y : M) : 0 ≤ D.weight y :=
  Finset.sum_nonneg fun a _ => mul_nonneg (D.nonneg a y) (D.normalWeight_nonneg a y)

theorem χ_eq_zero_of_notMem {a : Fin D.m} {y : M} (hy : y ∉ tsupport (D.χ a)) : D.χ a y = 0 :=
  image_eq_zero_of_notMem_tsupport hy

theorem weight_eq_zero_of_mem {y : M} (hy : y ∈ C) : D.weight y = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  unfold normalWeight
  split
  · next h => exact mul_eq_zero_of_left (D.χ_eq_zero_of_notMem fun h' => D.supp_none a h h' hy) _
  · next p h =>
    by_cases hf : y ∈ flatDomain (D.flat p)
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
      split_ifs with hi
      · have := ((D.flat_eq p hf.1 hf.2).mp hy) i hi
        simp [flatCoord, this]
      · rfl
    · exact mul_eq_zero_of_left (D.χ_eq_zero_of_notMem fun h' => hf (D.supp_some a p h h')) _

theorem weight_pos_of_notMem {y : M} (hy : y ∉ C) : 0 < D.weight y := by
  classical
  obtain ⟨a, -, ha⟩ : ∃ a ∈ Finset.univ, 0 < D.χ a y := by
    by_contra h
    push Not at h
    have : ∑ a, D.χ a y ≤ 0 := Finset.sum_nonpos fun a _ => h a (Finset.mem_univ a)
    rw [D.sum_one] at this
    exact absurd this (by norm_num)
  have hN : 0 < D.normalWeight a y := by
    unfold normalWeight
    split
    · exact zero_lt_one
    · next p h =>
      have hf : y ∈ flatDomain (D.flat p) := D.supp_some a p h (subset_tsupport _ ha.ne')
      have hnot := mt (D.flat_eq p hf.1 hf.2).mpr hy
      simp only [complexCoordinatePlane, mem_ofPred_eq, not_forall] at hnot
      obtain ⟨i, hi, hne⟩ := hnot
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i : Fin n =>
        if D.kdim p ≤ i.1 then Complex.normSq (flatCoord (D.flat p) i y) else 0)
        (fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]) (Finset.mem_univ i))
      simp only [if_pos hi]
      exact Complex.normSq_pos.mpr hne
  exact lt_of_lt_of_le (mul_pos ha hN) (Finset.single_le_sum
    (f := fun a => D.χ a y * D.normalWeight a y)
    (fun a _ => mul_nonneg (D.nonneg a y) (D.normalWeight_nonneg a y)) (Finset.mem_univ a))

theorem contDiffAt_normSq_comp {f : ComplexModel n → ℂ} {u : ComplexModel n}
    (hf : ∀ᶠ u' in 𝓝 u, DifferentiableAt ℂ f u') :
    ContDiffAt ℝ ∞ (fun u' => Complex.normSq (f u')) u := by
  obtain ⟨V, hVsub, hV, huV⟩ := mem_nhds_iff.mp hf
  have hc : ContDiffAt ℂ ∞ f u :=
    contDiffAt_of_differentiableOn_complex (fun x hx => (hVsub hx).differentiableWithinAt) hV huV
  have := (contDiff_norm_sq ℝ (E := ℂ)).contDiffAt.comp u (hc.restrict_scalars ℝ)
  simpa [Function.comp_def, Complex.normSq_eq_norm_sq] using this

theorem chartSmooth_weight : ChartSmooth (n := n) D.weight := by
  intro e u hu
  refine ContDiffAt.contDiffWithinAt ?_
  simp only [weight]
  refine ContDiffAt.sum fun a _ => ?_
  have hχ : ContDiffAt ℝ ∞ (fun u' => D.χ a (e.val.symm u')) u :=
    (D.smooth a e).contDiffAt (e.val.open_target.mem_nhds hu)
  unfold normalWeight
  split
  · simpa using hχ
  · next p h =>
    by_cases hf : e.val.symm u ∈ flatDomain (D.flat p)
    · refine hχ.mul (ContDiffAt.sum fun i _ => ?_)
      split_ifs
      · refine contDiffAt_normSq_comp ?_
        have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' flatDomain (D.flat p)) :=
          e.val.isOpen_inter_preimage_symm (isOpen_flatDomain _)
        filter_upwards [hopen.mem_nhds ⟨hu, hf⟩] with u' hu'
        exact mdifferentiableAt_iff_differentiableAt.mp
          ((holomorphicAt_flatCoord (D.flat p) i hu'.2).self_of_nhds.comp u'
            (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hu'.1))
      · exact contDiffAt_const
    · have hcl : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (tsupport (D.χ a))ᶜ) :=
        e.val.isOpen_inter_preimage_symm (isClosed_tsupport _).isOpen_compl
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hcl.mem_nhds ⟨hu, fun h' => hf (D.supp_some a p h h')⟩] with u' hu'
      rw [D.χ_eq_zero_of_notMem hu'.2, zero_mul]

end BlanchardData

end

end Hironaka.BlanchardWeight

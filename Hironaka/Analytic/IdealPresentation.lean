import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.PotentialTheory.AnalyticSingularitiesBasic
import Hironaka.Analytic.ERealChordUSC
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus

set_option autoImplicit false

/-!
# The `O(1)` calculus of ideal weights

Source: Copy-4, `sec:qpsh` (the paragraph on `ψ_𝔞`) and Step 5 of
`prop:principalization` (`transcendental-nakamaye-copy4-20260911`).

The manuscript writes `ψ_𝔞 = log ∑ |g_i|²` for local generators `g_i` of a
coherent ideal `𝔞` and then uses, without comment, the three facts that make
`ψ_𝔞` well defined *up to a bounded function*:

* **monotonicity** — `𝔞 ⊆ 𝔟` implies `ψ_𝔞 ≤ ψ_𝔟 + O(1)` locally;
* **well-definedness** — two presentations of the same ideal differ by `O(1)`;
* **boundedness above** — on a compact manifold `ψ_𝔞 ≤ O(1)`.

Step 5 of `prop:principalization` is, after the geometry is stripped away,
exactly a computation in this calculus: the displayed chain
`ψ_D + χ ≤ … ≤ φ_{Q_M} ∘ π + O(1)` compares finitely many weights by inclusion
of the underlying ideals and discards the rest because they are bounded above.

Everything here is stated for `HasAnalyticSingularitiesOfType φ c 𝔞`
(`FirstPass/GlobalAnalyticSingularities`), i.e. for a *function* presented by an
ideal rather than for the weight itself, so that the results apply verbatim to
the potentials the manuscript manipulates.  The comparison constant is global on
a compact manifold, which is the form Step 5 uses.

The analytic core is finite Cauchy--Schwarz.  Two special cases of it are
already in the tree — `Pending/AnalyticSingularities.generatorLog_le_of_holomorphic_matrix`
(for a normed space, with an explicit global matrix) and
`Pending/QuantitativeRegularizationLocalBergman.generatorLog_le_add_of_generatorNormSq_le`
(for `ComplexModel d`) — but neither applies on a manifold, and neither allows the
number of coefficients to vary with the generator being expanded, which it must
here: `IsInSpanAt` chooses its own finite family for each germ.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealWeightComparison

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities

/-! ### The pointwise inequality -/

section Pointwise

variable {X : Type*}

/-- A positive multiplicative comparison of squared generator norms gives the
corresponding logarithmic comparison.  Stated for an arbitrary type: no
regularity of the generators is used. -/
theorem generatorLog_le_add_of_generatorNormSq_le {N P : ℕ}
    {f : Fin N → X → ℂ} {g : Fin P → X → ℂ} {y : X} {A : ℝ} (hA : 0 < A)
    (hfg : generatorNormSq f y ≤ A * generatorNormSq g y) :
    generatorLog f y ≤ generatorLog g y + (Real.log A : EReal) := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  calc
    ENNReal.log (ENNReal.ofReal (∑ i, ‖f i y‖ ^ 2)) ≤
        ENNReal.log (ENNReal.ofReal (A * ∑ j, ‖g j y‖ ^ 2)) :=
      ENNReal.log_monotone (ENNReal.ofReal_le_ofReal
        (by simpa only [generatorNormSq] using hfg))
    _ = ENNReal.log (ENNReal.ofReal A * ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) := by
      rw [ENNReal.ofReal_mul hA.le]
    _ = ENNReal.log (ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) + (Real.log A : EReal) := by
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hA, add_comm]

/-- `ψ_g` is bounded above by `log A` wherever `∑|gᵢ|² ≤ A`. -/
theorem generatorLog_le_of_generatorNormSq_le {N : ℕ} {f : Fin N → X → ℂ} {y : X}
    {A : ℝ} (hA : 0 < A) (hfy : generatorNormSq f y ≤ A) :
    generatorLog f y ≤ (Real.log A : EReal) := by
  rw [generatorLog_eq_log_sum]
  calc ENNReal.log (ENNReal.ofReal (∑ i, ‖f i y‖ ^ 2))
      ≤ ENNReal.log (ENNReal.ofReal A) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal
          (by simpa only [generatorNormSq] using hfy))
    _ = (Real.log A : EReal) := ENNReal.log_ofReal_of_pos hA

/-- Composing the generators with `f` composes their weight with `f`. -/
theorem generatorLog_comp {W : Type*} {N : ℕ} (g : Fin N → X → ℂ) (f : W → X) (y : W) :
    generatorLog (fun i => g i ∘ f) y = generatorLog g (f y) := rfl

/-- Each member of a family is dominated by the whole family. -/
theorem norm_sq_le_generatorNormSq {P : ℕ} (h : Fin P → X → ℂ) (y : X) (j : Fin P) :
    ‖h j y‖ ^ 2 ≤ generatorNormSq h y :=
  Finset.single_le_sum (f := fun j : Fin P => ‖h j y‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- A family whose members are all taken from `h` — repetitions allowed, and with
no relation between the two index sets — is dominated by `h` with the constant
given by its own cardinality. -/
theorem generatorNormSq_le_of_forall_eq {K P : ℕ} {s : Fin K → X → ℂ}
    {h : Fin P → X → ℂ} {y : X} (hs : ∀ k, ∃ j, s k y = h j y) :
    generatorNormSq s y ≤ (K : ℝ) * generatorNormSq h y := by
  have hterm : ∀ k : Fin K, ‖s k y‖ ^ 2 ≤ generatorNormSq h y := by
    intro k
    obtain ⟨j, hj⟩ := hs k
    rw [hj]
    exact norm_sq_le_generatorNormSq h y j
  calc generatorNormSq s y = ∑ k, ‖s k y‖ ^ 2 := rfl
    _ ≤ ∑ _k : Fin K, generatorNormSq h y := Finset.sum_le_sum fun k _ => hterm k
    _ = (K : ℝ) * generatorNormSq h y := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- **Finite Cauchy--Schwarz.**  A holomorphic combination of members of `h` is
dominated by `h`, with a constant read off from the coefficients at the point.
The coefficient family is indexed independently of `h`. -/
theorem norm_sq_le_of_eq_sum {K P : ℕ} {a s : Fin K → X → ℂ} {h : Fin P → X → ℂ}
    {y : X} {v : ℂ} (hs : ∀ k, ∃ j, s k y = h j y)
    (heq : v = ∑ k, a k y * s k y) :
    ‖v‖ ^ 2 ≤ ((∑ k, ‖a k y‖ ^ 2) * (K : ℝ)) * generatorNormSq h y := by
  have hcs : ‖v‖ ^ 2 ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 := by
    rw [heq]
    calc
      ‖∑ k, a k y * s k y‖ ^ 2 ≤ (∑ k, ‖a k y * s k y‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ = (∑ k, ‖a k y‖ * ‖s k y‖) ^ 2 := by simp_rw [norm_mul]
      _ ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hcoeff : (0 : ℝ) ≤ ∑ k, ‖a k y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖v‖ ^ 2 ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 := hcs
    _ ≤ (∑ k, ‖a k y‖ ^ 2) * ((K : ℝ) * generatorNormSq h y) :=
      mul_le_mul_of_nonneg_left (generatorNormSq_le_of_forall_eq hs) hcoeff
    _ = ((∑ k, ‖a k y‖ ^ 2) * (K : ℝ)) * generatorNormSq h y := by ring

end Pointwise

/-! ### Local domination by a family -/

section Dominated

variable {X : Type*} [TopologicalSpace X]

/-- `v` is **locally dominated** by the family `g` at `x`: `|v|² ≤ B ∑ⱼ|gⱼ|²` on a
neighbourhood of `x`, for some `B > 0`.  This is the quantitative shadow of "the
germ of `v` at `x` lies in the ideal generated by `g`", and it is what a
comparison of weights actually consumes: it is stable under holomorphic
combinations and under composition with a continuous map, neither of which is
visible at the level of `IsInSpanAt`. -/
def DominatedAt {P : ℕ} (g : Fin P → X → ℂ) (x : X) (v : X → ℂ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, ‖v y‖ ^ 2 ≤ B * generatorNormSq g y

/-- A member of the family is dominated by it. -/
theorem dominatedAt_of_eq {P : ℕ} {g : Fin P → X → ℂ} {x : X} {v : X → ℂ}
    (hv : ∃ j, v = g j) : DominatedAt g x v := by
  obtain ⟨j, rfl⟩ := hv
  exact ⟨1, one_pos, Filter.Eventually.of_forall fun y => by
    simpa using norm_sq_le_generatorNormSq g y j⟩

/-- **Domination is stable under holomorphic combinations.**  The coefficients
only need to be continuous at the point, and the number of them is arbitrary. -/
theorem DominatedAt.sum {P K : ℕ} {g : Fin P → X → ℂ} {x : X}
    {a s : Fin K → X → ℂ} {v : X → ℂ}
    (ha : ∀ k, ContinuousAt (a k) x) (hs : ∀ k, DominatedAt g x (s k))
    (heq : v =ᶠ[𝓝 x] fun y => ∑ k, a k y * s k y) :
    DominatedAt g x v := by
  choose B hB hBy using hs
  set A : ℝ := (∑ k, ‖a k x‖ ^ 2) + 1 with hAdef
  have hA : 0 < A := by
    have : (0 : ℝ) ≤ ∑ k, ‖a k x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hSB : (0 : ℝ) ≤ ∑ k, B k := Finset.sum_nonneg fun k _ => (hB k).le
  have hcont : ContinuousAt (fun y => ∑ k, ‖a k y‖ ^ 2) x :=
    tendsto_finsetSum _ fun k _ => ((ha k).norm).pow 2
  have hAy : ∀ᶠ y in 𝓝 x, (∑ k, ‖a k y‖ ^ 2) ≤ A :=
    (hcont.eventually_lt continuousAt_const (by rw [hAdef]; exact lt_add_one _)).mono
      fun _ hy => hy.le
  have hpos : 0 < A * (∑ k, B k) + 1 := by nlinarith
  refine ⟨A * (∑ k, B k) + 1, hpos, ?_⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ k, ‖s k y‖ ^ 2 ≤ B k * generatorNormSq g y :=
    eventually_all.mpr hBy
  filter_upwards [heq, hAy, hall] with y hy hyA hyB
  have hQ : (0 : ℝ) ≤ generatorNormSq g y := generatorNormSq_nonneg g y
  have hss : (∑ k, ‖s k y‖ ^ 2) ≤ (∑ k, B k) * generatorNormSq g y := by
    calc (∑ k, ‖s k y‖ ^ 2) ≤ ∑ k, B k * generatorNormSq g y :=
          Finset.sum_le_sum fun k _ => hyB k
      _ = (∑ k, B k) * generatorNormSq g y := by rw [Finset.sum_mul]
  have hssnn : (0 : ℝ) ≤ ∑ k, ‖s k y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : ‖v y‖ ^ 2 ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 := by
    rw [hy]
    calc ‖∑ k, a k y * s k y‖ ^ 2 ≤ (∑ k, ‖a k y * s k y‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
      _ = (∑ k, ‖a k y‖ * ‖s k y‖) ^ 2 := by simp_rw [norm_mul]
      _ ≤ (∑ k, ‖a k y‖ ^ 2) * ∑ k, ‖s k y‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hstep : (∑ k, ‖a k y‖ ^ 2) * (∑ k, ‖s k y‖ ^ 2)
      ≤ A * ((∑ k, B k) * generatorNormSq g y) :=
    mul_le_mul hyA hss hssnn hA.le
  nlinarith

/-- A finite family, each member of which is dominated, is dominated as a
family. -/
theorem exists_nhds_generatorNormSq_le_of_forall_dominatedAt {Q P : ℕ}
    {g : Fin Q → X → ℂ} {h : Fin P → X → ℂ} {x : X}
    (hg : ∀ i, DominatedAt h x (g i)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, generatorNormSq g y ≤ B * generatorNormSq h y := by
  choose B hB hBy using hg
  have hsum : (0 : ℝ) ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => (hB i).le
  refine ⟨(∑ i, B i) + 1, by linarith, ?_⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, ‖g i y‖ ^ 2 ≤ B i * generatorNormSq h y :=
    eventually_all.mpr hBy
  filter_upwards [hall] with y hy
  calc generatorNormSq g y = ∑ i, ‖g i y‖ ^ 2 := rfl
    _ ≤ ∑ i, B i * generatorNormSq h y := Finset.sum_le_sum fun i _ => hy i
    _ = (∑ i, B i) * generatorNormSq h y := by rw [Finset.sum_mul]
    _ ≤ ((∑ i, B i) + 1) * generatorNormSq h y := by
      have := generatorNormSq_nonneg h y
      nlinarith

/-- **The local comparison of weights**, in its domination form. -/
theorem moreSingularAt_generatorLog_of_forall_dominatedAt {Q P : ℕ}
    {g : Fin Q → X → ℂ} {h : Fin P → X → ℂ} {x : X}
    (hg : ∀ i, DominatedAt h x (g i)) :
    MoreSingularAt (generatorLog g) (generatorLog h) x := by
  obtain ⟨B, hB, hBy⟩ := exists_nhds_generatorNormSq_le_of_forall_dominatedAt hg
  exact ⟨Real.log B, hBy.mono fun y hy => generatorLog_le_add_of_generatorNormSq_le hB hy⟩

end Dominated

/-! ### From an inclusion of germs to a local comparison of weights -/

section Germ

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A germ in the span of `h` is dominated by `h`.  This is the only place where
`IsInSpanAt` is unpacked: the coefficients it produces are holomorphic, hence
continuous, and its index set is its own. -/
theorem dominatedAt_of_isInSpanAt {P : ℕ} {h : Fin P → M → ℂ} {v : M → ℂ} {x : M}
    (hv : IsInSpanAt (n := n) (· ∈ range h) x v) : DominatedAt h x v := by
  obtain ⟨-, K, s, a, hs, ha, hsum⟩ := hv
  exact DominatedAt.sum (fun k => (ha k).continuousAt)
    (fun k => dominatedAt_of_eq ((hs k).imp fun _ hj => hj.symm)) hsum

/-- One germ in the span of `h`: `|v|²` is locally dominated by `∑ |hⱼ|²`. -/
theorem exists_nhds_norm_sq_le_of_isInSpanAt {P : ℕ} {h : Fin P → M → ℂ}
    {v : M → ℂ} {x : M} (hv : IsInSpanAt (n := n) (· ∈ range h) x v) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, ‖v y‖ ^ 2 ≤ B * generatorNormSq h y :=
  dominatedAt_of_isInSpanAt hv

/-- A whole finite family in the span of `h` is locally dominated by `h`. -/
theorem exists_nhds_generatorNormSq_le_of_forall_isInSpanAt {Q P : ℕ}
    {g : Fin Q → M → ℂ} {h : Fin P → M → ℂ} {x : M}
    (hg : ∀ i, IsInSpanAt (n := n) (· ∈ range h) x (g i)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, generatorNormSq g y ≤ B * generatorNormSq h y :=
  exists_nhds_generatorNormSq_le_of_forall_dominatedAt
    fun i => dominatedAt_of_isInSpanAt (hg i)

/-- **The local comparison of ideal weights.**  If every member of `g` lies, as a
germ at `x`, in the ideal generated by `h`, then `ψ_g ≤ ψ_h + O(1)` near `x`. -/
theorem moreSingularAt_generatorLog_of_forall_isInSpanAt {Q P : ℕ}
    {g : Fin Q → M → ℂ} {h : Fin P → M → ℂ} {x : M}
    (hg : ∀ i, IsInSpanAt (n := n) (· ∈ range h) x (g i)) :
    MoreSingularAt (generatorLog g) (generatorLog h) x :=
  moreSingularAt_generatorLog_of_forall_dominatedAt
    fun i => dominatedAt_of_isInSpanAt (hg i)

end Germ

/-! ### Globalisation over a compact manifold -/

section Global

variable {X : Type*} [TopologicalSpace X]

/-- A germwise additive comparison with a locally varying constant has, on a
compact space, one global constant.  This is the step the manuscript takes
silently whenever it writes `+O(1)` for a weight on all of `X`. -/
theorem moreSingularOn_univ_of_forall_moreSingularAt [CompactSpace X]
    {u v : X → EReal} (h : ∀ x, MoreSingularAt u v x) :
    MoreSingularOn u v univ := by
  choose C hC using h
  obtain ⟨t, -, hcov⟩ :=
    isCompact_univ.elim_nhds_subcover (fun x => {y | u y ≤ v y + (C x : EReal)})
      (fun x _ => hC x)
  refine ⟨∑ z ∈ t, |C z|, fun y _ => ?_⟩
  obtain ⟨z, hzt, hzy⟩ := mem_iUnion₂.mp (hcov (mem_univ y))
  refine hzy.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  exact (le_abs_self (C z)).trans
    (Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) hzt)

end Global

/-! ### Transfer to the presented functions -/

section Transfer

variable {X : Type*} [TopologicalSpace X]

/-- **Transfer.**  A comparison of generator weights becomes a comparison of the
functions they present, absorbing both bounded remainders into the constant.
The two presentations are germ-level, so they may live on different
neighbourhoods. -/
theorem moreSingularAt_of_moreSingularAt_generatorLog {u u' : X → EReal} {c : ℝ}
    (hc : 0 < c) {N P : ℕ} {g : Fin N → X → ℂ} {h : Fin P → X → ℂ} {x : X}
    {R R' : X → ℝ} {C₀ C₀' : ℝ}
    (hueq : ∀ᶠ y in 𝓝 x, u y = (c : EReal) * generatorLog g y + (R y : EReal))
    (hu'eq : ∀ᶠ y in 𝓝 x, u' y = (c : EReal) * generatorLog h y + (R' y : EReal))
    (hRb : ∀ᶠ y in 𝓝 x, R y ≤ C₀) (hR'b : ∀ᶠ y in 𝓝 x, -C₀' ≤ R' y)
    (hlog : MoreSingularAt (generatorLog g) (generatorLog h) x) :
    MoreSingularAt u u' x := by
  obtain ⟨D, hD⟩ := hlog
  refine ⟨c * D + C₀ + C₀', ?_⟩
  filter_upwards [hueq, hu'eq, hRb, hR'b, hD] with y hy hy' hyR hyR' hyD
  rw [hy, hy']
  have hscale : (c : EReal) * generatorLog g y
      ≤ (c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal) := by
    calc (c : EReal) * generatorLog g y
        ≤ (c : EReal) * (generatorLog h y + (D : EReal)) :=
          monotone_eReal_const_mul hc.le hyD
      _ = (c : EReal) * generatorLog h y + (c : EReal) * ((D : ℝ) : EReal) :=
          EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le)
            (EReal.coe_ne_top _) _ _
      _ = (c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal) := by
          rw [← EReal.coe_mul]
  calc (c : EReal) * generatorLog g y + (R y : EReal)
      ≤ ((c : EReal) * generatorLog h y + ((c * D : ℝ) : EReal)) + (R y : EReal) :=
        add_le_add hscale le_rfl
    _ = (c : EReal) * generatorLog h y + ((c * D + R y : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
    _ ≤ (c : EReal) * generatorLog h y
          + ((R' y + (c * D + C₀ + C₀') : ℝ) : EReal) := by
        refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
        linarith
    _ = ((c : EReal) * generatorLog h y + (R' y : EReal))
          + ((c * D + C₀ + C₀' : ℝ) : EReal) := by
        rw [EReal.coe_add, ← add_assoc]

end Transfer

/-! ### Monotonicity, well-definedness and boundedness of ideal weights -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Every generator of a local presentation is a member of the ideal it
presents. -/
theorem mem_of_isPresentation {𝔞 : GermIdeal n M} {U : Set M} (hU : IsOpen U)
    {x : M} (hxU : x ∈ U) {N : ℕ} {g : Fin N → M → ℂ}
    (hgdiff : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U)
    (hgiff : ∀ y ∈ U, ∀ k, 𝔞.mem y k ↔ IsInSpanAt (n := n) (· ∈ range g) y k)
    (i : Fin N) : 𝔞.mem x (g i) := by
  have hhol : HolomorphicAt n (g i) x :=
    Filter.eventually_of_mem (hU.mem_nhds hxU)
      fun y hy => (hgdiff i y hy).mdifferentiableAt (hU.mem_nhds hy)
  refine (hgiff x hxU (g i)).mpr ?_
  exact isInSpanAt_of_eq_mul (S := fun s => s ∈ range g) ⟨i, rfl⟩ hhol
    (holomorphicAt_const 1) (Filter.Eventually.of_forall fun y => (one_mul _).symm)

/-- **Monotonicity of ideal weights, at a point.**  If `𝔞 ⊆ 𝔟` then a function
with analytic singularities of type `(c, 𝔞)` is more singular, up to a bounded
germ, than one of type `(c, 𝔟)`. -/
theorem moreSingularAt_of_le {φ φ' : M → EReal} {c : ℚ} {𝔞 𝔟 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hle : 𝔞.Le 𝔟) (x : M) : MoreSingularAt φ φ' x := by
  obtain ⟨hc, -, hpres⟩ := hφ
  obtain ⟨-, -, hpres'⟩ := hφ'
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff, R', C₀', hR'b, hφ'eq⟩ := hpres' x
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hspan : ∀ i, IsInSpanAt (n := n) (· ∈ range h) x (g i) := fun i =>
    (hhiff x hxU' (g i)).mp
      (hle x (g i) (mem_of_isPresentation hU hxU hgdiff hgiff i))
  exact moreSingularAt_of_moreSingularAt_generatorLog hcR
    (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => hφeq y hy)
    (Filter.eventually_of_mem (hU'.mem_nhds hxU') fun y hy => hφ'eq y hy)
    (Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => (abs_le.mp (hRb y hy)).2)
    (Filter.eventually_of_mem (hU'.mem_nhds hxU') fun y hy => (abs_le.mp (hR'b y hy)).1)
    (moreSingularAt_generatorLog_of_forall_isInSpanAt hspan)

/-- **Monotonicity of ideal weights on a compact manifold**, with one constant.
This is the form Step 5 of `prop:principalization` uses. -/
theorem moreSingularOn_univ_of_le [CompactSpace M] {φ φ' : M → EReal} {c : ℚ}
    {𝔞 𝔟 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔟)
    (hle : 𝔞.Le 𝔟) : MoreSingularOn φ φ' univ :=
  moreSingularOn_univ_of_forall_moreSingularAt (moreSingularAt_of_le hφ hφ' hle)

/-- **`ψ_𝔞` is well defined up to `O(1)`.**  Two functions with analytic
singularities of the *same* type differ by a bounded function on a compact
manifold.  Stated as two additive comparisons, so no difference of possibly
infinite values is formed. -/
theorem sameSingularityTypeOn_univ_of_eq_type [CompactSpace M] {φ φ' : M → EReal}
    {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := n) φ' c 𝔞) :
    SameSingularityTypeOn φ φ' univ :=
  ⟨moreSingularOn_univ_of_le hφ hφ' (fun _ _ hg => hg),
   moreSingularOn_univ_of_le hφ' hφ (fun _ _ hg => hg)⟩

/-- A function with analytic singularities is bounded above near every point:
its generators are continuous, so `ψ_g` is. -/
theorem moreSingularAt_const {φ : M → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) (x : M) :
    MoreSingularAt φ (fun _ => (0 : EReal)) x := by
  obtain ⟨hc, -, hpres⟩ := hφ
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres x
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hgc : ∀ i, ContinuousAt (g i) x := fun i =>
    ((hgdiff i x hxU).mdifferentiableAt (hU.mem_nhds hxU)).continuousAt
  set A : ℝ := generatorNormSq g x + 1 with hAdef
  have hA : 0 < A := by have := generatorNormSq_nonneg g x; linarith
  have hcont : ContinuousAt (fun y => ∑ i, ‖g i y‖ ^ 2) x :=
    tendsto_finsetSum _ fun i _ => ((hgc i).norm).pow 2
  have hAy : ∀ᶠ y in 𝓝 x, generatorNormSq g y ≤ A :=
    (hcont.eventually_lt continuousAt_const (by rw [hAdef]; exact lt_add_one _)).mono
      fun _ hy => hy.le
  refine ⟨(c : ℝ) * Real.log A + C₀, ?_⟩
  filter_upwards [hU.mem_nhds hxU, hAy] with y hyU hyA
  rw [hφeq y hyU, zero_add]
  have h1 : ((c : ℝ) : EReal) * generatorLog g y
      ≤ (((c : ℝ) * Real.log A : ℝ) : EReal) := by
    calc ((c : ℝ) : EReal) * generatorLog g y
        ≤ ((c : ℝ) : EReal) * ((Real.log A : ℝ) : EReal) :=
          monotone_eReal_const_mul hcR.le (generatorLog_le_of_generatorNormSq_le hA hyA)
      _ = (((c : ℝ) * Real.log A : ℝ) : EReal) := by rw [← EReal.coe_mul]
  calc ((c : ℝ) : EReal) * generatorLog g y + (R y : EReal)
      ≤ (((c : ℝ) * Real.log A : ℝ) : EReal) + ((C₀ : ℝ) : EReal) :=
        add_le_add h1 (EReal.coe_le_coe_iff.mpr (abs_le.mp (hRb y hyU)).2)
    _ = (((c : ℝ) * Real.log A + C₀ : ℝ) : EReal) := by rw [← EReal.coe_add]

/-- **A weight is bounded above on a compact manifold**, with one constant.
Step 5 of `prop:principalization` discards five of its terms this way. -/
theorem exists_le_of_hasAnalyticSingularitiesOfType [CompactSpace M]
    {φ : M → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) :
    ∃ C : ℝ, ∀ y, φ y ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ :=
    moreSingularOn_univ_of_forall_moreSingularAt (moreSingularAt_const hφ)
  exact ⟨C, fun y => by simpa using hC y (mem_univ y)⟩

end Ideal

/-! ### Pulling back an ideal weight -/

section Pullback

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel p) Z]
  [IsComplexManifold p Z]

/-- Domination passes to germs pulled back along a map continuous at the
point. -/
theorem DominatedAt.comp {N : ℕ} {g : Fin N → M → ℂ} {v : M → ℂ} {f : Z → M}
    {y : Z} (hv : DominatedAt g (f y) v) (hf : ContinuousAt f y) :
    DominatedAt (fun i => g i ∘ f) y (v ∘ f) := by
  obtain ⟨B, hB, hBy⟩ := hv
  exact ⟨B, hB, hf.eventually hBy⟩

/-- **The weight of a pulled-back ideal** (Copy-4, `sec:qpsh`).  If `φ` presents
`𝔞` on `M` and `φ'` presents `𝔞 𝒪_Z` on `Z`, then `φ ∘ f` and `φ'` have the same
singularity type at every point: locally `ψ_𝔞 ∘ f = ψ_{𝔞 𝒪_Z} + O(1)`.

The case in which `𝔞 𝒪_Z` is invertible is the comparison
`ψ_𝔟 ∘ π = ψ_{G} + O(1)` between the weight of an ideal and that of the divisor
principalizing it, which Step 5 of `prop:principalization` uses three times
(`ψ_{𝔅_M} ∘ π`, `ψ_{𝔅_m} ∘ π` and `ψ_{𝓘_V} ∘ π`).

Both directions are genuine: one says the pullbacks of generators generate, the
other that every generator of the pullback ideal is a holomorphic combination of
them.  Neither requires `f` to be proper, surjective, or a modification. -/
theorem sameSingularityTypeAt_comp_pullback {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {φ' : Z → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := p) φ' c (GermIdeal.pullback f 𝔞))
    (y : Z) : SameSingularityTypeAt (φ ∘ f) φ' y := by
  obtain ⟨hc, hcoh, hpres⟩ := hφ
  obtain ⟨-, -, hpres'⟩ := hφ'
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hφeq⟩ := hpres (f y)
  obtain ⟨U', hU', hyU', P, h, hhdiff, hhiff, R', C₀', hR'b, hφ'eq⟩ := hpres' y
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hfc : ContinuousAt f y := hf.continuous.continuousAt
  have hpre : f ⁻¹' U ∈ 𝓝 y := hfc.preimage_mem_nhds (hU.mem_nhds hxU)
  -- every generator of `𝔞 𝒪_Z` is a holomorphic combination of the `gᵢ ∘ f`
  have hdom1 : ∀ j, DominatedAt (fun i => g i ∘ f) y (h j) := by
    intro j
    obtain ⟨-, K, s, b, hs, hb, hsum⟩ :=
      RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp (mem_of_isPresentation hU' hyU' hhdiff hhiff j)
    refine DominatedAt.sum (fun k => (hb k).continuousAt) (fun k => ?_) hsum
    obtain ⟨a, hamem, hak⟩ := hs k
    rw [hak]
    exact DominatedAt.comp
      (dominatedAt_of_isInSpanAt ((hgiff (f y) hxU a).mp hamem)) hfc
  -- conversely each `gᵢ ∘ f` is a section of `𝔞 𝒪_Z`
  have hdom2 : ∀ i, DominatedAt h y (g i ∘ f) := by
    intro i
    have hmemM : 𝔞.mem (f y) (g i) := mem_of_isPresentation hU hxU hgdiff hgiff i
    have hholgf : HolomorphicAt p (g i ∘ f) y :=
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hmemM).comp_contMDiff
        (Filter.Eventually.of_forall fun z => hf.contMDiffAt)
    exact dominatedAt_of_isInSpanAt ((hhiff y hyU' (g i ∘ f)).mp
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (isInSpanAt_of_eq_mul ⟨g i, hmemM, rfl⟩ hholgf (holomorphicAt_const 1)
          (Filter.Eventually.of_forall fun _ => (one_mul _).symm))))
  have hcompeq : ∀ᶠ y' in 𝓝 y, (φ ∘ f) y'
      = ((c : ℝ) : EReal) * generatorLog (fun i => g i ∘ f) y' + ((R (f y') : ℝ) : EReal) :=
    Filter.eventually_of_mem hpre fun y' hy' => hφeq (f y') hy'
  have hcompR : ∀ᶠ y' in 𝓝 y, R (f y') ≤ C₀ :=
    Filter.eventually_of_mem hpre fun y' hy' => (abs_le.mp (hRb (f y') hy')).2
  have hcompR' : ∀ᶠ y' in 𝓝 y, -C₀ ≤ R (f y') :=
    Filter.eventually_of_mem hpre fun y' hy' => (abs_le.mp (hRb (f y') hy')).1
  have h'eq : ∀ᶠ y' in 𝓝 y, φ' y'
      = ((c : ℝ) : EReal) * generatorLog h y' + (R' y' : EReal) :=
    Filter.eventually_of_mem (hU'.mem_nhds hyU') fun y' hy' => hφ'eq y' hy'
  have h'Rle : ∀ᶠ y' in 𝓝 y, R' y' ≤ C₀' :=
    Filter.eventually_of_mem (hU'.mem_nhds hyU') fun y' hy' => (abs_le.mp (hR'b y' hy')).2
  have h'Rge : ∀ᶠ y' in 𝓝 y, -C₀' ≤ R' y' :=
    Filter.eventually_of_mem (hU'.mem_nhds hyU') fun y' hy' => (abs_le.mp (hR'b y' hy')).1
  exact ⟨moreSingularAt_of_moreSingularAt_generatorLog hcR hcompeq h'eq hcompR h'Rge
      (moreSingularAt_generatorLog_of_forall_dominatedAt hdom2),
    moreSingularAt_of_moreSingularAt_generatorLog hcR h'eq hcompeq h'Rle hcompR'
      (moreSingularAt_generatorLog_of_forall_dominatedAt hdom1)⟩

/-- The same comparison with a single constant, on a compact source. -/
theorem sameSingularityTypeOn_univ_comp_pullback [CompactSpace Z] {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {φ' : Z → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    (hφ' : HasAnalyticSingularitiesOfType (n := p) φ' c (GermIdeal.pullback f 𝔞)) :
    SameSingularityTypeOn (φ ∘ f) φ' univ :=
  ⟨moreSingularOn_univ_of_forall_moreSingularAt
      fun y => (sameSingularityTypeAt_comp_pullback hf hφ hφ' y).1,
   moreSingularOn_univ_of_forall_moreSingularAt
      fun y => (sameSingularityTypeAt_comp_pullback hf hφ hφ' y).2⟩

end Pullback

end

end Hironaka.IdealWeightComparison

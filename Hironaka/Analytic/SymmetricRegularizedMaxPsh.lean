import Hironaka.Analytic.SymmetricRegularizedMax
import Hironaka.Analytic.RegularizedMaxPsh
import Hironaka.Analytic.IdealFunctionMaxGluing
import Hironaka.Analytic.BoundedGlobalTruncation

set_option autoImplicit false

/-!
# The symmetric regularized maximum of plurisubharmonic functions

Extends Demailly's symmetric regularized maximum `M_δ` of `Hironaka.SymmetricRegularizedMax` to
extended-real entries and proves that it preserves plurisubharmonicity and `θ`-plurisubharmonicity
(Demailly, *Complex analytic and differential geometry*, I.5.18; Copy-4, before
`lem:regularization`, `main-Nulllocus.tex:839-850`).

## The extended-real `M_δ`

`ermax δ S t` is `M_δ` over the entries of `S` that are not `-∞`, `-∞` if all of them are, and
`+∞` if some entry is `+∞`.  This is what the integral formula gives with the convention
`-∞ + τ = -∞`: entries equal to `-∞` never attain the maximum under the integral.  So a branch
equal to `-∞` at a point simply drops out there (Copy-4: "on `Z_0` every branch equals `-∞`, so
`(eq:reg-glue)` equals `-∞` there whichever branches are used").

## Plurisubharmonicity

The proof follows `Hironaka.RegularizedMaxPsh` (the binary case), with the two-variable tangent
replaced by the subgradient `SymmetricRegularizedMax.exists_subgradient`:

* **upper semicontinuity** uses monotonicity, translation equivariance and exact independence:
  near a point, the entries that are `-∞` there are below any prescribed level, hence drop out
  of `M_δ` exactly;
* **the submean inequality** comes from an exact affine minorant at every centre: a convex
  combination `∑ λ_i u_i + c` of the finite branches with positive weights, which lies below
  `M_δ(u)` everywhere (subgradient inequality plus exact independence for the branches that
  become `-∞`) and agrees with it at the centre; convex combinations of plurisubharmonic
  functions are plurisubharmonic (`Hironaka.PshConvexCone`), and
  `RegularizedMaxPsh.hasDiscSubmeanOn_of_tangentMinorants` transfers the submean inequality.

Translation equivariance under a real function (`ermax_add_coe`) then moves the statement to a
background form `θ`, exactly as for the ordinary maximum
(`IdealFunctionMaxGluing.thetaPlurisubharmonic_of_locally_finset_sup`).

## Main results

* `discPshOn_ermax`, `plurisubharmonicAt_ermax`, `plurisubharmonicOn_ermax`;
* `thetaPlurisubharmonic_ermax`: `M_δ` of `θ`-PSH functions is `θ`-PSH, no curvature lost;
* `thetaPlurisubharmonic_of_locally_ermax`: a function which near every point is `M_δ` of
  finitely many branches `θ`-PSH on a neighbourhood is `θ`-PSH (the form the gluing uses).
-/

open Set Filter Function
open scoped Topology

namespace Hironaka.SymmetricRegularizedMaxPsh

open Hironaka
open Hironaka.SymmetricRegularizedMax
open Hironaka.RegularizedMaxPsh

noncomputable section

/-! ### Extended-real arithmetic -/

theorem add_coe_eq_top_iff (x : EReal) (c : ℝ) : x + (c : EReal) = ⊤ ↔ x = ⊤ := by
  induction x using EReal.rec with
  | bot => simp
  | coe x => simp only [← EReal.coe_add, EReal.coe_ne_top]
  | top => simp

theorem add_coe_eq_bot_iff (x : EReal) (c : ℝ) : x + (c : EReal) = ⊥ ↔ x = ⊥ := by
  rw [EReal.add_eq_bot_iff]
  simp

theorem toReal_add_coe {x : EReal} (hx : x ≠ ⊤) (hx' : x ≠ ⊥) (c : ℝ) :
    (x + (c : EReal)).toReal = x.toReal + c := by
  rw [EReal.toReal_add hx hx' (EReal.coe_ne_top c) (EReal.coe_ne_bot c), EReal.toReal_coe]

theorem coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem finset_sum_eq_bot {ι : Type*} {s : Finset ι} {f : ι → EReal} {a : ι} (ha : a ∈ s)
    (hfa : f a = ⊥) : ∑ i ∈ s, f i = ⊥ := by
  classical
  rw [← Finset.add_sum_erase s f ha, hfa, EReal.bot_add]

/-! ### The extended-real regularized maximum -/

variable {ι : Type*}

/-- The entries of `S` at which `t` is not `-∞`. -/
def finitePart (S : Finset ι) (t : ι → EReal) : Finset ι :=
  open Classical in S.filter fun i => t i ≠ ⊥

theorem mem_finitePart {S : Finset ι} {t : ι → EReal} {i : ι} :
    i ∈ finitePart S t ↔ i ∈ S ∧ t i ≠ ⊥ := by
  unfold finitePart
  classical
  simp only [Finset.mem_filter]

theorem finitePart_subset (S : Finset ι) (t : ι → EReal) : finitePart S t ⊆ S := fun _ hi =>
  (mem_finitePart.mp hi).1

variable [Fintype ι]

open Classical in
/-- **The extended-real regularized maximum** over `S`: `M_δ` of the finite entries, `-∞` if
all entries are `-∞`, `+∞` if some entry is `+∞`. -/
def ermax (δ : ℝ) (S : Finset ι) (t : ι → EReal) : EReal :=
  if ∃ i ∈ S, t i = ⊤ then ⊤
  else if (finitePart S t).Nonempty then
    ((rmax δ (finitePart S t) fun i => (t i).toReal : ℝ) : EReal)
  else ⊥

theorem ermax_of_finite {δ : ℝ} {S : Finset ι} {t : ι → EReal} (htop : ∀ i ∈ S, t i ≠ ⊤)
    (hF : (finitePart S t).Nonempty) :
    ermax δ S t = ((rmax δ (finitePart S t) fun i => (t i).toReal : ℝ) : EReal) := by
  have : ¬ ∃ i ∈ S, t i = ⊤ := fun ⟨i, hi, h⟩ => htop i hi h
  simp only [ermax, if_neg this, if_pos hF]

theorem ermax_of_bot {δ : ℝ} {S : Finset ι} {t : ι → EReal} (hbot : ∀ i ∈ S, t i = ⊥) :
    ermax δ S t = ⊥ := by
  have h1 : ¬ ∃ i ∈ S, t i = ⊤ := fun ⟨i, hi, h⟩ => by simp [hbot i hi] at h
  have h2 : ¬ (finitePart S t).Nonempty := fun ⟨i, hi⟩ =>
    (mem_finitePart.mp hi).2 (hbot i (mem_finitePart.mp hi).1)
  simp only [ermax, if_neg h1, if_neg h2]

theorem ermax_ne_top {δ : ℝ} {S : Finset ι} {t : ι → EReal} (htop : ∀ i ∈ S, t i ≠ ⊤) :
    ermax δ S t ≠ ⊤ := by
  by_cases hF : (finitePart S t).Nonempty
  · rw [ermax_of_finite htop hF]
    exact EReal.coe_ne_top _
  · have hbot : ∀ i ∈ S, t i = ⊥ := fun i hi => by
      by_contra h
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, h⟩⟩
    rw [ermax_of_bot hbot]
    exact bot_ne_top

/-- On real entries `ermax` is `rmax`. -/
theorem ermax_coe {δ : ℝ} {S : Finset ι} (hS : S.Nonempty) (s : ι → ℝ) :
    ermax δ S (fun i => (s i : EReal)) = ((rmax δ S s : ℝ) : EReal) := by
  have hF : finitePart S (fun i => (s i : EReal)) = S := by
    ext i
    simp only [mem_finitePart, EReal.coe_ne_bot, ne_eq, not_false_eq_true, and_true]
  rw [ermax_of_finite (fun i _ => EReal.coe_ne_top (s i)) (by rw [hF]; exact hS), hF]
  simp only [EReal.toReal_coe]

/-- **`M_δ` dominates each of its entries.** -/
theorem le_ermax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} {t : ι → EReal} {i : ι} (hi : i ∈ S) :
    t i ≤ ermax δ S t := by
  by_cases htop : ∃ k ∈ S, t k = ⊤
  · simp only [ermax, if_pos htop, le_top]
  · push Not at htop
    by_cases hbot : t i = ⊥
    · rw [hbot]
      exact bot_le
    · have hiF : i ∈ finitePart S t := mem_finitePart.mpr ⟨hi, hbot⟩
      rw [ermax_of_finite htop ⟨i, hiF⟩, ← EReal.coe_toReal (htop i hi) hbot]
      exact EReal.coe_le_coe_iff.mpr (le_rmax hδ hiF fun i => (t i).toReal)

/-- **`M_δ ≤ max + δ`.** -/
theorem ermax_le {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} {t : ι → EReal} {c : ℝ}
    (hc : ∀ i ∈ S, t i ≤ (c : EReal)) : ermax δ S t ≤ ((c + δ : ℝ) : EReal) := by
  have htop : ∀ i ∈ S, t i ≠ ⊤ := fun i hi h => by
    have := hc i hi
    rw [h, top_le_iff] at this
    exact EReal.coe_ne_top c this
  by_cases hF : (finitePart S t).Nonempty
  · rw [ermax_of_finite htop hF, EReal.coe_le_coe_iff]
    refine rmax_le hδ hF fun i hi => ?_
    have hi' := mem_finitePart.mp hi
    have := EReal.toReal_le_toReal (hc i hi'.1) hi'.2 (EReal.coe_ne_top c)
    rwa [EReal.toReal_coe] at this
  · have hbot : ∀ i ∈ S, t i = ⊥ := fun i hi => by
      by_contra h
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, h⟩⟩
    rw [ermax_of_bot hbot]
    exact bot_le

/-- **`M_δ` is nondecreasing in each entry.** -/
theorem ermax_mono {δ : ℝ} {S : Finset ι} {t t' : ι → EReal} (h : ∀ i ∈ S, t i ≤ t' i) :
    ermax δ S t ≤ ermax δ S t' := by
  by_cases htop' : ∃ k ∈ S, t' k = ⊤
  · simp only [ermax, if_pos htop', le_top]
  push Not at htop'
  have htop : ∀ i ∈ S, t i ≠ ⊤ := fun i hi => ne_top_of_le_ne_top (htop' i hi) (h i hi)
  by_cases hF : (finitePart S t).Nonempty
  · have hsub : finitePart S t ⊆ finitePart S t' := fun i hi => by
      have hi' := mem_finitePart.mp hi
      exact mem_finitePart.mpr ⟨hi'.1, fun hb => hi'.2 (le_bot_iff.mp (hb ▸ h i hi'.1))⟩
    rw [ermax_of_finite htop hF, ermax_of_finite htop' (hF.mono hsub), EReal.coe_le_coe_iff]
    refine (rmax_mono fun i hi => ?_).trans (rmax_mono_set hsub hF _)
    have hi' := mem_finitePart.mp hi
    exact EReal.toReal_le_toReal (h i hi'.1) hi'.2 (htop' i hi'.1)
  · have hbot : ∀ i ∈ S, t i = ⊥ := fun i hi => by
      by_contra hb
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, hb⟩⟩
    rw [ermax_of_bot hbot]
    exact bot_le

/-- **Translation equivariance**: `M_δ(t + c) = M_δ(t) + c` for a real `c`. -/
theorem ermax_add_coe {δ : ℝ} (hδ : 0 < δ) (S : Finset ι) (t : ι → EReal) (c : ℝ) :
    ermax δ S (fun i => t i + (c : EReal)) = ermax δ S t + (c : EReal) := by
  have hFeq : finitePart S (fun i => t i + (c : EReal)) = finitePart S t := by
    ext i
    simp only [mem_finitePart, ne_eq, add_coe_eq_bot_iff]
  by_cases htop : ∃ k ∈ S, t k = ⊤
  · have htop2 : ∃ k ∈ S, t k + (c : EReal) = ⊤ := by
      obtain ⟨k, hk, h⟩ := htop
      exact ⟨k, hk, (add_coe_eq_top_iff _ c).mpr h⟩
    simp only [ermax, if_pos htop, if_pos htop2, EReal.top_add_coe]
  push Not at htop
  have htop2 : ∀ i ∈ S, t i + (c : EReal) ≠ ⊤ := fun i hi h =>
    htop i hi ((add_coe_eq_top_iff _ c).mp h)
  by_cases hF : (finitePart S t).Nonempty
  · rw [ermax_of_finite htop2 (hFeq ▸ hF), ermax_of_finite htop hF, hFeq, ← EReal.coe_add,
      EReal.coe_eq_coe_iff, ← rmax_add_const hδ hF]
    refine rmax_congr fun i hi => ?_
    have hi' := mem_finitePart.mp hi
    exact toReal_add_coe (htop i hi'.1) hi'.2 c
  · have hbot : ∀ i ∈ S, t i = ⊥ := fun i hi => by
      by_contra hb
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, hb⟩⟩
    have hbot2 : ∀ i ∈ S, t i + (c : EReal) = ⊥ := fun i hi => by rw [hbot i hi, EReal.bot_add]
    rw [ermax_of_bot hbot, ermax_of_bot hbot2, EReal.bot_add]

/-- `ermax` over `S` only sees the entries in `S`. -/
theorem ermax_congr {δ : ℝ} {S : Finset ι} {t t' : ι → EReal} (h : ∀ i ∈ S, t i = t' i) :
    ermax δ S t = ermax δ S t' :=
  le_antisymm (ermax_mono fun i hi => (h i hi).le) (ermax_mono fun i hi => (h i hi).ge)

/-- `ermax = -∞` exactly when every entry is `-∞` (entries `< +∞`). -/
theorem ermax_eq_bot_iff {δ : ℝ} {S : Finset ι} {t : ι → EReal} (htop : ∀ i ∈ S, t i ≠ ⊤) :
    ermax δ S t = ⊥ ↔ ∀ i ∈ S, t i = ⊥ := by
  refine ⟨fun h => ?_, ermax_of_bot⟩
  by_contra hne
  push Not at hne
  obtain ⟨i, hi, hib⟩ := hne
  rw [ermax_of_finite htop ⟨i, mem_finitePart.mpr ⟨hi, hib⟩⟩] at h
  exact EReal.coe_ne_bot _ h

/-! ### A real comparison used twice -/

/-- If every index of `F` outside `G` is beaten by `δ` by an index of `F ∩ G`, then
`M_δ` over `F` is at most `M_δ` over `G`. -/
theorem rmax_le_rmax_of_dominated [DecidableEq ι] {δ : ℝ} {F G : Finset ι} {s : ι → ℝ}
    (hFG : (F ∩ G).Nonempty) (hdom : ∀ i ∈ F, i ∉ G → ∃ j ∈ F ∩ G, s i + δ ≤ s j) :
    rmax δ F s ≤ rmax δ G s := by
  rw [rmax_eq_of_dominated Finset.inter_subset_left hFG fun i hi hiFG =>
    hdom i hi fun hiG => hiFG (Finset.mem_inter.mpr ⟨hi, hiG⟩)]
  exact rmax_mono_set Finset.inter_subset_right hFG s

/-! ### Plurisubharmonicity -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [Fintype ι] in
/-- A finite positive combination of disc-PSH functions is disc-PSH. -/
theorem discPshOn_finset_sum {s : Finset ι} {c : ι → ℝ} {u : ι → E → EReal} {U : Set E}
    (hc : ∀ i ∈ s, 0 < c i) (hu : ∀ i ∈ s, DiscPshOn (u i) U) :
    DiscPshOn (fun y => ∑ i ∈ s, (c i : EReal) * u i y) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have := RegularizedMaxPsh.discPshOn_const (E := E) 0 U
      simpa using this
  | insert a s ha ih =>
      have hrest := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      have hhead := (hu a (Finset.mem_insert_self a s)).const_mul
        (hc a (Finset.mem_insert_self a s))
      have := hhead.add hrest
      simpa only [Finset.sum_insert ha] using this

omit [NormedSpace ℂ E] in
/-- **Upper semicontinuity of `M_δ` of upper semicontinuous functions.** -/
theorem upperSemicontinuousOn_ermax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    {u : ι → E → EReal} {U : Set E} (hu : ∀ i ∈ S, UpperSemicontinuousOn (u i) U)
    (htop : ∀ i ∈ S, ∀ x ∈ U, u i x ≠ ⊤) :
    UpperSemicontinuousOn (fun y => ermax δ S fun i => u i y) U := by
  classical
  intro x hx M hM
  change ermax δ S (fun i => u i x) < M at hM
  by_cases hF : (finitePart S fun i => u i x).Nonempty
  · set F := finitePart S fun i => u i x with hFdef
    set a : ι → ℝ := fun i => (u i x).toReal with hadef
    rw [ermax_of_finite (fun i hi => htop i hi x hx) hF] at hM
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hM
    rw [EReal.coe_lt_coe_iff] at hr1
    set ε : ℝ := r - rmax δ F a with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    obtain ⟨j, hj⟩ := hF
    set b : ι → ℝ := fun i => if i ∈ F then a i + ε else a j - δ with hbdef
    have hev : ∀ᶠ y in 𝓝[U] x, ∀ i ∈ S, u i y < (b i : EReal) := by
      refine (Filter.eventually_all_finset S).mpr fun i hi => hu i hi x hx _ ?_
      show u i x < (b i : EReal)
      by_cases hiF : i ∈ F
      · have hi' := mem_finitePart.mp hiF
        rw [← EReal.coe_toReal (htop i hi x hx) hi'.2]
        simp only [hbdef, if_pos hiF, hadef, EReal.coe_lt_coe_iff]
        linarith
      · have hib : u i x = ⊥ := by
          by_contra hne
          exact hiF (mem_finitePart.mpr ⟨hi, hne⟩)
        rw [hib]
        exact EReal.bot_lt_coe _
    filter_upwards [hev] with y hy
    have hbF : rmax δ F b = rmax δ F a + ε := by
      rw [← rmax_add_const hδ ⟨j, hj⟩]
      exact rmax_congr fun i hi => by simp only [hbdef, if_pos hi]
    have hSF : rmax δ S b = rmax δ F b := by
      refine rmax_eq_of_dominated (finitePart_subset S _) ⟨j, hj⟩ fun i _ hiF => ⟨j, hj, ?_⟩
      have hiF' : i ∉ F := hiF
      simp only [hbdef, if_neg hiF', if_pos hj]
      linarith
    calc ermax δ S (fun i => u i y) ≤ ermax δ S (fun i => (b i : EReal)) :=
          ermax_mono fun i hi => (hy i hi).le
      _ = ((rmax δ S b : ℝ) : EReal) := ermax_coe hS b
      _ = (r : EReal) := by rw [hSF, hbF, hεdef]; congr 1; ring
      _ < M := hr2
  · have hbot : ∀ i ∈ S, u i x = ⊥ := fun i hi => by
      by_contra hb
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, hb⟩⟩
    rw [ermax_of_bot hbot] at hM
    obtain ⟨r, -, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hM
    have hev : ∀ᶠ y in 𝓝[U] x, ∀ i ∈ S, u i y < ((r - δ : ℝ) : EReal) := by
      refine (Filter.eventually_all_finset S).mpr fun i hi => hu i hi x hx _ ?_
      show u i x < ((r - δ : ℝ) : EReal)
      rw [hbot i hi]
      exact EReal.bot_lt_coe _
    filter_upwards [hev] with y hy
    calc ermax δ S (fun i => u i y) ≤ ((r - δ + δ : ℝ) : EReal) :=
          ermax_le hδ fun i hi => (hy i hi).le
      _ = (r : EReal) := by congr 1; ring
      _ < M := hr2

/-- **The exact affine minorant at a centre.**  At `x`, there is a disc-PSH function below
`M_δ(u)` on `U` which agrees with it at `x`. -/
theorem exists_tangentMinorant {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    {u : ι → E → EReal} {U : Set E} (hu : ∀ i ∈ S, DiscPshOn (u i) U) {x : E} (hx : x ∈ U) :
    ∃ g : E → EReal, HasDiscSubmeanOn g U ∧
      (∀ y ∈ U, g y ≤ ermax δ S fun i => u i y) ∧ g x = ermax δ S fun i => u i x := by
  classical
  have htop : ∀ i ∈ S, ∀ y ∈ U, u i y ≠ ⊤ := fun i hi y hy => (hu i hi).ne_top y hy
  by_cases hF : (finitePart S fun i => u i x).Nonempty
  · set F := finitePart S fun i => u i x with hFdef
    set a : ι → ℝ := fun i => (u i x).toReal with hadef
    obtain ⟨lam, hlam0, hlamF, hlam1, hsub⟩ := exists_subgradient hδ hF a
    set P : Finset ι := F.filter fun i => 0 < lam i with hPdef
    have hPF : P ⊆ F := Finset.filter_subset _ _
    have hPS : P ⊆ S := hPF.trans (finitePart_subset S _)
    have hlamP : ∀ i, i ∉ P → lam i = 0 := fun i hiP => by
      by_cases hiF : i ∈ F
      · have : ¬ 0 < lam i := fun h => hiP (Finset.mem_filter.mpr ⟨hiF, h⟩)
        exact le_antisymm (not_lt.mp this) (hlam0 i)
      · exact hlamF i hiF
    have hsumP : ∀ f : ι → ℝ, ∑ i, lam i * f i = ∑ i ∈ P, lam i * f i := fun f => by
      rw [← Finset.sum_subset (Finset.subset_univ P) fun i _ hiP => by rw [hlamP i hiP, zero_mul]]
    have hPne : P.Nonempty := by
      by_contra hP
      rw [Finset.not_nonempty_iff_eq_empty] at hP
      have h := hsumP fun _ => 1
      simp only [mul_one, hP, Finset.sum_empty] at h
      linarith
    obtain ⟨j₀, hj₀⟩ := hPne
    have hfinx : ∀ i ∈ P, u i x = (a i : EReal) := fun i hi =>
      (EReal.coe_toReal (htop i (hPS hi) x hx) (mem_finitePart.mp (hPF hi)).2).symm
    set c₀ : ℝ := rmax δ F a - ∑ i, lam i * a i with hc₀def
    refine ⟨fun y => (∑ i ∈ P, (lam i : EReal) * u i y) + (c₀ : EReal), ?_, ?_, ?_⟩
    · exact ((discPshOn_finset_sum (fun i hi => (Finset.mem_filter.mp hi).2)
        fun i hi => hu i (hPS hi)).add (RegularizedMaxPsh.discPshOn_const c₀ U)).submean
    · intro y hy
      show (∑ i ∈ P, (lam i : EReal) * u i y) + (c₀ : EReal) ≤ _
      by_cases hbot : ∃ i ∈ P, u i y = ⊥
      · obtain ⟨i, hi, hib⟩ := hbot
        have hterm : (lam i : EReal) * u i y = ⊥ := by
          rw [hib, EReal.coe_mul_bot_of_pos (Finset.mem_filter.mp hi).2]
        rw [finset_sum_eq_bot (f := fun i => (lam i : EReal) * u i y) hi hterm, EReal.bot_add]
        exact bot_le
      · push Not at hbot
        set G := finitePart S fun i => u i y with hGdef
        have hPG : P ⊆ G := fun i hi => mem_finitePart.mpr ⟨hPS hi, hbot i hi⟩
        set s' : ι → ℝ := fun i => if u i y = ⊥ then (u j₀ y).toReal - δ else (u i y).toReal
          with hs'def
        have hsP : ∀ i ∈ P, (u i y : EReal) = (s' i : EReal) := fun i hi => by
          simp only [hs'def, if_neg (hbot i hi)]
          exact (EReal.coe_toReal (htop i (hPS hi) y hy) (hbot i hi)).symm
        have hgy : (∑ i ∈ P, (lam i : EReal) * u i y) + (c₀ : EReal)
            = ((rmax δ F a + ∑ i, lam i * (s' i - a i) : ℝ) : EReal) := by
          rw [Finset.sum_congr rfl fun i hi => by rw [hsP i hi]]
          have hc : ∑ i ∈ P, (lam i : EReal) * (s' i : EReal)
              = ((∑ i ∈ P, lam i * s' i : ℝ) : EReal) := by
            rw [coe_finset_sum]
            exact Finset.sum_congr rfl fun i _ => (EReal.coe_mul _ _).symm
          rw [hc, ← EReal.coe_add, EReal.coe_eq_coe_iff, hc₀def, hsumP (fun i => s' i - a i),
            hsumP a]
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        have hj₀G : j₀ ∈ G := hPG hj₀
        rw [hgy, ermax_of_finite (fun i hi => htop i hi y hy) ⟨j₀, hj₀G⟩, EReal.coe_le_coe_iff]
        refine (hsub s').trans ?_
        have hj₀y : u j₀ y ≠ ⊥ := hbot j₀ hj₀
        have hs'j₀ : s' j₀ = (u j₀ y).toReal := by simp only [hs'def, if_neg hj₀y]
        calc rmax δ F s' ≤ rmax δ G s' := by
              refine rmax_le_rmax_of_dominated ⟨j₀, Finset.mem_inter.mpr ⟨hPF hj₀, hj₀G⟩⟩
                fun i hiF hiG => ⟨j₀, Finset.mem_inter.mpr ⟨hPF hj₀, hj₀G⟩, ?_⟩
              have hib : u i y = ⊥ := by
                by_contra hne
                exact hiG (mem_finitePart.mpr ⟨finitePart_subset S _ hiF, hne⟩)
              rw [hs'j₀]
              simp only [hs'def, if_pos hib]
              linarith
          _ = rmax δ G fun i => (u i y).toReal := rmax_congr fun i hi => by
              simp only [hs'def, if_neg (mem_finitePart.mp hi).2]
    · show (∑ i ∈ P, (lam i : EReal) * u i x) + (c₀ : EReal) = _
      rw [ermax_of_finite (fun i hi => htop i hi x hx) ⟨j₀, hPF hj₀⟩,
        Finset.sum_congr rfl fun i hi => by rw [hfinx i hi]]
      have hc : ∑ i ∈ P, (lam i : EReal) * (a i : EReal)
          = ((∑ i ∈ P, lam i * a i : ℝ) : EReal) := by
        rw [coe_finset_sum]
        exact Finset.sum_congr rfl fun i _ => (EReal.coe_mul _ _).symm
      rw [hc, ← EReal.coe_add, EReal.coe_eq_coe_iff, hc₀def, hsumP a]
      ring
  · have hbot : ∀ i ∈ S, u i x = ⊥ := fun i hi => by
      by_contra hb
      exact hF ⟨i, mem_finitePart.mpr ⟨hi, hb⟩⟩
    obtain ⟨i₀, hi₀⟩ := hS
    exact ⟨u i₀, (hu i₀ hi₀).submean, fun y _ => le_ermax (t := fun i => u i y) hδ hi₀,
      by rw [hbot i₀ hi₀, ermax_of_bot hbot]⟩

/-- **`M_δ` of disc-PSH functions is disc-PSH** (Demailly, CADG I.5.18, `N` variables). -/
theorem discPshOn_ermax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    {u : ι → E → EReal} {U : Set E} (hu : ∀ i ∈ S, DiscPshOn (u i) U) :
    DiscPshOn (fun y => ermax δ S fun i => u i y) U :=
  ⟨fun x hx => ermax_ne_top fun i hi => (hu i hi).ne_top x hx,
    upperSemicontinuousOn_ermax hδ hS (fun i hi => (hu i hi).upperSemicontinuousOn)
      fun i hi => (hu i hi).ne_top,
    hasDiscSubmeanOn_of_tangentMinorants fun _ hx => exists_tangentMinorant hδ hS hu hx⟩

/-- **`M_δ` of PSH germs is a PSH germ.** -/
theorem plurisubharmonicAt_ermax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    {u : ι → E → EReal} {x : E} (hu : ∀ i ∈ S, PlurisubharmonicAt (u i) x) :
    PlurisubharmonicAt (fun y => ermax δ S fun i => u i y) x := by
  choose! V hVo hxV hV using hu
  refine ⟨⋂ i ∈ S, V i, isOpen_biInter_finset hVo, mem_iInter₂.mpr hxV,
    discPshOn_ermax hδ hS fun i hi => (hV i hi).mono (biInter_subset_of_mem hi)⟩

/-- **`M_δ` of PSH functions is PSH.** -/
theorem plurisubharmonicOn_ermax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    {u : ι → E → EReal} {U : Set E} (hu : ∀ i ∈ S, PlurisubharmonicOn (u i) U) :
    PlurisubharmonicOn (fun y => ermax δ S fun i => u i y) U :=
  fun x hx => plurisubharmonicAt_ermax hδ hS fun i hi => hu i hi x hx

/-! ### `θ`-plurisubharmonicity -/

section Theta

open Hironaka.AnalyticGluingData
open Hironaka.BoundedGlobalProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`M_δ` of `θ`-PSH functions is `θ`-PSH**, with no loss of curvature. -/
theorem thetaPlurisubharmonic_ermax {θ : SmoothRealForm n M 2} {δ : ℝ} (hδ : 0 < δ)
    {S : Finset ι} (hS : S.Nonempty) {u : ι → M → EReal}
    (hu : ∀ i ∈ S, ThetaPlurisubharmonic θ (u i)) :
    ThetaPlurisubharmonic θ (fun x => ermax δ S fun i => u i x) := by
  intro e z hz
  obtain ⟨i₀, hi₀⟩ := hS
  obtain ⟨W, ρ, hzW, hρ, _⟩ := hu i₀ hi₀ e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hmain := plurisubharmonicOn_ermax hδ ⟨i₀, hi₀⟩ fun i hi =>
    ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hu i hi) e hρ
  have heq : (fun y => chartFunction (fun x => ermax δ S fun i => u i x) e y + (ρ y : EReal))
      = fun y => ermax δ S fun i => chartFunction (u i) e y + (ρ y : EReal) := by
    funext y
    rw [ermax_add_coe hδ]
    rfl
  rw [heq]
  exact hmain

/-- **Gluing by `M_δ`.**  A function which near every point equals `M_δ` of finitely many
branches that are `θ`-PSH on a neighbourhood of that point is `θ`-PSH.  (The analogue of
`IdealFunctionMaxGluing.thetaPlurisubharmonic_of_locally_finset_sup` for `M_δ`.) -/
theorem thetaPlurisubharmonic_of_locally_ermax (θ : ClosedRealOneOneForm n M) {δ : ℝ}
    (hδ : 0 < δ) {Ψ : M → EReal} {b : ι → M → EReal}
    (hloc : ∀ p : M, ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ ∃ J : Finset ι, J.Nonempty ∧
      (∀ j ∈ J, ThetaPlurisubharmonicOn θ.val (b j) N) ∧
      ∀ y ∈ N, Ψ y = ermax δ J fun j => b j y) :
    ThetaPlurisubharmonic θ.val Ψ := by
  intro e z hz
  obtain ⟨N, hN, hpN, J, hJne, hJ, hΨ⟩ := hloc (e.val.symm z)
  obtain ⟨W₀, ρ, hzW₀, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  set W : Set (ComplexModel n) := W₀ ∩ (e.val.target ∩ e.val.symm ⁻¹' N) with hWdef
  have hWopen : IsOpen W := hρ.1.inter (e.val.isOpen_inter_preimage_symm hN)
  refine ⟨W, ρ, ⟨hzW₀, hz, hpN⟩, hρ.mono hWopen inter_subset_left, ?_⟩
  intro y hy
  have hρW : IsSmoothLocalPotential θ.val e W ρ := hρ.mono hWopen inter_subset_left
  have hM : PlurisubharmonicAt
      (fun x => ermax δ J fun j => chartFunction (b j) e x + (ρ x : EReal)) y :=
    plurisubharmonicAt_ermax hδ hJne fun j hj =>
      IdealFunctionMaxGluing.ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential (hJ j hj)
        e hρW hy hy.2.2
  refine hM.congr ?_
  filter_upwards [hWopen.mem_nhds hy] with x hx
  rw [ermax_add_coe hδ]
  simp only [chartFunction]
  rw [hΨ _ hx.2.2]

end Theta

end

end Hironaka.SymmetricRegularizedMaxPsh

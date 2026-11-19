import Hironaka.Analytic.CoherentIdealWeight
import Hironaka.Analytic.CompactCollarCutoff
import Hironaka.Analytic.PotentialTheory.LocalPotentials
import Hironaka.Analytic.MeteredDivisorPositivity
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.ThetaPshIdentityPrinciple
import Hironaka.Analytic.AnalyticGluingData
import Hironaka.Analytic.BoundedSmoothOffPoleMerge
import Hironaka.MarkedIdeal.IdealWeightLowerBound
import Hironaka.Analytic.KahlerDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:ideal-function` by maximum gluing

Source: Copy-4, `lem:ideal-function`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1065-1094`):

> Let `(Z, ω_Z)` be a connected compact Kähler manifold and let `𝔞 ⊆ 𝒪_Z` be a
> nonzero coherent ideal.  There is a quasi-psh function `Ψ_𝔞` on `Z` with
> analytic singularities of type `(1, 𝔞)` which is smooth on the complement of the
> zero locus of `𝔞`.

Copy-4 glues the local weights `ψ_j = log ∑_i |g_{j,i}|²` of a finite cover with a
regularized maximum and the cut-offs of Step 3 of `lem:regularization`.

## Why this module exists

`TN.3.4.DIVISORSIDE`: the correction term of Copy-4 Step 5 is
`χ = ((C-1)/M) Ψ_m ∘ π` with `Ψ_m` from `lem:ideal-function` applied to `𝔧 𝔅_m`
(`eq:def-Psi`), and three fields of
`Copy4StepFiveExceptionalWeightData` (`correction_weight`, `positive_correction`,
`smooth_rho_at_y`) are statements about `χ`.  The project's only weight of a
coherent ideal, `CoherentIdealWeight.IdealPartition.weightLog`, is glued with a
partition of unity *inside* the logarithm and is **not** known to be quasi-psh —
its docstring says so and names the fix: "a maximum over the pieces rather than a
convex combination".  This module is that fix.

## The construction, and how it differs from Copy-4's

We use the plain maximum `Ψ = max_{j : z ∈ V_j} (ψ_j + A χ_j)` instead of the
regularized one.  The boundary argument is Copy-4's: near a point of `∂V_j` the
cut-off `χ_j` vanishes while some `χ_l` equals one, and `ψ_j ≤ ψ_l + C_B` on
`V_j ∩ V_l`, so with `A ≥ C_B` the `j`-th branch never wins there; hence near
every point `Ψ` is the maximum of finitely many branches defined on a whole
neighbourhood, and the maximum of `θ`-PSH functions is `θ`-PSH.  No
Grauert–Remmert extension is needed: the branches are `θ`-PSH *across* the zero
locus, where they equal `-∞`.

What the plain maximum loses is smoothness: it is smooth only where one branch
is alone.  The cover is therefore built around a prescribed point `x₀`, which is
covered by ONE patch only, and the conclusion is smoothness on a neighbourhood of
`x₀` (when `x₀` is off the zero locus).  That is all Copy-4 Step 5 uses: it needs
`χ` smooth near *some* point of `W` off `Supp D` (Step 6), and `x₀` can be chosen
generic on `V` before `D` is known, since `π^{-1}(O) ∩ W` is a nonempty open
subset of `W` and `Supp D ∩ W` is a proper analytic subset.  This is a WEAKER
conclusion than Copy-4's lemma, and is labelled as such.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealFunctionMaxGluing

open Hironaka Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  IdealWeightComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Gluing `θ`-PSH branches by a finite maximum -/

/-- A `θ`-PSH-on-`Ω` function is PSH against **every** smooth local potential of
`θ`, at every chart point lying over `Ω`. -/
theorem ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential
    {θ : SmoothRealForm n M 2} {u : M → EReal} {Ω : Set M}
    (hu : ThetaPlurisubharmonicOn θ u Ω) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) {z : ComplexModel n} (hzW : z ∈ W)
    (hzΩ : e.val.symm z ∈ Ω) :
    PlurisubharmonicAt (fun y => chartFunction u e y + (ρ y : EReal)) z := by
  obtain ⟨V, σ, hzV, hσ, hpσ⟩ := hu e z (hρ.2.1 hzW) hzΩ
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  have hpρ : PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) (W ∩ V) :=
    (_root_.Hironaka.PotentialTheory.GlobalPotentials.smoothLocalPotential_psh_iff θ e (W ∩ V) ρ σ (hρ.mono hWV inter_subset_left)
      (hσ.mono hWV inter_subset_right) (chartFunction u e)).mpr
      (hpσ.mono inter_subset_right)
  exact hpρ z ⟨hzW, hzV⟩

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Adding a real number commutes with a finite supremum in `EReal`. -/
theorem finset_sup_add_coe {ι : Type*} (s : Finset ι) (f : ι → EReal) (r : ℝ) :
    s.sup f + (r : EReal) = s.sup fun j => f j + (r : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ← ih]
      exact (max_add_add_right (f a) (s.sup f) (r : EReal)).symm

/-- A finite supremum of functions PSH at a point is PSH there (the empty
supremum is the constant `⊥`, which is PSH in this development). -/
theorem plurisubharmonicAt_finset_sup {ι : Type*} (s : Finset ι)
    {f : ι → ComplexModel n → EReal} {z : ComplexModel n}
    (hf : ∀ j ∈ s, PlurisubharmonicAt (f j) z) :
    PlurisubharmonicAt (fun y => s.sup fun j => f j y) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using plurisubharmonicAt_const (⊥ : EReal) bot_ne_top z
  | insert a s ha ih =>
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sup_insert]
      exact h1.max h2

/-- **Gluing by a finite maximum.**  If near every point `Ψ` coincides with the
maximum of finitely many branches, each `θ`-PSH on that neighbourhood, then `Ψ`
is `θ`-PSH. -/
theorem thetaPlurisubharmonic_of_locally_finset_sup {ι : Type*}
    (θ : ClosedRealOneOneForm n M) {Ψ : M → EReal} {b : ι → M → EReal}
    (hloc : ∀ p : M, ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ ∃ J : Finset ι,
      (∀ j ∈ J, ThetaPlurisubharmonicOn θ.val (b j) N) ∧
      ∀ y ∈ N, Ψ y = J.sup fun j => b j y) :
    ThetaPlurisubharmonic θ.val Ψ := by
  intro e z hz
  obtain ⟨N, hN, hpN, J, hJ, hΨ⟩ := hloc (e.val.symm z)
  obtain ⟨W₀, ρ, hzW₀, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  set W : Set (ComplexModel n) := W₀ ∩ (e.val.target ∩ e.val.symm ⁻¹' N) with hWdef
  have hWopen : IsOpen W := hρ.1.inter (e.val.isOpen_inter_preimage_symm hN)
  refine ⟨W, ρ, ⟨hzW₀, hz, hpN⟩, hρ.mono hWopen inter_subset_left, ?_⟩
  intro y hy
  have hρW : IsSmoothLocalPotential θ.val e W ρ := hρ.mono hWopen inter_subset_left
  have hsup : PlurisubharmonicAt
      (fun x => J.sup fun j => chartFunction (b j) e x + (ρ x : EReal)) y :=
    plurisubharmonicAt_finset_sup J fun j hj =>
      ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential (hJ j hj) e hρW hy hy.2.2
  refine hsup.congr ?_
  filter_upwards [hWopen.mem_nhds hy] with x hx
  rw [← finset_sup_add_coe]
  simp only [chartFunction]
  rw [hΨ _ hx.2.2]

/-! ### The branches `ψ_j + A χ_j` -/

/-- **A branch is `θ`-PSH on its generator domain.**  If `h` is a real function
which is `θ`-PSH (as an `EReal` function) and `g` is a finite family holomorphic
on the open set `T`, then `log ∑ |g_i|² + h` is `θ`-PSH over `T`.  The
logarithm is PSH across the common zeros of `g`, where it equals `-∞`. -/
theorem thetaPlurisubharmonicOn_generatorLog_add {θ : SmoothRealForm n M 2}
    {h : M → ℝ} (hh : ThetaPlurisubharmonic θ fun x => (h x : EReal))
    {T : Set M} (hT : IsOpen T) {N : ℕ} {g : Fin N → M → ℂ}
    (hg : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) T) :
    ThetaPlurisubharmonicOn θ (fun x => generatorLog g x + (h x : EReal)) T := by
  intro e z hz hzT
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hh e z hz
  set D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' T with hDdef
  have hD : IsOpen D := e.val.isOpen_inter_preimage_symm hT
  have hW' : IsOpen (W ∩ D) := hρ.1.inter hD
  refine ⟨W ∩ D, ρ, ⟨hzW, hz, hzT⟩, hρ.mono hW' inter_subset_left, ?_⟩
  intro y hy
  have hgen : HolomorphicGeneratorsAt (fun i w => g i (e.val.symm w)) y :=
    ⟨D, hD, hy.2, fun i => MeteredDivisorPositivity.differentiableOn_comp_chartSymm e (hg i)⟩
  have h1 : PlurisubharmonicAt
      (fun w => generatorLog (fun i w => g i (e.val.symm w)) w) y := by
    have := plurisubharmonicAt_scaled_generatorLog hgen one_pos
    simpa [EReal.coe_one, one_mul] using this
  have h2 := hp y hy.1
  refine (h1.add h2).congr (Eventually.of_forall fun w => ?_)
  simp only [chartFunction]
  rw [add_assoc]
  rfl

/-- **The cut-off term.**  A chart-smooth `χ` with `ddᶜχ + Cω ≥ 0` gives, for
`A ≥ 0`, the `(A C ω)`-PSH function `A χ`. -/
theorem thetaPlurisubharmonic_const_mul_of_ddc_lower (omega : KahlerBackground n M)
    {χ : M → ℝ} (hχ : ChartSmooth (n := n) χ) {C A : ℝ} (hA : 0 ≤ A)
    (hsemi : (ManifoldTubePositivity.ddcClosedForm χ hχ + C • omega.form).val.IsSemipositive) :
    ThetaPlurisubharmonic ((A * C) • omega.form).val fun x => ((A * χ x : ℝ) : EReal) := by
  have hAχ : ChartSmooth (n := n) fun x => A * χ x := fun e => (hχ e).const_smul A
  refine (LocalPotentials.thetaPlurisubharmonic_smooth_iff _ _ hAχ).mpr ?_
  intro e z hz v
  have hs := hsemi e z hz v
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] at hs
  have hddc : smoothDDC (fun y => A * χ (e.val.symm y)) z
      = A • smoothDDC (fun y => χ (e.val.symm y)) z :=
    smoothDDC_smul e.val.open_target (hχ e) A hz
  rw [ClosedRealOneOneForm.coeff_smul, hddc]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at hs ⊢
  rw [ManifoldTubePositivity.ddcClosedForm, SmoothDDCForm.ddcForm_coeff] at hs
  nlinarith [mul_nonneg hA hs]

/-! ### Uniform comparison of two generator families on a compact set -/

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A germwise additive comparison at every point of a compact set has one
constant on that set. -/
theorem exists_le_add_of_isCompact {u v : M → EReal} {K : Set M} (hK : IsCompact K)
    (h : ∀ x ∈ K, MoreSingularAt u v x) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, u y ≤ v y + (C : EReal) := by
  classical
  choose! C hC using h
  obtain ⟨t, htK, hcov⟩ :=
    hK.elim_nhds_subcover (fun x => {y | u y ≤ v y + (C x : EReal)}) (fun x hx => hC x hx)
  refine ⟨∑ z ∈ t, |C z|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun y hy => ?_⟩
  obtain ⟨z, hzt, hzy⟩ := mem_iUnion₂.mp (hcov hy)
  refine hzy.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  exact (le_abs_self (C z)).trans
    (Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) hzt)

/-! ### The cover -/

variable (n M) in
/-- A finite cover adapted to gluing the local weights of `𝔞` by a maximum:
generator domains `T j`, open `V j` with `closure (V j) ⊆ T j`, cores `U j`
covering `M`, and chart-smooth cut-offs `χ j` equal to `1` on `U j` with
`tsupport (χ j) ⊆ V j`. -/
structure GluingCover (𝔞 : GermIdeal n M) (ι : Type*) [Fintype ι] where
  T : ι → Set M
  isOpen_T : ∀ j, IsOpen (T j)
  arity : ι → ℕ
  gen : (j : ι) → Fin (arity j) → M → ℂ
  gen_mdifferentiableOn : ∀ j i,
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (gen j i) (T j)
  gen_spec : ∀ j, ∀ y ∈ T j, ∀ f,
    𝔞.mem y f ↔ IsInSpanAt (n := n) (· ∈ range (gen j)) y f
  V : ι → Set M
  isOpen_V : ∀ j, IsOpen (V j)
  closure_V_subset : ∀ j, closure (V j) ⊆ T j
  U : ι → Set M
  isOpen_U : ∀ j, IsOpen (U j)
  cover : ∀ y, ∃ j, y ∈ U j
  χ : ι → M → ℝ
  χ_smooth : ∀ j, ChartSmooth (n := n) (χ j)
  χ_nonneg : ∀ j y, 0 ≤ χ j y
  χ_le_one : ∀ j y, χ j y ≤ 1
  χ_eq_one : ∀ j, ∀ y ∈ U j, χ j y = 1
  tsupport_χ_subset : ∀ j, tsupport (χ j) ⊆ V j

namespace GluingCover

variable {𝔞 : GermIdeal n M} {ι : Type*} [Fintype ι] (P : GluingCover n M 𝔞 ι)

theorem U_subset_V (j : ι) : P.U j ⊆ P.V j := fun y hy =>
  P.tsupport_χ_subset j (subset_tsupport _
    (Function.mem_support.mpr (by rw [P.χ_eq_one j y hy]; exact one_ne_zero)))

/-- Two generator families of the cover are comparable on the overlap of their
patches: `ψ_j ≤ ψ_l + C_B` on `V j ∩ V l`, with one constant for all pairs. -/
theorem exists_generatorLog_le [CompactSpace M] :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal) := by
  classical
  have hpair : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ closure (P.V j) ∩ closure (P.V l),
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (C : EReal) := by
    intro j l
    refine exists_le_add_of_isCompact
      ((isClosed_closure.inter isClosed_closure).isCompact) fun x hx => ?_
    have hxj : x ∈ P.T j := P.closure_V_subset j hx.1
    have hxl : x ∈ P.T l := P.closure_V_subset l hx.2
    refine moreSingularAt_generatorLog_of_forall_isInSpanAt (n := n) fun i => ?_
    refine (P.gen_spec l x hxl _).mp ((P.gen_spec j x hxj _).mpr ?_)
    refine isInSpanAt_of_eq_mul ⟨i, rfl⟩ ?_ (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
    filter_upwards [(P.isOpen_T j).mem_nhds hxj] with z hz
    exact (P.gen_mdifferentiableOn j i z hz).mdifferentiableAt ((P.isOpen_T j).mem_nhds hz)
  choose C hC0 hC using hpair
  refine ⟨∑ j, ∑ l, C j l, Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hC0 j l,
    fun j l y hy => ?_⟩
  refine (hC j l y ⟨subset_closure hy.1, subset_closure hy.2⟩).trans
    (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  calc C j l ≤ ∑ l', C j l' :=
        Finset.single_le_sum (f := fun l' => C j l') (fun l' _ => hC0 j l') (Finset.mem_univ l)
    _ ≤ ∑ j', ∑ l', C j' l' :=
        Finset.single_le_sum (f := fun j' => ∑ l', C j' l')
          (fun j' _ => Finset.sum_nonneg fun l' _ => hC0 j' l') (Finset.mem_univ j)

/-- The `j`-th branch `ψ_j + A χ_j`. -/
def branch (A : ℝ) (j : ι) (y : M) : EReal :=
  generatorLog (P.gen j) y + ((A * P.χ j y : ℝ) : EReal)

open Classical in
/-- **The glued function** `Ψ = max_{j : y ∈ V j} (ψ_j + A χ_j)`. -/
def glue (A : ℝ) (y : M) : EReal :=
  Finset.univ.sup fun j => if y ∈ P.V j then P.branch A j y else ⊥

open Classical in
/-- **Near every point the glued function is the maximum of the branches whose
patch contains that point.**  The other branches drop out because their cut-off
vanishes near the point while the cut-off of a patch whose core contains the
point equals one, and `A ≥ C_B`. -/
theorem exists_nhds_glue_eq {A CB : ℝ} (hA : CB ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal)) (p : M) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ (∀ j, p ∈ P.V j → N ⊆ P.V j) ∧
      ∀ y ∈ N, P.glue A y = Finset.univ.sup fun j => if p ∈ P.V j then P.branch A j y else ⊥ := by
  obtain ⟨l, hpl⟩ := P.cover p
  set N : Set M := (⋂ j, if p ∈ P.V j then P.V j else (tsupport (P.χ j))ᶜ) ∩ P.U l with hNdef
  have hN : IsOpen N := by
    refine (isOpen_iInter_of_finite fun j => ?_).inter (P.isOpen_U l)
    split_ifs
    · exact P.isOpen_V j
    · exact (isClosed_tsupport _).isOpen_compl
  have hpN : p ∈ N := by
    refine ⟨mem_iInter.mpr fun j => ?_, hpl⟩
    split_ifs with h
    · exact h
    · exact fun ht => h (P.tsupport_χ_subset j ht)
  have hNV : ∀ j, p ∈ P.V j → N ⊆ P.V j := fun j hj y hy => by
    have := mem_iInter.mp hy.1 j
    rwa [if_pos hj] at this
  refine ⟨N, hN, hpN, hNV, fun y hy => le_antisymm ?_ ?_⟩
  · refine Finset.sup_le fun j _ => ?_
    by_cases hyj : y ∈ P.V j
    · rw [if_pos hyj]
      by_cases hpj : p ∈ P.V j
      · refine le_trans ?_ (Finset.le_sup (f := fun j => if p ∈ P.V j then P.branch A j y else ⊥)
          (Finset.mem_univ j))
        simp only [if_pos hpj, le_refl]
      · -- the `j`-th cut-off vanishes at `y`, the `l`-th equals one
        have hyt : y ∉ tsupport (P.χ j) := by
          have := mem_iInter.mp hy.1 j
          rwa [if_neg hpj] at this
        have hχj : P.χ j y = 0 := image_eq_zero_of_notMem_tsupport hyt
        have hχl : P.χ l y = 1 := P.χ_eq_one l y hy.2
        have hpVl : p ∈ P.V l := P.U_subset_V l hpl
        have hyl : y ∈ P.V l := P.U_subset_V l hy.2
        refine le_trans ?_ (Finset.le_sup (f := fun j => if p ∈ P.V j then P.branch A j y else ⊥)
          (Finset.mem_univ l))
        simp only [if_pos hpVl, branch, hχj, hχl, mul_zero, mul_one, EReal.coe_zero, add_zero]
        exact (hcomp j l y ⟨hyj, hyl⟩).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hA))
    · rw [if_neg hyj]
      exact bot_le
  · refine Finset.sup_le fun j _ => ?_
    by_cases hpj : p ∈ P.V j
    · rw [if_pos hpj]
      refine le_trans ?_ (Finset.le_sup (f := fun j => if y ∈ P.V j then P.branch A j y else ⊥)
        (Finset.mem_univ j))
      simp only [if_pos (hNV j hpj hy), le_refl]
    · rw [if_neg hpj]
      exact bot_le

open Classical in
/-- The local identity in `Finset.filter` form, as the gluing lemma consumes it. -/
theorem exists_nhds_glue_eq_filter {A CB : ℝ} (hA : CB ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal)) (p : M) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ (∀ j, p ∈ P.V j → N ⊆ P.V j) ∧
      ∀ y ∈ N, P.glue A y =
        (Finset.univ.filter fun j => p ∈ P.V j).sup fun j => P.branch A j y := by
  obtain ⟨N, hN, hpN, hNV, hglue⟩ := P.exists_nhds_glue_eq hA hcomp p
  refine ⟨N, hN, hpN, hNV, fun y hy => ?_⟩
  rw [hglue y hy, Finset.sup_ite, Finset.sup_bot, sup_bot_eq]

/-- **The glued function is quasi-psh**: with `C` dominating every `ddᶜχ_j` and
`A ≥ C_B`, `A ≥ 0`, it is `(A C ω)`-PSH. -/
theorem thetaPlurisubharmonic_glue (omega : KahlerBackground n M) {A CB C : ℝ}
    (hA0 : 0 ≤ A) (hA : CB ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal))
    (hC : ∀ j, (ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j)
      + C • omega.form).val.IsSemipositive) :
    ThetaPlurisubharmonic ((A * C) • omega.form).val (P.glue A) := by
  classical
  refine thetaPlurisubharmonic_of_locally_finset_sup ((A * C) • omega.form)
    (b := fun j => P.branch A j) fun p => ?_
  obtain ⟨N, hN, hpN, hNV, hglue⟩ := P.exists_nhds_glue_eq_filter hA hcomp p
  refine ⟨N, hN, hpN, Finset.univ.filter fun j => p ∈ P.V j, fun j hj => ?_, hglue⟩
  have hpj : p ∈ P.V j := (Finset.mem_filter.mp hj).2
  have hbr := thetaPlurisubharmonicOn_generatorLog_add
    (thetaPlurisubharmonic_const_mul_of_ddc_lower omega (P.χ_smooth j) hA0 (hC j))
    (P.isOpen_T j) (P.gen_mdifferentiableOn j)
  intro e z hz hzN
  exact hbr e z hz (P.closure_V_subset j (subset_closure (hNV j hpj hzN)))

/-- Sandwich of the glued function between two shifts of one local weight: at
points of `N ⊆ U l` (where the local identity holds), `ψ_l + A ≤ Ψ ≤ ψ_l + A + C_B`. -/
theorem glue_bounds {A CB : ℝ} (hA0 : 0 ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal))
    {l : ι} {y : M} (hy : y ∈ P.U l) :
    generatorLog (P.gen l) y + (A : EReal) ≤ P.glue A y ∧
      P.glue A y ≤ generatorLog (P.gen l) y + ((A + CB : ℝ) : EReal) := by
  classical
  have hyl : y ∈ P.V l := P.U_subset_V l hy
  constructor
  · refine le_trans ?_ (Finset.le_sup (f := fun j => if y ∈ P.V j then P.branch A j y else ⊥)
      (Finset.mem_univ l))
    simp only [if_pos hyl, branch, P.χ_eq_one l y hy, mul_one, le_refl]
  · refine Finset.sup_le fun j _ => ?_
    by_cases hyj : y ∈ P.V j
    · simp only [if_pos hyj, branch]
      have h1 : ((A * P.χ j y : ℝ) : EReal) ≤ (A : EReal) :=
        EReal.coe_le_coe_iff.mpr (mul_le_of_le_one_right hA0 (P.χ_le_one j y))
      calc generatorLog (P.gen j) y + ((A * P.χ j y : ℝ) : EReal)
          ≤ generatorLog (P.gen l) y + (CB : EReal) + (A : EReal) :=
            add_le_add (hcomp j l y ⟨hyj, hyl⟩) h1
        _ = generatorLog (P.gen l) y + ((A + CB : ℝ) : EReal) := by
            rw [add_assoc, add_comm (CB : EReal), ← EReal.coe_add]
    · simp only [if_neg hyj, bot_le]

/-- **The glued function has analytic singularities of type `(1, 𝔞)`.** -/
theorem hasAnalyticSingularitiesOfType_glue (h𝔞 : 𝔞.IsCoherent) {A CB : ℝ} (hA0 : 0 ≤ A)
    (hCB : 0 ≤ CB)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l,
      generatorLog (P.gen j) y ≤ generatorLog (P.gen l) y + (CB : EReal)) :
    HasAnalyticSingularitiesOfType (n := n) (P.glue A) 1 𝔞 := by
  classical
  refine ⟨one_pos, h𝔞, fun x => ?_⟩
  obtain ⟨l, hxl⟩ := P.cover x
  have hUT : P.U l ⊆ P.T l := fun y hy =>
    P.closure_V_subset l (subset_closure (P.U_subset_V l hy))
  refine ⟨P.U l, P.isOpen_U l, hxl, P.arity l, P.gen l,
    fun i => (P.gen_mdifferentiableOn l i).mono hUT,
    fun y hy => P.gen_spec l y (hUT hy),
    fun y => if generatorLog (P.gen l) y = ⊥ then A
      else (P.glue A y - generatorLog (P.gen l) y).toReal,
    A + CB, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨hlow, hup⟩ := P.glue_bounds hA0 hcomp hy
    by_cases hbot : generatorLog (P.gen l) y = ⊥
    · simp only [if_pos hbot]
      rw [abs_of_nonneg hA0]
      linarith
    · simp only [if_neg hbot]
      have htop := generatorLog_ne_top (P.gen l) y
      lift generatorLog (P.gen l) y to ℝ using ⟨htop, hbot⟩ with g hg
      have hgt : P.glue A y ≠ ⊤ :=
        ne_top_of_le_ne_top (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _) hup
      have hgb : P.glue A y ≠ ⊥ :=
        ne_bot_of_le_ne_bot (by rw [← EReal.coe_add]; exact EReal.coe_ne_bot _) hlow
      lift P.glue A y to ℝ using ⟨hgt, hgb⟩ with v hv
      rw [← EReal.coe_add] at hlow
      rw [← EReal.coe_add] at hup
      have h1 := EReal.coe_le_coe_iff.mp hlow
      have h2 := EReal.coe_le_coe_iff.mp hup
      rw [← EReal.coe_sub, EReal.toReal_coe, abs_le]
      constructor <;> linarith
  · obtain ⟨hlow, hup⟩ := P.glue_bounds hA0 hcomp hy
    simp only [Rat.cast_one, EReal.coe_one, one_mul]
    by_cases hbot : generatorLog (P.gen l) y = ⊥
    · simp only [if_pos hbot]
      rw [hbot] at hup ⊢
      rw [EReal.bot_add] at hup ⊢
      exact le_bot_iff.mp hup
    · simp only [if_neg hbot]
      have htop := generatorLog_ne_top (P.gen l) y
      lift generatorLog (P.gen l) y to ℝ using ⟨htop, hbot⟩ with g hg
      have hgt : P.glue A y ≠ ⊤ :=
        ne_top_of_le_ne_top (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _) hup
      have hgb : P.glue A y ≠ ⊥ :=
        ne_bot_of_le_ne_bot (by rw [← EReal.coe_add]; exact EReal.coe_ne_bot _) hlow
      lift P.glue A y to ℝ using ⟨hgt, hgb⟩ with v hv
      rw [← EReal.coe_sub, EReal.toReal_coe, ← EReal.coe_add]
      congr 1
      ring

/-- **Where one patch is alone, the glued function is that patch's branch.** -/
theorem glue_eq_of_isolated {A : ℝ} {j₀ : ι} {O : Set M} (hOU : O ⊆ P.U j₀)
    (hOV : ∀ j, j ≠ j₀ → Disjoint O (P.V j)) {y : M} (hy : y ∈ O) :
    P.glue A y = generatorLog (P.gen j₀) y + (A : EReal) := by
  classical
  have hyV : y ∈ P.V j₀ := P.U_subset_V j₀ (hOU hy)
  refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
  · by_cases hj : j = j₀
    · subst hj
      simp only [if_pos hyV, branch, P.χ_eq_one j y (hOU hy), mul_one, le_refl]
    · have : y ∉ P.V j := fun hyj => Set.disjoint_left.mp (hOV j hj) hy hyj
      simp only [if_neg this, bot_le]
  · refine le_trans ?_ (Finset.le_sup (f := fun j => if y ∈ P.V j then P.branch A j y else ⊥)
      (Finset.mem_univ j₀))
    simp only [if_pos hyV, branch, P.χ_eq_one j₀ y (hOU hy), mul_one, le_refl]

/-- **Smoothness at an isolated point off the zero locus.**  If `x₀` lies in an
open `O ⊆ U j₀` which meets no other patch, and the `j₀`-th generators do not all
vanish at `x₀`, the glued function is smooth near `x₀`. -/
theorem isSmoothNear_glue {A : ℝ} {j₀ : ι} {O : Set M} (hO : IsOpen O) (hOU : O ⊆ P.U j₀)
    (hOV : ∀ j, j ≠ j₀ → Disjoint O (P.V j)) {x₀ : M} (hx₀ : x₀ ∈ O)
    (hne : 0 < generatorNormSq (P.gen j₀) x₀) :
    IsSmoothNear (n := n) (P.glue A) x₀ := by
  have hUT : P.U j₀ ⊆ P.T j₀ := fun y hy =>
    P.closure_V_subset j₀ (subset_closure (P.U_subset_V j₀ hy))
  have hcont : ContinuousOn (generatorNormSq (P.gen j₀)) (P.T j₀) := by
    unfold generatorNormSq
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact ((P.gen_mdifferentiableOn j₀ i).continuousOn.norm).pow 2
  set S : Set M := O ∩ (P.T j₀ ∩ generatorNormSq (P.gen j₀) ⁻¹' Ioi 0) with hSdef
  have hS : IsOpen S := hO.inter (hcont.isOpen_inter_preimage (P.isOpen_T j₀) isOpen_Ioi)
  have hx₀S : x₀ ∈ S := ⟨hx₀, hUT (hOU hx₀), hne⟩
  refine ⟨S, hS, hx₀S, fun y => Real.log (generatorNormSq (P.gen j₀) y) + A, fun e => ?_,
    fun y hy => ?_⟩
  · set D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' S with hDdef
    have hD : IsOpen D := e.val.isOpen_inter_preimage_symm hS
    have hD' : D ⊆ e.val.target ∩ e.val.symm ⁻¹' P.T j₀ := fun z hz => ⟨hz.1, hz.2.2.1⟩
    have hsq : ContDiffOn ℝ ∞ (generatorNormSq fun i z => P.gen j₀ i (e.val.symm z)) D :=
      BoundedSmoothOffPoleMerge.contDiffOn_generatorNormSq hD fun i =>
        (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e
          (P.gen_mdifferentiableOn j₀ i)).mono hD'
    refine ((hsq.log fun z hz => ?_).add contDiffOn_const)
    exact (hz.2.2.2 : 0 < generatorNormSq (P.gen j₀) (e.val.symm z)).ne'
  · have hpos : 0 < generatorNormSq (P.gen j₀) y := hy.2.2
    rw [P.glue_eq_of_isolated hOU hOV hy.1, generatorLog, logNormSq, generatorVector_norm_sq,
      ENNReal.log_ofReal_of_pos hpos, EReal.coe_add]

end GluingCover

/-! ### Constructing the cover -/

/-- **One patch.**  Around a point of an open set `G`: an open core `U`, an open
`V` with `closure V ⊆ G` and `closure U ⊆ V`, and a chart-smooth cut-off with
values in `[0,1]`, equal to `1` on `U`, with `tsupport ⊆ V`. -/
theorem exists_patch {x : M} {G : Set M} (hG : IsOpen G) (hx : x ∈ G) :
    ∃ (U V : Set M) (χ : M → ℝ), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ closure V ⊆ G ∧
      closure U ⊆ V ∧ ChartSmooth (n := n) χ ∧ (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧
      (∀ y ∈ U, χ y = 1) ∧ tsupport χ ⊆ V := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  obtain ⟨V, hV, hxV, hVG, -⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hG (singleton_subset_iff.mpr hx)
  obtain ⟨V', hV', hxV', hV'V, -⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hV hxV
  obtain ⟨U, hU, hxU, hUV', hUc⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hV' hxV'
  obtain ⟨ρ, hρ, hρlow, hρup, ⟨W, -, hUW, hρW⟩, hρoff⟩ :=
    CompactCollarCutoff.exists_chartSmooth_collar (n := n) hUc hV' hUV'
  refine ⟨U, V, fun y => ρ y + 1, hU, hV, singleton_subset_iff.mp hxU, hVG,
    hUV'.trans (subset_closure.trans hV'V), fun e => (hρ e).add contDiffOn_const,
    fun y => by linarith [hρlow y], fun y => by linarith [hρup y],
    fun y hy => by show ρ y + 1 = 1; rw [hρW y (hUW (subset_closure hy))]; ring, ?_⟩
  refine (closure_mono fun y hy => ?_).trans hV'V
  by_contra hyV'
  exact hy (by simp only [hρoff y hyV']; ring)

/-- **The cover, built around a prescribed point.**  `x₀` lies in an open `O`
contained in the core of ONE patch `j₀` and disjoint from every other patch. -/
theorem exists_gluingCover [CompactSpace M] {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (x₀ : M) :
    ∃ (ι : Type) (_ : Fintype ι) (P : GluingCover n M 𝔞 ι) (j₀ : ι) (O : Set M),
      IsOpen O ∧ x₀ ∈ O ∧ O ⊆ P.U j₀ ∧ ∀ j, j ≠ j₀ → Disjoint O (P.V j) := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  choose S hS hmem N g hg hspec using h𝔞
  -- the distinguished patch
  obtain ⟨U₀, V₀, χ₀, hU₀, hV₀, hx₀U₀, hV₀S, hU₀V₀, hχ₀, hχ₀0, hχ₀1, hχ₀U, hχ₀V⟩ :=
    exists_patch (n := n) (hS x₀) (hmem x₀)
  obtain ⟨O, hO, hx₀O, hOU₀, -⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU₀
      (singleton_subset_iff.mpr hx₀U₀)
  -- patches away from `closure O`, covering the complement of `U₀`
  have hG : ∀ x, x ∉ U₀ → IsOpen (S x ∩ (closure O)ᶜ) ∧ x ∈ S x ∩ (closure O)ᶜ :=
    fun x hx => ⟨(hS x).inter isClosed_closure.isOpen_compl, hmem x, fun h => hx (hOU₀ h)⟩
  have hpatch : ∀ x, x ∉ U₀ → ∃ (U V : Set M) (χ : M → ℝ), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧
      closure V ⊆ S x ∩ (closure O)ᶜ ∧ closure U ⊆ V ∧ ChartSmooth (n := n) χ ∧
      (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧ (∀ y ∈ U, χ y = 1) ∧ tsupport χ ⊆ V :=
    fun x hx => exists_patch (n := n) (hG x hx).1 (hG x hx).2
  choose! U V χ hU hV hxU hVS _hUV hχ hχ0 hχ1 hχU hχV using hpatch
  have hK : IsCompact (U₀ᶜ) := hU₀.isClosed_compl.isCompact
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U fun x hx => (hU x hx).mem_nhds (hxU x hx)
  set pt : Fin t.card → M := fun a => (t.equivFin.symm a).val with hpt
  have hptK : ∀ a, pt a ∉ U₀ := fun a => htK _ (t.equivFin.symm a).property
  let ι := Option (Fin t.card)
  let arity : ι → ℕ := fun j => Option.elim j (N x₀) fun a => N (pt a)
  let P : GluingCover n M 𝔞 ι :=
    { T := fun j => Option.elim j (S x₀) fun a => S (pt a)
      isOpen_T := fun j => by cases j <;> simp [hS]
      arity := arity
      gen := fun j => Option.rec (motive := fun j => Fin (arity j) → M → ℂ) (g x₀)
        (fun a => g (pt a)) j
      gen_mdifferentiableOn := fun j => by cases j <;> simp [arity, hg]
      gen_spec := fun j => by
        cases j with
        | none => exact hspec x₀
        | some a => exact hspec (pt a)
      V := fun j => Option.elim j V₀ fun a => V (pt a)
      isOpen_V := fun j => by cases j <;> simp [hV₀, hV _ (hptK _)]
      closure_V_subset := fun j => by
        cases j with
        | none => exact hV₀S
        | some a => exact (hVS _ (hptK a)).trans inter_subset_left
      U := fun j => Option.elim j U₀ fun a => U (pt a)
      isOpen_U := fun j => by cases j <;> simp [hU₀, hU _ (hptK _)]
      cover := fun y => by
        by_cases hy : y ∈ U₀
        · exact ⟨none, hy⟩
        · obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcov hy)
          refine ⟨some (t.equivFin ⟨x, hxt⟩), ?_⟩
          simpa [pt] using hyx
      χ := fun j => Option.elim j χ₀ fun a => χ (pt a)
      χ_smooth := fun j => by cases j <;> simp [hχ₀, hχ _ (hptK _)]
      χ_nonneg := fun j => by cases j <;> simp [hχ₀0, hχ0 _ (hptK _)]
      χ_le_one := fun j => by cases j <;> simp [hχ₀1, hχ1 _ (hptK _)]
      χ_eq_one := fun j => by
        cases j with
        | none => exact hχ₀U
        | some a => exact hχU _ (hptK a)
      tsupport_χ_subset := fun j => by
        cases j with
        | none => exact hχ₀V
        | some a => exact hχV _ (hptK a) }
  refine ⟨ι, inferInstance, P, none, O, hO, singleton_subset_iff.mp hx₀O,
    subset_closure.trans hOU₀, fun j hj => ?_⟩
  cases j with
  | none => exact absurd rfl hj
  | some a =>
      refine Set.disjoint_left.mpr fun y hyO hyV => ?_
      have := hVS _ (hptK a) (subset_closure hyV)
      exact this.2 (subset_closure hyO)

/-! ### `lem:ideal-function` -/

/-- **Copy-4 `lem:ideal-function`, maximum-gluing form.**  On a compact complex
manifold with a Kähler background, for every coherent ideal `𝔞` and every point
`x₀` there are `Ψ` and `c > 0` such that

* `Ψ` is `(c ω)`-PSH, i.e. `ddᶜΨ ≥ -c ω` (the `c_Ψ` of `eq:def-Psi`);
* `Ψ` has analytic singularities of type `(1, 𝔞)`;
* if `x₀ ∉ Z(𝔞)`, then `Ψ` is smooth near `x₀` and finite at `x₀`.

Copy-4 asserts smoothness on all of `X \ Z(𝔞)`; this form gives it near the
prescribed point only (see the module docstring for why that is what Step 5
uses).  No hypothesis on `𝔞` beyond coherence: for the zero ideal `Ψ ≡ -∞` is
allowed (`⊥` is PSH in this development), which is why finiteness at `x₀` and
nondegeneracy are stated separately, under `x₀ ∉ Z(𝔞)`. -/
theorem exists_idealFunction [CompactSpace M] (omega : KahlerBackground n M)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (x₀ : M) :
    ∃ (Ψ : M → EReal) (c : ℝ), 0 < c ∧
      ThetaPlurisubharmonic (c • omega.form).val Ψ ∧
      HasAnalyticSingularitiesOfType (n := n) Ψ 1 𝔞 ∧
      (x₀ ∉ 𝔞.zeroLocus → IsSmoothNear (n := n) Ψ x₀ ∧ Ψ x₀ ≠ ⊥) := by
  obtain ⟨ι, _, P, j₀, O, hO, hx₀O, hOU, hOV⟩ := exists_gluingCover h𝔞 x₀
  obtain ⟨CB, hCB, hcomp⟩ := P.exists_generatorLog_le
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun j => ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j))
  have hA0 : (0 : ℝ) ≤ CB + 1 := by linarith
  refine ⟨P.glue (CB + 1), (CB + 1) * C, by positivity,
    P.thetaPlurisubharmonic_glue omega hA0 (by linarith) hcomp hsemi,
    P.hasAnalyticSingularitiesOfType_glue h𝔞 hA0 hCB hcomp, fun hx₀ => ?_⟩
  have hUT : P.U j₀ ⊆ P.T j₀ := fun y hy =>
    P.closure_V_subset j₀ (subset_closure (P.U_subset_V j₀ hy))
  have hpos : 0 < generatorNormSq (P.gen j₀) x₀ :=
    IdealWeightLowerBound.generatorNormSq_pos_of_notMem_zeroLocus (hUT (hOU hx₀O))
      (P.gen_spec j₀) hx₀
  refine ⟨P.isSmoothNear_glue hO hOU hOV hx₀O hpos, ?_⟩
  rw [P.glue_eq_of_isolated hOU hOV hx₀O, generatorLog, logNormSq, generatorVector_norm_sq,
    ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_add]
  exact EReal.coe_ne_bot _

/-- **The quasi-psh form**, on a connected manifold and away from the zero
locus: `Ψ` is a `(c ω)`-PSH potential in the project's strong sense (locally
nondegenerate), by the identity principle. -/
theorem exists_isThetaPshPotential_idealFunction [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x₀ : M}
    (hx₀ : x₀ ∉ 𝔞.zeroLocus) :
    ∃ (Ψ : M → EReal) (c : ℝ), 0 < c ∧
      IsThetaPshPotential (c • omega.form).val Ψ ∧
      HasAnalyticSingularitiesOfType (n := n) Ψ 1 𝔞 ∧ IsSmoothNear (n := n) Ψ x₀ := by
  obtain ⟨Ψ, c, hc, hpsh, hsing, hsmooth⟩ := exists_idealFunction omega h𝔞 x₀
  obtain ⟨hsm, hne⟩ := hsmooth hx₀
  exact ⟨Ψ, c, hc, ⟨hpsh,
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh ⟨x₀, hne⟩⟩,
    hsing, hsm⟩

end

end Hironaka.IdealFunctionMaxGluing

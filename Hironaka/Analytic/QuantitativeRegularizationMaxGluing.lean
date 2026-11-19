import Hironaka.Analytic.IdealFunctionMaxGluing
import Hironaka.Analytic.PrincipalizationGluingLocalAssembly

set_option autoImplicit false

/-!
# Copy-4 `lem:regularization`, Steps 3--4: gluing local branches on a fixed cover

Source: Copy-4, `lem:regularization`, Steps 3 and 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:969-1060`);
blueprint `ana:regularization`.

Copy-4 fixes, depending only on `(Z, ω_Z)`, a finite cover `U_j ⋐ V_j` with cut-offs
`χ_j ∈ C^∞_c(V_j)` equal to `1` on `U_j` and a constant `C_χ` with `ddᶜχ_j ≥ -C_χ ω_Z`.  For
each `ζ`, `φ ∈ PSH(Z, ζ)` and `m ≥ 1` it builds local Bergman branches `φ_{j,m}` on `V_j` with

* `ζ + ddᶜφ_{j,m} ≥ 0` on `V_j` (`eq:reg-local-positivity`),
* `φ_{j,m} ≤ φ_{l,m} + C_B/m` on `V_j ∩ V_l` with `C_B` independent of `ζ, φ, m`
  (`eq:reg-overlap`),
* `φ_{j,m} ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)` near every point of `U_j` (Step 4),

and glues them (`eq:reg-glue`).  This module proves that the gluing step turns such branch
data into the statement of `lem:regularization`, with `c = (C_B + 1) C_χ`.

## The construction, and how it differs from Copy-4's

We glue with the plain maximum `φ_m = max_{j : z ∈ V_j} (φ_{j,m} + ((C_B + 1)/m) χ_j)` instead
of Copy-4's regularized maximum `M_δ`.  The boundary argument is Copy-4's: near a point of
`∂V_j` the cut-off `χ_j` vanishes while some `χ_l` equals one, so by `eq:reg-overlap` the
`j`-th branch does not exceed the `l`-th there; hence near every point `φ_m` is the maximum
of finitely many branches defined on a whole neighbourhood, and the maximum of `θ`-PSH
functions is `θ`-PSH.  The plain maximum is not smooth off `Z(𝓘(mφ))`, but the statement
does not ask for smoothness, and in exchange neither the Grauert--Remmert extension nor the
ideal equality `eq:reg-ideal-equality` (Copy-4's appeal to `DEL00, Prop. 1.2`) is needed:
the branches are `ζ`-PSH *across* their pole sets.  The same gluing, with generator logs as
branches, is `IdealFunctionMaxGluing` (`lem:ideal-function`).

## Main results

* `CutoffCover`: the fixed cover with cut-offs.
* `CutoffCover.thetaPlurisubharmonic_glue`, `CutoffCover.le_glue`,
  `CutoffCover.isThetaPshPotential_glue`: the glued function is
  `(ζ + A C_χ ω)`-PSH, locally nondegenerate, and dominates every branch on its patch.
* `exists_regularization_of_branches`: the statement of
  `QuantitativeRegularization.demailly1992_exists_regularization_multiplierIdeal_lowerBound`
  from branch data on a fixed cover.  What is left of `lem:regularization` is exactly
  Copy-4's Steps 1--2 and the germ half of Step 4 *on a fixed cover*: the branches with a
  weight-independent overlap constant.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.QuantitativeRegularizationMaxGluing

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.AnalyticGluingData

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n M) in
/-- **A fixed finite cover with cut-offs** (Copy-4 `lem:regularization`, Step 3): open patches
`V j`, open cores `U j` covering `M`, and chart-smooth cut-offs `0 ≤ χ j`, equal to `1` on
`U j`, with `tsupport (χ j) ⊆ V j`. -/
structure CutoffCover (ι : Type*) [Fintype ι] where
  V : ι → Set M
  isOpen_V : ∀ j, IsOpen (V j)
  U : ι → Set M
  isOpen_U : ∀ j, IsOpen (U j)
  cover : ∀ y, ∃ j, y ∈ U j
  χ : ι → M → ℝ
  χ_smooth : ∀ j, ChartSmooth (n := n) (χ j)
  χ_nonneg : ∀ j y, 0 ≤ χ j y
  χ_eq_one : ∀ j, ∀ y ∈ U j, χ j y = 1
  tsupport_χ_subset : ∀ j, tsupport (χ j) ⊆ V j

namespace CutoffCover

variable {ι : Type*} [Fintype ι] (P : CutoffCover n M ι)

theorem U_subset_V (j : ι) : P.U j ⊆ P.V j := fun y hy =>
  P.tsupport_χ_subset j (subset_tsupport _
    (Function.mem_support.mpr (by rw [P.χ_eq_one j y hy]; exact one_ne_zero)))

/-- The `j`-th branch `b_j + A χ_j`. -/
def branch (b : ι → M → EReal) (A : ℝ) (j : ι) (y : M) : EReal :=
  b j y + ((A * P.χ j y : ℝ) : EReal)

open Classical in
/-- **The glued function** `max_{j : y ∈ V j} (b_j + A χ_j)` (`⊥` where no patch applies,
which never happens since the cores cover `M`). -/
def glue (b : ι → M → EReal) (A : ℝ) (y : M) : EReal :=
  Finset.univ.sup fun j => if y ∈ P.V j then P.branch b A j y else ⊥

open Classical in
/-- On its patch, the glued function dominates the shifted branch. -/
theorem branch_le_glue (b : ι → M → EReal) (A : ℝ) {j : ι} {y : M} (hy : y ∈ P.V j) :
    P.branch b A j y ≤ P.glue b A y := by
  refine le_trans ?_ (Finset.le_sup (f := fun j => if y ∈ P.V j then P.branch b A j y else ⊥)
    (Finset.mem_univ j))
  simp only [if_pos hy, le_refl]

/-- **On its patch, the glued function dominates the branch** (Copy-4 Step 4: "the
regularized maximum dominates each of its entries", and `χ_j ≥ 0`). -/
theorem le_glue (b : ι → M → EReal) {A : ℝ} (hA : 0 ≤ A) {j : ι} {y : M}
    (hy : y ∈ P.V j) : b j y ≤ P.glue b A y := by
  refine le_trans ?_ (P.branch_le_glue b A hy)
  unfold branch
  exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg hA (P.χ_nonneg j y)))

open Classical in
/-- **Near every point the glued function is the maximum of the branches whose patch
contains that point.**  The other branches drop out because their cut-off vanishes near the
point while the cut-off of a patch whose core contains the point equals one, and
`A ≥ C_B`. -/
theorem exists_nhds_glue_eq_filter (b : ι → M → EReal) {A CB : ℝ} (hA : CB ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal)) (p : M) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ (∀ j, p ∈ P.V j → N ⊆ P.V j) ∧
      ∀ y ∈ N, P.glue b A y =
        (Finset.univ.filter fun j => p ∈ P.V j).sup fun j => P.branch b A j y := by
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
  refine ⟨N, hN, hpN, hNV, fun y hy => ?_⟩
  have key : P.glue b A y =
      Finset.univ.sup fun j => if p ∈ P.V j then P.branch b A j y else ⊥ := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le fun j _ => ?_
      by_cases hyj : y ∈ P.V j
      · rw [if_pos hyj]
        by_cases hpj : p ∈ P.V j
        · refine le_trans ?_
            (Finset.le_sup (f := fun j => if p ∈ P.V j then P.branch b A j y else ⊥)
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
          refine le_trans ?_
            (Finset.le_sup (f := fun j => if p ∈ P.V j then P.branch b A j y else ⊥)
            (Finset.mem_univ l))
          simp only [if_pos hpVl, branch, hχj, hχl, mul_zero, mul_one, EReal.coe_zero, add_zero]
          exact (hcomp j l y ⟨hyj, hyl⟩).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hA))
      · rw [if_neg hyj]
        exact bot_le
    · refine Finset.sup_le fun j _ => ?_
      by_cases hpj : p ∈ P.V j
      · rw [if_pos hpj]
        exact P.branch_le_glue b A (hNV j hpj hy)
      · rw [if_neg hpj]
        exact bot_le
  rw [key, Finset.sup_ite, Finset.sup_bot, sup_bot_eq]

/-- **The glued function is quasi-psh**: if every branch is `ζ`-PSH on its patch,
`ddᶜχ_j ≥ -C ω` for every `j`, and `0 ≤ C_B ≤ A`, then the glued function is
`(ζ + A C ω)`-PSH. -/
theorem thetaPlurisubharmonic_glue (omega : KahlerBackground n M) (ζ : ClosedRealOneOneForm n M)
    (b : ι → M → EReal) {A CB C : ℝ} (hA0 : 0 ≤ A) (hA : CB ≤ A)
    (hb : ∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j))
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal))
    (hC : ∀ j, (ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j)
      + C • omega.form).val.IsSemipositive) :
    ThetaPlurisubharmonic (ζ + (A * C) • omega.form).val (P.glue b A) := by
  classical
  refine IdealFunctionMaxGluing.thetaPlurisubharmonic_of_locally_finset_sup
    (ζ + (A * C) • omega.form) (b := fun j => P.branch b A j) fun p => ?_
  obtain ⟨N, hN, hpN, hNV, hglue⟩ := P.exists_nhds_glue_eq_filter b hA hcomp p
  refine ⟨N, hN, hpN, Finset.univ.filter fun j => p ∈ P.V j, fun j hj => ?_, hglue⟩
  have hpj : p ∈ P.V j := (Finset.mem_filter.mp hj).2
  have hcut := IdealFunctionMaxGluing.thetaPlurisubharmonic_const_mul_of_ddc_lower omega
    (P.χ_smooth j) hA0 (hC j)
  have hbr : ThetaPlurisubharmonicOn (ζ + (A * C) • omega.form).val (P.branch b A j) (P.V j) :=
    PrincipalizationGluingLocalAssembly.thetaPlurisubharmonicOn_add (hb j)
      (fun e z hz _ => hcut e z hz)
  intro e z hz hzN
  exact hbr e z hz (hNV j hpj hzN)

/-- **The glued function is a `(ζ + A C ω)`-PSH potential**: in addition to
`thetaPlurisubharmonic_glue`, it is `-∞` on no open set as soon as each branch is `-∞` on no
open neighbourhood of a point of its core. -/
theorem isThetaPshPotential_glue (omega : KahlerBackground n M) (ζ : ClosedRealOneOneForm n M)
    (b : ι → M → EReal) {A CB C : ℝ} (hA0 : 0 ≤ A) (hA : CB ≤ A)
    (hb : ∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j))
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal))
    (hC : ∀ j, (ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j)
      + C • omega.form).val.IsSemipositive)
    (hnd : ∀ j, ∀ x ∈ P.U j, ∀ O : Set M, IsOpen O → x ∈ O → ∃ y ∈ O, b j y ≠ ⊥) :
    IsThetaPshPotential (ζ + (A * C) • omega.form).val (P.glue b A) := by
  refine ⟨P.thetaPlurisubharmonic_glue omega ζ b hA0 hA hb hcomp hC, fun x O hO hxO => ?_⟩
  obtain ⟨l, hxl⟩ := P.cover x
  obtain ⟨y, ⟨hyO, hyV⟩, hy⟩ :=
    hnd l x hxl (O ∩ P.V l) (hO.inter (P.isOpen_V l)) ⟨hxO, P.U_subset_V l hxl⟩
  refine ⟨y, hyO, fun hbot => hy ?_⟩
  have := P.le_glue b hA0 hyV
  rw [hbot] at this
  exact le_bot_iff.mp this

end CutoffCover

/-! ### `lem:regularization` from branch data on a fixed cover -/

/-- **Copy-4 `lem:regularization` from local branches on a fixed cover** (Steps 3--4).
Suppose a fixed finite cover with cut-offs `P` and a constant `C_B ≥ 0` (both chosen before
`ζ`, `φ`, `m`) carry, for every `ζ`, every `φ ∈ PSH(Z, ζ)` and every `m ≥ 1`, branches
`b_j` that are `ζ`-PSH on `V_j`, satisfy `b_j ≤ b_l + C_B/m` on `V_j ∩ V_l`, are `-∞` on no
open neighbourhood of a point of `U_j`, and dominate `m⁻¹ log ∑ |g_i|²` near every point
of `U_j` for every finite family of germs of `𝓘(mφ)` there.  Then the conclusion of
`lem:regularization` holds, with `c = (C_B + 1) C_χ`. -/
theorem exists_regularization_of_branches {d : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] [CompactSpace Z]
    (omegaZ : KahlerBackground d Z) {ι : Type*} [Fintype ι] (P : CutoffCover d Z ι)
    {CB : ℝ} (hCB : 0 ≤ CB)
    (hbranch : ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ → ∀ m : ℕ, 1 ≤ m →
          ∃ b : ι → Z → EReal,
            (∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j)) ∧
            (∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + ((CB / (m : ℝ) : ℝ) : EReal)) ∧
            (∀ j, ∀ x ∈ P.U j, ∀ O : Set Z, IsOpen O → x ∈ O → ∃ y ∈ O, b j y ≠ ⊥) ∧
            (∀ j, ∀ x ∈ P.U j, ∀ (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ b j y)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ φm : Z → EReal,
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            ∀ (x : Z) (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y := by
  obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omegaZ
    (fun j => ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j))
  refine ⟨(CB + 1) * Cχ, by positivity, fun ζ φ hφ m hm => ?_⟩
  obtain ⟨b, hb, hcomp, hnd, hlow⟩ := hbranch ζ φ hφ m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set A : ℝ := (CB + 1) / (m : ℝ) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hA : CB / (m : ℝ) ≤ A := div_le_div_of_nonneg_right (by linarith) hmpos.le
  have hform : (CB + 1) * Cχ / (m : ℝ) = A * Cχ := by rw [hAdef]; ring
  refine ⟨P.glue b A, ?_, fun x N g hg => ?_⟩
  · rw [hform]
    exact P.isThetaPshPotential_glue omegaZ ζ b hA0 hA hb hcomp hsemi hnd
  · obtain ⟨j, hxj⟩ := P.cover x
    obtain ⟨C, hC⟩ := hlow j x hxj N g hg
    refine ⟨C, ?_⟩
    filter_upwards [hC, (P.isOpen_U j).mem_nhds hxj] with y hy hyU
    exact hy.trans (P.le_glue b hA0 (P.U_subset_V j hyU))

end

end Hironaka.QuantitativeRegularizationMaxGluing

import Hironaka.Analytic.SymmetricRegularizedMaxPsh
import Hironaka.Analytic.QuantitativeRegularizationMaxGluing

set_option autoImplicit false

/-!
# Copy-4 `lem:regularization`, Step 3, with Demailly's regularized maximum

Source: Copy-4, `lem:regularization`, Step 3, equation `(eq:reg-glue)`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:969-1024`):

  `φ_m(z) = M_δ(φ_{j,m}(z) + ((C_B + 1)/m) χ_j(z) : z ∈ V_j)`,

the regularized maximum of the branches defined at `z`.

`Hironaka.QuantitativeRegularizationMaxGluing` glues the same branch data on the same fixed cover
(`CutoffCover`) with the plain maximum, which suffices for `lem:regularization` itself.  The
regularized maximum is needed where the glued function must be smooth away from its poles
(the analytic-singularity clause of Demailly's approximation theorem, `bou02-volume:2.6`, in the
I-0489 convention): near every point the glued function is `M_δ` of finitely many branches
defined on a whole neighbourhood (`exists_nhds_rglue_eq`), and `M_δ` is `C^∞`
(`contDiffOn_rmax_comp`), so the glued function is smooth wherever the branches are.

## The boundary argument

Copy-4's: near a point of `∂V_j`, `χ_j = 0` while `χ_l = 1` for some patch `l` whose core contains
the point, so by `(eq:reg-overlap)` the `j`-th entry is beaten by at least `δ` by the `l`-th as soon
as `A ≥ C_B + δ` (Copy-4 takes `A = (C_B + 1)/m`, `δ = 1/(4m)`).  By the **exact independence** of
`M_δ` (`SymmetricRegularizedMaxPsh.ermax_eq_of_dominated`) the `j`-th entry then does not
contribute at all.  The comparison is used in its extended-real form, so the branches may be
`-∞` (on the zero locus of the multiplier ideal); no extension theorem across that locus is
needed because the branches are `ζ`-PSH across it and `M_δ` preserves this
(`SymmetricRegularizedMaxPsh.thetaPlurisubharmonic_of_locally_ermax`).

## Main results

* `rglue`: the glued function.
* `exists_nhds_rglue_eq`: locally `M_δ` of the branches whose patch contains the
  point.
* `thetaPlurisubharmonic_rglue`, `isThetaPshPotential_rglue`: the glued
  function is `(ζ + A C ω)`-PSH (a potential when the branches are nondegenerate).
* `le_rglue`, `rglue_le`: `b_j ≤ φ_m` on `V_j`, and `φ_m ≤ max + A + δ`.
* `exists_regularization_of_branches_rmax`: the statement of
  `QuantitativeRegularizationMaxGluing.exists_regularization_of_branches`, with the glued function
  `M_δ`-glued (`δ = 1/(2m)`, `c = (C_B + 1) C_χ`) and its local `M_δ` representation recorded.
-/

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace Hironaka.DemaillySymmetricGluing

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.AnalyticGluingData
open Hironaka.SymmetricRegularizedMax
open Hironaka.SymmetricRegularizedMaxPsh
open Hironaka.QuantitativeRegularizationMaxGluing

noncomputable section

/-! ### Two facts about `M_δ` -/

section Facts

variable {ι : Type*} [Fintype ι]

/-- **Exact independence for extended-real entries.**  If every entry of `T` outside `F ⊆ T` is
beaten by `δ` by an entry of `F`, the regularized maximum over `T` equals the one over `F`. -/
theorem ermax_eq_of_dominated {δ : ℝ} {F T : Finset ι} (hFT : F ⊆ T) {t : ι → EReal}
    (hdom : ∀ i ∈ T, i ∉ F → ∃ j ∈ F, t i + (δ : EReal) ≤ t j) :
    ermax δ T t = ermax δ F t := by
  classical
  by_cases htop : ∃ k ∈ T, t k = ⊤
  · obtain ⟨k, hkT, hk⟩ := htop
    have htopF : ∃ k ∈ F, t k = ⊤ := by
      by_cases hkF : k ∈ F
      · exact ⟨k, hkF, hk⟩
      · obtain ⟨j, hj, hkj⟩ := hdom k hkT hkF
        rw [hk, EReal.top_add_coe, top_le_iff] at hkj
        exact ⟨j, hj, hkj⟩
    have htopT : ∃ k ∈ T, t k = ⊤ := ⟨k, hkT, hk⟩
    simp only [ermax, if_pos htopT, if_pos htopF]
  push Not at htop
  have htopF : ∀ i ∈ F, t i ≠ ⊤ := fun i hi => htop i (hFT hi)
  have hsub : finitePart F t ⊆ finitePart T t := fun i hi => by
    have hi' := mem_finitePart.mp hi
    exact mem_finitePart.mpr ⟨hFT hi'.1, hi'.2⟩
  -- every finite entry of `T` outside `F` is beaten by a finite entry of `F`
  have hdom' : ∀ i ∈ finitePart T t, i ∉ finitePart F t →
      ∃ j ∈ finitePart F t, (t i).toReal + δ ≤ (t j).toReal := by
    intro i hi hiF
    have hi' := mem_finitePart.mp hi
    have hiF' : i ∉ F := fun h => hiF (mem_finitePart.mpr ⟨h, hi'.2⟩)
    obtain ⟨j, hj, hij⟩ := hdom i hi'.1 hiF'
    have hjb : t j ≠ ⊥ := fun h => by
      rw [h, le_bot_iff, add_coe_eq_bot_iff] at hij
      exact hi'.2 hij
    refine ⟨j, mem_finitePart.mpr ⟨hj, hjb⟩, ?_⟩
    have := EReal.toReal_le_toReal hij
      (fun h => hi'.2 ((add_coe_eq_bot_iff _ δ).mp h)) (htopF j hj)
    rwa [toReal_add_coe (htop i hi'.1) hi'.2] at this
  by_cases hF : (finitePart F t).Nonempty
  · rw [ermax_of_finite htop (hF.mono hsub), ermax_of_finite htopF hF,
      rmax_eq_of_dominated hsub hF hdom']
  · have hT : ¬ (finitePart T t).Nonempty := by
      rintro ⟨i, hi⟩
      by_cases hiF : i ∈ finitePart F t
      · exact hF ⟨i, hiF⟩
      · obtain ⟨j, hj, -⟩ := hdom' i hi hiF
        exact hF ⟨j, hj⟩
    have hbot : ∀ {S : Finset ι}, ¬ (finitePart S t).Nonempty → ∀ i ∈ S, t i = ⊥ :=
      fun {S} hS i hi => by
        by_contra hb
        exact hS ⟨i, mem_finitePart.mpr ⟨hi, hb⟩⟩
    rw [ermax_of_bot (hbot hT), ermax_of_bot (hbot hF)]

/-- **`M_δ` of smooth functions is smooth.** -/
theorem contDiffOn_rmax_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ∞}
    (δ : ℝ) {J : Finset ι} {f : ι → X → ℝ} {O : Set X}
    (hf : ∀ j ∈ J, ContDiffOn ℝ k (f j) O) :
    ContDiffOn ℝ k (fun y => rmax δ J fun j => f j y) O := by
  classical
  have heq : (fun y => rmax δ J fun j => f j y)
      = fun y => rmax δ J fun j => if j ∈ J then f j y else 0 :=
    funext fun y => rmax_congr fun j hj => by rw [if_pos hj]
  rw [heq]
  refine ((contDiff_rmax δ J).of_le (by exact_mod_cast le_top)).comp_contDiffOn
    (contDiffOn_pi.mpr fun j => ?_)
  by_cases hj : j ∈ J
  · simpa only [if_pos hj] using hf j hj
  · simpa only [if_neg hj] using contDiffOn_const

end Facts

/-! ### The glued function -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section Glue

variable {ι : Type*} [Fintype ι] (P : CutoffCover n M ι)

open Classical in
/-- The patches containing `y`. -/
def activeSet (y : M) : Finset ι := Finset.univ.filter fun j => y ∈ P.V j

theorem mem_activeSet {y : M} {j : ι} : j ∈ activeSet P y ↔ y ∈ P.V j := by
  classical
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem activeSet_nonempty (y : M) : (activeSet P y).Nonempty := by
  obtain ⟨l, hl⟩ := P.cover y
  exact ⟨l, (mem_activeSet P).mpr (P.U_subset_V l hl)⟩

/-- **The glued function** `M_δ(b_j + A χ_j : y ∈ V_j)` (Copy-4 `(eq:reg-glue)`). -/
def rglue (δ : ℝ) (b : ι → M → EReal) (A : ℝ) (y : M) : EReal :=
  ermax δ (activeSet P y) fun j => P.branch b A j y

/-- On its patch, the glued function dominates the shifted branch. -/
theorem branch_le_rglue {δ : ℝ} (hδ : 0 < δ) (b : ι → M → EReal) (A : ℝ) {j : ι} {y : M}
    (hy : y ∈ P.V j) : P.branch b A j y ≤ rglue P δ b A y :=
  le_ermax (t := fun j => P.branch b A j y) hδ ((mem_activeSet P).mpr hy)

/-- **On its patch, the glued function dominates the branch** (`χ_j ≥ 0`, `A ≥ 0`). -/
theorem le_rglue {δ : ℝ} (hδ : 0 < δ) (b : ι → M → EReal) {A : ℝ} (hA : 0 ≤ A) {j : ι}
    {y : M} (hy : y ∈ P.V j) : b j y ≤ rglue P δ b A y := by
  refine le_trans ?_ (branch_le_rglue P hδ b A hy)
  unfold CutoffCover.branch
  exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg hA (P.χ_nonneg j y)))

/-- **The glued function is at most `max + A + δ`**: if every branch is `≤ c` on its patch,
the glued function is `≤ c + A + δ` (`0 ≤ χ ≤ 1` is not assumed; `A χ_j ≤ A` is). -/
theorem rglue_le {δ : ℝ} (hδ : 0 < δ) (b : ι → M → EReal) {A c : ℝ} {y : M}
    (hb : ∀ j, y ∈ P.V j → b j y + ((A * P.χ j y : ℝ) : EReal) ≤ ((c + A : ℝ) : EReal)) :
    rglue P δ b A y ≤ ((c + A + δ : ℝ) : EReal) :=
  ermax_le hδ fun j hj => hb j ((mem_activeSet P).mp hj)

/-- **Near every point the glued function is `M_δ` of the branches whose patch contains the
point**, provided `C_B + δ ≤ A`. -/
theorem exists_nhds_rglue_eq {δ : ℝ} (b : ι → M → EReal) {A CB : ℝ} (hA : CB + δ ≤ A)
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal)) (p : M) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ (∀ j, p ∈ P.V j → N ⊆ P.V j) ∧
      ∀ y ∈ N, rglue P δ b A y = ermax δ (activeSet P p) fun j => P.branch b A j y := by
  classical
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
  have hsub : activeSet P p ⊆ activeSet P y := fun j hj =>
    (mem_activeSet P).mpr (hNV j ((mem_activeSet P).mp hj) hy)
  refine ermax_eq_of_dominated hsub fun j hjy hjp => ?_
  have hpj : p ∉ P.V j := fun h => hjp ((mem_activeSet P).mpr h)
  have hyt : y ∉ tsupport (P.χ j) := by
    have := mem_iInter.mp hy.1 j
    rwa [if_neg hpj] at this
  have hχj : P.χ j y = 0 := image_eq_zero_of_notMem_tsupport hyt
  have hχl : P.χ l y = 1 := P.χ_eq_one l y hy.2
  refine ⟨l, (mem_activeSet P).mpr (P.U_subset_V l hpl), ?_⟩
  simp only [CutoffCover.branch, hχj, hχl, mul_zero, mul_one, EReal.coe_zero, add_zero]
  calc b j y + (δ : EReal) ≤ b l y + (CB : EReal) + (δ : EReal) :=
        add_le_add_left (hcomp j l y ⟨(mem_activeSet P).mp hjy, P.U_subset_V l hy.2⟩) _
    _ = b l y + ((CB + δ : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    _ ≤ b l y + (A : EReal) := add_le_add_right (EReal.coe_le_coe_iff.mpr hA) _

/-- **The glued function is quasi-psh**: if every branch is `ζ`-PSH on its patch,
`ddᶜχ_j ≥ -C ω`, `0 ≤ A` and `C_B + δ ≤ A`, then the glued function is `(ζ + A C ω)`-PSH. -/
theorem thetaPlurisubharmonic_rglue (omega : KahlerBackground n M)
    (ζ : ClosedRealOneOneForm n M) (b : ι → M → EReal) {δ A CB C : ℝ} (hδ : 0 < δ)
    (hA0 : 0 ≤ A) (hA : CB + δ ≤ A)
    (hb : ∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j))
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal))
    (hC : ∀ j, (ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j)
      + C • omega.form).val.IsSemipositive) :
    ThetaPlurisubharmonic (ζ + (A * C) • omega.form).val (rglue P δ b A) := by
  refine thetaPlurisubharmonic_of_locally_ermax (ζ + (A * C) • omega.form) hδ
    (b := fun j => P.branch b A j) fun p => ?_
  obtain ⟨N, hN, hpN, hNV, hglue⟩ := exists_nhds_rglue_eq P b hA hcomp p
  refine ⟨N, hN, hpN, activeSet P p, activeSet_nonempty P p, fun j hj => ?_, hglue⟩
  have hpj : p ∈ P.V j := (mem_activeSet P).mp hj
  have hcut := IdealFunctionMaxGluing.thetaPlurisubharmonic_const_mul_of_ddc_lower omega
    (P.χ_smooth j) hA0 (hC j)
  have hbr : ThetaPlurisubharmonicOn (ζ + (A * C) • omega.form).val (P.branch b A j) (P.V j) :=
    PrincipalizationGluingLocalAssembly.thetaPlurisubharmonicOn_add (hb j)
      (fun e z hz _ => hcut e z hz)
  intro e z hz hzN
  exact hbr e z hz (hNV j hpj hzN)

/-- **The glued function is a `(ζ + A C ω)`-PSH potential** when each branch is `-∞` on no
open neighbourhood of a point of its core. -/
theorem isThetaPshPotential_rglue (omega : KahlerBackground n M)
    (ζ : ClosedRealOneOneForm n M) (b : ι → M → EReal) {δ A CB C : ℝ} (hδ : 0 < δ)
    (hA0 : 0 ≤ A) (hA : CB + δ ≤ A)
    (hb : ∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j))
    (hcomp : ∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + (CB : EReal))
    (hC : ∀ j, (ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j)
      + C • omega.form).val.IsSemipositive)
    (hnd : ∀ j, ∀ x ∈ P.U j, ∀ O : Set M, IsOpen O → x ∈ O → ∃ y ∈ O, b j y ≠ ⊥) :
    IsThetaPshPotential (ζ + (A * C) • omega.form).val (rglue P δ b A) := by
  refine ⟨thetaPlurisubharmonic_rglue P omega ζ b hδ hA0 hA hb hcomp hC, fun x O hO hxO => ?_⟩
  obtain ⟨l, hxl⟩ := P.cover x
  obtain ⟨y, ⟨hyO, hyV⟩, hy⟩ :=
    hnd l x hxl (O ∩ P.V l) (hO.inter (P.isOpen_V l)) ⟨hxO, P.U_subset_V l hxl⟩
  refine ⟨y, hyO, fun hbot => hy ?_⟩
  have := le_rglue P hδ b hA0 hyV
  rw [hbot] at this
  exact le_bot_iff.mp this

end Glue

/-! ### `lem:regularization` from branch data, glued with `M_δ` -/

/-- **Copy-4 `lem:regularization` from local branches on a fixed cover, glued with Demailly's
regularized maximum** (`(eq:reg-glue)` literally).  Same hypotheses as
`QuantitativeRegularizationMaxGluing.exists_regularization_of_branches`; the glued function is
`M_δ`-glued with `δ = 1/(2m)` and `A = (C_B + 1)/m`, and besides the conclusion of
`lem:regularization` it is recorded that near every point it is `M_δ` of finitely many shifted
branches defined on a neighbourhood of that point (the form in which smoothness away from the
poles is read off). -/
theorem exists_regularization_of_branches_rmax {d : ℕ} {Z : Type*} [TopologicalSpace Z]
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
          ∃ (b : ι → Z → EReal) (φm : Z → EReal),
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            (∀ (x : Z) (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y) ∧
            (∀ j, ∀ y ∈ P.V j, b j y ≤ φm y) ∧
            ∀ p : Z, ∃ N : Set Z, IsOpen N ∧ p ∈ N ∧ ∃ J : Finset ι, J.Nonempty ∧
              (∀ j ∈ J, N ⊆ P.V j) ∧
              ∀ y ∈ N, φm y = ermax (1 / (2 * (m : ℝ))) J fun j =>
                b j y + ((((CB + 1) / (m : ℝ)) * P.χ j y : ℝ) : EReal) := by
  obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omegaZ
    (fun j => ManifoldTubePositivity.ddcClosedForm (P.χ j) (P.χ_smooth j))
  refine ⟨(CB + 1) * Cχ, by positivity, fun ζ φ hφ m hm => ?_⟩
  obtain ⟨b, hb, hcomp, hnd, hlow⟩ := hbranch ζ φ hφ m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set A : ℝ := (CB + 1) / (m : ℝ) with hAdef
  set δ : ℝ := 1 / (2 * (m : ℝ)) with hδdef
  have hδ : 0 < δ := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hA : CB / (m : ℝ) + δ ≤ A := by
    have hgap : A - (CB / (m : ℝ) + δ) = 1 / (2 * (m : ℝ)) := by
      rw [hAdef, hδdef]
      field_simp
      ring
    have : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
    linarith
  have hform : (CB + 1) * Cχ / (m : ℝ) = A * Cχ := by rw [hAdef]; ring
  refine ⟨b, rglue P δ b A, ?_, fun x N g hg => ?_, fun j y hy => le_rglue P hδ b hA0 hy,
    fun p => ?_⟩
  · rw [hform]
    exact isThetaPshPotential_rglue P omegaZ ζ b hδ hA0 hA hb hcomp hsemi hnd
  · obtain ⟨j, hxj⟩ := P.cover x
    obtain ⟨C, hC⟩ := hlow j x hxj N g hg
    refine ⟨C, ?_⟩
    filter_upwards [hC, (P.isOpen_U j).mem_nhds hxj] with y hy hyU
    exact hy.trans (le_rglue P hδ b hA0 (P.U_subset_V j hyU))
  · obtain ⟨N, hN, hpN, hNV, hglue⟩ := exists_nhds_rglue_eq P b hA hcomp p
    exact ⟨N, hN, hpN, activeSet P p, activeSet_nonempty P p,
      fun j hj => hNV j ((mem_activeSet P).mp hj), hglue⟩

end

end Hironaka.DemaillySymmetricGluing

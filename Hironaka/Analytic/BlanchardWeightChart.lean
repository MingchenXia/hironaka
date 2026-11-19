import Hironaka.Analytic.BlanchardWeight
import Hironaka.Blowup.BlowupWeightLevi

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Blanchard weight in a monomial chart

Let `D` be Blanchard data along `C` (`BlanchardWeight.BlanchardData`), `q ∈ C` the centre of a
partition function `χ_{a₀}`, and `γ(w) = e_q⁻¹ Φ_q⁻¹ σⱼ(w)` the `j`-th monomial map of the
flattening at `q`.  Near a point `w₀` with `p = γ(w₀) ∈ C` and `χ_{a₀}(p) > 0`,

`U(γ w) = |wⱼ|² Ũ(w)`,  `Ũ = blowupWeight j c B`,  `c_b = χ_b ∘ γ`,  `B_b = H_b ∘ γ`,

where `H_b` expresses the normal coordinates of the `b`-th flattening in terms of those of
`Φ_q` (Hadamard), and `H_{a₀} = id`; moreover `Ũ` is smooth and positive near `w₀`
(`exists_blowupWeight_factor`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlanchardWeightChart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupMonomialCharts BlanchardWeight BlowupWeightLevi

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The monomial map `γ = e⁻¹ Φ⁻¹ σⱼ`, on all of `ℂⁿ`. -/
def monomialMap {y₀ : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀))
    (k : ℕ) (j : Fin n) (w : ComplexModel n) : M :=
  (chartAt (ComplexModel n) y₀).symm (Φ.invFun (monomial k j w))

theorem flatCoord_monomialMap {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {w : ComplexModel n}
    (hw : monomial k j w ∈ Φ.target) {l : Fin n} (hl : k ≤ l.1) :
    flatCoord Φ l (monomialMap Φ k j w) = w j * hatCoord j w l := by
  simp only [flatCoord, monomialMap]
  rw [(flatInverse_mem Φ hw hΦsrc).2, monomial_apply]
  by_cases hlj : l = j
  · subst hlj; simp [hatCoord]
  · simp [hatCoord, hl, hlj, mul_comm]

theorem continuousAt_monomialMap {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {w : ComplexModel n}
    (hw : monomial k j w ∈ Φ.target) : ContinuousAt (monomialMap Φ k j) w := by
  have h1 : ContinuousAt (monomial k j) w := (contDiff_monomial k j).continuous.continuousAt
  have h2 : ContinuousAt Φ.invFun (monomial k j w) :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).continuousAt
  have h3 : ContinuousAt (chartAt (ComplexModel n) y₀).symm (Φ.invFun (monomial k j w)) :=
    (chartAt (ComplexModel n) y₀).continuousAt_symm (hΦsrc (Φ.mapsTo_invFun hw))
  exact ContinuousAt.comp (f := Φ.invFun ∘ monomial k j) h3 (h2.comp h1)

theorem mdifferentiableAt_monomialMap {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {w : ComplexModel n}
    (hw : monomial k j w ∈ Φ.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (monomialMap Φ k j) w := by
  have h1 : DifferentiableAt ℂ (fun w => Φ.invFun (monomial k j w)) w :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hw)).comp w
      ((contDiff_monomial k j).differentiable (by simp) w)
  exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
    (chart_mem_atlas (ComplexModel n) y₀) (hΦsrc (Φ.mapsTo_invFun hw))).comp w h1.mdifferentiableAt

theorem contDiffAt_monomialMap_comp {y₀ : M}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ} {j : Fin n}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) {w : ComplexModel n} (hw : monomial k j w ∈ Φ.target) :
    ContDiffAt ℝ ∞ (fun w => g (monomialMap Φ k j w)) w := by
  have h1 : ContDiffAt ℂ ∞ (fun w => Φ.invFun (monomial k j w)) w :=
    (contDiffAt_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target hw).comp w
      (contDiff_monomial k j).contDiffAt
  have h2 := (hg ⟨chartAt (ComplexModel n) y₀, chart_mem_atlas _ y₀⟩).contDiffAt
    ((chartAt (ComplexModel n) y₀).open_target.mem_nhds (hΦsrc (Φ.mapsTo_invFun hw)))
  exact ContDiffAt.comp (g := fun z => g ((chartAt (ComplexModel n) y₀).symm z)) w h2
    (h1.restrict_scalars ℝ)

namespace BlanchardData

variable {C : Set M} (D : BlanchardData n C)

/-- Hadamard coefficients of every block relative to the flattening at `q`, near `p`. -/
theorem exists_hadamard {q : C} {a₀ : Fin D.m} (ha₀ : D.center a₀ = some q) {p : M}
    (hp : p ∈ C) (hpq : p ∈ flatDomain (D.flat q)) (b : Fin D.m) :
    ∃ H : Fin n → Fin n → M → ℂ, (∀ i l, HolomorphicAt n (H i l) p) ∧
      (∀ i l, l.1 < D.kdim q → H i l = 0) ∧
      (b = a₀ → ∀ i l, H i l = fun _ => if D.kdim q ≤ l.1 ∧ i = l then 1 else 0) ∧
      ∀ᶠ y in 𝓝 p, D.χ b y * D.normalWeight b y =
        D.χ b y * ∑ i, Complex.normSq (∑ l, H i l y * flatCoord (D.flat q) l y) := by
  classical
  by_cases hb : b = a₀
  · subst hb
    refine ⟨fun i l _ => if D.kdim q ≤ l.1 ∧ i = l then 1 else 0, fun i l => holomorphicAt_const _,
      fun i l hl => by funext y; simp [show ¬ D.kdim q ≤ l.1 by omega], fun _ i l => rfl,
      Eventually.of_forall fun y => ?_⟩
    congr 1
    unfold BlanchardWeight.BlanchardData.normalWeight
    rw [ha₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · by_cases hi : D.kdim q ≤ i.1 <;> simp [hi]
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  have hzero : p ∉ tsupport (D.χ b) →
      ∃ H : Fin n → Fin n → M → ℂ, (∀ i l, HolomorphicAt n (H i l) p) ∧
        (∀ i l, l.1 < D.kdim q → H i l = 0) ∧
        (b = a₀ → ∀ i l, H i l = fun _ => if D.kdim q ≤ l.1 ∧ i = l then 1 else 0) ∧
        ∀ᶠ y in 𝓝 p, D.χ b y * D.normalWeight b y =
          D.χ b y * ∑ i, Complex.normSq (∑ l, H i l y * flatCoord (D.flat q) l y) := by
    intro hpt
    refine ⟨fun _ _ => 0, fun _ _ => holomorphicAt_const 0, fun _ _ _ => rfl,
      fun h => absurd h hb, ?_⟩
    filter_upwards [(isClosed_tsupport (D.χ b)).isOpen_compl.mem_nhds hpt] with y hy
    rw [D.χ_eq_zero_of_notMem hy, zero_mul, zero_mul]
  cases hc : D.center b with
  | none => exact hzero fun h => D.supp_none b hc h hp
  | some r =>
    by_cases hpt : p ∈ tsupport (D.χ b)
    · have hpr : p ∈ flatDomain (D.flat r) := D.supp_some b r hc hpt
      have hHad : ∀ i : Fin n, ∃ Hi : Fin n → M → ℂ, (∀ l, HolomorphicAt n (Hi l) p) ∧
          (∀ l, l.1 < D.kdim q → Hi l = 0) ∧
          (D.kdim r ≤ i.1 → ∀ᶠ y in 𝓝 p,
            flatCoord (D.flat r) i y = ∑ l, Hi l y * flatCoord (D.flat q) l y) := by
        intro i
        by_cases hi : D.kdim r ≤ i.1
        · obtain ⟨Hi, h0, hh, heq⟩ := exists_eq_sum_flatCoord (D.flat q) (D.flat_src q)
            (D.flat_eq q) hpq
            (flatCoord_mem_vanishingIdeal (D.flat r) (D.flat_eq r) hi hpr)
          exact ⟨Hi, hh, h0, fun _ => heq⟩
        · exact ⟨fun _ _ => 0, fun _ => holomorphicAt_const 0, fun _ _ => rfl,
            fun h => absurd h hi⟩
      choose H hH h0 heq using hHad
      refine ⟨fun i => if D.kdim r ≤ i.1 then H i else fun _ _ => 0, fun i l => ?_,
        fun i l hl => ?_, fun h => absurd h hb, ?_⟩
      · by_cases hi : D.kdim r ≤ i.1
        · simp only [hi, if_true]; exact hH i l
        · simp only [hi, if_false]; exact holomorphicAt_const 0
      · by_cases hi : D.kdim r ≤ i.1
        · simp only [hi, if_true]; exact h0 i l hl
        · simp only [hi, if_false]; rfl
      · have hall : ∀ᶠ y in 𝓝 p, ∀ i : Fin n, D.kdim r ≤ i.1 →
            flatCoord (D.flat r) i y = ∑ l, H i l y * flatCoord (D.flat q) l y :=
          eventually_all.2 fun i => by
            by_cases hi : D.kdim r ≤ i.1
            · exact (heq i hi).mono fun _ h _ => h
            · exact Eventually.of_forall fun _ h => absurd h hi
        filter_upwards [hall] with y hy
        congr 1
        unfold BlanchardWeight.BlanchardData.normalWeight
        rw [hc]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : D.kdim r ≤ i.1
        · simp only [hi, if_true, hy i hi]
        · simp [hi]
    · exact hzero hpt

/-- **The Blanchard weight in a monomial chart.** -/
theorem exists_blowupWeight_factor {q : C} {a₀ : Fin D.m} (ha₀ : D.center a₀ = some q)
    {j : Fin n} (hj : D.kdim q ≤ j.1) {w₀ : ComplexModel n}
    (hw₀ : monomial (D.kdim q) j w₀ ∈ (D.flat q).target)
    (hp : monomialMap (D.flat q) (D.kdim q) j w₀ ∈ C)
    (hχ : 0 < D.χ a₀ (monomialMap (D.flat q) (D.kdim q) j w₀)) :
    ∃ (B : Fin D.m → Fin n → Fin n → M → ℂ) (V : Set (ComplexModel n)), IsOpen V ∧ w₀ ∈ V ∧
      (∀ w ∈ V, monomial (D.kdim q) j w ∈ (D.flat q).target) ∧
      ContDiffOn ℝ ∞ (blowupWeight j (fun b w => D.χ b (monomialMap (D.flat q) (D.kdim q) j w))
        (fun b i l w => B b i l (monomialMap (D.flat q) (D.kdim q) j w))) V ∧
      (∀ w ∈ V, 0 < blowupWeight j (fun b w => D.χ b (monomialMap (D.flat q) (D.kdim q) j w))
        (fun b i l w => B b i l (monomialMap (D.flat q) (D.kdim q) j w)) w) ∧
      (∀ w ∈ V, D.weight (monomialMap (D.flat q) (D.kdim q) j w) = Complex.normSq (w j) *
        blowupWeight j (fun b w => D.χ b (monomialMap (D.flat q) (D.kdim q) j w))
          (fun b i l w => B b i l (monomialMap (D.flat q) (D.kdim q) j w)) w) ∧
      (∀ i l y, B a₀ i l y = if D.kdim q ≤ l.1 ∧ i = l then 1 else 0) := by
  classical
  set k := D.kdim q
  set Φ := D.flat q
  set γ := monomialMap Φ k j with hγ
  set p := γ w₀
  have hpq : p ∈ flatDomain Φ := (flatInverse_mem Φ hw₀ (D.flat_src q)).1
  choose B hBh hB0 hBa hBeq using exists_hadamard D ha₀ hp hpq
  set U := blowupWeight j (fun b w => D.χ b (γ w)) (fun b i l w => B b i l (γ w)) with hU
  have hγc := continuousAt_monomialMap (D.flat_src q) hw₀
  have hT : IsOpen {w : ComplexModel n | monomial k j w ∈ Φ.target} :=
    Φ.isOpen_target.preimage (contDiff_monomial k j).continuous
  -- differentiability of the coefficients near `w₀`
  have hBd : ∀ b i l, ∀ᶠ w in 𝓝 w₀, DifferentiableAt ℂ (fun w => B b i l (γ w)) w := by
    intro b i l
    filter_upwards [hT.mem_nhds hw₀, hγc.eventually (hBh b i l)] with w hw hB
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hB.comp w (mdifferentiableAt_monomialMap (D.flat_src q) hw))
  set P : ComplexModel n → Prop := fun w => monomial k j w ∈ Φ.target ∧
    (∀ b i l, ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (fun w => B b i l (γ w)) w') ∧
    (∀ b, D.χ b (γ w) * D.normalWeight b (γ w) =
      D.χ b (γ w) * ∑ i, Complex.normSq (∑ l, B b i l (γ w) * flatCoord Φ l (γ w))) with hP
  have hPev : ∀ᶠ w in 𝓝 w₀, P w := by
    refine Filter.Eventually.and (hT.mem_nhds hw₀ : ∀ᶠ w in 𝓝 w₀, monomial k j w ∈ Φ.target)
      (Filter.Eventually.and ?_ ?_)
    · exact eventually_all.2 fun b => eventually_all.2 fun i => eventually_all.2 fun l =>
        (hBd b i l).eventually_nhds
    · exact hγc.eventually (eventually_all.2 hBeq)
  have hsmooth : ∀ w, P w → ContDiffAt ℝ ∞ U w := by
    intro w hw
    refine ContDiffAt.sum fun b _ => ?_
    refine (contDiffAt_monomialMap_comp (D.flat_src q) (D.smooth b) hw.1).mul
      (ContDiffAt.sum fun i _ => BlanchardWeight.BlanchardData.contDiffAt_normSq_comp ?_)
    have hall : ∀ᶠ w' in 𝓝 w, ∀ l, DifferentiableAt ℂ (fun w => B b i l (γ w)) w' :=
      eventually_all.2 fun l => hw.2.1 b i l
    filter_upwards [hall] with w' hw'
    refine DifferentiableAt.fun_sum fun l _ => (hw' l).mul ?_
    unfold hatCoord
    by_cases hl : l = j
    · simp only [hl, if_true]; exact differentiableAt_const _
    · simp only [hl, if_false]
      exact (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hU0 : 0 < U w₀ := by
    have hterm : 0 < D.χ a₀ (γ w₀) *
        ∑ i, Complex.normSq (∑ l, B a₀ i l (γ w₀) * hatCoord j w₀ l) := by
      refine mul_pos hχ (lt_of_lt_of_le ?_ (Finset.single_le_sum
        (f := fun i => Complex.normSq (∑ l, B a₀ i l (γ w₀) * hatCoord j w₀ l))
        (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ j)))
      rw [Finset.sum_eq_single j]
      · simp only [hBa a₀ rfl, hatCoord]
        simp [show D.kdim q ≤ j.1 from hj]
      · intro l _ hl; simp [hBa a₀ rfl, Ne.symm hl]
      · simp
    exact lt_of_lt_of_le hterm (Finset.single_le_sum
      (f := fun b => D.χ b (γ w₀) * ∑ i, Complex.normSq (∑ l, B b i l (γ w₀) * hatCoord j w₀ l))
      (fun b _ => mul_nonneg (D.nonneg b _) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))
      (Finset.mem_univ a₀))
  have hposev : ∀ᶠ w in 𝓝 w₀, 0 < U w :=
    (hsmooth w₀ hPev.self_of_nhds).continuousAt.eventually (lt_mem_nhds hU0)
  have hsub : ∀ w ∈ interior {w | P w ∧ 0 < U w}, P w ∧ 0 < U w := fun w hw =>
    (interior_subset (s := {w | P w ∧ 0 < U w}) hw : w ∈ {w | P w ∧ 0 < U w})
  refine ⟨B, interior {w | P w ∧ 0 < U w}, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr (hPev.and hposev), fun w hw => (hsub w hw).1.1,
    fun w hw => (hsmooth w (hsub w hw).1).contDiffWithinAt,
    fun w hw => (hsub w hw).2, fun w hw => ?_, fun i l y => by rw [hBa a₀ rfl i l]⟩
  obtain ⟨⟨hwT, -, hwe⟩, -⟩ := hsub w hw
  simp only [blowupWeight, BlanchardWeight.BlanchardData.weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hwe b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum : ∑ l, B b i l (γ w) * flatCoord Φ l (γ w) =
      w j * ∑ l, B b i l (γ w) * hatCoord j w l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k ≤ l.1
    · rw [flatCoord_monomialMap (D.flat_src q) hwT hl]; ring
    · rw [hB0 b i l (by omega)]; simp
  rw [hsum, map_mul]
  ring

end BlanchardData

end

end Hironaka.BlanchardWeightChart

import TranscendentalNakamaye.Pending.IdealOrderArithmetic
import TranscendentalNakamaye.Pending.HolomorphicAnalytic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Multiplicativity of the order: `ord_x(g^ν) = ν · ord_x(g)`

Blueprint `hir:order-power` (`blueprint/src/hironaka.tex`, Hironaka phase H1).  Source: Włodarczyk 2005 §2.9
(`supp(𝓘^ν, μν) = supp(𝓘, μ)`, used in Lemma `le:operations` for sums of marked ideals with different marks).

## Main results

* `ContinuousMultilinearMap.eq_zero_of_symmetric_of_apply_diag`: **polarization** -- a symmetric continuous
  multilinear map over `ℂ` which vanishes on the diagonal is zero.
* `iterDeriv_ofFn_eq_iteratedFDeriv`: the iterated directional derivatives of TN23's `HolomorphicTaylorTail` are
  the values of `iteratedFDeriv`.
* `mem_idealPow_pointIdeal_iff_iteratedFDeriv`: `g ∈ 𝔪_x^q ⟺ D^j(g ∘ e⁻¹)(e x) = 0` for `j < q`
  (preferred chart `e`).
* `mem_idealPow_of_pow_mem`: if `g^ν ∈ 𝔪_x^{νμ}` with `ν ≥ 1`, then `g ∈ 𝔪_x^μ`.  Proof: if not, let `a < μ`
  be the order of `g`; by polarization some direction `y` has `D^a G(p)(y, …, y) ≠ 0`, so `t ↦ G(p + t y)`
  has order exactly `a` at `0` and its `ν`-th power order `νa < νμ` (mathlib's `analyticOrderAt_pow`),
  contradicting `g^ν ∈ 𝔪_x^{νμ}`.
* `cosupport_idealPow_mul_eq` (`N = M`): `cosupp(𝔞^ν, μν) = cosupp(𝔞, μ)` for `ν ≥ 1`;
  `cosupport_sumIdeal_idealPow` (Włodarczyk `le:operations`(1) for two marked ideals):
  `cosupp(𝔞^ν + 𝔟^μ, μν) = cosupp(𝔞, μ) ∩ cosupp(𝔟, ν)` for `μ, ν ≥ 1`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.OrderMultiplicativity

open FirstPass FirstPass.HolomorphicIdealSheaves
open TranscendentalNakamaye.Pending.IdealWeightPowers TranscendentalNakamaye.Pending.GermIdealOrder
  TranscendentalNakamaye.Pending.DerivativeIdeal TranscendentalNakamaye.Pending.OrderTaylor
  TranscendentalNakamaye.Pending.HolomorphicTaylorTail TranscendentalNakamaye.Pending.IdealOrderArithmetic
  TranscendentalNakamaye.Pending.RestrictedIdealExtension TranscendentalNakamaye.Pending.HolomorphicAnalytic

noncomputable section

/-! ### Polarization -/

section Polarization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Moving the inserted vector of `update (fun _ => y) i w` to the front is a permutation. -/
theorem update_const_comp_swap {k : ℕ} (y w : E) (i : Fin (k + 1)) :
    Function.update (fun _ : Fin (k + 1) => y) i w ∘ Equiv.swap 0 i =
      Fin.cons w (fun _ : Fin k => y) := by
  funext j
  simp only [Function.comp_apply]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · rw [Fin.cons_succ]
    by_cases hj : j.succ = i
    · subst hj
      simp [(Fin.succ_ne_zero j).symm]
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j) hj]
      simp [hj]

/-- **Polarization**: a symmetric continuous multilinear map over `ℂ` vanishing on the diagonal is zero. -/
theorem eq_zero_of_symmetric_of_apply_diag :
    ∀ (k : ℕ) (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F),
      (∀ (σ : Equiv.Perm (Fin k)) (m : Fin k → E), Φ (m ∘ σ) = Φ m) →
      (∀ y : E, Φ (fun _ => y) = 0) → Φ = 0
  | 0, Φ, _, hdiag => by
    ext m
    have hm : m = fun _ => 0 := funext fun i => i.elim0
    rw [hm, hdiag 0]
    rfl
  | k + 1, Φ, hsym, hdiag => by
    classical
    have hcons : ∀ y w : E, Φ (Fin.cons w (fun _ : Fin k => y)) = 0 := by
      intro y w
      have h1 : HasDerivAt (fun t : ℂ => (fun _ : Fin (k + 1) => y + t • w)) (fun _ => w) 0 := by
        refine hasDerivAt_pi.2 fun _ => ?_
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add y
      have h2 := Φ.hasFDerivAt (fun _ : Fin (k + 1) => y + (0 : ℂ) • w)
      have hline : HasDerivAt (fun t : ℂ => Φ (fun _ => y + t • w))
          (Φ.linearDeriv (fun _ => y + (0 : ℂ) • w) (fun _ => w)) 0 :=
        h2.comp_hasDerivAt (x := (0 : ℂ)) (f := fun t : ℂ => (fun _ : Fin (k + 1) => y + t • w)) h1
      have hzero : (fun t : ℂ => Φ (fun _ => y + t • w)) = fun _ => 0 := funext fun t => hdiag _
      rw [hzero] at hline
      have hsum := hline.unique (hasDerivAt_const (0 : ℂ) (0 : F))
      rw [ContinuousMultilinearMap.linearDeriv_apply] at hsum
      simp only [zero_smul, add_zero] at hsum
      have hterm : ∀ i : Fin (k + 1),
          Φ (Function.update (fun _ => y) i w) = Φ (Fin.cons w (fun _ : Fin k => y)) := by
        intro i
        rw [← hsym (Equiv.swap 0 i) (Function.update (fun _ => y) i w), update_const_comp_swap]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
      rw [← Nat.cast_smul_eq_nsmul ℂ] at hsum
      exact (smul_eq_zero.mp hsum).resolve_left (by exact_mod_cast Nat.succ_ne_zero k)
    ext m
    have hcurry : Φ.curryLeft (m 0) = 0 := by
      refine eq_zero_of_symmetric_of_apply_diag k _ (fun σ m' => ?_) (fun y => ?_)
      · simp only [ContinuousMultilinearMap.curryLeft_apply]
        have h := hsym (Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.cons (m 0) m')
        rw [← h]
        congr 1
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      · simp only [ContinuousMultilinearMap.curryLeft_apply]
        exact hcons y (m 0)
    have := congrArg (fun Ψ => Ψ (Fin.tail m)) hcurry
    simpa [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail] using this

end Polarization

/-! ### Iterated directional derivatives and `iteratedFDeriv` -/

section Iterated

variable {n : ℕ}

/-- **`iterDeriv` is `iteratedFDeriv`** for holomorphic functions on an open set of `ℂⁿ`. -/
theorem iterDeriv_ofFn_eq_iteratedFDeriv {G : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) :
    ∀ (k : ℕ) (m : Fin k → ComplexModel n) {z : ComplexModel n}, z ∈ U →
      iterDeriv (List.ofFn m) G z = iteratedFDeriv ℂ k G z m
  | 0, m, z, _ => by simp
  | k + 1, m, z, hz => by
    have han : AnalyticOnNhd ℂ G U := analyticOnNhd_of_differentiableOn hU hG
    have hdiff : DifferentiableAt ℂ (iteratedFDeriv ℂ k G) z :=
      ((han.iteratedFDeriv k) z hz).differentiableAt
    have heq : iterDeriv (List.ofFn fun i : Fin k => m i.succ) G =ᶠ[𝓝 z]
        fun z' => iteratedFDeriv ℂ k G z' (Fin.tail m) :=
      eventually_of_mem (hU.mem_nhds hz) fun z' hz' =>
        iterDeriv_ofFn_eq_iteratedFDeriv hU hG k (fun i => m i.succ) hz'
    rw [List.ofFn_succ, iterDeriv_cons, dirDeriv, iteratedFDeriv_succ_apply_left, heq.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hdiff]

/-- Every list of directions is `List.ofFn` of its entries. -/
theorem iterDeriv_eq_iteratedFDeriv {G : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) (L : List (ComplexModel n)) {z : ComplexModel n}
    (hz : z ∈ U) : iterDeriv L G z = iteratedFDeriv ℂ L.length G z L.get := by
  conv_lhs => rw [← List.ofFn_get L]
  exact iterDeriv_ofFn_eq_iteratedFDeriv hU hG L.length L.get hz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Order and derivatives, `iteratedFDeriv` form**: in the preferred chart `e` at `x`,
`g ∈ 𝔪_x^q` if and only if `D^j(g ∘ e⁻¹)(e x) = 0` for every `j < q`. -/
theorem mem_idealPow_pointIdeal_iff_iteratedFDeriv {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x)
    (q : ℕ) :
    (idealPow (pointIdeal n x) q).mem x g ↔
      ∀ j < q, iteratedFDeriv ℂ j (g ∘ (complexChartAt (n := n) x).val.symm)
        ((complexChartAt (n := n) x).val x) = 0 := by
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hg)
  have hGU : DifferentiableOn ℂ (g ∘ e.val.symm) U := fun z hz => (hU z hz).differentiableWithinAt
  rw [mem_idealPow_pointIdeal_iff hxe hg q]
  constructor
  · intro h j hj
    ext m
    rw [← iterDeriv_ofFn_eq_iteratedFDeriv hUo hGU j m hpU, ← iterChartDeriv_eq_iterDeriv e g _ hxe]
    exact h _ (by simpa using hj)
  · intro h L hL
    rw [iterChartDeriv_eq_iterDeriv e g L hxe, iterDeriv_eq_iteratedFDeriv hUo hGU L hpU, h _ hL]
    rfl

/-- `g ∈ 𝔞` gives `g^ν ∈ 𝔞^ν`. -/
theorem pow_mem_idealPow {𝔞 : GermIdeal n M} {x : M} {g : M → ℂ} (hg : 𝔞.mem x g)
    (hhol : HolomorphicAt n g x) : ∀ ν : ℕ, (idealPow 𝔞 ν).mem x (fun p => g p ^ ν)
  | 0 => by
    show HolomorphicAt n (fun p => g p ^ 0) x
    simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | ν + 1 => by
    have h := mul_mem_idealPow_succ (pow_mem_idealPow hg hhol ν) hg
      ((holomorphicAt_of_mem_idealPow (pow_mem_idealPow hg hhol ν)).mul hhol)
    exact mem_idealPow_congr h (Eventually.of_forall fun p => (pow_succ (g p) ν).symm)

/-- **Multiplicativity of the order**: if `g^ν ∈ 𝔪_x^{νμ}` with `ν ≥ 1`, then `g ∈ 𝔪_x^μ`. -/
theorem mem_idealPow_of_pow_mem {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x) {ν μ : ℕ}
    (hν : 1 ≤ ν) (h : (idealPow (pointIdeal n x) (ν * μ)).mem x (fun p => g p ^ ν)) :
    (idealPow (pointIdeal n x) μ).mem x g := by
  classical
  set e := complexChartAt (n := n) x
  set p := e.val x
  set G : ComplexModel n → ℂ := g ∘ e.val.symm
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hg)
  have hGU : DifferentiableOn ℂ G U := fun z hz => (hU z hz).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G U := analyticOnNhd_of_differentiableOn hUo hGU
  have hHU : DifferentiableOn ℂ (fun z => G z ^ ν) U := hGU.pow ν
  have hHan : AnalyticOnNhd ℂ (fun z => G z ^ ν) U := analyticOnNhd_of_differentiableOn hUo hHU
  have hgν : HolomorphicAt n (fun p => g p ^ ν) x := (holomorphicAt_of_mem_idealPow h)
  -- the two characterisations
  have hchar := mem_idealPow_pointIdeal_iff_iteratedFDeriv hg μ
  have hcharν := (mem_idealPow_pointIdeal_iff_iteratedFDeriv hgν (ν * μ)).mp h
  by_contra hgμ
  rw [hchar] at hgμ
  push Not at hgμ
  have hex : ∃ j, iteratedFDeriv ℂ j G p ≠ 0 := by
    obtain ⟨j, -, hj⟩ := hgμ
    exact ⟨j, hj⟩
  set a := Nat.find hex
  have ha : iteratedFDeriv ℂ a G p ≠ 0 := Nat.find_spec hex
  have hlow : ∀ i < a, iteratedFDeriv ℂ i G p = 0 := fun i hi => by
    simpa using Nat.find_min hex hi
  have haμ : a < μ := by
    obtain ⟨j, hj, hjne⟩ := hgμ
    exact lt_of_le_of_lt (Nat.find_min' hex hjne) hj
  -- polarization: a direction `y` on which the `a`-th derivative does not vanish
  obtain ⟨y, hy⟩ : ∃ y, iteratedFDeriv ℂ a G p (fun _ => y) ≠ 0 := by
    by_contra! hall
    exact ha (eq_zero_of_symmetric_of_apply_diag a _
      (fun σ m => ((hGan p hpU).contDiffAt).iteratedFDeriv_comp_perm m σ) hall)
  -- the restriction to the line `t ↦ p + t y`
  set φ : ℂ → ℂ := fun t => G (p + t • y)
  have hline : Continuous fun t : ℂ => p + t • y := continuous_const.add (continuous_id.smul continuous_const)
  have hφan : AnalyticAt ℂ φ 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => p + t • y) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have : AnalyticAt ℂ G (p + (0 : ℂ) • y) := by simpa using hGan p hpU
    exact AnalyticAt.comp (g := G) (f := fun t : ℂ => p + t • y) this hlin
  have hGcd : ContDiffOn ℂ ∞ G U := hGan.contDiffOn hUo.uniqueDiffOn
  have hHcd : ContDiffOn ℂ ∞ (fun z => G z ^ ν) U := hHan.contDiffOn hUo.uniqueDiffOn
  have hφder : ∀ i, iteratedDeriv i φ 0 = iteratedFDeriv ℂ i G p (fun _ => y) := fun i =>
    iteratedDeriv_comp_line hUo hGcd hpU y i
  have hφord : analyticOrderAt φ 0 = a := by
    have h1 : (a : ℕ∞) ≤ analyticOrderAt φ 0 :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hφan).mpr fun i hi => by
        rw [hφder i, hlow i hi]
        rfl
    have h2 : ¬ ((a + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt φ 0 := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hφan]
      intro hall
      exact hy (by rw [← hφder a]; exact hall a (Nat.lt_succ_self a))
    refine le_antisymm ?_ h1
    by_contra hlt
    exact h2 (Order.add_one_le_of_lt (lt_of_not_ge hlt))
  -- the `ν`-th power
  have hψ : (φ ^ ν) = fun t => (fun z => G z ^ ν) (p + t • y) := by
    funext t
    simp [φ]
  have hψder : ∀ i, iteratedDeriv i (φ ^ ν) 0 =
      iteratedFDeriv ℂ i (fun z => G z ^ ν) p (fun _ => y) := fun i => by
    rw [hψ]
    exact iteratedDeriv_comp_line hUo hHcd hpU y i
  have hHeq : (fun p => g p ^ ν) ∘ e.val.symm = fun z => G z ^ ν := rfl
  have hle : ((ν * μ : ℕ) : ℕ∞) ≤ analyticOrderAt (φ ^ ν) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hφan.pow ν)).mpr fun i hi => by
      rw [hψder i]
      have := hcharν i hi
      rw [hHeq] at this
      rw [this]
      rfl
  rw [analyticOrderAt_pow hφan, hφord] at hle
  have : ν * μ ≤ ν * a := by
    rw [nsmul_eq_mul] at hle
    exact_mod_cast hle
  have : ν * a < ν * μ := Nat.mul_lt_mul_of_pos_left haμ hν
  omega

/-! ### Cosupports of powers and of sums of marked ideals -/

variable {𝔞 𝔟 : GermIdeal n M}

/-- **`cosupp(𝔞^ν, μν) = cosupp(𝔞, μ)`** for `ν ≥ 1` (`N = M`, `𝔞` an ideal of holomorphic germs). -/
theorem cosupport_idealPow_mul_eq (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {ν : ℕ} (hν : 1 ≤ ν)
    (μ : ℕ) : cosupport n univ (idealPow 𝔞 ν) (μ * ν) = cosupport n univ 𝔞 μ := by
  refine Subset.antisymm ?_ (cosupport_subset_cosupport_idealPow μ ν)
  rintro x ⟨-, hx⟩
  refine ⟨mem_univ x, fun g hg => ⟨g, ?_, Eventually.of_forall fun _ _ => rfl⟩⟩
  have hpow := mem_idealPow_of_vanishesToOrderOn_univ (hx _ (pow_mem_idealPow hg (h𝔞 x g hg) ν))
  rw [Nat.mul_comm] at hpow
  exact mem_idealPow_of_pow_mem (h𝔞 x g hg) hν hpow

/-- **The sum of two marked ideals** (Włodarczyk `le:operations`(1)): for `μ, ν ≥ 1`,
`cosupp(𝔞^ν + 𝔟^μ, μν) = cosupp(𝔞, μ) ∩ cosupp(𝔟, ν)` (`N = M`). -/
theorem cosupport_sumIdeal_idealPow (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) {μ ν : ℕ} (hμ : 1 ≤ μ) (hν : 1 ≤ ν) :
    cosupport n univ (sumIdeal (idealPow 𝔞 ν) (idealPow 𝔟 μ)) (μ * ν) =
      cosupport n univ 𝔞 μ ∩ cosupport n univ 𝔟 ν := by
  rw [cosupport_sumIdeal (fun x g hg => holomorphicAt_of_mem_idealPow hg)
      (fun x g hg => holomorphicAt_of_mem_idealPow hg),
    cosupport_idealPow_mul_eq h𝔞 hν μ, Nat.mul_comm, cosupport_idealPow_mul_eq h𝔟 hμ ν]

end Iterated

end

end TranscendentalNakamaye.Pending.OrderMultiplicativity

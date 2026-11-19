import Hironaka.Analytic.GermPrimeNullstellensatz
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.MultiplierIdealBergmanNadelManifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Rückert's Nullstellensatz with a uniform power (Demailly, CADG II.4.22)

Source: Demailly, *Complex analytic and differential geometry*, II.4.22 (Rückert's
Nullstellensatz); the finite-cover globalisation is the one recorded in
`Hironaka.UniformNullstellensatzPowerInterface`.

For coherent ideal sheaves `𝔞, 𝔯 ⊆ 𝒪_M` on a compact complex manifold with
`Z(𝔯) ⊆ Z(𝔞)` there is `N > 0` with `𝔞^N ⊆ 𝔯` (`exists_idealPow_le_of_zeroLocus_subset`).
Its statement is character for character that of the named input
`UniformNullstellensatzPower.demaillyII422_exists_idealPow_le_of_zeroLocus_subset`.

## Proof

* **Germs, radical form** (`vanishingIdeal_le_radical`): for any ideal `I ⊆ 𝒪_n` containing the
  germs of `f_1, …, f_s`, a germ vanishing on `{f = 0}` lies in `√I`, because
  `√I = ⋂ {P prime ⊇ I}` and each prime contains the vanishing ideal
  (`GermPrimeNullstellensatz.vanishingIdeal_le_of_isPrime`).
* **Germs, power form** (`exists_powFam_eq_sum`): if the germs `g_i` vanish on `{r = 0}`, then
  `(g) ⊆ √(r)`, the ideal `(g)` is finitely generated, so `(g)^N ⊆ (r)`
  (`Ideal.exists_pow_le_of_le_radical_of_fg`); every product of `N` of the `g_i` is then an
  explicit holomorphic combination of the `r_j` near `0`.
* **On the manifold, at one point** (`exists_nhds_idealPow_le`): read the coherence generators
  `a_i` of `𝔞` and `r_j` of `𝔯` at `x` in the chart at `x`, translated to `0`; `Z(𝔯) ⊆ Z(𝔞)`
  says the `a_i` vanish on `{r = 0}`; the identities `∏ a_{σ l} = ∑ c_j r_j` pulled back to `M`
  hold on a neighbourhood of `x`, and a member of `𝔞^N` is a holomorphic combination of the
  products `∏ a_{σ l}` (`isInSpanAt_powFam_of_mem_idealPow`).
* **Compactness**: finitely many such neighbourhoods cover `M`; take the largest exponent
  (`idealPow_le_of_le`: `𝔞^{N'} ⊆ 𝔞^N` for `N ≤ N'`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.RueckertNullstellensatz

open Hironaka.HolomorphicIdealSheaves AnalyticGermDecomposition IdealWeightPowers
  IdealWeightComparison RelativePrincipalizationSpan GermIdealPullbackCalculus
open GermParametrizationFunctions (toGerm toGerm_mk rep toGerm_eq_rep
  eventually_differentiableAt_rep germ_coe_sum)

noncomputable section

/-! ### Products of generators -/

section PowFam

variable {X : Type*} {K : ℕ}

/-- `powFam a N σ = ∏_{l < N} a_{σ l}`, by recursion on `N`. -/
def powFam (a : Fin K → X → ℂ) : (N : ℕ) → (Fin N → Fin K) → X → ℂ
  | 0, _ => fun _ => 1
  | N + 1, σ => fun y => powFam a N (Fin.init σ) y * a (σ (Fin.last N)) y

theorem powFam_succ (a : Fin K → X → ℂ) (N : ℕ) (σ : Fin (N + 1) → Fin K) :
    powFam a (N + 1) σ = fun y => powFam a N (Fin.init σ) y * a (σ (Fin.last N)) y :=
  rfl

theorem powFam_snoc (a : Fin K → X → ℂ) (N : ℕ) (σ : Fin N → Fin K) (i : Fin K) :
    powFam a (N + 1) (Fin.snoc σ i) = fun y => powFam a N σ y * a i y := by
  rw [powFam_succ, Fin.init_snoc, Fin.snoc_last]

theorem powFam_comp {Y : Type*} (a : Fin K → X → ℂ) (φ : Y → X) :
    ∀ (N : ℕ) (σ : Fin N → Fin K), powFam (fun i => a i ∘ φ) N σ = powFam a N σ ∘ φ
  | 0, _ => rfl
  | N + 1, σ => by
      rw [powFam_succ, powFam_succ, powFam_comp a φ N]
      rfl

end PowFam

/-! ### Germs at `0 ∈ ℂⁿ` -/

section Germs

variable {n : ℕ}

/-- **Rückert's Nullstellensatz, radical form.**  If the germs of `f_1, …, f_s` lie in `I`, every
germ vanishing on `{f_1 = ⋯ = f_s = 0}` near `0` lies in `√I`. -/
theorem vanishingIdeal_le_radical (I : Ideal (HolGerm (ComplexModel n))) {s : ℕ}
    (f : Fin s → ComplexModel n → ℂ)
    (hf : ∀ j, ∃ hfj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f j) z, HolGerm.mk (f j) hfj ∈ I) :
    vanishingIdeal {z | ∀ j, f j z = 0} ≤ I.radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hIJ, hJp⟩ := hJ
  have : J.IsPrime := hJp
  exact GermPrimeNullstellensatz.vanishingIdeal_le_of_isPrime J f fun j =>
    (hf j).imp fun _ h => hIJ h

theorem eventually_differentiableAt_powFam {K : ℕ} (g : Fin K → ComplexModel n → ℂ)
    (hg : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g i) z) :
    ∀ (N : ℕ) (σ : Fin N → Fin K), ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (powFam g N σ) z
  | 0, _ => eventually_differentiableAt_const 1
  | N + 1, σ => eventually_differentiableAt_mul
      (eventually_differentiableAt_powFam g hg N (Fin.init σ)) (hg _)

theorem mk_powFam_mem_pow {K : ℕ} (g : Fin K → ComplexModel n → ℂ)
    (hg : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g i) z) :
    ∀ (N : ℕ) (σ : Fin N → Fin K),
      HolGerm.mk (powFam g N σ) (eventually_differentiableAt_powFam g hg N σ) ∈
        (Ideal.span (range fun i => HolGerm.mk (g i) (hg i))) ^ N
  | 0, _ => by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | N + 1, σ => by
      rw [pow_succ]
      have h := Ideal.mul_mem_mul (mk_powFam_mem_pow g hg N (Fin.init σ))
        (Ideal.subset_span ⟨σ (Fin.last N), rfl⟩ :
          HolGerm.mk (g (σ (Fin.last N))) (hg _) ∈
            Ideal.span (range fun i => HolGerm.mk (g i) (hg i)))
      rw [← HolGerm.mk_mul] at h
      exact h

/-- **Rückert's Nullstellensatz, power form, for germs.**  If the germs `g_i` vanish on the
common zero set of the `r_j` near `0`, then for some `N > 0` every product of `N` of the `g_i`
is a holomorphic combination of the `r_j` near `0`. -/
theorem exists_powFam_eq_sum {K R : ℕ} (g : Fin K → ComplexModel n → ℂ)
    (hg : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g i) z) (r : Fin R → ComplexModel n → ℂ)
    (hr : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r j) z)
    (hvan : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ j, r j z = 0) → g i z = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ σ : Fin N → Fin K, ∃ c : Fin R → ComplexModel n → ℂ,
      (∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (c j) z) ∧
      ∀ᶠ z in 𝓝 (0 : ComplexModel n), powFam g N σ z = ∑ j, c j z * r j z := by
  set Ir : Ideal (HolGerm (ComplexModel n)) :=
    Ideal.span (range fun j => HolGerm.mk (r j) (hr j)) with hIr
  set Ig : Ideal (HolGerm (ComplexModel n)) :=
    Ideal.span (range fun i => HolGerm.mk (g i) (hg i)) with hIg
  have hrad : Ig ≤ Ir.radical := by
    rw [hIg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine vanishingIdeal_le_radical Ir r (fun j => ⟨hr j, Ideal.subset_span ⟨j, rfl⟩⟩) ?_
    exact mem_vanishingIdeal_mk.2 (hvan i)
  have hfg : Ig.FG := Submodule.fg_span (finite_range _)
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  refine ⟨N + 1, N.succ_pos, fun σ => ?_⟩
  have hmem : HolGerm.mk (powFam g (N + 1) σ) (eventually_differentiableAt_powFam g hg _ σ) ∈ Ir :=
    hN (Ideal.pow_le_pow_right N.le_succ (mk_powFam_mem_pow g hg (N + 1) σ))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  refine ⟨fun j => rep (c j), fun j => eventually_differentiableAt_rep _, ?_⟩
  have h := congrArg toGerm hc
  simp only [map_sum, smul_eq_mul, map_mul, toGerm_mk] at h
  simp only [toGerm_eq_rep] at h
  have h2 : ((fun z => ∑ j, rep (c j) z * r j z : ComplexModel n → ℂ) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = (powFam g (N + 1) σ : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
    rw [germ_coe_sum]
    exact h
  exact (Germ.coe_eq.1 h2).mono fun z hz => hz.symm

end Germs

/-! ### On a complex manifold -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A product of two spanned germs is spanned by the pairwise products of the spanning
functions (`IdealWeightPowers.isInSpanAt_mulFamily_mul` for arbitrary spanning sets). -/
theorem isInSpanAt_mul {S T : (M → ℂ) → Prop} {y : M} {p q : M → ℂ}
    (hShol : ∀ s, S s → HolomorphicAt n s y) (hThol : ∀ t, T t → HolomorphicAt n t y)
    (hp : IsInSpanAt (n := n) S y p) (hq : IsInSpanAt (n := n) T y q) :
    IsInSpanAt (n := n) (fun u => ∃ s t, S s ∧ T t ∧ u = fun z => s z * t z) y
      (fun z => p z * q z) := by
  obtain ⟨-, K, s, α, hs, hα, hsum⟩ := hp
  obtain ⟨-, L, t, β, ht, hβ, hsum'⟩ := hq
  have hterm : ∀ k : Fin K × Fin L,
      IsInSpanAt (n := n) (fun u => ∃ s t, S s ∧ T t ∧ u = fun z => s z * t z) y
        (fun z => α k.1 z * β k.2 z * (s k.1 z * t k.2 z)) := by
    rintro ⟨i, j⟩
    exact isInSpanAt_of_eq_mul ⟨s i, t j, hs i, ht j, rfl⟩
      (((hα i).mul (hβ j)).mul ((hShol _ (hs i)).mul (hThol _ (ht j))))
      ((hα i).mul (hβ j)) (Eventually.of_forall fun _ => rfl)
  have hsum2 := IsInSpanAt.sum (n := n) (Finset.univ : Finset (Fin K × Fin L))
    fun k _ => hterm k
  refine isInSpanAt_congr hsum2 ?_
  filter_upwards [hsum, hsum'] with z hz hz'
  rw [hz, hz', Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem holomorphicAt_powFam {K : ℕ} {a : Fin K → M → ℂ} {y : M}
    (ha : ∀ i, HolomorphicAt n (a i) y) :
    ∀ (N : ℕ) (σ : Fin N → Fin K), HolomorphicAt n (powFam a N σ) y
  | 0, _ => holomorphicAt_const (n := n) 1
  | N + 1, σ => (holomorphicAt_powFam ha N (Fin.init σ)).mul (ha _)

/-- **A member of `𝔞^N` is a holomorphic combination of products of `N` generators.** -/
theorem isInSpanAt_powFam_of_mem_idealPow {𝔞 : GermIdeal n M} {U : Set M} {K : ℕ}
    {a : Fin K → M → ℂ} (ha_hol : ∀ y ∈ U, ∀ i, HolomorphicAt n (a i) y)
    (ha_iff : ∀ y ∈ U, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := n) (· ∈ range a) y g) :
    ∀ (N : ℕ), ∀ y ∈ U, ∀ v, (idealPow 𝔞 N).mem y v →
      IsInSpanAt (n := n) (· ∈ range (powFam a N)) y v
  | 0, y, _, v, hv => by
      rw [idealPow_zero, mem_unitIdeal_iff] at hv
      refine IsInSpanAt.mono ?_ hv
      rintro s ⟨_, rfl⟩
      exact ⟨Fin.elim0, rfl⟩
  | N + 1, y, hy, v, hv => by
      rw [idealPow_succ] at hv
      have hv' : IsInSpanAt (n := n)
          (fun s => ∃ p q, (idealPow 𝔞 N).mem y p ∧ 𝔞.mem y q ∧ s = p * q) y v := hv
      refine IsInSpanAt.trans ?_ hv'
      rintro s ⟨p, q, hp, hq, rfl⟩
      have h1 := isInSpanAt_powFam_of_mem_idealPow ha_hol ha_iff N y hy p hp
      have h2 := (ha_iff y hy q).1 hq
      have h3 := isInSpanAt_mul (n := n)
        (fun s hs => by obtain ⟨σ, rfl⟩ := hs; exact holomorphicAt_powFam (ha_hol y hy) N σ)
        (fun t ht => by obtain ⟨i, rfl⟩ := ht; exact ha_hol y hy i) h1 h2
      refine IsInSpanAt.mono ?_ h3
      rintro u ⟨s, t, ⟨σ, rfl⟩, ⟨i, rfl⟩, rfl⟩
      exact ⟨Fin.snoc σ i, powFam_snoc a N σ i⟩

/-- Members of a coherent ideal are holomorphic. -/
theorem holomorphicAt_of_mem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ}
    (hg : 𝔞.mem x g) : HolomorphicAt n g x := by
  obtain ⟨U, -, hxU, N, s, -, hgen⟩ := h𝔞 x
  exact ((hgen x hxU g).1 hg).1

/-- `𝔞^{N'} ⊆ 𝔞^N` for `N ≤ N'`, `𝔞` coherent. -/
theorem idealPow_le_of_le {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {N N' : ℕ} (h : N ≤ N') :
    (idealPow 𝔞 N').Le (idealPow 𝔞 N) := by
  induction N', h using Nat.le_induction with
  | base => exact fun _ _ hg => hg
  | succ k _ ih =>
      intro x g hg
      rw [idealPow_succ] at hg
      exact ih x g (mul_le_left (isCoherent_idealPow h𝔞 k)
        (fun hm => holomorphicAt_of_mem h𝔞 hm) x g hg)

/-- **Rückert's Nullstellensatz near one point.**  For coherent `𝔞, 𝔯` with
`Z(𝔯) ⊆ Z(𝔞)`, every point has a neighbourhood on which `𝔞^N ⊆ 𝔯` for some `N > 0`. -/
theorem exists_nhds_idealPow_le {𝔞 𝔯 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (h𝔯 : 𝔯.IsCoherent) (hz : 𝔯.zeroLocus ⊆ 𝔞.zeroLocus) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ, 0 < N ∧
      ∀ y ∈ U, ∀ v, (idealPow 𝔞 N).mem y v → 𝔯.mem y v := by
  classical
  obtain ⟨Ua, hUa, hxa, K, a, ha_diff, ha_iff⟩ := h𝔞 x
  obtain ⟨Ur, hUr, hxr, R, r, hr_diff, hr_iff⟩ := h𝔯 x
  have ha_hol : ∀ y ∈ Ua, ∀ i, HolomorphicAt n (a i) y := fun y hy i =>
    eventually_of_mem (hUa.mem_nhds hy) fun z hz =>
      (ha_diff i z hz).mdifferentiableAt (hUa.mem_nhds hz)
  have hr_hol : ∀ y ∈ Ur, ∀ j, HolomorphicAt n (r j) y := fun y hy j =>
    eventually_of_mem (hUr.mem_nhds hy) fun z hz =>
      (hr_diff j z hz).mdifferentiableAt (hUr.mem_nhds hz)
  set e := chartAt (ComplexModel n) x with he
  set x₀ : ComplexModel n := e x with hx₀
  have hxs : x ∈ e.source := mem_chart_source _ x
  -- the generators read in the chart, translated to `0`
  set aT : Fin K → ComplexModel n → ℂ := fun i z => a i (e.symm (z + x₀)) with haTdef
  set rT : Fin R → ComplexModel n → ℂ := fun j z => r j (e.symm (z + x₀)) with hrTdef
  have hT0 : Tendsto (fun z : ComplexModel n => z + x₀) (𝓝 0) (𝓝 x₀) := by
    simpa using ((continuous_add_const x₀).tendsto (0 : ComplexModel n))
  have hlift : ∀ f : M → ℂ, HolomorphicAt n f x →
      ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => f (e.symm (z + x₀))) z := by
    intro f hf
    filter_upwards [hT0.eventually
      (MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm hxs hf)]
      with z hz
    exact DifferentiableAt.comp (g := fun w => f (e.symm w))
      (f := fun z : ComplexModel n => z + x₀) z hz (differentiableAt_id.add_const x₀)
  have haT : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (aT i) z :=
    fun i => hlift (a i) (ha_hol x hxa i)
  have hrT : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (rT j) z :=
    fun j => hlift (r j) (hr_hol x hxr j)
  have hTs : Tendsto (fun z : ComplexModel n => e.symm (z + x₀)) (𝓝 0) (𝓝 x) := by
    have h := (e.continuousAt_symm (e.map_source hxs)).tendsto.comp hT0
    rwa [e.left_inv hxs] at h
  -- `Z(𝔯) ⊆ Z(𝔞)` in the chart
  have hvan : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ j, rT j z = 0) → aT i z = 0 := by
    intro i
    filter_upwards [hTs.eventually (hUa.mem_nhds hxa), hTs.eventually (hUr.mem_nhds hxr)]
      with z hza hzr hrz
    have hyZ : e.symm (z + x₀) ∈ 𝔯.zeroLocus := by
      intro g hg
      obtain ⟨-, N', s, c, hs, -, hsum⟩ := (hr_iff _ hzr g).1 hg
      rw [hsum.self_of_nhds]
      refine Finset.sum_eq_zero fun l _ => ?_
      obtain ⟨j, hj⟩ := hs l
      rw [← hj]
      have := hrz j
      simp only [hrTdef] at this
      rw [this, mul_zero]
    exact hz hyZ _ (mem_of_isPresentation hUa hza ha_diff ha_iff i)
  obtain ⟨N, hNpos, hN⟩ := exists_powFam_eq_sum aT haT rT hrT hvan
  choose c hc hceq using hN
  -- pull the identities back to `M`
  have hT' : Tendsto (fun y => e y - x₀) (𝓝 x) (𝓝 0) := by
    have h : Tendsto (fun y => e y - x₀) (𝓝 x) (𝓝 (x₀ - x₀)) :=
      ((e.continuousAt hxs).sub continuousAt_const).tendsto
    rwa [sub_self] at h
  set cH : (Fin N → Fin K) → Fin R → M → ℂ := fun σ j y => c σ j (e y - x₀) with hcHdef
  have hcH : ∀ σ j, HolomorphicAt n (cH σ j) x := by
    intro σ j
    refine MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart
      (W := fun w => c σ j (w - x₀)) hxs ?_
    have hT'' : Tendsto (fun w : ComplexModel n => w - x₀) (𝓝 x₀) (𝓝 0) := by
      simpa using ((continuous_sub_right x₀).tendsto x₀)
    filter_upwards [hT''.eventually (hc σ j)] with w hw
    exact DifferentiableAt.comp (g := c σ j) (f := fun w : ComplexModel n => w - x₀) w hw
      (differentiableAt_id.sub_const x₀)
  have hid : ∀ σ, ∀ᶠ y in 𝓝 x, powFam a N σ y = ∑ j, cH σ j y * r j y := by
    intro σ
    filter_upwards [hT'.eventually (hceq σ), e.open_source.mem_nhds hxs] with y hy hys
    have hback : e.symm (e y - x₀ + x₀) = y := by rw [sub_add_cancel, e.left_inv hys]
    have h1 : powFam aT N σ (e y - x₀) = powFam a N σ y := by
      have hcomp : aT = fun i => a i ∘ (fun z => e.symm (z + x₀)) := rfl
      rw [hcomp, powFam_comp]
      simp only [Function.comp_apply, hback]
    rw [← h1, hy]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hcHdef, hrTdef, hback]
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Ua ∧ y ∈ Ur ∧ ∀ σ, (∀ j, HolomorphicAt n (cH σ j) y) ∧
      (powFam a N σ =ᶠ[𝓝 y] fun y' => ∑ j, cH σ j y' * r j y') := by
    filter_upwards [hUa.mem_nhds hxa, hUr.mem_nhds hxr,
      eventually_all.2 fun σ => eventually_all.2 fun j => (hcH σ j).eventually_nhds,
      eventually_all.2 fun σ => (hid σ).eventually_nhds] with y h1 h2 h3 h4
    exact ⟨h1, h2, fun σ => ⟨h3 σ, h4 σ⟩⟩
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.1 hev
  refine ⟨U, hU, hxU, N, hNpos, fun y hy v hv => ?_⟩
  obtain ⟨hya, hyr, hyσ⟩ := hUsub hy
  have h1 := isInSpanAt_powFam_of_mem_idealPow (U := Ua) ha_hol ha_iff N y hya v hv
  refine (hr_iff y hyr v).2 (IsInSpanAt.trans ?_ h1)
  rintro s ⟨σ, rfl⟩
  obtain ⟨hhol, heq⟩ := hyσ σ
  exact ⟨holomorphicAt_powFam (ha_hol y hya) N σ, R, r, cH σ, fun j => ⟨j, rfl⟩, hhol, heq⟩

/-- **Rückert's Nullstellensatz with a uniform power** (Demailly, CADG II.4.22; compactness).
For coherent ideal sheaves on a compact complex manifold, `Z(𝔯) ⊆ Z(𝔞)` gives `N > 0` with
`𝔞^N ⊆ 𝔯`.  The statement is that of
`UniformNullstellensatzPower.demaillyII422_exists_idealPow_le_of_zeroLocus_subset`. -/
theorem exists_idealPow_le_of_zeroLocus_subset [CompactSpace M]
    {𝔞 𝔯 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔯 : 𝔯.IsCoherent)
    (hz : 𝔯.zeroLocus ⊆ 𝔞.zeroLocus) :
    ∃ N : ℕ, 0 < N ∧ (idealPow 𝔞 N).Le 𝔯 := by
  classical
  choose U hU hxU N hN hle using exists_nhds_idealPow_le h𝔞 h𝔯 hz
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨t.sup N + 1, Nat.succ_pos _, fun y v hv => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hNx : N x ≤ t.sup N + 1 := (Finset.le_sup hxt).trans (Nat.le_succ _)
  exact hle x y hyx v (idealPow_le_of_le h𝔞 hNx y v hv)

end Manifold

end

end Hironaka.RueckertNullstellensatz

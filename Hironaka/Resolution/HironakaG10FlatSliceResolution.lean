import Hironaka.Resolution.HironakaG10FlatResolutionStart
import Hironaka.Analytic.HolomorphicTaylorTail

/-! # Restricting a free resolution to a hyperplane on which the coordinate is regular

Sheaf-level input of Douady 1966, §7 n° 3, Prop. 6 (and §8 n° 3): if `𝓕 = coker d₀` is flat over
the `w`-line along `w = 0` — `w` is a non-zero-divisor on the stalks of `𝓕` at the points of
`{w = 0}` — then the restriction to `w = 0` of a free resolution of `𝓕` is a free resolution of the
fibre `𝓕(0) = coker d₀(0, ·)` (`Tor₁(𝓕, O/w) = 0`). All statements are at the level of germs, at
every point of a neighbourhood (`OkaRelationSheaf`).

* `RegularAt F φ y`: `φ` is a non-zero-divisor on `coker F` at `y` (`φ c ∈ im F ⇒ c ∈ im F`, germs);
  `NonZeroDivisorAt φ y`: `φ` is a non-zero-divisor on germs at `y`.
* `regularAt_of_exactStartOn`: inside a resolution, `φ` is automatically regular on `coker G` at the
  points where the start `(G, F)` is exact (exactness at `L₁` + `φ` a non-zero-divisor on germs).
* On `ℂ × P` (first coordinate `w`): `nonZeroDivisorAt_fst`; `exists_eq_fst_mul` (a germ vanishing
  on `w = 0` is divisible by `w`, from `HolomorphicTaylorTail.exists_taylor_tail`);
  **`isCombinationAt_slice`**, `exactStartOn_slice`: an exact start `(G, F)` with `w` regular on
  `coker F` restricts to an exact start `(G(0,·), F(0,·))` on `{z | (0, z) ∈ U}`;
  **`ResolvesOn.slice`**: a free resolution of length `m` of `coker F` restricts to a free resolution
  of length `m` of `coker F(0,·)`.
BP: hironaka-g10-flat-slice-resolution.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatSliceResolution
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HolomorphicTaylorTail

section General
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- `φ` is a non-zero-divisor on the cokernel of `F` at `y` (germs): if `φ c ∈ im F`, then
`c ∈ im F`. -/
def RegularAt (F : ι₀ → ι₁ → X → ℂ) (φ : X → ℂ) (y : X) : Prop :=
  ∀ c : ι₀ → X → ℂ, (∀ i, HolAt (c i) y) →
    IsCombinationAt (columns F) y (fun i x => φ x * c i x) → IsCombinationAt (columns F) y c

/-- `φ` is a non-zero-divisor on germs of holomorphic functions at `y`. -/
def NonZeroDivisorAt (φ : X → ℂ) (y : X) : Prop :=
  ∀ h : X → ℂ, HolAt h y → (∀ᶠ x in 𝓝 y, φ x * h x = 0) → ∀ᶠ x in 𝓝 y, h x = 0

/-- **Regularity is automatic in the interior of a resolution**: if `(G, F)` is an exact start on an
open `U` and `φ` is a non-zero-divisor on germs at `y ∈ U`, then `φ` is regular on `coker G` at `y`. -/
theorem regularAt_of_exactStartOn {U : Set X} {G : ι₁ → ι₂ → X → ℂ} {F : ι₀ → ι₁ → X → ℂ}
    (h : ExactStartOn U G F) (hU : IsOpen U) {y : X} (hy : y ∈ U) {φ : X → ℂ}
    (hφ : NonZeroDivisorAt φ y) : RegularAt G φ y := by
  intro c hc hφc
  obtain ⟨e, -, he⟩ := hφc
  refine h.exact y hy c ⟨hc, fun i => ?_⟩
  -- `φ · (F c) = F G e = 0`, so `F c = 0`
  refine hφ (fun x => ∑ j, c j x * F i j x)
    (HolAt.fintype_sum fun j => (hc j).mul (holAt_of_differentiableOn hU (h.holF i j) hy)) ?_
  have hev : ∀ᶠ x in 𝓝 y, (∀ j, φ x * c j x = ∑ k, e k x * G j k x) ∧ x ∈ U :=
    (eventually_all.2 fun j => he j).and (hU.mem_nhds hy)
  filter_upwards [hev] with x ⟨hx, hxU⟩
  calc φ x * ∑ j, c j x * F i j x = ∑ j, (φ x * c j x) * F i j x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, (∑ k, e k x * G j k x) * F i j x := Finset.sum_congr rfl fun j _ => by rw [hx j]
    _ = ∑ k, e k x * ∑ j, F i j x * G j k x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := Finset.sum_eq_zero fun k _ => by rw [h.comp i k x hxU, mul_zero]

end General

/-! ## Restriction to `w = 0` on `ℂ × P` -/

section Slice
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **The first coordinate is a non-zero-divisor on germs** (identity principle: `{w ≠ 0}` is dense). -/
theorem nonZeroDivisorAt_fst (y : ℂ × P) : NonZeroDivisorAt (fun x : ℂ × P => x.1) y := by
  intro h hh hφh
  obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hφh.and hh)
  refine eventually_nhds_iff.2 ⟨V, fun x hx => ?_, hVo, hyV⟩
  by_cases hx1 : x.1 = 0
  · have hL : Tendsto (fun t : ℂ => ((x.1 + t, x.2) : ℂ × P)) (𝓝[≠] 0) (𝓝 x) := by
      have hc : Continuous fun t : ℂ => ((x.1 + t, x.2) : ℂ × P) :=
        (continuous_const.add continuous_id).prodMk continuous_const
      have := hc.tendsto 0
      simp only [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun t : ℂ => h (x.1 + t, x.2)) (𝓝[≠] 0) (𝓝 (h x)) :=
      ((hV x hx).2.continuousAt.tendsto).comp hL
    have h0 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (x.1 + t, x.2) = 0 := by
      filter_upwards [hL.eventually (hVo.mem_nhds hx), self_mem_nhdsWithin] with t ht htne
      have := (hV _ ht).1
      rw [hx1, zero_add] at this ⊢
      exact (mul_eq_zero.mp this).resolve_left htne
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (h0.mono fun t ht => ht.symm))
  · exact (mul_eq_zero.mp (hV x hx).1).resolve_left hx1

/-- **Division by the first coordinate**: a germ at a point of `{w = 0}` vanishing on `{w = 0}` is
`w` times a germ. -/
theorem exists_eq_fst_mul {G : ℂ × P → ℂ} {y : ℂ × P} (hG : HolAt G y) (hy : y.1 = 0)
    (hvan : ∀ᶠ z in 𝓝 y.2, G (0, z) = 0) :
    ∃ c : ℂ × P → ℂ, HolAt c y ∧ ∀ᶠ x in 𝓝 y, G x = x.1 * c x := by
  obtain ⟨H, hHd, hHeq⟩ := exists_taylor_tail hG ((1 : ℂ), (0 : P)) 1
  -- the linear map `x ↦ ((0, x.2), x.1)` sends `y` to `(y, 0)`
  set L : ℂ × P → (ℂ × P) × ℂ := fun x => (((0 : ℂ), x.2), x.1) with hLdef
  have hLc : Continuous L := (continuous_const.prodMk continuous_snd).prodMk continuous_fst
  have hLd : ∀ x, DifferentiableAt ℂ L x := fun x =>
    ((differentiableAt_const _).prodMk differentiableAt_snd).prodMk differentiableAt_fst
  have hLy : L y = (y, 0) := by
    rw [hLdef]
    simp only
    rw [← hy]
  have hLt : Tendsto L (𝓝 y) (𝓝 (y, (0 : ℂ))) := hLy ▸ hLc.continuousAt.tendsto
  refine ⟨fun x => H (L x), ?_, ?_⟩
  · exact (hLt.eventually hHd).mono fun x hx => hx.comp x (hLd x)
  · have h2 : Tendsto (fun x : ℂ × P => x.2) (𝓝 y) (𝓝 y.2) := continuous_snd.continuousAt.tendsto
    filter_upwards [hLt.eventually hHeq, h2.eventually hvan] with x hx hx0
    have hpt : (L x).1 + (L x).2 • ((1 : ℂ), (0 : P)) = x := by
      rw [hLdef]
      ext
      · simp
      · simp
    rw [hpt] at hx
    rw [hx]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
      List.replicate_zero, iterDeriv_nil, pow_zero, mul_one, one_mul, pow_one]
    show G ((0 : ℂ), x.2) + x.1 * H (L x) = x.1 * H (L x)
    rw [hx0, zero_add]

/-- The restriction of a matrix of functions on `ℂ × P` to `w = 0`. -/
def sliceZero {κ ι : Type*} (F : κ → ι → ℂ × P → ℂ) : κ → ι → P → ℂ := fun i j z => F i j (0, z)

omit [NormedSpace ℂ P] in
theorem tendsto_zero_prod (z₀ : P) :
    Tendsto (fun z : P => ((0 : ℂ), z)) (𝓝 z₀) (𝓝 ((0 : ℂ), z₀)) :=
  (continuous_const.prodMk continuous_id).continuousAt.tendsto

theorem HolAt.comp_zero_prod {f : ℂ × P → ℂ} {z₀ : P} (hf : HolAt f ((0 : ℂ), z₀)) :
    HolAt (fun z : P => f (0, z)) z₀ :=
  ((tendsto_zero_prod z₀).eventually hf).mono fun z hz =>
    hz.comp z ((differentiableAt_const _).prodMk differentiableAt_id)

theorem differentiableOn_sliceZero {κ ι : Type*} {U : Set (ℂ × P)} {D : κ → ι → ℂ × P → ℂ}
    (hD : ∀ i j, DifferentiableOn ℂ (D i j) U) (i : κ) (j : ι) :
    DifferentiableOn ℂ (sliceZero D i j) {z : P | ((0 : ℂ), z) ∈ U} :=
  (hD i j).comp ((differentiableOn_const _).prodMk differentiableOn_id) fun _ hz => hz

/-- **Restriction of an exact start to `w = 0`, pointwise**: if `(G, F)` is an exact start on an
open `U` and `w` is regular on `coker F` at `(0, z₀)`, every relation of `F(0,·)` at `z₀` is a
combination of the columns of `G(0,·)`. -/
theorem isCombinationAt_slice {U : Set (ℂ × P)} {G : ι₁ → ι₂ → ℂ × P → ℂ}
    {F : ι₀ → ι₁ → ℂ × P → ℂ} (h : ExactStartOn U G F) (hU : IsOpen U) {z₀ : P}
    (hz₀ : ((0 : ℂ), z₀) ∈ U) (hreg : RegularAt F (fun x => x.1) ((0 : ℂ), z₀))
    (b : ι₁ → P → ℂ) (hb : IsRelationAt (sliceZero F) z₀ b) :
    IsCombinationAt (columns (sliceZero G)) z₀ b := by
  set y : ℂ × P := ((0 : ℂ), z₀) with hydef
  have hFy : ∀ i j, HolAt (F i j) y := fun i j => holAt_of_differentiableOn hU (h.holF i j) hz₀
  -- `b` extended constantly in `w`
  set bt : ι₁ → ℂ × P → ℂ := fun j x => b j x.2 with hbt
  have hbt_hol : ∀ j, HolAt (bt j) y := fun j =>
    (hb.1 j).comp (f := b j) (φ := fun x : ℂ × P => x.2) continuous_snd fun x => differentiableAt_snd
  -- `F bt` vanishes on `w = 0`, hence is `w · c`
  have hdiv : ∀ i, ∃ c : ℂ × P → ℂ, HolAt c y ∧
      ∀ᶠ x in 𝓝 y, ∑ j, bt j x * F i j x = x.1 * c x := by
    intro i
    refine exists_eq_fst_mul (HolAt.fintype_sum fun j => (hbt_hol j).mul (hFy i j)) rfl ?_
    exact hb.2 i
  choose c hc hcF using hdiv
  -- regularity: `c ∈ im F`
  obtain ⟨e, he, hce⟩ := hreg c hc ⟨bt, hbt_hol, fun i => (hcF i).mono fun x hx => hx.symm⟩
  -- `bt − w e` is a relation of `F`, hence a combination of the columns of `G`
  have hrel : IsRelationAt F y (fun j x => bt j x - x.1 * e j x) := by
    refine ⟨fun j => (hbt_hol j).sub ((holAt_of_differentiableOn isOpen_univ
      (differentiableOn_fst) (mem_univ y)).mul (he j)), fun i => ?_⟩
    have hev : ∀ᶠ x in 𝓝 y, ∑ j, bt j x * F i j x = x.1 * c i x ∧
        c i x = ∑ j, e j x * F i j x := (hcF i).and (hce i)
    filter_upwards [hev] with x ⟨h1, h2⟩
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [h1, h2, Finset.mul_sum]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨f, hf, hfG⟩ := h.exact y hz₀ _ hrel
  -- restrict to `w = 0`
  refine ⟨fun l z => f l (0, z), fun l => HolAt.comp_zero_prod (hf l), fun j => ?_⟩
  filter_upwards [(tendsto_zero_prod z₀).eventually (hfG j)] with z hz
  simp only [hbt, zero_mul, sub_zero] at hz
  exact hz

/-- **An exact start restricts to an exact start on `w = 0`** when `w` is regular on `coker F` at
the points of `U ∩ {w = 0}`. -/
theorem exactStartOn_slice {U : Set (ℂ × P)} {G : ι₁ → ι₂ → ℂ × P → ℂ}
    {F : ι₀ → ι₁ → ℂ × P → ℂ} (h : ExactStartOn U G F) (hU : IsOpen U)
    (hreg : ∀ z : P, ((0 : ℂ), z) ∈ U → RegularAt F (fun x => x.1) ((0 : ℂ), z)) :
    ExactStartOn {z : P | ((0 : ℂ), z) ∈ U} (sliceZero G) (sliceZero F) := by
  exact ⟨differentiableOn_sliceZero h.holF, differentiableOn_sliceZero h.holG,
    fun i k z hz => h.comp i k _ hz,
    fun z hz b hb => isCombinationAt_slice h hU hz (hreg z hz) b hb⟩

/-- **A free resolution restricts to a free resolution of the fibre** (`Tor₁(𝓕, O/w) = 0`): if
`ResolvesOn U m F` on an open `U` and `w` is regular on `coker F` at the points of `U ∩ {w = 0}`,
then `ResolvesOn {z | (0, z) ∈ U} m F(0,·)`. -/
theorem ResolvesOn.slice {U : Set (ℂ × P)} (hU : IsOpen U) :
    ∀ (m : ℕ) {a b : ℕ} (F : Fin a → Fin b → ℂ × P → ℂ), ResolvesOn U m F →
      (∀ z : P, ((0 : ℂ), z) ∈ U → RegularAt F (fun x => x.1) ((0 : ℂ), z)) →
      ResolvesOn {z : P | ((0 : ℂ), z) ∈ U} m (sliceZero F)
  | 0, _, _, F, hres, _ => differentiableOn_sliceZero hres
  | m + 1, _, _, F, hres, hreg => by
      obtain ⟨c, G, hGF, hres'⟩ := hres
      exact ⟨c, sliceZero G, exactStartOn_slice hGF hU hreg, ResolvesOn.slice hU m G hres'
        fun z hz => regularAt_of_exactStartOn hGF hU hz (nonZeroDivisorAt_fst _)⟩

end Slice

end
end Hironaka.HironakaG10FlatSliceResolution

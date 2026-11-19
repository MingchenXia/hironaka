import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.SimultaneousNormalCrossings

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Blowing up a codimension-one centre inside the support of a marked ideal of maximal order

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor): "After the
blow-up `σ` at such a component `C ⊆ supp(𝓘, μ)` the induced support `supp(𝓘', μ)` does not
intersect the exceptional divisor of `σ`" -- used in Step 1ba of the algorithm (elimination of the
codimension-one components of the support).  Blueprint `bcalc:codim-one` (chapter
`blowup-calculus.tex`).

Pointwise form (`notMem_cosupport_controlledTransform_of_codim_one`): let `C ⊆ cosupp(𝔞, μ)`
(`μ ≥ 1`, `𝔞` coherent, orders on the whole manifold) be the centre of the blowup `π`, of dimension
`n - 1` at `x = π z`, and let `ord_x 𝔞 ≤ μ` (`x ∉ cosupp(𝔞, μ + 1)`).  Then `z ∉ cosupp(σ^c(𝔞, μ), μ)`.
Proof: near `x`, `𝓘_C = (u)` (flattening coordinates, Hadamard); the Hadamard bridge gives
`𝔞 ⊆ 𝓘_C^μ = (u^μ)`; an element `f = c · u^μ` of `𝔞_x` of order `μ` has `c(x) ≠ 0`; and
`u ∘ π = d · h` with `d(z) ≠ 0` for a local equation `h` of the exceptional divisor (both `u ∘ π` and
`h` generate `π^*𝓘_C` at `z`).  So `f ∘ π = h^μ · (c ∘ π) d^μ` and the controlled transform contains
the unit `(c ∘ π) d^μ` at `z`.

For a marked ideal of maximal order (`D^μ 𝔞 = 𝒪`) every point has `ord_x 𝔞 ≤ μ`
(`notMem_cosupport_succ_of_isMaximalOrder`), whence `le:codim1`'s transform half
(`cosupport_controlledTransform_inter_preimage_eq_empty`) and its marked-ideal form for the
corrected transform (`cosupp_geoTransform_inter_preimage_eq_empty`).

Not here: the first half of `le:codim1` (the codimension-one components of the support are smooth
and isolated).

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOneCentre

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  BlowupFlatCoordinates BlowupControlledTransform BlowupExceptionalDivisor BlowupFunctionTransform
  BlowupDerivativeIdeal HadamardBridge DerivativeIdeal MaximalContact VanishingIdealCoherent
  RelativePrincipalizationSpan SimultaneousNormalCrossings MarkedIdeals IdealWeightPowers

noncomputable section

variable {n : ℕ}

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The ideal of a hypersurface is locally principal**: if `C` is regular of dimension `n - 1`
at `x` (`0 < n`), a flattening coordinate generates `𝓘_C` at every point of a neighbourhood of
`x`. -/
theorem exists_generator_vanishingIdeal_of_regularAtDim {C : Set X} {x : X} (hn : 0 < n)
    (hC : RegularAtDim (n := n) C x (n - 1)) :
    ∃ (U : Set X) (u : X → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, HolomorphicAt n u y) ∧
      ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) C).mem y g ↔ IsInSpanAt (n := n) (· = u) y g := by
  obtain ⟨-, -, Φ, hΦt, -, hflat⟩ := hC
  set last : Fin n := ⟨n - 1, Nat.sub_lt hn one_pos⟩ with hlast
  refine ⟨flatDomain (y₀ := x) Φ, flatCoord (y₀ := x) Φ last, isOpen_flatDomain Φ,
    mem_flatDomain_self Φ, fun y hy => holomorphicAt_flatCoord Φ last hy,
    fun y hy g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦt hflat hy hg
    refine isInSpanAt_of_eq_mul rfl hg.1 (hbhol last) ?_
    filter_upwards [hbeq] with y' h
    rw [h, Finset.sum_eq_single last]
    · intro i _ hi
      rw [hb0 i (by
        have h1 := i.2
        have h2 : i.1 ≠ n - 1 := fun h => hi (Fin.ext h)
        omega)]
      simp
    · simp
  · exact mem_vanishingIdeal_of_isInSpanAt (g := fun _ : Fin 1 => flatCoord (y₀ := x) Φ last)
      (fun _ => flatCoord_mem_vanishingIdeal Φ hflat le_rfl hy)
      (hg.mono fun s hs => ⟨0, hs.symm⟩)

/-- Vanishing to order `q` passes to germs that agree near the point. -/
theorem VanishesToOrderOn.congr {N : Set X} {x : X} {q : ℕ} {f g : X → ℂ}
    (hf : VanishesToOrderOn n N x q f) (hfg : f =ᶠ[𝓝 x] g) : VanishesToOrderOn n N x q g := by
  obtain ⟨h, hh, hfh⟩ := hf
  exact ⟨h, hh, by filter_upwards [hfh, hfg] with y h1 h2 hy; rw [← h2, h1 hy]⟩

/-- A holomorphic germ vanishing at `x` has order `≥ μ` in its `μ`-th power. -/
theorem vanishesToOrderOn_pow {N : Set X} {x : X} (hxN : x ∈ N) {u : X → ℂ}
    (hu : HolomorphicAt n u x) (hux : u x = 0) :
    ∀ μ : ℕ, VanishesToOrderOn n N x μ (fun y => u y ^ μ)
  | 0 => by simpa using vanishesToOrderOn_zero (N := N) (holomorphicAt_const (1 : ℂ) (x := x))
  | μ + 1 => by
    have h1 : VanishesToOrderOn n N x 1 u := (vanishesToOrderOn_one_iff hxN hu).mpr hux
    simpa [pow_succ] using (vanishesToOrderOn_pow hxN hu hux μ).mul h1

/-- **An element of order `μ` in `(u^μ)` has a unit cofactor**: if `f = c · u^μ` near `x` with
`u(x) = 0` and `f` not of order `≥ μ + 1` at `x`, then `c(x) ≠ 0`. -/
theorem apply_ne_zero_of_not_vanishesToOrderOn {x : X} {u c f : X → ℂ} (hu : HolomorphicAt n u x)
    (hux : u x = 0) (hc : HolomorphicAt n c x) {μ : ℕ}
    (hfc : f =ᶠ[𝓝 x] fun y => c y * u y ^ μ)
    (hfo : ¬ VanishesToOrderOn n univ x (μ + 1) f) : c x ≠ 0 := by
  intro hc0
  apply hfo
  have h1 : VanishesToOrderOn n univ x 1 c := (vanishesToOrderOn_one_iff (mem_univ x) hc).mpr hc0
  have h2 := h1.mul (vanishesToOrderOn_pow (mem_univ x) hu hux μ)
  rw [Nat.add_comm] at h2
  exact VanishesToOrderOn.congr h2 hfc.symm

end Local

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The controlled transform contains a unit over a codimension-one point of the centre where
the order is exactly `μ`** (Wlodarczyk `le:codim1`, pointwise). -/
theorem notMem_cosupport_controlledTransform_of_codim_one (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ)
    (hsub : C ⊆ cosupport n univ 𝔞 μ) {z : Y} (hzC : π z ∈ C)
    (hcodim : RegularAtDim (n := n) C (π z) (n - 1))
    (hord : π z ∉ cosupport n univ 𝔞 (μ + 1)) :
    z ∉ cosupport n univ (controlledTransform hπ 𝔞 μ) μ := by
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨U, u, -, hxU, hu, hgen⟩ := exists_generator_vanishingIdeal_of_regularAtDim hn hcodim
  have hπat : ∀ᶠ y' in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y' :=
    Eventually.of_forall fun y' => hπ.contMDiff y'
  -- an element of `𝔞` of order exactly `μ` at `π z`
  obtain ⟨f, hf, hfo⟩ : ∃ f, 𝔞.mem (π z) f ∧ ¬ VanishesToOrderOn n univ (π z) (μ + 1) f := by
    by_contra hall
    push Not at hall
    exact hord ⟨mem_univ _, fun f hf => hall f hf⟩
  -- the Hadamard bridge: `f = c · u^μ`
  have hfC : (idealPow (vanishingIdeal (n := n) C) μ).mem (π z) f :=
    le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 hsub (π z) f hf
  obtain ⟨-, c, hc, hfc⟩ := isInSpanAt_eq_iff.mp
    ((idealPow_mem_iff_of_generator hu hgen μ (π z) hxU f).mp hfC)
  have humem : (vanishingIdeal (n := n) C).mem (π z) u :=
    (hgen _ hxU u).mpr (isInSpanAt_of_eq_mul rfl (hu _ hxU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp))
  have hux : u (π z) = 0 := humem.2.self_of_nhds hzC
  have hcx : c (π z) ≠ 0 := apply_ne_zero_of_not_vanishesToOrderOn (hu _ hxU) hux hc hfc hfo
  -- a local equation `h` of the exceptional divisor; `u ∘ π = d · h`
  obtain ⟨U', h, hzU', hh⟩ := exists_isLocalEquation hπ z
  have huπ : (exceptionalDivisor hπ).ideal.mem z (u ∘ π) := by
    rw [exceptionalDivisor_ideal, GermIdeal.mem_pullback_iff]
    exact isInSpanAt_of_eq_mul ⟨u, humem, rfl⟩ ((hu _ hxU).comp_contMDiff hπat)
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)
  obtain ⟨-, d, hd, hud⟩ := isInSpanAt_eq_iff.mp ((hh.generates z hzU' _).mp huπ)
  -- `h = d' · (u ∘ π)`
  have hhmem : (exceptionalDivisor hπ).ideal.mem z h :=
    (hh.generates z hzU' h).mpr (isInSpanAt_of_eq_mul rfl (hh.holomorphicAt hzU')
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp))
  have hhu : IsInSpanAt (n := n) (· = u ∘ π) z h := by
    rw [exceptionalDivisor_ideal, GermIdeal.mem_pullback_iff] at hhmem
    refine IsInSpanAt.trans (fun s hs => ?_) hhmem
    obtain ⟨a, ha, rfl⟩ := hs
    obtain ⟨hahol, e, he, hae⟩ := isInSpanAt_eq_iff.mp ((hgen _ hxU a).mp ha)
    refine isInSpanAt_of_eq_mul rfl (hahol.comp_contMDiff hπat) (he.comp_contMDiff hπat) ?_
    filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hae] with y hy
    exact hy
  obtain ⟨-, d', hd', hhd'⟩ := isInSpanAt_eq_iff.mp hhu
  -- `d' d = 1` near `z`, so `d z ≠ 0`
  have hdd : (fun y => d' y * d y) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
    refine eventuallyEq_of_pow_mul hh hzU' (μ := 1) (hd'.mul hd) (holomorphicAt_const 1) ?_
    filter_upwards [hud, hhd'] with y h1 h2
    have h3 : h y = d' y * (d y * h y) := by
      rw [← h1]
      exact h2
    simp only [pow_one, mul_one]
    linear_combination -h3
  have hdz : d z ≠ 0 := by
    intro h0
    have := hdd.self_of_nhds
    simp only [h0, mul_zero] at this
    exact zero_ne_one this
  -- the controlled transform contains `(c ∘ π) · d^μ`
  have hmem : (controlledTransform hπ 𝔞 μ).mem z (fun y => c (π y) * d y ^ μ) := by
    refine mem_controlledTransform_of_eq_pow_mul hh hzU' hf
      ((hc.comp_contMDiff hπat).mul (BlowupFunctionTransform.holomorphicAt_pow hd μ)) ?_
    filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hfc, hud] with y h1 h2
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
    ring
  have hhol : HolomorphicAt n (fun y => c (π y) * d y ^ μ) z :=
    (hc.comp_contMDiff hπat).mul (BlowupFunctionTransform.holomorphicAt_pow hd μ)
  rintro ⟨-, hz⟩
  have h1 := (vanishesToOrderOn_one_iff (mem_univ z) hhol).mp ((hz _ hmem).mono hμ)
  exact mul_ne_zero hcx (pow_ne_zero μ hdz) h1

/-- **A marked ideal of maximal order has order at most `μ` everywhere**:
`cosupp(𝔞, μ + 1) = ∅` when `D^μ 𝔞 = 𝒪`. -/
theorem notMem_cosupport_succ_of_isMaximalOrder {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔞 : GermIdeal n M} {μ : ℕ}
    (hmax : IsMaximalOrder 𝔞 μ) (x : M) : x ∉ cosupport n univ 𝔞 (μ + 1) := by
  intro hx
  have h := cosupport_add_subset_cosupport_iterDerivIdeal 𝔞 1 μ (by rwa [Nat.add_comm] at hx)
  have h1 := (vanishesToOrderOn_one_iff (mem_univ x) (holomorphicAt_const 1)).mp (h.2 _ (hmax x))
  exact one_ne_zero h1

/-- **Wlodarczyk `le:codim1`, transform half**: if `(𝔞, μ)` is of maximal order (`μ ≥ 1`, `𝔞`
coherent) and the centre `C ⊆ cosupp(𝔞, μ)` has dimension `n - 1` at each of its points, then after
the blowup along `C` the cosupport of `σ^c(𝔞, μ)` does not meet the exceptional divisor. -/
theorem cosupport_controlledTransform_inter_preimage_eq_empty (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    (hsub : C ⊆ cosupport n univ 𝔞 μ) (hcodim : ∀ x ∈ C, RegularAtDim (n := n) C x (n - 1)) :
    cosupport n univ (controlledTransform hπ 𝔞 μ) μ ∩ π ⁻¹' C = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hz =>
    notMem_cosupport_controlledTransform_of_codim_one hπ h𝔞 hμ hsub hz.2 (hcodim _ hz.2)
      (notMem_cosupport_succ_of_isMaximalOrder hmax _) hz.1

/-- **`le:codim1`, transform half, for marked ideals with `N = M`**: the cosupport of the
corrected transform does not meet the new exceptional divisor. -/
theorem cosupp_geoTransform_inter_preimage_eq_empty {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hmax : IsMaximalOrder 𝔪.ideal 𝔪.d)
    (hπ : IsBlowupAlong n C π) (hsub : C ⊆ 𝔪.cosupp)
    (hcodim : ∀ x ∈ C, RegularAtDim (n := n) C x (n - 1)) :
    (𝔪.geoTransform C π).cosupp ∩ π ⁻¹' C = ∅ := by
  have hsub' : C ⊆ cosupport n univ 𝔪.ideal 𝔪.d := by
    intro x hx
    have := hsub hx
    rwa [MarkedIdeal.cosupp, hN] at this
  have h := cosupport_controlledTransform_inter_preimage_eq_empty hπ h𝔞 hd hmax hsub' hcodim
  rw [MarkedIdeal.cosupp, MarkedIdeal.geoTransform_N_eq_univ (C := C) (π := π) hN hπ,
    MarkedIdeal.geoTransform_ideal_eq_controlledTransform (C := C) (π := π) hN h𝔞 hπ,
    MarkedIdeal.geoTransform_d]
  exact h

end Blowup

end

end Hironaka.CodimOneCentre

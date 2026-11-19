import Hironaka.Invariant.MonomialPart
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Monomial ideals under the blowup of a centre with normal crossings: the generator form

Hironaka phase H2 (TN3), the design node `hir:monomial-blowup` (`blueprint/src/hironaka.tex`), taken
by TN3 on TN-CLASSICAL's request (I-0977 C-0059 / C-0060 / C-0061), in the generator form.
Blueprint `bcalc:monomial-chart`, `bcalc:monomial-transform` (chapter `blowup-calculus.tex`).
Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the monomial charts of `le:inclusions` and
Step 2b of the proof of `pr:resol` (the transform of a monomial marked ideal); Bierstone--Milman
2008 (`bierstone-milman08-functoriality`) §5.

Let `π : Y → X` be the blowup along `C`, `E` a simple normal crossings divisor with which `C` has
only normal crossings, and `z ∈ Y` over `C`.

* `exists_monomial_chart`: there are a monomial chart `W` (holomorphic on an open `U ∋ z`, with
  injective differential at `z`, so `W - W z` is a coordinate system at `z`), an index `j` and
  indices `s i` of the members, such that `𝒪(-D) = (W_j)` at every point of `U`; for every member
  `E_i` whose strict transform `E_i'` passes through `z`, `𝓘_{E_i'} = (W_{s i})` on `U`, with
  `s i ≠ j`, `W_{s i}(z) = 0`, the `s i` distinct; and for local generators `u_i` of `𝓘_{E_i}` at
  `π z` and exponents `a_i`,
  `(∏_{π z ∈ E_i} u_i^{a_i}) ∘ π = c · W_j^{e} · ∏_{z ∈ E_i'} W_{s i}^{a_i}` near `z`, with
  `c(z) ≠ 0` and `e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`.
* `mem_controlledTransform_iff_of_eq`: if `𝔞 = (m)` at `π z` and `m ∘ π = c · h^e · q` near `z`
  with `𝒪(-D) = (h)`, `c(z) ≠ 0` and `μ ≤ e`, then `σ^c(𝔞, μ) = (h^{e-μ} q)` at `z`.
* `exists_monomial_chart_transform`: hence the controlled transform of a monomial ideal
  `(∏ u_i^{a_i})` with mark `μ ≤ e` is generated at `z` by `W_j^{e-μ} ∏_{z ∈ E_i'} W_{s i}^{a_i}`
  (`a_D = ∑_{C ⊆ E_i} a_i - μ`, `S(z) = {i | z ∈ E_i'}`); `mem_geoTransform_iff_of_eq`: the same
  for the transform of a marked ideal `(M, M, E, 𝔞, d)` (`N = M`, coherent ideal).
* `frequently_ne_zero_of_generator`: a local generator of `𝒪(-D)` vanishes identically near no
  point.
* `exists_snc_chart_geoTransform` (and `_of_flat`, from flat coordinates at `π z`): the same in
  coordinates `Θ` centred at `z` adapted to `E' = (E_1', …, E_s', π⁻¹ C)` -- the members of `E'`
  through `z` are the hyperplanes `{Θ_{σ i} = 0}` (`σ` injective on them) and the transformed ideal
  of `(M, M, E, 𝔞, d)` is `(∏_{z ∈ E'_i} Θ_{σ i}^{a'_i})` at `z`, `a'_i = a_i` (`i < s`),
  `a'_s = e - d`: the input shape of `MonomialCase` (section `Principal`).  Helpers:
  `mem_centre_iff_of_generator`, `mem_iff_of_vanishingIdeal_eq` (zero sets from generators),
  `prod_map_append_singleton`.

Proof of the chart statement: coordinates `Φ` at `π z` adapted to `C` and `E`
(`SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`), `E_i = {Φ_{s i} = 0}`; the
monomial chart `σⱼ` through `z` (`exists_monomialLocalInverse`), `Φ ∘ π = σⱼ(W)`; then
`Φ_{s i} ∘ π = W_{s i} W_j` (`k_C ≤ s i ≠ j`, the members containing `C`), `= W_j` (`s i = j`),
or `= W_{s i}` (`s i < k_C`); the generators `u_i` differ from `Φ_{s i}` by units
(`exists_unit_of_isInSpanAt`), and the factors `W_{s i}` with `W_{s i}(z) ≠ 0` are units too.
"`C ⊆ E_i` near `π z` iff `k_C ≤ s i`" is `eventually_subset_iff_le` (as in `MemberPullback`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupFlatCoordinates
  Hironaka.BlowupMonomialCharts
  Hironaka.BlowupLocalSurjectivity
  Hironaka.BlowupExceptionalDivisor
  Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupStrictIdeal
  Hironaka.BlowupSNCTransform Hironaka.NormalCrossings
  Hironaka.SimultaneousNormalCrossings
  Hironaka.MemberPullback
  Hironaka.MonomialPart Hironaka.GermIdealOrder
  Hironaka.IdealWeightPowers
  Hironaka.BlowupControlledTransform
  Hironaka.InvertibleIdealQuotient

noncomputable section

variable {n : ℕ}

/-! ### Generators of one principal ideal differ by a unit -/

section Germ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Two generators of one principal ideal differ by a unit**: if `u ∈ (φ)` and `φ ∈ (u)` at `x`,
and `φ` vanishes identically near no point (frequently nonzero near `x`), then `u = c φ` near `x`
with `c(x) ≠ 0`. -/
theorem exists_unit_of_isInSpanAt {x : M} {u φ : M → ℂ}
    (huφ : IsInSpanAt (n := n) (· = φ) x u) (hφu : IsInSpanAt (n := n) (· = u) x φ)
    (hne : ∃ᶠ y in 𝓝 x, φ y ≠ 0) :
    ∃ c : M → ℂ, HolomorphicAt n c x ∧ c x ≠ 0 ∧ u =ᶠ[𝓝 x] fun y => c y * φ y := by
  obtain ⟨-, c, hc, hcu⟩ := isInSpanAt_eq_iff.mp huφ
  obtain ⟨hφ, c', hc', hcφ⟩ := isInSpanAt_eq_iff.mp hφu
  refine ⟨c, hc, fun h0 => ?_, hcu⟩
  have hf : HolomorphicAt n (fun y => 1 - c' y * c y) x :=
    GiraudAlong.holomorphicAt_sub (holomorphicAt_const 1) (hc'.mul hc)
  have h1 : (fun y => (1 - c' y * c y) * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hcu, hcφ] with y h1 h2
    have h3 : φ y = c' y * (c y * φ y) := by rw [← h1]; exact h2
    show (1 - c' y * c y) * φ y = 0
    linear_combination h3
  have h3 := (eventually_eq_zero_of_mul_eventually_eq_zero hf hφ hne h1).self_of_nhds
  simp [h0] at h3

end Germ

/-! ### Members containing the centre, in adapted coordinates -/

section Adapted

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`C ⊆ H` near `x` iff the coordinate of `H` is not a free coordinate of `C`**: in coordinates
`Φ` at `x` in which `C = ℂᵏ × 0` and `H = {w_t = 0}` (`x ∈ C ∩ H`). -/
theorem eventually_subset_iff_le {x : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}
    (hΦt : Φ.source ⊆ (chartAt (ComplexModel n) x).target) {C H : Set X} {k : ℕ} {t : Fin n}
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k))
    (hflatH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x y) t = 0))
    (hxC : x ∈ C) (hxH : x ∈ H) :
    (∀ᶠ y in 𝓝 x, y ∈ C → y ∈ H) ↔ k ≤ t.1 := by
  have hz' : x ∈ flatDomain Φ := ⟨mem_chart_source _ x, Φ.center_mem_source⟩
  constructor
  · intro hCH
    by_contra hlt
    push Not at hlt
    have hpt : Φ.toFun (chartAt (ComplexModel n) x x) ∈ Φ.target := Φ.mapsTo_toFun hz'.2
    have hpC := (hflatC hz'.1 hz'.2).mp hxC
    have hpH := (hflatH hz'.1 hz'.2).mp hxH
    -- the curve `ε ↦ e⁻¹ Φ⁻¹ (Φ (e x) + ε e_t)` runs inside `C` and leaves `H`
    have hwc : Continuous fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ) := by fun_prop
    have htend : Tendsto (fun ε : ℂ => Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ)) (𝓝 0)
        (𝓝 (Φ.toFun (chartAt (ComplexModel n) x x))) := by
      simpa using hwc.tendsto 0
    have hinv : Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x)) =
        chartAt (ComplexModel n) x x := Φ.left_inv _ hz'.2
    have hψ : Tendsto (fun ε : ℂ => (chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ε • EuclideanSpace.single t (1 : ℂ)))) (𝓝 0) (𝓝 x) := by
      have h1 : ContinuousAt Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x)) :=
        Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds hpt)
      have h2 : ContinuousAt (chartAt (ComplexModel n) x).symm
          (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x))) := by
        rw [hinv]
        exact (chartAt (ComplexModel n) x).continuousAt_symm
          ((chartAt (ComplexModel n) x).map_source hz'.1)
      have h3 := (h2.comp h1).tendsto.comp htend
      simpa [Function.comp_def, hinv, (chartAt (ComplexModel n) x).left_inv hz'.1] using h3
    have hwt : ∀ᶠ ε in 𝓝 (0 : ℂ), Φ.toFun (chartAt (ComplexModel n) x x) +
        ε • EuclideanSpace.single t (1 : ℂ) ∈ Φ.target :=
      htend (Φ.isOpen_target.mem_nhds hpt)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((hψ.eventually hCH).and hwt)
    have hε : dist ((r / 2 : ℝ) : ℂ) 0 < r := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    obtain ⟨hCHε, hwtε⟩ := hball hε
    have hsrc := Φ.mapsTo_invFun hwtε
    have htgt := hΦt hsrc
    have hys := (chartAt (ComplexModel n) x).map_target htgt
    have hey := (chartAt (ComplexModel n) x).right_inv htgt
    have hyΦ : chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ)))) ∈ Φ.source := by
      rw [hey]; exact hsrc
    have hΦy : Φ.toFun (chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x x) +
          ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ))))) =
        Φ.toFun (chartAt (ComplexModel n) x x) +
          ((r / 2 : ℝ) : ℂ) • EuclideanSpace.single t (1 : ℂ) := by
      rw [hey]; exact Φ.right_inv _ hwtε
    have hyC := (hflatC hys hyΦ).mpr (by
      rw [hΦy]
      intro l hl
      have hlt' : l ≠ t := fun h => by rw [h] at hl; omega
      simp [hpC l hl, hlt'])
    have hyH := (hflatH hys hyΦ).mp (hCHε hyC)
    rw [hΦy] at hyH
    simp [hpH] at hyH
    linarith
  · intro hkt
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hz'] with y hy hyC
    refine (hflatH hy.1 hy.2).mpr ?_
    exact (hflatC hy.1 hy.2).mp hyC t hkt

end Adapted

/-! ### The monomial chart over a point of the centre -/

section Chart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **The monomial chart over a point of the centre** (the ambient half of `hir:monomial-blowup`,
in the generator form).  Let `π` be the blowup along `C`, `E` a simple normal crossings divisor
with which `C` has only normal crossings, and `π z ∈ C`.  There are a monomial chart `W` on an open
`U ∋ z` (with injective differential at `z`), an index `j` and indices `s i` such that:
`W_j(z) = 0` and `𝒪(-D) = (W_j)` on `U`; for every member `E_i` with `z ∈ E_i'`: `π z ∈ E_i`,
`s i ≠ j`, `W_{s i}(z) = 0` and `𝓘_{E_i'} = (W_{s i})` on `U`; the `s i` of the members through
`π z` are distinct; and for holomorphic generators `u_i` of `𝓘_{E_i}` at `π z` and exponents
`a_i`, `(∏_{π z ∈ E_i} u_i^{a_i}) ∘ π = c · W_j^e · ∏_{z ∈ E_i'} W_{s i}^{a_i}` near `z`,
`c(z) ≠ 0`, `e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`. -/
theorem exists_monomial_chart (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y} (hzC : π z ∈ C) :
    ∃ (j : Fin n) (s : Fin E.length → Fin n) (W : Y → ComplexModel n) (U : Set Y),
      IsOpen U ∧ z ∈ U ∧
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W y) ∧
      Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
        (chartAt (ComplexModel n) z z)) ∧
      W z j = 0 ∧
      (∀ y ∈ U, ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔
        IsInSpanAt (n := n) (· = fun w => W w j) y g) ∧
      (∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i ∧ s i ≠ j ∧ W z (s i) = 0 ∧
        ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem y g ↔
          IsInSpanAt (n := n) (· = fun w => W w (s i)) y g) ∧
      Set.InjOn s {i | π z ∈ E.get i} ∧
      ∀ (a : Fin E.length → ℕ) (u : Fin E.length → X → ℂ),
        (∀ i, π z ∈ E.get i → HolomorphicAt n (u i) (π z) ∧
          ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
            IsInSpanAt (n := n) (· = u i) (π z) g) →
        ∃ c : Y → ℂ, HolomorphicAt n c z ∧ c z ≠ 0 ∧
          (fun w => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), u i (π w) ^ a i)
            =ᶠ[𝓝 z] fun w => c w *
              W w j ^ (∑ i ∈ Finset.univ.filter
                (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a i) *
              ∏ i ∈ Finset.univ.filter (fun i => z ∈ geoStrictTransform π C (E.get i)),
                W w (s i) ^ a i := by
  classical
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  obtain ⟨kC, kN, Φ, s, hΦt, -, hsinj, hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (subset_univ C) hE (isTransverse_univ_of_isSNCDivisor hE)
      hnc hzC
  have hx' : π z ∈ flatDomain Φ := ⟨mem_chart_source _ (π z), Φ.center_mem_source⟩
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatH : ∀ i, π z ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (s i) = 0) :=
    fun i hi y hy hyΦ => (hflat hy hyΦ).2.2 i hi
  have hflatH' : ∀ i, π z ∈ E.get i → ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace {s i}) :=
    fun i hi y hy hyΦ => by rw [mem_coordSubspace_singleton]; exact hflatH i hi hy hyΦ
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hx'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz'' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz'').2]; exact Φ.mapsTo_toFun (hWeq z' hz'').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  have hFinj : ∀ u ∈ O, Function.Injective (fderiv ℂ
      (fun ζ => W ((chartAt (ComplexModel n) u).symm ζ)) (chartAt (ComplexModel n) u u)) :=
    fun u hu => injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hu
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hWzj : W z j = 0 := (hCu z hzO).mp hzC
  have hHu : ∀ i, π z ∈ E.get i → ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔
      j ∉ ({s i} : Finset (Fin n)) ∧ W u ∈ coordSubspace {s i}) :=
    fun i hi u hu => mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC (hflatH' i hi) hj hO hWs
      hWeq hℓ hu
  have hzH : ∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hE.1 _ (List.get_mem _ _)) hi
  -- the strict transform through `z`, in the chart
  have hS' : ∀ i, π z ∈ E.get i →
      (z ∈ geoStrictTransform π C (E.get i) ↔ s i ≠ j ∧ W z (s i) = 0) := by
    intro i hi
    rw [hHu i hi z hzO, mem_coordSubspace_singleton, Finset.mem_singleton]
    exact ⟨fun h => ⟨fun h' => h.1 h'.symm, h.2⟩, fun h => ⟨fun h' => h.1 h'.symm, h.2⟩⟩
  refine ⟨j, s, W, O, hO, hzO, hWs, hFinj z hzO, hWzj, fun y hy g => ?_, fun i hi => ?_, hsinj,
    fun a u hu => ?_⟩
  · rw [exceptionalDivisor_mem_iff_of_chart hπ hΦt hflatC hj hO hWs hWeq hy g,
      isInSpanAt_range_one_iff]
  · have hxi := hzH i hi
    obtain ⟨hsj, hWs0⟩ := (hS' i hxi).mp hi
    refine ⟨hxi, hsj, hWs0, fun y hy g => ?_⟩
    have hHu' : ∀ u ∈ O, (u ∈ geoStrictTransform π C (E.get i) ↔ W u (s i) = 0) := fun u hu => by
      rw [hHu i hxi u hu, mem_coordSubspace_singleton, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨fun h' => hsj h'.symm, h⟩⟩
    rw [← LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hO
      (fun u hu => holomorphicAt_coord hO hWs (s i) hu)
      (fun u hu _ => let ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hu (hFinj u hu) (s i)
        ⟨complexChartAt (n := n) u, v, mem_complexChartAt_source u, hv⟩) hy g]
    refine vanishingIdeal_mem_congr ?_ g
    filter_upwards [hO.mem_nhds hy] with u hu
    exact ⟨fun h => ⟨(hHu' u hu).mp h, hu⟩, fun h => (hHu' u hu).mpr h.1⟩
  · -- unit factors `u i = c i · Φ_{s i}` near `π z`
    have hunit : ∀ i, ∃ c : X → ℂ, π z ∈ E.get i → HolomorphicAt n c (π z) ∧ c (π z) ≠ 0 ∧
        u i =ᶠ[𝓝 (π z)] fun y => c y * flatCoord Φ (s i) y := by
      intro i
      by_cases hi : π z ∈ E.get i
      · obtain ⟨huhol, hgen⟩ := hu i hi
        have hgenφ := vanishingIdeal_mem_iff_flatCoord Φ (hflatH i hi) hx'
        have hφhol : HolomorphicAt n (flatCoord Φ (s i)) (π z) :=
          holomorphicAt_flatCoord Φ (s i) hx'
        have huI : (vanishingIdeal (n := n) (E.get i)).mem (π z) (u i) :=
          (hgen (u i)).mpr (isInSpanAt_self rfl huhol)
        have hφI : (vanishingIdeal (n := n) (E.get i)).mem (π z) (flatCoord Φ (s i)) :=
          (hgenφ _).mpr (isInSpanAt_self rfl hφhol)
        have hne : ∃ᶠ y in 𝓝 (π z), flatCoord Φ (s i) y ≠ 0 :=
          (frequently_flatMap_ne_zero hΦt hx' {s i}).mono fun y hy =>
            hy.2.1 (s i) (Finset.mem_singleton_self _)
        obtain ⟨c, hc, hcz, hcu⟩ :=
          exists_unit_of_isInSpanAt ((hgenφ (u i)).mp huI) ((hgen _).mp hφI) hne
        exact ⟨c, fun _ => ⟨hc, hcz, hcu⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hi⟩
    choose c hc using hunit
    -- `C ⊆ E_i` near `π z` iff `k_C ≤ s i`
    have hdich : ∀ i, π z ∈ E.get i →
        ((∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) ↔ kC ≤ (s i).1) :=
      fun i hi => eventually_subset_iff_le hΦt hflatC (hflatH i hi) hzC hi
    -- the unit part of each factor
    let g : Fin E.length → Y → ℂ := fun i =>
      if kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0 then fun w => W w (s i) ^ a i else fun _ => 1
    have hgpos : ∀ i, (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) → g i = fun w => W w (s i) ^ a i :=
      fun i hP => by simp only [g]; rw [if_pos hP]
    have hgneg : ∀ i, ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) → g i = fun _ => 1 :=
      fun i hP => by simp only [g]; rw [if_neg hP]
    have hghol : ∀ i, HolomorphicAt n (g i) z := by
      intro i
      by_cases hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0
      · rw [hgpos i hP]
        exact CompanionReduction.holomorphicAt_pow_of (holomorphicAt_coord hO hWs (s i) hzO) (a i)
      · rw [hgneg i hP]
        exact holomorphicAt_const 1
    have hgz : ∀ i, g i z ≠ 0 := by
      intro i
      by_cases hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0
      · rw [hgpos i hP]
        exact pow_ne_zero _ hP.2.2
      · rw [hgneg i hP]
        exact one_ne_zero
    -- the factor of each member through `π z`
    have hπt : Tendsto π (𝓝 z) (𝓝 (π z)) := hπ.contMDiff.continuous.tendsto z
    have hper : ∀ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), ∀ᶠ w in 𝓝 z,
        u i (π w) ^ a i = (c i (π w) ^ a i * g i w) *
          W w j ^ (if (∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i) then a i else 0) *
          W w (s i) ^ (if z ∈ geoStrictTransform π C (E.get i) then a i else 0) := by
      intro i hiT
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      filter_upwards [hπt.eventually (hc i hi).2.2, hO.mem_nhds hzO] with w hw hwO
      have hflatW : flatCoord Φ (s i) (π w) = monomial kC j (W w) (s i) := by
        simp only [flatCoord]
        rw [(hWeq w hwO).2]
      rw [hw, mul_pow, hflatW, monomial_apply]
      by_cases hsj : s i = j
      · have hJ : ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := (hdich i hi).mpr (hsj ▸ hj)
        have hS : z ∉ geoStrictTransform π C (E.get i) := fun h => ((hS' i hi).mp h).1 hsj
        have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => h.2.1 hsj
        rw [hgneg i hP, if_neg (fun h => h.2 hsj), if_pos hJ, if_neg hS, hsj]
        ring
      · by_cases hk : kC ≤ (s i).1
        · have hJ : ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := (hdich i hi).mpr hk
          by_cases hWz : W z (s i) = 0
          · have hS : z ∈ geoStrictTransform π C (E.get i) := (hS' i hi).mpr ⟨hsj, hWz⟩
            have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => h.2.2 hWz
            rw [hgneg i hP, if_pos ⟨hk, hsj⟩, if_pos hJ, if_pos hS]
            ring
          · have hS : z ∉ geoStrictTransform π C (E.get i) := fun h => hWz ((hS' i hi).mp h).2
            have hP : kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0 := ⟨hk, hsj, hWz⟩
            rw [hgpos i hP, if_pos ⟨hk, hsj⟩, if_pos hJ, if_neg hS]
            ring
        · have hJ : ¬ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i := fun h => hk ((hdich i hi).mp h)
          have hWz : W z (s i) = 0 := by
            have h1 : monomial kC j (W z) (s i) = W z (s i) := by
              rw [monomial_apply, if_neg (fun h => hk h.1)]
            rw [← h1, (hWeq z hzO).2]
            exact (hflatH i hi (mem_chart_source _ (π z)) Φ.center_mem_source).mp hi
          have hS : z ∈ geoStrictTransform π C (E.get i) := (hS' i hi).mpr ⟨hsj, hWz⟩
          have hP : ¬ (kC ≤ (s i).1 ∧ s i ≠ j ∧ W z (s i) ≠ 0) := fun h => hk h.1
          rw [hgneg i hP, if_neg (fun h => hk h.1), if_neg hJ, if_pos hS]
          ring
    refine ⟨fun w => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), c i (π w) ^ a i * g i w,
      ?_, ?_, ?_⟩
    · have hπd : ∀ᶠ w in 𝓝 z,
          MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
        Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
      refine holomorphicAt_finset_prod _ fun i hiT => ?_
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      exact (CompanionReduction.holomorphicAt_pow_of
        (HadamardBridge.holomorphicAt_comp_map hπd (hc i hi).1) (a i)).mul (hghol i)
    · refine Finset.prod_ne_zero_iff.mpr fun i hiT => ?_
      have hi : π z ∈ E.get i := (Finset.mem_filter.mp hiT).2
      exact mul_ne_zero (pow_ne_zero _ (hc i hi).2.1) (hgz i)
    · have hall := (Filter.eventually_all_finset _).mpr hper
      filter_upwards [hall] with w hw
      rw [Finset.prod_congr rfl hw, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.filter_filter]
      congr 1
      have hpw : ∀ i, W w (s i) ^ (if z ∈ geoStrictTransform π C (E.get i) then a i else 0) =
          if z ∈ geoStrictTransform π C (E.get i) then W w (s i) ^ a i else 1 := by
        intro i
        split_ifs <;> simp
      rw [Finset.prod_congr rfl fun i _ => hpw i, ← Finset.prod_filter, Finset.filter_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hzH i h, h⟩⟩

end Chart

/-! ### The controlled transform of a principal ideal with an exceptional factor -/

section Transform

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The controlled transform of a principal ideal with an exceptional factor**: if `𝔞 = (m)` at
`π z` and `m ∘ π = c · h^e · q` near `z`, with `𝒪(-D) = (h)` at `z`, `h` vanishing identically near
no point, `c(z) ≠ 0` and `μ ≤ e`, then `σ^c(𝔞, μ) = (h^{e-μ} q)` at `z`. -/
theorem mem_controlledTransform_iff_of_eq (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    {m : X → ℂ} {z : Y} (hm : HolomorphicAt n m (π z))
    (hgen : ∀ g, 𝔞.mem (π z) g ↔ IsInSpanAt (n := n) (· = m) (π z) g) {h c q : Y → ℂ}
    (hD : ∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔ IsInSpanAt (n := n) (· = h) z g)
    (hh : HolomorphicAt n h z) (hhne : ∃ᶠ y in 𝓝 z, h y ≠ 0) (hc : HolomorphicAt n c z)
    (hcz : c z ≠ 0) (hq : HolomorphicAt n q z) {e μ : ℕ} (hμe : μ ≤ e)
    (heq : (fun w => m (π w)) =ᶠ[𝓝 z] fun w => c w * h w ^ e * q w) (g : Y → ℂ) :
    (controlledTransform hπ 𝔞 μ).mem z g ↔
      IsInSpanAt (n := n) (· = fun w => h w ^ (e - μ) * q w) z g := by
  have hpb : ∀ f, (GermIdeal.pullback (m := n) π 𝔞).mem z f ↔
      IsInSpanAt (n := n) (· = m ∘ π) z f :=
    pullback_mem_iff_of_generator hπ.contMDiff hm hgen
  have hhμ : (idealPow (exceptionalDivisor hπ).ideal μ).mem z (fun y => h y ^ μ) :=
    pow_mem_idealPow ((hD h).mpr (isInSpanAt_self rfl hh)) hh μ
  have hhpow : HolomorphicAt n (fun y => h y ^ (e - μ) * q y) z :=
    (CompanionReduction.holomorphicAt_pow_of hh _).mul hq
  have he : ∀ y, h y ^ e = h y ^ μ * h y ^ (e - μ) := fun y => by
    rw [← pow_add, Nat.add_sub_cancel' hμe]
  constructor
  · rintro ⟨hghol, hg⟩
    -- `h^μ g ∈ π^*𝔞 = (m ∘ π)`, then cancel `h^μ`
    obtain ⟨-, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp ((hpb _).mp (hg _ hhμ))
    refine isInSpanAt_eq_iff.mpr ⟨hghol, fun y => b y * c y, hb.mul hc, ?_⟩
    have hsub := eventually_eq_zero_of_mul_eventually_eq_zero
      (f := fun y => g y - b y * c y * (h y ^ (e - μ) * q y)) (m := fun y => h y ^ μ)
      (GiraudAlong.holomorphicAt_sub hghol ((hb.mul hc).mul hhpow))
      (CompanionReduction.holomorphicAt_pow_of hh μ) (hhne.mono fun y hy => pow_ne_zero _ hy) (by
        filter_upwards [hbeq, heq] with y h1 h2
        simp only [Function.comp_apply] at h1
        calc (g y - b y * c y * (h y ^ (e - μ) * q y)) * h y ^ μ
            = h y ^ μ * g y - b y * (c y * (h y ^ μ * h y ^ (e - μ)) * q y) := by ring
          _ = 0 := by rw [h1, h2, he]; ring)
    filter_upwards [hsub] with y hy
    exact sub_eq_zero.mp hy
  · intro hg
    obtain ⟨hghol, b, hb, hbeq⟩ := isInSpanAt_eq_iff.mp hg
    refine ⟨hghol, fun p hp => ?_⟩
    obtain ⟨p', hp', hpeq⟩ :=
      exists_eq_mul_pow_of_mem_idealPow (fun g' hg' => (hD g').mp hg') hp
    refine (hpb _).mpr (isInSpanAt_eq_iff.mpr ⟨(holomorphicAt_of_mem_idealPow hp).mul hghol,
      fun y => p' y * b y * (c y)⁻¹,
      (hp'.mul hb).mul (BlowupFlatCoordinates.HolomorphicAt.inv hc hcz), ?_⟩)
    filter_upwards [hpeq, hbeq, heq, hc.continuousAt.eventually (isOpen_ne.mem_nhds hcz)]
      with y h1 h2 h3 h4
    show p y * g y = p' y * b y * (c y)⁻¹ * (m ∘ π) y
    simp only [Function.comp_apply]
    rw [h1, h2, h3, he]
    have h5 : (c y)⁻¹ * c y = 1 := inv_mul_cancel₀ h4
    linear_combination (-(p' y * b y * (h y ^ μ * h y ^ (e - μ)) * q y)) * h5

/-- `W_j` vanishes identically near no point of `U`: its zero set in `U` is `D ∩ U`, which has
empty interior. -/
theorem frequently_ne_zero_of_generator (hπ : IsBlowupAlong n C π) {U : Set Y} (hU : IsOpen U)
    {h : Y → ℂ}
    (hD : ∀ y ∈ U, ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔ IsInSpanAt (n := n) (· = h) y g)
    {z : Y} (hz : z ∈ U) : ∃ᶠ y in 𝓝 z, h y ≠ 0 := by
  rw [Filter.Frequently]
  intro hall
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp ((hU.eventually_mem hz).and hall)
  -- every point of `V` lies on `D`
  have hVD : V ⊆ π ⁻¹' C := by
    intro y hy
    have hyU : y ∈ U := (hVsub hy).1
    have hsupp : y ∈ (exceptionalDivisor hπ).support := by
      intro g hg
      obtain ⟨-, a, -, hga⟩ := isInSpanAt_eq_iff.mp ((hD y hyU g).mp hg)
      rw [hga.self_of_nhds]
      have : h y = 0 := by simpa using (hVsub hy).2
      simp [this]
    rwa [support_exceptionalDivisor hπ] at hsupp
  have hint : z ∈ interior (π ⁻¹' C) := interior_mono hVD (hVo.interior_eq.symm ▸ hzV)
  rw [ExceptionalFibres.interior_preimage_eq_empty hπ] at hint
  exact hint

/-- **The transform of a marked ideal `(M, M, E, 𝔞, d)` with a principal ideal with an exceptional
factor** (`N = M`, `𝔞` coherent): the transformed ideal is the controlled transform
(`MarkedIdeal.geoTransform_ideal_eq_controlledTransform`), so it is `(h^{e-d} q)` at `z`. -/
theorem mem_geoTransform_iff_of_eq (hπ : IsBlowupAlong n C π) (𝔪 : MarkedIdeals.MarkedIdeal n X)
    (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) {m : X → ℂ} {z : Y}
    (hm : HolomorphicAt n m (π z))
    (hgen : ∀ g, 𝔪.ideal.mem (π z) g ↔ IsInSpanAt (n := n) (· = m) (π z) g) {h c q : Y → ℂ}
    (hD : ∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔ IsInSpanAt (n := n) (· = h) z g)
    (hh : HolomorphicAt n h z) (hhne : ∃ᶠ y in 𝓝 z, h y ≠ 0) (hc : HolomorphicAt n c z)
    (hcz : c z ≠ 0) (hq : HolomorphicAt n q z) {e : ℕ} (hde : 𝔪.d ≤ e)
    (heq : (fun w => m (π w)) =ᶠ[𝓝 z] fun w => c w * h w ^ e * q w) (g : Y → ℂ) :
    (𝔪.geoTransform C π).ideal.mem z g ↔
      IsInSpanAt (n := n) (· = fun w => h w ^ (e - 𝔪.d) * q w) z g := by
  rw [MarkedIdeals.MarkedIdeal.geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪) hN h𝔞 hπ]
  exact mem_controlledTransform_iff_of_eq hπ hm hgen hD hh hhne hc hcz hq hde heq g

end Transform

/-! ### Monomial ideals: the transform in the monomial chart -/

section Monomial

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

open Classical in
/-- **`hir:monomial-blowup`, ambient, generator form.**  In the monomial chart of
`exists_monomial_chart` (whose properties are repeated here), for a monomial ideal
`𝔞 = (∏_{π z ∈ E_i} u_i^{a_i})` at `π z` (`u_i` holomorphic generators of `𝓘_{E_i}`) and a mark
`μ ≤ e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`, the controlled transform is
`σ^c(𝔞, μ) = (W_j^{e-μ} ∏_{z ∈ E_i'} W_{s i}^{a_i})` at `z`: monomial, with exponent `e - μ` on the
exceptional divisor `D = {W_j = 0}` and `a_i` on the strict transforms `E_i' = {W_{s i} = 0}`
through `z`. -/
theorem exists_monomial_chart_transform (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y} (hzC : π z ∈ C) :
    ∃ (j : Fin n) (s : Fin E.length → Fin n) (W : Y → ComplexModel n) (U : Set Y),
      IsOpen U ∧ z ∈ U ∧
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W y) ∧
      Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
        (chartAt (ComplexModel n) z z)) ∧
      W z j = 0 ∧
      (∀ y ∈ U, ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔
        IsInSpanAt (n := n) (· = fun w => W w j) y g) ∧
      (∀ i, z ∈ geoStrictTransform π C (E.get i) → π z ∈ E.get i ∧ s i ≠ j ∧ W z (s i) = 0 ∧
        ∀ y ∈ U, ∀ g, (vanishingIdeal (n := n) (geoStrictTransform π C (E.get i))).mem y g ↔
          IsInSpanAt (n := n) (· = fun w => W w (s i)) y g) ∧
      Set.InjOn s {i | π z ∈ E.get i} ∧
      ∀ (a : Fin E.length → ℕ) (u : Fin E.length → X → ℂ),
        (∀ i, π z ∈ E.get i → HolomorphicAt n (u i) (π z) ∧
          ∀ g, (vanishingIdeal (n := n) (E.get i)).mem (π z) g ↔
            IsInSpanAt (n := n) (· = u i) (π z) g) →
        ∀ (𝔞 : GermIdeal n X), (∀ g, 𝔞.mem (π z) g ↔ IsInSpanAt (n := n)
            (· = fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i), u i x ^ a i) (π z) g) →
        ∀ μ : ℕ, μ ≤ ∑ i ∈ Finset.univ.filter
            (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a i →
        ∀ g, (controlledTransform hπ 𝔞 μ).mem z g ↔ IsInSpanAt (n := n)
          (· = fun w => W w j ^ ((∑ i ∈ Finset.univ.filter
              (fun i => π z ∈ E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ E.get i), a i) - μ) *
            ∏ i ∈ Finset.univ.filter (fun i => z ∈ geoStrictTransform π C (E.get i)),
              W w (s i) ^ a i) z g := by
  classical
  obtain ⟨j, s, W, U, hU, hzU, hWs, hinj, hWzj, hD, hH, hsinj, hmono⟩ :=
    exists_monomial_chart hπ hE hnc hzC
  refine ⟨j, s, W, U, hU, hzU, hWs, hinj, hWzj, hD, hH, hsinj, fun a u hu 𝔞 h𝔞 μ hμ g => ?_⟩
  obtain ⟨c, hc, hcz, heq⟩ := hmono a u hu
  have hm : HolomorphicAt n (fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ E.get i),
      u i x ^ a i) (π z) :=
    holomorphicAt_finset_prod _ fun i hiT =>
      CompanionReduction.holomorphicAt_pow_of (hu i (Finset.mem_filter.mp hiT).2).1 (a i)
  have hWj : HolomorphicAt n (fun w => W w j) z := holomorphicAt_coord hU hWs j hzU
  have hq : HolomorphicAt n (fun w => ∏ i ∈ Finset.univ.filter
      (fun i => z ∈ geoStrictTransform π C (E.get i)), W w (s i) ^ a i) z :=
    holomorphicAt_finset_prod _ fun i _ =>
      CompanionReduction.holomorphicAt_pow_of (holomorphicAt_coord hU hWs (s i) hzU) (a i)
  exact mem_controlledTransform_iff_of_eq hπ hm h𝔞 (hD z hzU) hWj
    (frequently_ne_zero_of_generator hπ hU hD hzU) hc hcz hq hμ heq g

end Monomial

/-! ### The transform in coordinates adapted to the transformed divisor -/

section SNCForm

section Germ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Where `𝓘_A = (h)` and `A` is closed, `A` is the zero set of `h`. -/
theorem mem_iff_of_vanishingIdeal_eq {A : Set M} (hA : IsClosed A) {h : M → ℂ} {y : M}
    (hh : HolomorphicAt n h y)
    (hI : ∀ g, (vanishingIdeal (n := n) A).mem y g ↔ IsInSpanAt (n := n) (· = h) y g) :
    y ∈ A ↔ h y = 0 := by
  constructor
  · intro hy
    obtain ⟨-, hev⟩ := (hI h).mpr (isInSpanAt_self rfl hh)
    exact hev.self_of_nhds hy
  · intro h0
    by_contra hy
    have h1 : (vanishingIdeal (n := n) A).mem y (fun _ => 1) := by
      refine ⟨holomorphicAt_const (n := n) (x := y) (1 : ℂ), ?_⟩
      filter_upwards [hA.isOpen_compl.mem_nhds hy] with y' hy' hA'
      exact absurd hA' hy'
    obtain ⟨-, a, -, ha⟩ := isInSpanAt_eq_iff.mp ((hI _).mp h1)
    have := ha.self_of_nhds
    simp [h0] at this

/-- Products over the indices of `E.map f ++ [P]`: the indices of `E`, then the last one. -/
theorem prod_map_append_singleton {α β R : Type*} [CommMonoid R] (E : List α) (f : α → β)
    (P : β) (F : Fin (E.map f ++ [P]).length → R) :
    ∏ i, F i = (∏ i : Fin E.length, F ⟨i.1, by simp⟩) * F ⟨E.length, by simp⟩ := by
  rw [← Fin.prod_congr' F (length_map_append_singleton E f P).symm, Fin.prod_univ_castSucc]
  rfl

end Germ

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- Where `𝒪(-D) = (h)`, `D = π⁻¹ C` is the zero set of `h`. -/
theorem mem_centre_iff_of_generator (hπ : IsBlowupAlong n C π) {h : Y → ℂ} {y : Y}
    (hh : HolomorphicAt n h y)
    (hD : ∀ g, (exceptionalDivisor hπ).ideal.mem y g ↔ IsInSpanAt (n := n) (· = h) y g) :
    π y ∈ C ↔ h y = 0 := by
  have hsupp : y ∈ (exceptionalDivisor hπ).support ↔ π y ∈ C := by
    rw [support_exceptionalDivisor hπ]; rfl
  rw [← hsupp]
  constructor
  · intro hy
    exact hy h ((hD h).mpr (isInSpanAt_self rfl hh))
  · intro h0 g hg
    obtain ⟨-, a, -, hga⟩ := isInSpanAt_eq_iff.mp ((hD g).mp hg)
    rw [hga.self_of_nhds]
    simp [h0]

open Classical in
/-- **`hir:monomial-blowup`, ambient, in coordinates adapted to the transformed divisor.**  Let
`(X, X, E, 𝔞, d)` be a marked ideal with `𝔞` coherent, `E` simple normal crossings, `C` with only
normal crossings with `E`, and `π z ∈ C`.  If `𝔞 = (∏_{π z ∈ E_i} u_i^{a_i})` at `π z`
(`u_i` holomorphic generators of `𝓘_{E_i}`) and `d ≤ e = ∑_{π z ∈ E_i, C ⊆ E_i near π z} a_i`, then
there are coordinates `Θ` centred at `z`, indices `σ` (injective on the members of
`E' = (E_1', …, E_s', π⁻¹ C)` through `z`) and exponents `a'` (`a'_i = a_i` for `i < s`,
`a'_s = e - d`) such that every member of `E'` through `z` is the coordinate hyperplane
`{Θ_{σ i} = 0}` and the transformed ideal is `(∏_{z ∈ E'_i} Θ_{σ i}^{a'_i})` at `z`: the hypotheses
of the principal monomial calculus of `MonomialCase` (section `Principal`) at `z`. -/
theorem exists_snc_chart_geoTransform (hπ : IsBlowupAlong n C π)
    (𝔪 : MarkedIdeals.MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hE : IsSNCDivisor n 𝔪.E) (hnc : HasNormalCrossings n C 𝔪.E) {z : Y} (hzC : π z ∈ C)
    (a : Fin 𝔪.E.length → ℕ) (u : Fin 𝔪.E.length → X → ℂ)
    (hu : ∀ i, π z ∈ 𝔪.E.get i → HolomorphicAt n (u i) (π z) ∧
      ∀ g, (vanishingIdeal (n := n) (𝔪.E.get i)).mem (π z) g ↔
        IsInSpanAt (n := n) (· = u i) (π z) g)
    (hgen : ∀ g, 𝔪.ideal.mem (π z) g ↔ IsInSpanAt (n := n)
      (· = fun x => ∏ i ∈ Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i), u i x ^ a i) (π z) g)
    (hd : 𝔪.d ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (σ : Fin (𝔪.geoTransform C π).E.length → Fin n)
      (a' : Fin (𝔪.geoTransform C π).E.length → ℕ),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      Set.InjOn σ {i | z ∈ (𝔪.geoTransform C π).E.get i} ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → ∀ {y : Y},
        y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).E.get i ↔
            Θ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0)) ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = a ⟨i.1, hi⟩) ∧
      (∀ i, ¬ i.1 < 𝔪.E.length → a' i = (∑ i ∈ Finset.univ.filter
        (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) ∧
      ∀ g, (𝔪.geoTransform C π).ideal.mem z g ↔ IsInSpanAt (n := n)
        (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => z ∈ (𝔪.geoTransform C π).E.get i),
          flatCoord Θ (σ i) y ^ a' i) z g := by
  classical
  obtain ⟨j, s, W, U, hU, hzU, hWs, hinj, hWzj, hD, hH, hsinj, hmono⟩ :=
    exists_monomial_chart_transform hπ hE hnc hzC
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := exists_recentred_coords hU hWs hzU hinj
  -- zero sets on `U`
  have hCu : ∀ y ∈ U, (π y ∈ C ↔ W y j = 0) := fun y hy =>
    mem_centre_iff_of_generator hπ (holomorphicAt_coord hU hWs j hy) (hD y hy)
  have hHu : ∀ i, z ∈ geoStrictTransform π C (𝔪.E.get i) → ∀ y ∈ U,
      (y ∈ geoStrictTransform π C (𝔪.E.get i) ↔ W y (s i) = 0) := fun i hi y hy =>
    mem_iff_of_vanishingIdeal_eq isClosed_closure (holomorphicAt_coord hU hWs (s i) hy)
      ((hH i hi).2.2.2 y hy)
  -- the recentred coordinates
  have hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
        y ∈ U ∧ ∀ k, Θ.toFun (chartAt (ComplexModel n) z y) k = W y k - W z k :=
    fun {y} hy hyΘ => by
      obtain ⟨hyU, hΘy⟩ := hΘ hy hyΘ
      exact ⟨hyU, fun k => by
        show Θ.toFun ((complexChartAt (n := n) z).val y) k = _
        rw [hΘy, PiLp.sub_apply]⟩
  have hget : ∀ i : Fin (𝔪.geoTransform C π).E.length, (𝔪.geoTransform C π).E.get i =
      if h : i.1 < 𝔪.E.length then geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) else π ⁻¹' C :=
    fun i => get_map_append_singleton 𝔪.E (geoStrictTransform π C) (π ⁻¹' C) i
  let σ : Fin (𝔪.geoTransform C π).E.length → Fin n := fun i =>
    if h : i.1 < 𝔪.E.length then s ⟨i.1, h⟩ else j
  let a' : Fin (𝔪.geoTransform C π).E.length → ℕ := fun i =>
    if h : i.1 < 𝔪.E.length then a ⟨i.1, h⟩ else (∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d
  refine ⟨Θ, σ, a', hΘt, hΘ0, ?_, ?_, fun i hi => dif_pos hi, fun i hi => dif_neg hi, ?_⟩
  · -- the indices of the members through `z` are distinct
    intro i hi i' hi' hii'
    simp only [Set.mem_ofPred_eq] at hi hi'
    rw [hget i] at hi
    rw [hget i'] at hi'
    simp only [σ] at hii'
    by_cases h : i.1 < 𝔪.E.length <;> by_cases h' : i'.1 < 𝔪.E.length
    · rw [dif_pos h] at hi hii'
      rw [dif_pos h'] at hi' hii'
      exact Fin.ext (Fin.mk.inj_iff.mp (hsinj (hH _ hi).1 (hH _ hi').1 hii'))
    · rw [dif_pos h] at hi hii'
      rw [dif_neg h'] at hii'
      exact absurd hii' (hH _ hi).2.1
    · rw [dif_neg h] at hii'
      rw [dif_pos h'] at hi' hii'
      exact absurd hii'.symm (hH _ hi').2.1
    · exact eq_of_not_lt h h'
  · -- the members through `z` are coordinate hyperplanes
    intro i hi y hy hyΘ
    obtain ⟨hyU, hΘy⟩ := hflat hy hyΘ
    rw [hget i] at hi ⊢
    simp only [σ]
    by_cases h : i.1 < 𝔪.E.length
    · simp only [dif_pos h] at hi ⊢
      rw [hΘy, (hH _ hi).2.2.1, sub_zero]
      exact hHu _ hi y hyU
    · simp only [dif_neg h]
      rw [hΘy, hWzj, sub_zero]
      exact hCu y hyU
  · -- the generator
    intro g
    rw [MarkedIdeals.MarkedIdeal.geoTransform_ideal_eq_controlledTransform (𝔪 := 𝔪) hN h𝔞 hπ,
      hmono a u hu 𝔪.ideal hgen 𝔪.d hd g]
    refine MemberPullback.isInSpanAt_eq_congr ?_ g
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds (mem_flatDomain_self Θ)] with y hy
    obtain ⟨-, hΘy⟩ := hflat hy.1 hy.2
    have hfc : ∀ k, W z k = 0 → flatCoord Θ k y = W y k := fun k hk => by
      show Θ.toFun (chartAt (ComplexModel n) z y) k = _
      rw [hΘy, hk, sub_zero]
    have hpt : ∀ i : Fin (𝔪.geoTransform C π).E.length,
        (if z ∈ (𝔪.geoTransform C π).E.get i then flatCoord Θ (σ i) y ^ a' i else 1) =
          if h : i.1 < 𝔪.E.length then
            (if z ∈ geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) then
              W y (s ⟨i.1, h⟩) ^ a ⟨i.1, h⟩ else 1)
          else W y j ^ ((∑ i ∈ Finset.univ.filter
            (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) := by
      intro i
      rw [hget i]
      by_cases h : i.1 < 𝔪.E.length
      · simp only [σ, a', dif_pos h]
        split_ifs with hzi
        · rw [hfc _ (hH _ hzi).2.2.1]
        · rfl
      · simp only [σ, a', dif_neg h]
        rw [if_pos (show z ∈ π ⁻¹' C from hzC), hfc _ hWzj]
    rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_congr rfl fun i _ => hpt i]
    have hprod := prod_map_append_singleton 𝔪.E (geoStrictTransform π C) (π ⁻¹' C)
      (fun i => if h : i.1 < 𝔪.E.length then
            (if z ∈ geoStrictTransform π C (𝔪.E.get ⟨i.1, h⟩) then
              W y (s ⟨i.1, h⟩) ^ a ⟨i.1, h⟩ else 1)
          else W y j ^ ((∑ i ∈ Finset.univ.filter
            (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d))
    refine Eq.trans (mul_comm _ _) (Eq.trans ?_ hprod.symm)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Fin.val_mk, dif_pos i.2, Fin.eta]
    · simp only [Fin.val_mk, lt_irrefl, not_false_eq_true, dif_neg]

open Classical in
/-- **The same, from flat coordinates at `π z`** (the shape of `MonomialCase`, section
`Principal`): if the members `E_i` through `π z` (`i ∈ T`) are the coordinate hyperplanes
`{Φ_{σ₀ i} = 0}` of a flattening `Φ` at `π z` and `𝔞 = (∏_{i ∈ T} Φ_{σ₀ i}^{a_i})` at `π z`, the
conclusion of `exists_snc_chart_geoTransform` holds (the `Φ_{σ₀ i}` generate the `𝓘_{E_i}`,
`MemberPullback.vanishingIdeal_mem_iff_flatCoord`). -/
theorem exists_snc_chart_geoTransform_of_flat (hπ : IsBlowupAlong n C π)
    (𝔪 : MarkedIdeals.MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hE : IsSNCDivisor n 𝔪.E) (hnc : HasNormalCrossings n C 𝔪.E) {z : Y} (hzC : π z ∈ C)
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}
    {σ₀ : Fin 𝔪.E.length → Fin n} {T : Finset (Fin 𝔪.E.length)}
    (hT : ∀ i, i ∈ T ↔ π z ∈ 𝔪.E.get i)
    (hA : ∀ i ∈ T, ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ 𝔪.E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) (σ₀ i) = 0))
    (a : Fin 𝔪.E.length → ℕ)
    (hgen : ∀ g, 𝔪.ideal.mem (π z) g ↔ IsInSpanAt (n := n)
      (· = fun x => ∏ i ∈ T, flatCoord Φ (σ₀ i) x ^ a i) (π z) g)
    (hd : 𝔪.d ≤ ∑ i ∈ Finset.univ.filter
      (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) :
    ∃ (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
      (σ : Fin (𝔪.geoTransform C π).E.length → Fin n)
      (a' : Fin (𝔪.geoTransform C π).E.length → ℕ),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z) = 0 ∧
      Set.InjOn σ {i | z ∈ (𝔪.geoTransform C π).E.get i} ∧
      (∀ i, z ∈ (𝔪.geoTransform C π).E.get i → ∀ {y : Y},
        y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ (𝔪.geoTransform C π).E.get i ↔
            Θ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0)) ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = a ⟨i.1, hi⟩) ∧
      (∀ i, ¬ i.1 < 𝔪.E.length → a' i = (∑ i ∈ Finset.univ.filter
        (fun i => π z ∈ 𝔪.E.get i ∧ ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ 𝔪.E.get i), a i) - 𝔪.d) ∧
      ∀ g, (𝔪.geoTransform C π).ideal.mem z g ↔ IsInSpanAt (n := n)
        (· = fun y => ∏ i ∈ Finset.univ.filter (fun i => z ∈ (𝔪.geoTransform C π).E.get i),
          flatCoord Θ (σ i) y ^ a' i) z g := by
  classical
  have hTeq : T = Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i) := by
    ext i
    simp [hT]
  subst hTeq
  refine exists_snc_chart_geoTransform hπ 𝔪 hN h𝔞 hE hnc hzC a (fun i => flatCoord Φ (σ₀ i))
    (fun i hi => ⟨holomorphicAt_flatCoord Φ (σ₀ i) (mem_flatDomain_self Φ), fun g =>
      vanishingIdeal_mem_iff_flatCoord Φ (hA i ((hT i).mpr hi)) (mem_flatDomain_self Φ) g⟩)
    hgen hd

end SNCForm

end

end Hironaka.MonomialBlowup

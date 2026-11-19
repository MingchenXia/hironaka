import Hironaka.Invariant.NonmonomialTransform
import Hironaka.Blowup.ExceptionalIdealPushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transforms of the monomial and nonmonomial parts along the companion tower (`N = M`)

Blueprint `hir:nonmonomial-transform` (`blueprint/src/hironaka.tex`, Hironaka phase H4, Step 2a of the resolution
algorithm, `N = M`).  Sources: Bierstone--Milman 2008, §5 (the monomial part `𝓜(𝓘)`, the nonmonomial part `𝓝(𝓘)` and
their transforms; the companion ideal); Włodarczyk 2005, Step 2a of the proof of `pr:resol`.

Let `(X, X, E, 𝔞, d)` be a well-formed marked ideal whose ideal is nonzero at every point, `𝓝 = 𝓝(𝔞)`, `𝓜 = 𝓜(𝔞)`
(`MonomialPart`), `o ≥ 1` with `ord 𝓝 ≤ o` on `cosupp(𝔞, d)`, and `𝒪 = (𝓝, o) + (𝓜, d - o)` (`o < d`) or `(𝓝, o)`
(`o ≥ d`) the companion ideal (`CompanionReduction.companion`).

* `mul_mem_iff_of_principal`: if `𝓜 = (m)` at `y`, then `(𝔟 𝓜)_y` is spanned by the `a m`, `a ∈ 𝔟_y`;
  `parts_eq_of_factor`: if `𝔞 = 𝔟 · 𝓜` with `𝓜` principal monomial at every point (`MonomialResolution.IsPrincipalAt`)
  and `𝔟` coherent and contained in the ideal of no member at its points, then `𝓝(𝔞) = 𝔟` and `𝓜(𝔞) = 𝓜`
  (`NonmonomialTransform`, the uniqueness of the factorization).
* `frequently_mem_notMem_of_hasNormalCrossings`: points of `C` off the members not containing `C` near `x` accumulate at
  `x ∈ C`; hence `le_sum_divExp_of_subset_cosupport`: if `C ⊆ cosupp(𝓜, μ)` for a monomial `𝓜`, then
  `μ ≤ ∑_{C ⊆ E_i near x} e_i(x)` (the generic-point argument).
* `exceptionalDivisor_mem_of_vanishingIdeal_mem`: at the points of `D = π⁻¹ C` the ideal of `π⁻¹ C` lies in `𝒪(-D)`
  (`D` is a smooth hypersurface, `𝒪(-D) = (W_j)` with `dW_j ≠ 0`).
* `isNonzeroAt_controlledTransform_of_notMem`: off `D` the controlled transform of a nonzero ideal is nonzero (the
  section of `π` over `X \ C`).
* `step` (one blowup): if `𝔞 = 𝔟 𝓜` as above, `𝔟` nonzero, `C` a closed submanifold with normal crossings with `E`,
  `C ⊆ cosupp(𝔟, o) ∩ cosupp(𝔞, d)` and `ord 𝔟 ≤ o` on `C`, then `σ^c(𝔞, d) = σ^c(𝔟, o) · 𝓜'` with
  `𝓜' = 𝒪(-(o - d)D) · σ^c(𝓜, d - o)` principal monomial at every point (TN3's
  `MonomialBlowup.exists_snc_chart_geoTransform_of_flat` over `C`, `MonomialResolution.isPrincipalAt_geoTransform_of_notMem`
  off `C`), and `σ^c(𝔟, o)` is again nonzero and contained in the ideal of no member of `E'` at its points (TN3's
  `ExceptionalIdealPushforward.exists_not_mem_exceptionalDivisor`, `exists_not_mem_vanishingIdeal_geoStrictTransform`).
* `nonmonomialPart_geoTransformAlong`: along every multiple test blow-up `T` of the companion ideal, `T` is one of
  `(X, X, E, 𝔞, d)`, the transform is well formed and nonzero at every point, `𝓝(𝔞_T) = (𝓝, o)_T`, `𝓜(𝔞_T)` is principal
  monomial at every point and `𝔞_T = 𝓝(𝔞_T) 𝓜(𝔞_T)`; `nonmonomialPart_geoTransformAlong_of_resolution`: if `T` resolves the
  companion ideal, `ord 𝓝(𝔞_T) < o` at every point of `cosupp(𝔞_T, d)`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter Finset
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialTransformTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong
  Hironaka.DivisorExponent Hironaka.MemberPullback
  Hironaka.MonomialPart Hironaka.NormalCrossings
  Hironaka.MonomialCase Hironaka.MonomialResolution
  Hironaka.NonmonomialTransform Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupExceptionalDivisor Hironaka.BlowupControlledTransform
  Hironaka.InvertibleIdealQuotient Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers
  Hironaka.CompanionReduction

noncomputable section

variable {n : ℕ}

/-! ### Products with a principal factor; identification of the two parts -/

section Factor

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`𝔟 · (m)`**: if `𝓜 = (m)` at `y`, the germs of `𝔟 𝓜` at `y` are the combinations of the `a m`, `a ∈ 𝔟_y`. -/
theorem mul_mem_iff_of_principal {𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) {y : M} {m : M → ℂ}
    (hm : HolomorphicAt n m y) (hgen : ∀ g, 𝓜.mem y g ↔ IsInSpanAt (n := n) (· = m) y g) (g : M → ℂ) :
    (𝔟.mul 𝓜).mem y g ↔
      IsInSpanAt (n := n) (fun s => ∃ a, 𝔟.mem y a ∧ s = fun p => a p * m p) y g := by
  have hhol : ∀ {a}, 𝔟.mem y a → HolomorphicAt n a y := fun ha =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 ha
  show IsInSpanAt (n := n) (fun s => ∃ a b, 𝔟.mem y a ∧ 𝓜.mem y b ∧ s = a * b) y g ↔ _
  constructor
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    rintro s ⟨a, b, ha, hb, rfl⟩
    obtain ⟨hbh, c, hc, hbc⟩ := isInSpanAt_eq_iff.mp ((hgen b).mp hb)
    have hca : 𝔟.mem y (fun p => c p * a p) := CompanionReduction.mul_mem_of_isCoherent h𝔟 hc ha
    refine isInSpanAt_of_eq_mul ⟨fun p => c p * a p, hca, rfl⟩ ((hhol ha).mul hbh) (holomorphicAt_const 1) ?_
    filter_upwards [hbc] with p hp
    simp only [Pi.mul_apply, hp]
    ring
  · refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
    rintro s ⟨a, ha, rfl⟩
    exact isInSpanAt_self ⟨a, m, ha, (hgen m).mpr (isInSpanAt_self rfl hm), rfl⟩ ((hhol ha).mul hm)

variable {E : List (Set M)}

/-- A germ outside a coherent ideal does not vanish near the point. -/
theorem isNonzeroAt_of_notMem {𝔞 𝔠 : GermIdeal n M} (h𝔠 : 𝔠.IsCoherent) {z : M} {a : M → ℂ}
    (ha : 𝔞.mem z a) (hna : ¬ 𝔠.mem z a) : IsNonzeroAt 𝔞 z := by
  refine ⟨a, ha, fun hall => hna ?_⟩
  have h0 : 𝔠.mem z (fun _ => 0) :=
    GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔠 BlowupStrictIdeal.isInSpanAt_zero
  exact mem_congr_of_isCoherent h𝔠 h0 (hall.mono fun p hp => (not_not.mp hp).symm)

/-- A product of a nonzero ideal and a principal monomial ideal is nonzero. -/
theorem isNonzeroAt_mul_of_isPrincipalAt {𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) (h𝓜 : 𝓜.IsCoherent)
    {z : M} {b : Fin E.length → ℕ} (hP : IsPrincipalAt 𝓜 E z b) (hne : IsNonzeroAt 𝔟 z) :
    IsNonzeroAt (𝔟.mul 𝓜) z := by
  obtain ⟨a, ha, hafreq⟩ := hne
  obtain ⟨m, hm, hmfreq⟩ := hP.isNonzeroAt h𝓜
  have hah := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 ha
  have hmh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝓜 hm
  have hmem : (𝔟.mul 𝓜).mem z (fun p => a p * m p) :=
    isInSpanAt_self (S := fun s => ∃ a b, 𝔟.mem z a ∧ 𝓜.mem z b ∧ s = a * b) ⟨a, m, ha, hm, rfl⟩ (hah.mul hmh)
  refine ⟨fun p => a p * m p, hmem, fun hall => hafreq ?_⟩
  have h0 := eventually_eq_zero_of_mul_eventually_eq_zero hah hmh hmfreq
    (hall.mono fun p hp => not_not.mp hp)
  exact h0.mono fun p hp => not_not.mpr hp

open Classical in
/-- **Identification of the two parts** (`hir:nonmonomial-transform`, `N = M`): if `𝔞 = 𝔟 · 𝓜` with `𝓜` principal monomial
at every point and `𝔟` coherent and contained in the ideal of no member of `E` at its points, then `𝓝(𝔞) = 𝔟` and
`𝓜(𝔞) = 𝓜` (`NonmonomialTransform`). -/
theorem parts_eq_of_factor (hn : 0 < n) (hE : IsSNCDivisor n E) {𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    (h𝓜 : 𝓜.IsCoherent) (hP : ∀ z, ∃ b, IsPrincipalAt 𝓜 E z b)
    (hnd : ∀ y i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧ ¬ (vanishingIdeal (n := n) (E.get i)).mem y a) :
    nonmonomialPart n (𝔟.mul 𝓜) E = 𝔟 ∧ monomialPart n (𝔟.mul 𝓜) E = 𝓜 := by
  have hcoh : (𝔟.mul 𝓜).IsCoherent := isCoherent_mul h𝔟 h𝓜
  have hhol : ∀ y g, (𝔟.mul 𝓜).mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  -- the data at one point
  have key : ∀ z, (∀ g, (nonmonomialPart n (𝔟.mul 𝓜) E).mem z g ↔ 𝔟.mem z g) ∧
      ∀ g, (monomialPart n (𝔟.mul 𝓜) E).mem z g ↔ 𝓜.mem z g := by
    intro z
    obtain ⟨b, hPz⟩ := hP z
    have hgen0 := hPz
    obtain ⟨-, -, -, -, -, -, hgenz⟩ := hgen0
    obtain ⟨Φ, σ, hΦsrc, hσ, hA, hev⟩ := hPz.eventually h𝓜
    set T : Finset (Fin E.length) := Finset.univ.filter fun i => z ∈ E.get i with hT_def
    have hT : ∀ i, i ∈ T ↔ z ∈ E.get i := fun i => by simp [hT_def]
    have hfac : ∀ᶠ y in 𝓝 z, ∀ g, (𝔟.mul 𝓜).mem y g ↔
        IsInSpanAt (n := n) (fun s => ∃ a, 𝔟.mem y a ∧ s = fun p => a p * ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i) y g := by
      filter_upwards [hev, (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyD g
      exact mul_mem_iff_of_principal h𝔟 (holomorphicAt_flatMonomial (σ := σ) (T := T) b hyD) hy g
    have hnd' : ∀ᶠ y in 𝓝 z, ∀ i ∈ T, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧
        ¬ (vanishingIdeal (n := n) (E.get i)).mem y a :=
      Eventually.of_forall fun y i _ hyi => hnd y i hyi
    refine ⟨nonmonomialPart_mem_iff_of_mul_principal hΦsrc hσ hA b hfac hnd' hn hE h𝔟 hhol hT, fun g => ?_⟩
    have hgz : ∀ g, 𝓜.mem z g ↔ IsInSpanAt (n := n) (· = fun p => ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i) z g :=
      hev.self_of_nhds
    rw [monomialPart_mem_iff_of_mul_principal hΦsrc hσ hA b hfac hnd' hn hE h𝔟 hhol hT g, hgz g]
  refine ⟨GermIdeal.ext (funext fun z => funext fun g => propext ((key z).1 g)),
    GermIdeal.ext (funext fun z => funext fun g => propext ((key z).2 g))⟩

end Factor

/-! ### The generic-point argument -/

section Generic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {E : List (Set M)} {C : Set M}

open Classical in
/-- **Generic points of a centre with normal crossings**: points of `C` that lie on no member `E_i` through `x` with
`C ⊄ E_i` near `x` accumulate at `x ∈ C`.  In coordinates adapted to `C = {w_t = 0, t ∈ S₀}` and `E_i = {w_t = 0, t ∈ S_i}`,
`C ⊄ E_i` near `x` forces some `t ∈ S_i \ S₀`; move those coordinates off `0` and keep the others. -/
theorem frequently_mem_notMem_of_hasNormalCrossings (hnc : HasNormalCrossings n C E) {x : M} (hx : x ∈ C) :
    ∃ᶠ y in 𝓝 x, y ∈ C ∧ ∀ i : Fin E.length, x ∈ E.get i →
      ¬ (∀ᶠ y' in 𝓝 x, y' ∈ C → y' ∈ E.get i) → y ∉ E.get i := by
  obtain ⟨S₀, S, ⟨Φ, hΦsrc, hΦ0, hcoord⟩, -⟩ := hnc x hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  set T' : Finset (Fin n) := (Finset.univ.filter fun i : Fin E.length => x ∈ E.get i).biUnion
    (fun i => S i \ S₀) with hT'
  have hT'S₀ : ∀ t ∈ T', t ∉ S₀ := by
    intro t ht
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_sdiff.mp hi).2
  have hC : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S₀) :=
    fun hy1 hy2 => hcoord none hx hy1 hy2
  have hEi : ∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S i)) :=
    fun i hxi _ hy1 hy2 => hcoord (some i) hxi hy1 hy2
  refine (frequently_flatMap_ne_zero hΦsrc hxD T').mono fun y ⟨hyD, hne, heq⟩ => ⟨?_, fun i hxi hnot hyi => ?_⟩
  · refine (hC hyD.1 hyD.2).mpr fun t ht => ?_
    have h1 : flatMap Φ y t = flatMap Φ x t := heq t fun h => hT'S₀ t h ht
    have h2 : flatMap Φ x t = 0 := by
      have h : (Φ.toFun ((complexChartAt (n := n) x).val x)) t = 0 := by rw [hΦ0]; simp
      exact h
    exact h1.trans h2
  · -- `S i ⊄ S₀`, else `C ⊆ E_i` near `x`
    have hsub : ¬ S i ⊆ S₀ := by
      intro hS
      refine hnot ?_
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y' hy' hy'C
      exact (hEi i hxi hy'.1 hy'.2).mpr fun t ht => (hC hy'.1 hy'.2).mp hy'C t (hS ht)
    obtain ⟨t, htS, htS₀⟩ := Finset.not_subset.mp hsub
    have htT : t ∈ T' := Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, Finset.mem_sdiff.mpr ⟨htS, htS₀⟩⟩
    exact hne t htT ((hEi i hxi hyD.1 hyD.2).mp hyi t htS)

open Classical in
/-- **The exponents of the members containing a centre in the cosupport of a monomial ideal** (the generic-point
argument of `hir:nonmonomial-transform`): if `𝓜` is monomial and nonzero, `C` has normal crossings with `E` and
`C ⊆ cosupp(𝓜, μ)`, then at `x ∈ C` the exponents of the members containing `C` near `x` add up to at least `μ`. -/
theorem le_sum_divExp_of_subset_cosupport (hn : 0 < n) (hE : IsSNCDivisor n E) {𝓜 : GermIdeal n M}
    (h𝓜 : 𝓜.IsCoherent) (hmono : (monomialPart n 𝓜 E).Le 𝓜) (h0 : ∀ y, IsNonzeroAt 𝓜 y)
    (hnc : HasNormalCrossings n C E) {μ : ℕ} (hCμ : C ⊆ cosupport n univ 𝓜 μ) {x : M} (hx : x ∈ C) :
    μ ≤ ∑ i ∈ Finset.univ.filter (fun i => x ∈ E.get i ∧ ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ E.get i),
      divExp n 𝓜 (E.get i) x := by
  obtain ⟨y, ⟨hyC, hyE⟩, hsub, hexp⟩ := ((frequently_mem_notMem_of_hasNormalCrossings hnc hx).and_eventually
    ((eventually_memberIdx_subset E hE.1 x).and (eventually_expData_eq hn hE h𝓜 h0 x))).exists
  have h1 := (mem_cosupport_iff_of_monomial hn hE h𝓜 hmono μ y).mp (hCμ hyC)
  rw [Finset.sum_congr rfl hexp] at h1
  have h2 : ∑ i ∈ memberIdx E y, expData n 𝓜 E x i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin E.length => y ∈ E.get i), divExp n 𝓜 (E.get i) x := by
    rw [memberIdx, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.valEmbedding_apply, expData, dif_pos i.2, Fin.eta]
  rw [h2] at h1
  refine h1.trans (Finset.sum_le_sum_of_subset fun i hi => ?_)
  have hyi : y ∈ E.get i := (Finset.mem_filter.mp hi).2
  have hxi : x ∈ E.get i := by
    obtain ⟨hlt, h⟩ := (mem_memberIdx E).mp (hsub ((mem_memberIdx E).mpr ⟨i.2, hyi⟩))
    exact h
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi, ?_⟩
  by_contra hnot
  exact hyE i hxi hnot hyi

end Generic

/-! ### The exceptional divisor -/

section Exceptional

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- **At the points of `D = π⁻¹ C` the ideal of `π⁻¹ C` lies in `𝒪(-D)`**: `π⁻¹ C` is a smooth hypersurface
(`BlowupSNCTransform.isSNCDivisor_preimage_centre`), so its ideal is generated by a coordinate `Φ_t`; `𝒪(-D) = (W_j)` with
`W_j` of nonzero differential (TN3's monomial chart); `W_j` vanishes on `π⁻¹ C`, so `W_j = c Φ_t`, and `c(z) ≠ 0` since
`W_j ∉ 𝔪_z²`; hence `Φ_t = c⁻¹ W_j ∈ 𝒪(-D)`. -/
theorem exceptionalDivisor_mem_of_vanishingIdeal_mem (hπ : IsBlowupAlong n C π) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hnc : HasNormalCrossings n C E) {z : Y} (hz : π z ∈ C) {g : Y → ℂ}
    (hg : (vanishingIdeal (n := n) (π ⁻¹' C)).mem z g) : (exceptionalDivisor hπ).ideal.mem z g := by
  have hn : 0 < n := SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hz
  obtain ⟨j, -, W, U, hU, hzU, hWs, hinj, -, hD, -⟩ := MonomialBlowup.exists_monomial_chart hπ hE hnc hz
  have hhol : ∀ y ∈ U, HolomorphicAt n (fun w => W w j) y := fun y hy =>
    BlowupStrictIdeal.holomorphicAt_coord hU hWs j hy
  have hzero : ∀ y ∈ U, (π y ∈ C ↔ W y j = 0) := fun y hy =>
    MonomialBlowup.mem_centre_iff_of_generator hπ (hhol y hy) (hD y hy)
  obtain ⟨Φ, σ, hΦsrc, hΦ0, -, hA⟩ := exists_snc_chart hn (BlowupSNCTransform.isSNCDivisor_preimage_centre hπ) z
  set i0 : Fin [π ⁻¹' C].length := ⟨0, by simp⟩ with hi0
  have hzi : z ∈ [π ⁻¹' C].get i0 := hz
  have hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Φ.source →
      (y ∈ π ⁻¹' C ↔ Φ.toFun (chartAt (ComplexModel n) z y) (σ i0) = 0) := fun hy1 hy2 => hA i0 hzi hy1 hy2
  have hzD : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hIgen := vanishingIdeal_mem_iff_flatCoord Φ hflat hzD
  have hΦt : HolomorphicAt n (flatCoord Φ (σ i0)) z := holomorphicAt_flatCoord Φ (σ i0) hzD
  -- `W_j` lies in the ideal of `π⁻¹ C`
  have hWI : (vanishingIdeal (n := n) (π ⁻¹' C)).mem z (fun w => W w j) := by
    refine ⟨hhol z hzU, ?_⟩
    filter_upwards [hU.mem_nhds hzU] with y hy hyC
    exact (hzero y hy).mp hyC
  obtain ⟨-, c, hc, hWc⟩ := isInSpanAt_eq_iff.mp ((hIgen _).mp hWI)
  -- `c(z) ≠ 0`: otherwise `W_j ∈ 𝔪_z²`
  have hcz : c z ≠ 0 := by
    intro hc0
    obtain ⟨v, hv⟩ := exists_chartDeriv_coord_ne_zero hWs hzU hinj j
    have hm1 : (pointIdeal n z).mem z c := mem_pointIdeal_of_apply_eq_zero hc hc0
    have hΦz : flatCoord Φ (σ i0) z = 0 := by
      have h : (Φ.toFun (chartAt (ComplexModel n) z z)) (σ i0) = 0 := by rw [hΦ0]; simp
      exact h
    have hm2 : (pointIdeal n z).mem z (flatCoord Φ (σ i0)) := mem_pointIdeal_of_apply_eq_zero hΦt hΦz
    have hpt : ∀ y' g', (pointIdeal n z).mem y' g' → HolomorphicAt n g' y' := fun _ _ hg' => hg'.1
    have h2 := mul_mem_idealPow_add hpt (pow_mem_idealPow hm1 hc 1) (pow_mem_idealPow hm2 hΦt 1)
    have h2' : (idealPow (pointIdeal n z) 2).mem z (fun w => W w j) :=
      OrderTaylor.mem_idealPow_congr h2 (hWc.mono fun y hy => by simp [hy])
    have h0 := OrderTaylor.iterChartDeriv_eq_zero_of_mem_idealPow (e := complexChartAt (n := n) z)
      (mem_chart_source _ z) h2' [v] (by simp)
    exact hv (by simpa using h0)
  -- conclusion
  obtain ⟨hgh, c', hc', hgc⟩ := isInSpanAt_eq_iff.mp ((hIgen g).mp hg)
  refine (hD z hzU g).mpr (isInSpanAt_eq_iff.mpr ⟨hgh, fun y => c' y * (c y)⁻¹,
    hc'.mul (RelativePrincipalizationSpan.holomorphicAt_inv hc hcz), ?_⟩)
  filter_upwards [hgc, hWc, hc.continuousAt.eventually (isOpen_ne.mem_nhds hcz)] with y h1 h2 h3
  rw [h1, h2]
  field_simp

/-- **Off the exceptional divisor the controlled transform of a nonzero ideal is nonzero**: `π` has a holomorphic
section over `X \ C` (`BlowupIsomorphismOff.exists_section_compl`), so `a ∘ π` does not vanish near `z` when `a` does not
vanish near `π z`. -/
theorem isNonzeroAt_controlledTransform_of_notMem (hπ : IsBlowupAlong n C π) {𝔟 : GermIdeal n X}
    (h𝔟 : 𝔟.IsCoherent) (o : ℕ) {z : Y} (hz : π z ∉ C) (hne : IsNonzeroAt 𝔟 (π z)) :
    IsNonzeroAt (controlledTransform hπ 𝔟 o) z := by
  obtain ⟨a, ha, hfreq⟩ := hne
  refine ⟨a ∘ π, CompanionReduction.pullback_le_controlledTransform hπ h𝔟 o z _
    (CompanionReduction.comp_mem_pullback' hπ h𝔟 ha), fun hall => hfreq ?_⟩
  obtain ⟨s, hs, hsπ, hsz⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hO : IsOpen Cᶜ := hπ.1.1.isOpen_compl
  have hcont := hs.continuous.continuousAt (x := ⟨π z, hz⟩)
  have h1 := hcont.eventually (by rw [hsz z hz]; exact hall)
  have hmap := map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ Cᶜ) (x := π z) hz (hO.mem_nhds hz)
  rw [← hmap, Filter.eventually_map]
  filter_upwards [h1] with p hp
  have hps : π (s p) = p.1 := congrFun hsπ p
  have hp' : a (π (s p)) = 0 := not_not.mp hp
  rw [hps] at hp'
  simpa using hp'

end Exceptional

/-! ### One blowup -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X}

/-- `𝔩^k = (h^k)` at a point where `𝔩 = (h)`. -/
theorem idealPow_mem_iff_of_generator {𝔩 : GermIdeal n Y} {z : Y} {h : Y → ℂ} (hh : HolomorphicAt n h z)
    (hgen : ∀ g, 𝔩.mem z g ↔ IsInSpanAt (n := n) (· = h) z g) (k : ℕ) (g : Y → ℂ) :
    (idealPow 𝔩 k).mem z g ↔ IsInSpanAt (n := n) (· = fun y => h y ^ k) z g := by
  constructor
  · intro hg
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_pow_of_mem_idealPow (fun g hg => (hgen g).mp hg) hg
    exact isInSpanAt_eq_iff.mpr ⟨holomorphicAt_of_mem_idealPow hg, c, hc, hgc⟩
  · intro hg
    obtain ⟨-, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
    have hpow := pow_mem_idealPow ((hgen h).mpr (isInSpanAt_self rfl hh)) hh k
    exact OrderTaylor.mem_idealPow_congr (mul_mem_idealPow hc hpow) hgc.symm

open Classical in
/-- **One blowup of `𝔟 · 𝓜`** (`hir:nonmonomial-transform`, one-blowup assembly, `N = M`).  Let `E` be simple normal
crossings, `𝓜` principal monomial at every point, `𝔟` coherent, nonzero and contained in the ideal of no member at its
points; let `C` (the centre of `π`) have normal crossings with `E`, lie in `cosupp(𝔟, o) ∩ cosupp(𝔟𝓜, d)`, with
`ord 𝔟 ≤ o` on `C`.  Then `σ^c(𝔟𝓜, d) = σ^c(𝔟, o) · 𝓜'` with `𝓜' = 𝒪(-(o - d)D) · σ^c(𝓜, d - o)` principal monomial at
every point for `E' = (E_1', …, E_s', π⁻¹ C)`, and `σ^c(𝔟, o)` is nonzero and contained in the ideal of no member of `E'`
at its points. -/
theorem step (hn : 0 < n) (hπ : IsBlowupAlong n C π) {E : List (Set X)} (hE : IsSNCDivisor n E)
    {𝔟 𝓜 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) (h𝓜 : 𝓜.IsCoherent) (hP : ∀ x, ∃ b, IsPrincipalAt 𝓜 E x b)
    (hnd : ∀ y i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧ ¬ (vanishingIdeal (n := n) (E.get i)).mem y a)
    (hnz : ∀ y, IsNonzeroAt 𝔟 y) {o d : ℕ} (hnc : HasNormalCrossings n C E)
    (hCb : C ⊆ cosupport n univ 𝔟 o) (hCa : C ⊆ cosupport n univ (𝔟.mul 𝓜) d)
    (hbd : ∀ x ∈ C, x ∉ cosupport n univ 𝔟 (o + 1)) :
    ∃ 𝓜' : GermIdeal n Y, 𝓜'.IsCoherent ∧
      controlledTransform hπ (𝔟.mul 𝓜) d = (controlledTransform hπ 𝔟 o).mul 𝓜' ∧
      (∀ z, ∃ b, IsPrincipalAt 𝓜' (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) z b) ∧
      (∀ y i, y ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i → ∃ a,
        (controlledTransform hπ 𝔟 o).mem y a ∧
          ¬ (vanishingIdeal (n := n) ((E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i)).mem y a) ∧
      ∀ y, IsNonzeroAt (controlledTransform hπ 𝔟 o) y := by
  have hCc : IsClosedSubmanifold n C := hπ.1
  have hhol𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  have hhol𝓜 : ∀ x g, 𝓜.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝓜 hg
  have hmono : (monomialPart n 𝓜 E).Le 𝓜 := fun x g hg =>
    (hP x).choose_spec.monomialPart_le hn hE h𝓜 g hg
  have h0𝓜 : ∀ y, IsNonzeroAt 𝓜 y := fun y => (hP y).choose_spec.isNonzeroAt h𝓜
  -- `C` lies in the cosupport of `𝓜` with the mark `d - o`
  have hC𝓜 : C ⊆ cosupport n univ 𝓜 (d - o) := by
    intro x hx
    by_cases hod : o ≤ d
    · exact GermOrderProduct.mem_cosupport_of_mem_cosupport_mul hhol𝔟 hhol𝓜 hod (hCa hx) (hbd x hx)
    · rw [show d - o = 0 by omega, cosupport_zero hhol𝓜]
      exact mem_univ x
  have hle𝔟 := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝔟 hCc hCb
  have hle𝓜 := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝓜 hCc hC𝓜
  have hI : (exceptionalDivisor hπ).ideal.IsCoherent := isCoherent_ideal _
  have hIp : ∀ k, (idealPow (exceptionalDivisor hπ).ideal k).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_idealPow hI
  have hσ𝔟 := isCoherent_controlledTransform hπ h𝔟 hle𝔟
  have hσ𝓜 := isCoherent_controlledTransform hπ h𝓜 hle𝓜
  have h𝓜' : ((idealPow (exceptionalDivisor hπ).ideal (o - d)).mul (controlledTransform hπ 𝓜 (d - o))).IsCoherent :=
    isCoherent_mul (hIp _) hσ𝓜
  -- the factorization `σ^c(𝔟𝓜, d) = σ^c(𝔟, o) · 𝒪(-(o - d)D) σ^c(𝓜, d - o)`
  have hfac : controlledTransform hπ (𝔟.mul 𝓜) d = (controlledTransform hπ 𝔟 o).mul
      ((idealPow (exceptionalDivisor hπ).ideal (o - d)).mul (controlledTransform hπ 𝓜 (d - o))) := by
    refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_mul hσ𝔟 h𝓜') ?_).symm
    rw [GermIdealTotalTransform.pullback_mul hπ.contMDiff h𝔟 h𝓜, pullback_eq_mul_controlledTransform hπ h𝔟 hle𝔟,
      pullback_eq_mul_controlledTransform hπ h𝓜 hle𝓜, mul_mul_mul_comm (hIp o) hσ𝔟 (hIp (d - o)) hσ𝓜,
      ← RestrictLeCalculus.idealPow_add hI, show o + (d - o) = d + (o - d) by omega,
      RestrictLeCalculus.idealPow_add hI,
      GermIdealTotalTransform.mul_assoc (hIp d) (hIp (o - d)) (isCoherent_mul hσ𝔟 hσ𝓜),
      ← GermIdealTotalTransform.mul_assoc (hIp (o - d)) hσ𝔟 hσ𝓜,
      RestrictLeCalculus.mul_comm' (idealPow (exceptionalDivisor hπ).ideal (o - d)) (controlledTransform hπ 𝔟 o),
      GermIdealTotalTransform.mul_assoc hσ𝔟 (hIp (o - d)) hσ𝓜]
  -- the transform of `(𝓜, d - o)` as a marked ideal
  set 𝔪M : MarkedIdeal n X := ⟨univ, E, 𝓜, d - o⟩ with h𝔪M
  have hσ𝓜eq : (𝔪M.geoTransform C π).ideal = controlledTransform hπ 𝓜 (d - o) :=
    geoTransform_ideal_eq_controlledTransform rfl h𝓜 hπ
  refine ⟨_, h𝓜', hfac, fun z => ?_, fun y i hy => ?_, fun y => ?_⟩
  · by_cases hz : π z ∈ C
    · -- over the centre: TN3's chart, and `𝒪(-D) = (Θ_D)` at `z`
      obtain ⟨Φ, σ₀, hΦsrc, hΦ0, hσ₀, hA₀, hgen₀⟩ := isPrincipalAt_of_monomial hn hE h𝓜 hmono (π z)
      have hd' := le_sum_divExp_of_subset_cosupport hn hE h𝓜 hmono h0𝓜 hnc hC𝓜 hz
      obtain ⟨Θ, σ, a', hΘt, hΘ0, hσ, hA, -, -, hgen⟩ :=
        MonomialBlowup.exists_snc_chart_geoTransform_of_flat hπ 𝔪M rfl h𝓜 hE hnc hz
          (T := Finset.univ.filter fun i => π z ∈ E.get i) (fun i => by simp [h𝔪M]) (fun i hi => hA₀ i (Finset.mem_filter.mp hi).2)
          (fun i => divExp n 𝓜 (E.get i) (π z)) hgen₀ hd'
      rw [hσ𝓜eq] at hgen
      set E' : List (Set Y) := E.map (geoStrictTransform π C) ++ [π ⁻¹' C] with hE'
      set iD : Fin E'.length := ⟨E.length, by simp [hE']⟩ with hiD
      have hE'D : E'.get iD = π ⁻¹' C := by
        have h := BlowupSNCTransform.get_map_append_singleton E (geoStrictTransform π C) (π ⁻¹' C) iD
        rw [dif_neg (show ¬ (iD : ℕ) < E.length from by simp [hiD])] at h
        exact h
      have hzD : z ∈ E'.get iD := by rw [hE'D]; exact hz
      have hzΘ : z ∈ flatDomain Θ := mem_flatDomain_self Θ
      have hflat : ∀ {y : Y}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ Θ.source →
          (y ∈ π ⁻¹' C ↔ Θ.toFun (chartAt (ComplexModel n) z y) (σ iD) = 0) := fun hy1 hy2 => by
        rw [← hE'D]; exact hA iD hzD hy1 hy2
      have hDgen : ∀ g, (exceptionalDivisor hπ).ideal.mem z g ↔
          IsInSpanAt (n := n) (· = flatCoord Θ (σ iD)) z g := by
        intro g
        rw [← vanishingIdeal_mem_iff_flatCoord Θ hflat hzΘ g]
        exact ⟨fun hg => BlowupStrictIdeal.pullback_vanishingIdeal_le hπ.contMDiff.continuous C z g hg,
          fun hg => exceptionalDivisor_mem_of_vanishingIdeal_mem hπ hE hnc hz hg⟩
      have hIk := idealPow_mem_iff_of_generator (holomorphicAt_flatCoord Θ (σ iD) hzΘ) hDgen (o - d)
      set F : Finset (Fin E'.length) := Finset.univ.filter fun i => z ∈ E'.get i with hF
      have hiDF : iD ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzD⟩
      have hq : HolomorphicAt n (fun y => ∏ i ∈ F, flatCoord Θ (σ i) y ^ a' i) z :=
        holomorphicAt_flatMonomial (σ := σ) (T := F) a' hzΘ
      set a'' : Fin E'.length → ℕ := fun i => if i = iD then a' i + (o - d) else a' i with ha''
      have hprod : ∀ y, flatCoord Θ (σ iD) y ^ (o - d) * ∏ i ∈ F, flatCoord Θ (σ i) y ^ a' i =
          ∏ i ∈ F, flatCoord Θ (σ i) y ^ a'' i := by
        intro y
        rw [← Finset.mul_prod_erase F (fun i => flatCoord Θ (σ i) y ^ a' i) hiDF,
          ← Finset.mul_prod_erase F (fun i => flatCoord Θ (σ i) y ^ a'' i) hiDF]
        have h1 : ∏ i ∈ F.erase iD, flatCoord Θ (σ i) y ^ a'' i = ∏ i ∈ F.erase iD, flatCoord Θ (σ i) y ^ a' i :=
          Finset.prod_congr rfl fun i hi => by
            simp only [ha'', if_neg (Finset.ne_of_mem_erase hi)]
        rw [h1]
        simp only [ha'', if_pos rfl, pow_add]
        ring
      refine ⟨a'', Θ, σ, hΘt, hΘ0, hσ, hA, fun g => ?_⟩
      rw [mul_mem_iff_of_generators hIk hgen (CompanionReduction.holomorphicAt_pow_of
        (holomorphicAt_flatCoord Θ (σ iD) hzΘ) _) hq g]
      exact MemberPullback.isInSpanAt_eq_congr (Eventually.of_forall hprod) g
    · -- off the centre: the transform of `(𝓜, d - o)` is principal, and `𝒪(-D)` is the unit ideal at `z`
      obtain ⟨b, hb⟩ := hP (π z)
      have hP' := isPrincipalAt_geoTransform_of_notMem hn hπ 𝔪M rfl hE h𝓜 hz hb
      rw [hσ𝓜eq] at hP'
      obtain ⟨Θ, σ, hΘt, hΘ0, hσ, hA, hgen⟩ := hP'
      have h1 : (exceptionalDivisor hπ).ideal.mem z (fun _ => (1 : ℂ)) :=
        one_mem_pullback_vanishingIdeal hz hπ.1.1
      have hIk : ∀ g, (idealPow (exceptionalDivisor hπ).ideal (o - d)).mem z g ↔
          IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) z g := by
        intro g
        rw [isInSpanAt_one_iff]
        refine ⟨fun hg => holomorphicAt_of_mem_idealPow hg, fun hg => ?_⟩
        refine mem_congr_of_isCoherent (hIp _)
          (CompanionReduction.mul_mem_of_isCoherent (hIp _) hg (one_mem_idealPow h1 (o - d))) ?_
        exact Eventually.of_forall fun p => mul_one _
      refine ⟨fun i => if h : i.1 < E.length then b ⟨i.1, h⟩ else 0, Θ, σ, hΘt, hΘ0, hσ, hA, fun g => ?_⟩
      rw [mul_mem_iff_of_generators hIk hgen (holomorphicAt_const 1)
        (holomorphicAt_flatMonomial (σ := σ) _ (mem_flatDomain_self Θ)) g]
      exact MemberPullback.isInSpanAt_eq_congr (Eventually.of_forall fun p => one_mul _) g
  · -- the transform of `𝔟` lies in the ideal of no member of `E'`
    rw [BlowupSNCTransform.get_map_append_singleton] at hy ⊢
    split_ifs at hy ⊢ with hi
    · exact ExceptionalIdealPushforward.exists_not_mem_vanishingIdeal_geoStrictTransform hπ h𝔟 hCb hy
        (Eventually.of_forall fun y' hy' => hnd y' _ hy'.1)
    · obtain ⟨a, ha, hna⟩ := ExceptionalIdealPushforward.exists_not_mem_exceptionalDivisor hπ h𝔟 hCb hy (hbd _ hy)
      exact ⟨a, ha, fun h => hna (exceptionalDivisor_mem_of_vanishingIdeal_mem hπ hE hnc hy h)⟩
  · by_cases hy : π y ∈ C
    · obtain ⟨a, ha, hna⟩ := ExceptionalIdealPushforward.exists_not_mem_exceptionalDivisor hπ h𝔟 hCb hy (hbd _ hy)
      exact isNonzeroAt_of_notMem (isCoherent_ideal _) ha hna
    · exact isNonzeroAt_controlledTransform_of_notMem hπ h𝔟 o hy (hnz _)

end Step

/-! ### The monomial part is principal monomial -/

section MonomialPartPrincipal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {E : List (Set M)} {𝔞 : GermIdeal n M}

open Classical in
/-- **The monomial part is principal monomial at every point** (`hir:monomial-part-ambient`): in simple normal crossings
coordinates at `x`, `𝓜(𝔞)_x = (∏_{x ∈ E_i} u_{σ i}^{e_i(x)})`. -/
theorem isPrincipalAt_monomialPart (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔞 : 𝔞.IsCoherent)
    (h0 : ∀ y, IsNonzeroAt 𝔞 y) (x : M) :
    IsPrincipalAt (monomialPart n 𝔞 E) E x (fun i => divExp n 𝔞 (E.get i) x) := by
  obtain ⟨Φ, σ, hΦsrc, hΦx, hσ, hA⟩ := exists_snc_chart hn hE x
  set T : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i with hT_def
  set e : Fin E.length → ℕ := fun i => divExp n 𝔞 (E.get i) x
  have hx : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  refine ⟨Φ, σ, hΦsrc, hΦx, fun i hi j hj hij =>
    hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩) hij, hA,
    fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · have hdiv : ∀ i ∈ T, ∃ c, HolomorphicAt n c x ∧ g =ᶠ[𝓝 x] fun z => c z * flatMap Φ z (σ i) ^ e i := by
      intro i hi
      have hxi : x ∈ E.get i := (Finset.mem_filter.mp hi).2
      exact exists_eq_mul_pow_of_mem_idealPow
        (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ (hA i hxi) hx g).mp hg) (hg.2 i hxi)
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_prod_of_forall hΦsrc (A := fun i => E.get i) e hx T
      (fun i hi _ hy1 hy2 => hA i (Finset.mem_filter.mp hi).2 hy1 hy2)
      (fun i _ y hy => (isClosedSubmanifold_get hn hE i).2 y hy) hσ hg.1 hdiv
    exact isInSpanAt_eq_iff.mpr ⟨hg.1, c, hc, hgc⟩
  · have hmM : (monomialPart n 𝔞 E).mem x (fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ e i) := by
      refine ⟨holomorphicAt_finset_prod T fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ i) hx) (e i), fun i hxi => ?_⟩
      have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
      exact flatMonomial_mem_idealPow_vanishingIdeal (fun i hi => hA i (Finset.mem_filter.mp hi).2) e hi
    exact GermIdealTotalTransform.mem_of_isInSpanAt_mem (isCoherent_monomialPart hn hE h𝔞 h0)
      (IsInSpanAt.mono (fun t ht => by rw [ht]; exact hmM) hg)

end MonomialPartPrincipal

/-! ### Along the companion tower -/

section Tower

variable {X : CMfd.{u} n}

open Classical in
/-- **The factorization along the companion tower** (the induction behind `nonmonomialPart_geoTransformAlong`): let
`𝔞 = 𝔟 · 𝓜` with `𝓜` principal monomial at every point, `𝔟` coherent, nonzero and contained in the ideal of no member
at its points, `(X, X, E, 𝔞, d)` well formed, `d, o ≥ 1` and `ord 𝔟 ≤ o` on `cosupp(𝔞, d)`.  Along every multiple test
blow-up `T` of the companion ideal `companion E 𝔟 𝓜 o d`, the transform `𝔞_T` of `(𝔞, d)` is `𝔟_T · 𝓜_T` with `𝔟_T` the
transform of `(𝔟, o)` (again coherent, nonzero, in the ideal of no member of `E_T`) and `𝓜_T` principal monomial at every
point (`step` at each stage, the bounds and the admissibility from `CompanionReduction.companion_reduction`). -/
theorem factor_along (hn : 0 < n) (E : List (Set X)) {𝔟 𝓜 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent)
    (h𝓜 : 𝓜.IsCoherent) (hP : ∀ x, ∃ b, IsPrincipalAt 𝓜 E x b)
    (hnd : ∀ y i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧ ¬ (vanishingIdeal (n := n) (E.get i)).mem y a)
    (hnz : ∀ y, IsNonzeroAt 𝔟 y) {o d : ℕ} (ho : 1 ≤ o) (hd : 1 ≤ d)
    (hwf : (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X).IsWellFormed)
    (hbound : ∀ x ∈ cosupport n univ (𝔟.mul 𝓜) d, x ∉ cosupport n univ 𝔟 (o + 1)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (companion E 𝔟 𝓜 o d) T →
      (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).IsWellFormed ∧
      (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N = univ ∧
      (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).N = univ ∧
      (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).E =
        (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E ∧
      (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.IsCoherent ∧
      (∀ y, IsNonzeroAt (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal y) ∧
      (∀ y i, y ∈ (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E.get i → ∃ a,
        (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.mem y a ∧
        ¬ (vanishingIdeal (n := n) ((geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E.get i)).mem y a) ∧
      ∃ 𝓜T : GermIdeal n Y, 𝓜T.IsCoherent ∧
        (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).ideal =
          (geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.mul 𝓜T ∧
        ∀ z, ∃ b, IsPrincipalAt 𝓜T (geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E z b
  | _, .refl, _ => ⟨hwf, rfl, rfl, rfl, h𝔟, hnz, hnd, 𝓜, h𝓜, rfl, hP⟩
  | _, .step T C π hπ, hT => by
      obtain ⟨hTp, -⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      obtain ⟨hwfT, hNT, hN𝔫T, hET, hcoh𝔫T, hnzT, hndT, 𝓜T, h𝓜T, hfacT, hPT⟩ :=
        factor_along hn E h𝔟 h𝓜 hP hnd hnz ho hd hwf hbound T hTp
      obtain ⟨hTm', hTn', -, -⟩ := companion_reduction E h𝔟 h𝓜 ho hd hbound (.step T C π hπ) hT
      obtain ⟨-, -, hbT, -⟩ := companion_reduction E h𝔟 h𝓜 ho hd hbound T hTp
      obtain ⟨-, hCm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hTm'
      obtain ⟨-, hCn⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hTn'
      set 𝔪T := geoTransformAlong (⟨univ, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T with h𝔪T
      set 𝔫T := geoTransformAlong (⟨univ, E, 𝔟, o⟩ : MarkedIdeal n X) T with h𝔫T
      have hd𝔪 : 𝔪T.d = d := d_geoTransformAlong _ T
      have hd𝔫 : 𝔫T.d = o := d_geoTransformAlong _ T
      have hCa : C ⊆ cosupport n univ (𝔫T.ideal.mul 𝓜T) d := by
        have h := hCm.2.1
        rw [MarkedIdeal.cosupp, hNT, hfacT, hd𝔪] at h
        exact h
      have hCb : C ⊆ cosupport n univ 𝔫T.ideal o := by
        have h := hCn.2.1
        rw [MarkedIdeal.cosupp, hN𝔫T, hd𝔫] at h
        exact h
      have hbd : ∀ x ∈ C, x ∉ cosupport n univ 𝔫T.ideal (o + 1) := fun x hx => hbT x (hCm.2.1 hx)
      obtain ⟨𝓜', h𝓜', hfac', hP', hnd', hnz'⟩ :=
        step hn hπ hwfT.isSNCDivisor hcoh𝔫T h𝓜T hPT hndT hnzT hCm.2.2 hCb hCa hbd
      have hσ𝔫 : (𝔫T.geoTransform C π).ideal = controlledTransform hπ 𝔫T.ideal o := by
        rw [geoTransform_ideal_eq_controlledTransform hN𝔫T hcoh𝔫T hπ, hd𝔫]
      have hσ𝔪 : (𝔪T.geoTransform C π).ideal = controlledTransform hπ (𝔫T.ideal.mul 𝓜T) d := by
        rw [geoTransform_ideal_eq_controlledTransform hNT hwfT.isCoherent hπ, hfacT, hd𝔪]
      have hle𝔫 := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hN𝔫T hcoh𝔫T hCn
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, 𝓜', h𝓜', ?_, ?_⟩
      · rw [geoTransformAlong_step]
        exact GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwfT hCm hπ
      · rw [geoTransformAlong_step]
        exact geoTransform_N_eq_univ hNT hπ
      · rw [geoTransformAlong_step]
        exact geoTransform_N_eq_univ hN𝔫T hπ
      · rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E, hET]
      · rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hN𝔫T hcoh𝔫T hπ]
        exact isCoherent_controlledTransform hπ hcoh𝔫T hle𝔫
      · rw [geoTransformAlong_step, hσ𝔫]
        exact hnz'
      · rw [geoTransformAlong_step, geoTransformAlong_step, hσ𝔫]
        intro y i hy
        exact hnd' y i hy
      · rw [geoTransformAlong_step, geoTransformAlong_step, hσ𝔪, hσ𝔫]
        exact hfac'
      · rw [geoTransformAlong_step]
        exact hP'

open Classical in
/-- **The transforms of the monomial and nonmonomial parts** (`hir:nonmonomial-transform`, `N = M`; Bierstone--Milman 2008
§5, Włodarczyk 2005 Step 2a).  Let `(X, X, E, 𝔞, d)` be well formed with `𝔞` nonzero at every point, `d, o ≥ 1`, and
`ord 𝓝(𝔞) ≤ o` on `cosupp(𝔞, d)`.  Along every multiple test blow-up `T` of the companion ideal of `(𝓝(𝔞), 𝓜(𝔞), o)`:
`T` is a multiple test blow-up of `(X, X, E, 𝔞, d)`, the transform is well formed with `N = M` and nonzero at every
point, its nonmonomial part is the transform of `(𝓝(𝔞), o)`, its monomial part is principal monomial at every point,
`𝔞_T = 𝓝(𝔞_T) 𝓜(𝔞_T)`, and `ord 𝓝(𝔞_T) ≤ o` on `cosupp(𝔞_T, d)`. -/
theorem nonmonomialPart_geoTransformAlong (hn : 0 < n) (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hN : 𝔪.N = univ) (h0 : ∀ y, IsNonzeroAt 𝔪.ideal y) {o : ℕ} (ho : 1 ≤ o) (hd : 1 ≤ 𝔪.d)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n univ (nonmonomialPart n 𝔪.ideal 𝔪.E) (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (companion 𝔪.E (nonmonomialPart n 𝔪.ideal 𝔪.E) (monomialPart n 𝔪.ideal 𝔪.E) o 𝔪.d) T) :
    IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsWellFormed ∧ (geoTransformAlong 𝔪 T).N = univ ∧
      (∀ z, IsNonzeroAt (geoTransformAlong 𝔪 T).ideal z) ∧
      nonmonomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E =
        (geoTransformAlong (⟨univ, 𝔪.E, nonmonomialPart n 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal ∧
      (∀ z, ∃ b, IsPrincipalAt (monomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E)
        (geoTransformAlong 𝔪 T).E z b) ∧
      (geoTransformAlong 𝔪 T).ideal =
        (nonmonomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E).mul
          (monomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E) ∧
      ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp,
        z ∉ cosupport n univ (nonmonomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E) (o + 1) := by
  have hE := h𝔪.isSNCDivisor
  have h𝔞 := h𝔪.isCoherent
  set 𝔟₀ := nonmonomialPart n 𝔪.ideal 𝔪.E with h𝔟₀def
  set 𝓜 := monomialPart n 𝔪.ideal 𝔪.E with h𝓜def
  have h𝔟₀ : 𝔟₀.IsCoherent := isCoherent_nonmonomialPart hn hE h𝔞 h0
  have h𝓜 : 𝓜.IsCoherent := isCoherent_monomialPart hn hE h𝔞 h0
  have hfac0 : 𝔪.ideal = 𝔟₀.mul 𝓜 := eq_mul_monomialPart hn hE h𝔞 h0
  have h𝔪eq : 𝔪 = ⟨univ, 𝔪.E, 𝔟₀.mul 𝓜, 𝔪.d⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN rfl hfac0 rfl
  have hP0 : ∀ x, ∃ b, IsPrincipalAt 𝓜 𝔪.E x b := fun x => ⟨_, isPrincipalAt_monomialPart hn hE h𝔞 h0 x⟩
  have hnd0 : ∀ y i, y ∈ 𝔪.E.get i → ∃ a, 𝔟₀.mem y a ∧ ¬ (vanishingIdeal (n := n) (𝔪.E.get i)).mem y a :=
    fun y i hyi => exists_mem_nonmonomialPart_notMem hn hE h𝔞 h0 hyi
  have hle : 𝔪.ideal.Le 𝔟₀ := by
    rw [hfac0]
    exact GermIdealPullbackCalculus.mul_le_left h𝔟₀
      (fun hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝓜 hg)
  have hnz0 : ∀ y, IsNonzeroAt 𝔟₀ y := fun y => by
    obtain ⟨g, hg, hgf⟩ := h0 y
    exact ⟨g, hle y g hg, hgf⟩
  have hwf : (⟨univ, 𝔪.E, 𝔟₀.mul 𝓜, 𝔪.d⟩ : MarkedIdeal n X).IsWellFormed := h𝔪eq ▸ h𝔪
  have hbound' : ∀ x ∈ cosupport n univ (𝔟₀.mul 𝓜) 𝔪.d, x ∉ cosupport n univ 𝔟₀ (o + 1) := by
    intro x hx
    refine hbound x ?_
    rw [MarkedIdeal.cosupp, hN, hfac0]
    exact hx
  have hkey := factor_along hn 𝔪.E h𝔟₀ h𝓜 hP0 hnd0 hnz0 ho hd hwf hbound' T hT
  obtain ⟨hTm, -, hbT, -⟩ := companion_reduction 𝔪.E h𝔟₀ h𝓜 ho hd hbound' T hT
  rw [← h𝔪eq] at hkey hTm hbT
  obtain ⟨hwfT, hNT, -, -, hcoh𝔫T, hnzT, hndT, 𝓜T, h𝓜T, hfacT, hPT⟩ := hkey
  obtain ⟨hnm, hm⟩ := parts_eq_of_factor hn hwfT.isSNCDivisor hcoh𝔫T h𝓜T hPT hndT
  rw [← hfacT] at hnm hm
  refine ⟨hTm, hwfT, hNT, fun z => ?_, hnm, fun z => ?_, ?_, fun z hz => ?_⟩
  · rw [hfacT]
    obtain ⟨b, hb⟩ := hPT z
    exact isNonzeroAt_mul_of_isPrincipalAt hcoh𝔫T h𝓜T hb (hnzT z)
  · rw [hm]; exact hPT z
  · rw [hnm, hm]; exact hfacT
  · rw [hnm]; exact hbT z hz

/-- **After a resolution of the companion ideal the order of the nonmonomial part has dropped** (`hir:nonmonomial-transform`,
last clause, `N = M`): `T` is a multiple test blow-up of `(X, X, E, 𝔞, d)` and `ord 𝓝(𝔞_T) < o` at every point of
`cosupp(𝔞_T, d)`. -/
theorem nonmonomialPart_geoTransformAlong_of_resolution (hn : 0 < n) (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hN : 𝔪.N = univ) (h0 : ∀ y, IsNonzeroAt 𝔪.ideal y) {o : ℕ} (ho : 1 ≤ o) (hd : 1 ≤ 𝔪.d)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n univ (nonmonomialPart n 𝔪.ideal 𝔪.E) (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoResolution (companion 𝔪.E (nonmonomialPart n 𝔪.ideal 𝔪.E) (monomialPart n 𝔪.ideal 𝔪.E) o 𝔪.d) T) :
    IsGeoTestTower 𝔪 T ∧ ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp,
      z ∉ cosupport n univ (nonmonomialPart n (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E) o := by
  have hE := h𝔪.isSNCDivisor
  have h𝔞 := h𝔪.isCoherent
  obtain ⟨hTm, -, -, -, hnm, -, -, -⟩ := nonmonomialPart_geoTransformAlong hn 𝔪 h𝔪 hN h0 ho hd hbound T hT.1
  set 𝔟₀ := nonmonomialPart n 𝔪.ideal 𝔪.E with h𝔟₀def
  set 𝓜 := monomialPart n 𝔪.ideal 𝔪.E with h𝓜def
  have h𝔟₀ : 𝔟₀.IsCoherent := isCoherent_nonmonomialPart hn hE h𝔞 h0
  have h𝓜 : 𝓜.IsCoherent := isCoherent_monomialPart hn hE h𝔞 h0
  have hfac0 : 𝔪.ideal = 𝔟₀.mul 𝓜 := eq_mul_monomialPart hn hE h𝔞 h0
  have h𝔪eq : 𝔪 = ⟨univ, 𝔪.E, 𝔟₀.mul 𝓜, 𝔪.d⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN rfl hfac0 rfl
  have hbound' : ∀ x ∈ cosupport n univ (𝔟₀.mul 𝓜) 𝔪.d, x ∉ cosupport n univ 𝔟₀ (o + 1) := by
    intro x hx
    refine hbound x ?_
    rw [MarkedIdeal.cosupp, hN, hfac0]
    exact hx
  obtain ⟨-, hres⟩ := companion_resolution 𝔪.E h𝔟₀ h𝓜 ho hd hbound' T hT
  rw [← h𝔪eq] at hres
  refine ⟨hTm, fun z hz hz' => hres z hz ?_⟩
  rw [hnm] at hz'
  have hnz0 : ∀ y, IsNonzeroAt 𝔟₀ y := fun y => by
    obtain ⟨g, hg, hgf⟩ := h0 y
    refine ⟨g, ?_, hgf⟩
    rw [hfac0] at hg
    exact GermIdealPullbackCalculus.mul_le_left h𝔟₀
      (fun hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝓜 hg) y g hg
  obtain ⟨-, -, hNo, -⟩ := factor_along hn 𝔪.E h𝔟₀ h𝓜 (fun x => ⟨_, isPrincipalAt_monomialPart hn hE h𝔞 h0 x⟩)
    (fun y i hyi => exists_mem_nonmonomialPart_notMem hn hE h𝔞 h0 hyi) hnz0 ho hd (h𝔪eq ▸ h𝔪) hbound' T hT.1
  rw [MarkedIdeal.cosupp, hNo, d_geoTransformAlong]
  exact hz'

end Tower

end

end Hironaka.NonmonomialTransformTower

import TranscendentalNakamaye.Pending.CodimOneCentreAlong
import TranscendentalNakamaye.Pending.TransformOffCentre
import TranscendentalNakamaye.Pending.AnalyticSubsetPreimage

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The codimension-one part of the support along a submanifold

Hironaka phase H2 (TN3), the H2 side of Step 1b of the maximal-order step inside a submanifold `N`
(`hir:maximal-order-step`, planned with `N` general: I-0977 C-0082): claimed on I-0977 C-0083.
Blueprint `bcalc:codim-one-local-along`, `bcalc:codim-one-part-along-def`,
`bcalc:codim-one-part-along`, `bcalc:codim-one-step-along` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor), first half ("all codimension one
components of `supp(𝓘, μ)` are smooth and isolated"; proof: a tangent direction has a smooth zero
set containing the support), read for the marked ideals `(M, N, E, 𝔞, μ)` of maximal order along `N`
of the induction; Włodarczyk 2009 (`wlodarczyk09-analytic-resolution`), Step 1ba.

Let `N` be a closed submanifold, `𝔞` coherent, `μ ≥ 1`, and `S = cosupp(𝔞|_N, μ)` (TN23's
`cosupport n N 𝔞 μ`).  Codimension is measured in `N`: at a point where `N` has dimension `k + 1`,
"codimension one" means dimension `k`.

* `isComplexAnalyticSubset_cosupport_along`: `S = N ∩ V(𝓓_N^{μ-1} 𝔞)` is analytic.
* `eventually_mem_iff_of_locDimGE_along`: if `A ⊆ S` is analytic, `N` has dimension `k + 1` at `x`
  and `dim_x A ≥ k`, then `A = N ∩ V(u)` near `x` for EVERY tangent direction `u` of `(𝔞|_N, μ)`
  along `N` on a neighbourhood of `x` (TN23's `IsTangentDirectionAlong`; filling lemma
  `CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE` with the hypersurface of maximal
  contact `N ∩ V(u)`, regular of dimension `k` by `IsTangentDirectionAlong.regularAtDim_contact`);
  `regularAtDim_of_locDimGE_along`: for `(𝔞|_N, μ)` of maximal order along `N`
  (`HomogenizedIdealAlong.IsMaximalOrderAlong`) such an `A` is regular of dimension `k` at `x`.
* The codimension-one part along `N`, `codimOnePartAlong N 𝔞 μ`: the points at which `S` is
  regular of dimension one less than `N`.  For `(𝔞|_N, μ)` of maximal order along `N`: it is the
  set of points of `S` of local dimension `≥ dim N - 1` (`mem_codimOnePartAlong_iff`), closed
  (`isClosed_codimOnePartAlong`), open in `S` (`exists_isOpen_cosupport_inter_eq_codimOnePartAlong`),
  a closed submanifold of codimension one in `N` at each of its points
  (`isClosedSubmanifold_codimOnePartAlong`, `regularAtDim_codimOnePartAlong`), equal to `N ∩ V(u)`
  near each of its points for every tangent direction `u` along `N`
  (`eventually_mem_codimOnePartAlong_iff_eq_zero`); `S \ R` is closed
  (`isClosed_cosupport_diff_codimOnePartAlong`) and its regular points have dimension `≤ dim N - 2`
  (`lt_of_regularAtDim_cosupport_diff_codimOnePartAlong`).
* Step 1ba inside `N`: blowing up `R`, the cosupport of the transform of `(M, N, E, 𝔞, μ)` misses
  the exceptional divisor (`cosupp_geoTransform_inter_preimage_codimOnePartAlong_eq_empty`, from
  `CodimOneCentreAlong`) and lies over `S \ R`
  (`cosupp_geoTransform_subset_preimage_diff_codimOnePartAlong`).

For `N = M` these are the statements of `Pending.CodimOneSupport` (`codimOnePart`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.CodimOneSupportAlong

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences GermIdealOrder
  RelativePrincipalizationSpan MarkedIdeals CodimOneSupport TangentDirectionAlong GiraudAlong
  HomogenizedIdealAlong AnalyticDimensionBasics RegularPointDimension DerivativeIdealAlongCoherent
  CodimOneCentreAlong TransformOffCentre DerivativeIdealAlong

noncomputable section

variable {n : ℕ}

section Support

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- **The support along `N` of a coherent ideal is analytic** (`N` a closed submanifold, `μ ≥ 1`):
`cosupp(𝔞|_N, μ) = N ∩ V(𝓓_N^{μ-1} 𝔞)`. -/
theorem isComplexAnalyticSubset_cosupport_along (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hμ : 1 ≤ μ) : IsComplexAnalyticSubset (n := n) (cosupport n N 𝔞 μ) := by
  obtain ⟨j, rfl⟩ : ∃ j, μ = j + 1 := ⟨μ - 1, by omega⟩
  rw [cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong
    (fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) hN.2 j]
  exact (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN).inter
    (isComplexAnalyticSubset_zeroLocus (isCoherent_iterDerivIdealAlong h𝔞 hN j))

/-- **Near a point of local dimension `dim N - 1`, an analytic part of the support along `N` is
the hypersurface of maximal contact of any tangent direction along `N`**: if `A ⊆ cosupp(𝔞|_N, μ)`
is analytic, `N` is regular of dimension `k + 1` at `x`, `dim_x A ≥ k` and `u` is a tangent
direction of `(𝔞|_N, μ)` along `N` on `U ∋ x`, then `A = N ∩ V(u)` near `x`. -/
theorem eventually_mem_iff_of_locDimGE_along (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hμ : 1 ≤ μ) {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAS : A ⊆ cosupport n N 𝔞 μ) {U : Set M} {u : M → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) {x : M} (hxU : x ∈ U) {k : ℕ}
    (hNk : RegularAtDim (n := n) N x (k + 1)) (hdim : LocDimGE (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ N ∧ u y = 0 := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hxA : x ∈ A := mem_of_locDimGE hA.isClosed hdim
  have hxS : x ∈ cosupport n N 𝔞 μ := hAS hxA
  have hux : u x = 0 := hu.cosupport_inter_subset hhol hμ ⟨hxS, hxU⟩
  obtain ⟨k', hNk', hH⟩ := hu.regularAtDim_contact hhol hN ⟨⟨hxS.1, hux⟩, hxU⟩
  have hkk : k' = k + 1 := eq_of_regularAtDim hNk' hNk
  rw [hkk, Nat.add_sub_cancel] at hH
  have hAH : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ N ∩ {y | u y = 0} ∩ U := by
    filter_upwards [hu.isOpen.mem_nhds hxU] with y hyU hyA
    exact ⟨⟨(hAS hyA).1, hu.cosupport_inter_subset hhol hμ ⟨hAS hyA, hyU⟩⟩, hyU⟩
  filter_upwards [eventually_mem_iff_of_regularAtDim_of_locDimGE hA hH hAH hdim,
    hu.isOpen.mem_nhds hxU] with y h hyU
  rw [h]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, hyU⟩⟩

/-- At a point of the support along `N` where `(𝔞|_N, μ)` has maximal order, a tangent direction
along `N` exists on a neighbourhood. -/
theorem exists_isTangentDirectionAlong_of_isMaximalOrderAlong (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (hmax : IsMaximalOrderAlong N 𝔞 μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) :
    ∃ (U : Set M) (u : M → ℂ), x ∈ U ∧ IsTangentDirectionAlong N 𝔞 μ U u :=
  exists_isTangentDirectionAlong h𝔞 hN hμ hx fun h => hmax x ⟨hx.1, h⟩

/-- **A point of local dimension `dim N - 1` of an analytic part of the support along `N` is a
regular point of dimension `dim N - 1`** (maximal order along `N`). -/
theorem regularAtDim_of_locDimGE_along (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hμ : 1 ≤ μ) (hmax : IsMaximalOrderAlong N 𝔞 μ) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hAS : A ⊆ cosupport n N 𝔞 μ) {x : M} {k : ℕ}
    (hNk : RegularAtDim (n := n) N x (k + 1)) (hdim : LocDimGE (n := n) A x k) :
    RegularAtDim (n := n) A x k := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hxA : x ∈ A := mem_of_locDimGE hA.isClosed hdim
  have hxS : x ∈ cosupport n N 𝔞 μ := hAS hxA
  obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirectionAlong_of_isMaximalOrderAlong h𝔞 hN hμ hmax hxS
  have hux : u x = 0 := hu.cosupport_inter_subset hhol hμ ⟨hxS, hxU⟩
  obtain ⟨k', hNk', hH⟩ := hu.regularAtDim_contact hhol hN ⟨⟨hxS.1, hux⟩, hxU⟩
  have hkk : k' = k + 1 := eq_of_regularAtDim hNk' hNk
  rw [hkk, Nat.add_sub_cancel] at hH
  refine regularAtDim_of_eventually_mem_iff ?_ hH
  filter_upwards [eventually_mem_iff_of_locDimGE_along h𝔞 hN hμ hA hAS hu hxU hNk hdim,
    hu.isOpen.mem_nhds hxU] with y h hyU
  rw [h]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, hyU⟩⟩

/-! ### The codimension-one part of the support along `N` -/

variable (N 𝔞 μ) in
/-- **The codimension-one part of the support along `N`**: the points at which
`cosupp(𝔞|_N, μ)` is regular of dimension one less than `N`. -/
def codimOnePartAlong : Set M :=
  {x | ∃ k, RegularAtDim (n := n) N x (k + 1) ∧ RegularAtDim (n := n) (cosupport n N 𝔞 μ) x k}

omit [IsComplexManifold n M] in
theorem codimOnePartAlong_subset : codimOnePartAlong N 𝔞 μ ⊆ cosupport n N 𝔞 μ :=
  fun _ ⟨_, _, h⟩ => h.2.1

/-- **The codimension-one part along `N` is the set of points of local dimension `dim N - 1`**
(maximal order along `N`). -/
theorem mem_codimOnePartAlong_iff (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrderAlong N 𝔞 μ) {x : M} :
    x ∈ codimOnePartAlong N 𝔞 μ ↔
      ∃ k, RegularAtDim (n := n) N x (k + 1) ∧ LocDimGE (n := n) (cosupport n N 𝔞 μ) x k :=
  ⟨fun ⟨k, hNk, hS⟩ => ⟨k, hNk, locDimGE_of_regularAtDim hS⟩, fun ⟨k, hNk, hS⟩ =>
    ⟨k, hNk, regularAtDim_of_locDimGE_along h𝔞 hN hμ hmax
      (isComplexAnalyticSubset_cosupport_along h𝔞 hN hμ) subset_rfl hNk hS⟩⟩

/-- **Near a point of the codimension-one part along `N`, the support is the codimension-one
part.** -/
theorem eventually_mem_codimOnePartAlong_iff {x : M} (hx : x ∈ codimOnePartAlong N 𝔞 μ) :
    ∀ᶠ y in 𝓝 x, y ∈ codimOnePartAlong N 𝔞 μ ↔ y ∈ cosupport n N 𝔞 μ := by
  obtain ⟨k, hNk, hS⟩ := hx
  filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hNk,
    RegularPatchNeighborhood.eventually_regularAtDim hS] with y hyN hyS
  exact ⟨fun h => codimOnePartAlong_subset h, fun h => ⟨k, hyN h.1, hyS h⟩⟩

/-- **The codimension-one part along `N` is closed** (Włodarczyk's "isolated"): a limit of points
of local dimension `dim N - 1` has local dimension `dim N - 1`, `N` having locally constant
dimension. -/
theorem isClosed_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrderAlong N 𝔞 μ) : IsClosed (codimOnePartAlong N 𝔞 μ) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hS : IsClosed (cosupport n N 𝔞 μ) := isClosed_cosupport_along h𝔞 hN μ
  have hxS : x ∈ cosupport n N 𝔞 μ :=
    hS.closure_subset (closure_mono codimOnePartAlong_subset hx)
  obtain ⟨kx, hkx⟩ := hN.2 x hxS.1
  have hev := RegularPatchNeighborhood.eventually_regularAtDim hkx
  -- a point of the codimension-one part near `x` fixes the dimension of `N` at `x`
  obtain ⟨y₀, hy₀ev, hy₀R⟩ := mem_closure_iff_nhds.mp hx _ hev
  obtain ⟨k₀, hNk₀, -⟩ := hy₀R
  have hk₀ : kx = k₀ + 1 := eq_of_regularAtDim (hy₀ev hNk₀.2.1) hNk₀
  refine (mem_codimOnePartAlong_iff h𝔞 hN hμ hmax).mpr ⟨k₀, hk₀ ▸ hkx, fun t ht => ?_⟩
  obtain ⟨y, ⟨hyt, hyev⟩, k, hNk, hSk⟩ := mem_closure_iff_nhds.mp hx _ (inter_mem ht hev)
  have hk : kx = k + 1 := eq_of_regularAtDim (hyev hSk.2.1.1) hNk
  exact ⟨y, hyt, k, by omega, hSk⟩

/-- **The codimension-one part along `N` is smooth, of codimension one in `N`.** -/
theorem regularAtDim_codimOnePartAlong {x : M} (hx : x ∈ codimOnePartAlong N 𝔞 μ) :
    ∃ k, RegularAtDim (n := n) N x (k + 1) ∧ RegularAtDim (n := n) (codimOnePartAlong N 𝔞 μ) x k := by
  obtain ⟨k, hNk, hS⟩ := hx
  exact ⟨k, hNk, regularAtDim_of_eventually_mem_iff
    (by filter_upwards [eventually_mem_codimOnePartAlong_iff ⟨k, hNk, hS⟩] with y h using h.symm) hS⟩

/-- **The codimension-one part along `N` is a closed submanifold** (a legitimate blowup centre). -/
theorem isClosedSubmanifold_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (hμ : 1 ≤ μ) (hmax : IsMaximalOrderAlong N 𝔞 μ) :
    IsClosedSubmanifold n (codimOnePartAlong N 𝔞 μ) :=
  ⟨isClosed_codimOnePartAlong h𝔞 hN hμ hmax, fun _ hx =>
    let ⟨k, _, h⟩ := regularAtDim_codimOnePartAlong hx
    ⟨k, h⟩⟩

/-- **The codimension-one part along `N` is open in the support.** -/
theorem exists_isOpen_cosupport_inter_eq_codimOnePartAlong :
    ∃ O : Set M, IsOpen O ∧ cosupport n N 𝔞 μ ∩ O = codimOnePartAlong N 𝔞 μ := by
  refine ⟨interior {y | y ∈ cosupport n N 𝔞 μ → y ∈ codimOnePartAlong N 𝔞 μ}, isOpen_interior,
    Subset.antisymm (fun y hy => interior_subset hy.2 hy.1) fun x hx => ⟨codimOnePartAlong_subset hx,
      mem_interior_iff_mem_nhds.mpr ?_⟩⟩
  filter_upwards [eventually_mem_codimOnePartAlong_iff hx] with y h using h.mpr

/-- **Near a point of the codimension-one part along `N`, the support is `N ∩ V(u)` for any tangent
direction `u` along `N`.** -/
theorem eventually_mem_codimOnePartAlong_iff_eq_zero (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {U : Set M} {u : M → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) {x : M} (hxU : x ∈ U)
    (hx : x ∈ codimOnePartAlong N 𝔞 μ) :
    ∀ᶠ y in 𝓝 x, y ∈ codimOnePartAlong N 𝔞 μ ↔ y ∈ N ∧ u y = 0 := by
  obtain ⟨k, hNk, hS⟩ := hx
  filter_upwards [eventually_mem_codimOnePartAlong_iff ⟨k, hNk, hS⟩,
    eventually_mem_iff_of_locDimGE_along h𝔞 hN hμ (isComplexAnalyticSubset_cosupport_along h𝔞 hN hμ)
      subset_rfl hu hxU hNk (locDimGE_of_regularAtDim hS)] with y h1 h2
  rw [h1, h2]

/-- **The rest of the support along `N` is closed.** -/
theorem isClosed_cosupport_diff_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) :
    IsClosed (cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ) := by
  obtain ⟨O, hO, hSO⟩ :=
    exists_isOpen_cosupport_inter_eq_codimOnePartAlong (N := N) (𝔞 := 𝔞) (μ := μ)
  have h : cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ = cosupport n N 𝔞 μ ∩ Oᶜ := by
    rw [← hSO]
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and]
    exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  rw [h]
  exact (isClosed_cosupport_along h𝔞 hN μ).inter hO.isClosed_compl

/-- **The rest of the support along `N` has codimension at least two in `N`**: at a point where
`N` has dimension `k + 1`, every regular point of `cosupp(𝔞|_N, μ) \ R` has dimension `< k`. -/
theorem lt_of_regularAtDim_cosupport_diff_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (hmax : IsMaximalOrderAlong N 𝔞 μ) {y : M}
    {j k : ℕ} (hNk : RegularAtDim (n := n) N y (k + 1))
    (hy : RegularAtDim (n := n) (cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ) y j) : j < k := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hyS : y ∈ cosupport n N 𝔞 μ := hy.2.1.1
  have hyR : y ∉ codimOnePartAlong N 𝔞 μ := hy.2.1.2
  have hSy : RegularAtDim (n := n) (cosupport n N 𝔞 μ) y j := by
    refine regularAtDim_of_inter_eq (isClosed_codimOnePartAlong h𝔞 hN hμ hmax).isOpen_compl hyR ?_ hy
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  obtain ⟨U, u, hyU, hu⟩ := exists_isTangentDirectionAlong_of_isMaximalOrderAlong h𝔞 hN hμ hmax hyS
  have hux : u y = 0 := hu.cosupport_inter_subset hhol hμ ⟨hyS, hyU⟩
  obtain ⟨k', hNk', hH⟩ := hu.regularAtDim_contact hhol hN ⟨⟨hyS.1, hux⟩, hyU⟩
  have hkk : k' = k + 1 := eq_of_regularAtDim hNk' hNk
  rw [hkk, Nat.add_sub_cancel] at hH
  have hSU : RegularAtDim (n := n) (cosupport n N 𝔞 μ ∩ U) y j :=
    regularAtDim_of_inter_eq hu.isOpen hyU (by rw [inter_assoc, inter_self]) hSy
  have hle : j ≤ k := BlowupStrictSubmanifold.le_of_regularAtDim_subset hSU hH
    fun z hz => ⟨⟨hz.1.1, hu.cosupport_inter_subset hhol hμ hz⟩, hz.2⟩
  refine lt_of_le_of_ne hle fun hj => hyR ⟨k, hNk, ?_⟩
  rw [← hj]
  exact hSy

/-! ### Weak tangent directions: controlled only on `N`

Along a tower the tangent direction `w` of the transform is controlled only on the strict transform
`N_T`: it agrees on `N_T` with combinations of germs of `𝓓_{N_T}^{μ-1}` and has multiplicity one
along `N_T` at its zeros on `N_T` (TN-CLASSICAL's `MaximalContactAlongTower.exists_contact_along`,
I-0977 C-0084).  The statements above hold for such `w`. -/

/-- A function agreeing on `N` near a point of the support along `N` with a combination of germs of
`𝓓_N^{μ-1} 𝔞` vanishes there. -/
theorem apply_eq_zero_of_isInSpanOnAt (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (hμ : 1 ≤ μ)
    {y : M} (hy : y ∈ cosupport n N 𝔞 μ) {w : M → ℂ}
    (hwD : IsInSpanOnAt (n := n) N ((iterDerivIdealAlong N 𝔞 (μ - 1)).mem y) y w) : w y = 0 := by
  obtain ⟨K, s, a, hs, -, hsum⟩ := hwD
  rw [hsum.self_of_nhds hy.1]
  exact Finset.sum_eq_zero fun i _ => by
    rw [TangentDirectionAlong.apply_eq_zero_of_mem_cosupport h𝔞 hμ hy (hs i), mul_zero]

/-- **The filling statement for a tangent direction controlled only on `N`**: if `A ⊆ cosupp(𝔞|_N, μ)`
is analytic, `N` is regular of dimension `k + 1` at `x`, `dim_x A ≥ k`, and `w` is holomorphic on an
open `O ∋ x`, agrees on `N` near each point of `O ∩ N` with a combination of germs of
`𝓓_N^{μ-1} 𝔞`, and has multiplicity one along `N` at its zeros on `N ∩ O`, then `A = N ∩ V(w)`
near `x`. -/
theorem eventually_mem_iff_of_locDimGE_along_of_isInSpanOnAt (h𝔞 : 𝔞.IsCoherent)
    (hμ : 1 ≤ μ) {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAS : A ⊆ cosupport n N 𝔞 μ) {O : Set M} {w : M → ℂ} (hO : IsOpen O)
    (hw : ∀ y ∈ O, HolomorphicAt n w y)
    (hwD : ∀ y ∈ O, y ∈ N → IsInSpanOnAt (n := n) N ((iterDerivIdealAlong N 𝔞 (μ - 1)).mem y) y w)
    (hw1 : ∀ y ∈ O, y ∈ N → w y = 0 →
      ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ), IsTangentField N e ξ y ∧ fieldDeriv e ξ w y ≠ 0)
    {x : M} (hxO : x ∈ O) {k : ℕ} (hNk : RegularAtDim (n := n) N x (k + 1))
    (hdim : LocDimGE (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ N ∧ w y = 0 := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hvan : ∀ y ∈ O, y ∈ cosupport n N 𝔞 μ → w y = 0 := fun y hyO hyS =>
    apply_eq_zero_of_isInSpanOnAt hhol hμ hyS (hwD y hyO hyS.1)
  have hxA : x ∈ A := mem_of_locDimGE hA.isClosed hdim
  have hxS : x ∈ cosupport n N 𝔞 μ := hAS hxA
  have hwx : w x = 0 := hvan x hxO hxS
  have hk' := hNk
  obtain ⟨hkn, -, Φ, hΦsrc, -, hflat⟩ := hk'
  obtain ⟨e, ξ, hξ, hne⟩ := hw1 x hxO hxS.1 hwx
  have hH := TangentDirectionAlong.regularAtDim_inter_zeroSet hΦsrc hflat hkn hO hw hxO hxS.1 hwx hξ hne
  rw [Nat.add_sub_cancel] at hH
  have hAH : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ N ∩ {y | w y = 0} ∩ O := by
    filter_upwards [hO.mem_nhds hxO] with y hyO hyA
    exact ⟨⟨(hAS hyA).1, hvan y hyO (hAS hyA)⟩, hyO⟩
  filter_upwards [eventually_mem_iff_of_regularAtDim_of_locDimGE hA hH hAH hdim, hO.mem_nhds hxO]
    with y h hyO
  rw [h]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, hyO⟩⟩

/-- **Near a point of the codimension-one part along `N`, the support is `N ∩ V(w)` for a tangent
direction `w` controlled only on `N`** (the hypotheses of
`eventually_mem_iff_of_locDimGE_along_of_isInSpanOnAt`). -/
theorem eventually_mem_codimOnePartAlong_iff_eq_zero_of_isInSpanOnAt (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {O : Set M} {w : M → ℂ} (hO : IsOpen O)
    (hw : ∀ y ∈ O, HolomorphicAt n w y)
    (hwD : ∀ y ∈ O, y ∈ N → IsInSpanOnAt (n := n) N ((iterDerivIdealAlong N 𝔞 (μ - 1)).mem y) y w)
    (hw1 : ∀ y ∈ O, y ∈ N → w y = 0 →
      ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ), IsTangentField N e ξ y ∧ fieldDeriv e ξ w y ≠ 0)
    {x : M} (hxO : x ∈ O) (hx : x ∈ codimOnePartAlong N 𝔞 μ) :
    ∀ᶠ y in 𝓝 x, y ∈ codimOnePartAlong N 𝔞 μ ↔ y ∈ N ∧ w y = 0 := by
  obtain ⟨k, hNk, hS⟩ := hx
  filter_upwards [eventually_mem_codimOnePartAlong_iff ⟨k, hNk, hS⟩,
    eventually_mem_iff_of_locDimGE_along_of_isInSpanOnAt h𝔞 hμ
      (isComplexAnalyticSubset_cosupport_along h𝔞 hN hμ) subset_rfl hO hw hwD hw1 hxO hNk
      (locDimGE_of_regularAtDim hS)] with y h1 h2
  rw [h1, h2]

end Support

/-! ### Step 1ba inside `N`: blowing up the codimension-one part -/

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}

open MarkedIdeal in
/-- **Step 1ba inside `N`**: for `(M, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent,
`d ≥ 1`, of maximal order along `N`, after the blowup along the codimension-one part of its support
along `N` the cosupport of the transform does not meet the exceptional divisor. -/
theorem cosupp_geoTransform_inter_preimage_codimOnePartAlong_eq_empty {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d)
    (hπ : IsBlowupAlong n (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π) :
    (𝔪.geoTransform (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π).cosupp ∩
      π ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d = ∅ :=
  cosupp_geoTransform_inter_preimage_eq_empty_along hπ hN h𝔞 hd hmax codimOnePartAlong_subset
    fun _ hx => let ⟨k, hNk, hR⟩ := regularAtDim_codimOnePartAlong hx
      ⟨k, hR, hNk⟩

open MarkedIdeal in
/-- **After the blowup of the codimension-one part along `N`, the support has codimension at least
two in `N`**: the cosupport of the transform lies over `cosupp(𝔞|_N, d) \ R`, a closed set whose
regular points have dimension `≤ dim N - 2`. -/
theorem cosupp_geoTransform_subset_preimage_diff_codimOnePartAlong {𝔪 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d)
    (hπ : IsBlowupAlong n (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π) :
    (𝔪.geoTransform (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π).cosupp ⊆
      π ⁻¹' (𝔪.cosupp \ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) := by
  intro z hz
  by_cases hzR : π z ∈ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d
  · have h := cosupp_geoTransform_inter_preimage_codimOnePartAlong_eq_empty hN h𝔞 hd hmax hπ
    exact (Set.eq_empty_iff_forall_notMem.mp h z ⟨hz, hzR⟩).elim
  · rw [← cosupp_geoTransform_diff_preimage 𝔪 hN.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) hπ]
    exact ⟨hz, hzR⟩

end Blowup

end

end TranscendentalNakamaye.Pending.CodimOneSupportAlong

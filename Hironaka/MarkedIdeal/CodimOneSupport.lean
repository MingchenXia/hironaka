import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Invariant.OrderTaylor
import Hironaka.MarkedIdeal.CodimOneCentre

set_option autoImplicit false

/-!
# The codimension-one part of the support of a marked ideal of maximal order

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor), first half:
"Let `(𝓘, μ)` be the marked ideal of maximal order whose support is of codimension `1`.  Then all
codimension one components of `supp(𝓘, μ)` are smooth and isolated."  Wlodarczyk's proof: a tangent
direction `u ∈ 𝓓^{μ-1}(𝓘)` has a smooth zero set containing the support.  Blueprint
`bcalc:analytic-fill`, `bcalc:irreducible-connected`, `bcalc:cosupport-analytic`,
`bcalc:codim-one-local`, `bcalc:codim-one-part-def`, `bcalc:codim-one-part`,
`bcalc:codim-one-components`, `bcalc:codim-one-step` (chapter `blowup-calculus.tex`); the transform
half is `bcalc:codim-one` (`Hironaka.CodimOneCentre`).

Analytic adaptation: "a codimension-one component inside the smooth hypersurface `V(u)` is open in
`V(u)`" is an identity-theorem statement, proved here in general:

* `eventually_mem_of_locDimGE` (filling): if an analytic set `A` lies near `x` inside a set `H`
  regular of dimension `k` at `x`, and `dim_x A ≥ k`, then `A = H` near `x`.  Proof: on a flattened
  ball `W` of `H` at `x`, `A ∩ W` has nonempty interior relative to `H ∩ W` (thin-dimension drop,
  `ThinDimensionDrop.lt_of_regularAtDim_of_thin`, applied in the open submanifold `W`), and then
  contains `H ∩ W` (identity theorem on the connected flattened ball,
  `RegularLocusComponent.FlatBall.inter_nbhd_subset_of_isOpen`).

For a coherent marked ideal `(𝔞, μ)` of maximal order (`μ ≥ 1`, orders on the whole manifold), with
support `S = cosupp(𝔞, μ)` (analytic, `isComplexAnalyticSubset_cosupport`):

* `eventually_mem_iff_of_locDimGE`: if `A ⊆ S` is analytic with `dim_x A ≥ n - 1`, then `A = V(u)`
  near `x` for EVERY tangent direction `u` on a neighbourhood of `x`;
* the codimension-one part `codimOnePart 𝔞 μ` (the regular points of `S` of dimension `n - 1`) is
  closed, open in `S`, a closed submanifold of pure dimension `n - 1`, equal to `V(u)` near each of
  its points; `S \ codimOnePart` is closed and every regular point of it has dimension `< n - 1`;
* `le:codim1`, first half: an irreducible component `V` of `S` with `dim V = n - 1` lies in the
  codimension-one part, is smooth (`regularAtDim_carrier`), equals `V(u)` near each of its points,
  is a connected component of `S` (`connectedComponentIn_eq_carrier`), and meets no other
  irreducible component of `S` (`disjoint_carrier`).
* Step 1ba: blowing up the codimension-one part, the cosupport of the controlled transform misses
  the exceptional divisor (`cosupport_controlledTransform_inter_preimage_codimOnePart_eq_empty`,
  from `CodimOneCentre`).

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.CodimOneSupport

open Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics RegularLocusComponent
  GermIdealOrder DerivativeIdeal MaximalContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Filling a regular set by an analytic set of the same local dimension -/

section Fill

/-- **Thin step of the filling lemma.**  On a flattened ball `W` of `H` at `x` (dimension `k`) on
which `A` lies inside `H`, if `dim_x A ≥ k` then `A` contains a nonempty relatively open part of
`H ∩ W`. -/
theorem exists_isOpen_inter_subset_of_locDimGE {A H : Set M} {x : M} {k : ℕ}
    (F : FlatBall (n := n) H x k) (hFA : ∀ y ∈ F.nbhd, y ∈ A → y ∈ H)
    (hdim : LocDimGE (n := n) A x k) :
    ∃ O : Set M, IsOpen O ∧ (O ∩ (H ∩ F.nbhd)).Nonempty ∧ O ∩ (H ∩ F.nbhd) ⊆ A := by
  set U : Opens M := ⟨F.nbhd, F.isOpen_nbhd⟩ with hUdef
  set T : Set U := (↑) ⁻¹' H with hTdef
  set T' : Set U := (↑) ⁻¹' A with hT'def
  have hTeq : T = (↑) ⁻¹' closure (H ∩ F.nbhd) := by
    ext p
    constructor
    · intro hp
      exact subset_closure ⟨hp, p.2⟩
    · intro hp
      exact F.nbhd_inter_closure_subset ⟨p.2, hp⟩
  have hTreg : ∀ p ∈ T, RegularAtDim (n := n) T p k := fun p hp =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (F.regularAtDim_of_mem hp p.2)
  have hTan : IsComplexAnalyticSubset (n := n) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hTeq ▸ isClosed_closure.preimage continuous_subtype_val, fun p hp => ⟨k, hTreg p hp⟩⟩
  have hTdim : DimLE (n := n) T k := fun p j hp =>
    (RegularPointDimension.eq_of_regularAtDim hp (hTreg p hp.2.1)).le
  have hT'T : T' ⊆ T := fun p hp => hFA p p.2 hp
  by_contra hcon
  have hthin : ∀ O : Set U, IsOpen O → O ∩ T ⊆ T' → O ∩ T = ∅ := by
    intro O hO hOT
    refine eq_empty_iff_forall_notMem.mpr fun p hp => hcon ⟨(↑) '' O,
      F.isOpen_nbhd.isOpenMap_subtype_val O hO, ⟨p, ⟨p, hp.1, rfl⟩, hp.2, p.2⟩, ?_⟩
    rintro _ ⟨⟨q, hqO, rfl⟩, hqH, -⟩
    exact hOT ⟨hqO, hqH⟩
  obtain ⟨y, hyW, j, hkj, hyj⟩ := hdim F.nbhd (F.isOpen_nbhd.mem_nhds F.mem_nbhd)
  have hj := ThinDimensionDrop.lt_of_regularAtDim_of_thin hTan hT'T hthin hTdim
    (y := ⟨y, hyW⟩) (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hyj)
  omega

/-- **Filling lemma.**  If the analytic set `A` lies near `x` inside a set `H` that is regular of
dimension `k` at `x`, and `dim_x A ≥ k`, then `H` lies in `A` near `x`. -/
theorem eventually_mem_of_locDimGE {A H : Set M} {x : M} {k : ℕ}
    (hA : IsComplexAnalyticSubset (n := n) A) (hH : RegularAtDim (n := n) H x k)
    (hAH : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ H) (hdim : LocDimGE (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ H → y ∈ A := by
  obtain ⟨P⟩ := hA x
  set e := (complexChartAt (n := n) x).val with he
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  obtain ⟨N₀, hN₀sub, hN₀o, hxN₀⟩ := mem_nhds_iff.mp hAH
  have hNo : IsOpen (P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' N₀)) :=
    P.isOpen_coordinateNeighborhood.inter (e.isOpen_inter_preimage_symm hN₀o)
  have hxN : e x ∈ P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' N₀) :=
    ⟨P.center_mem_coordinateNeighborhood, e.map_source hxs, by
      rw [mem_preimage, e.left_inv hxs]
      exact hxN₀⟩
  obtain ⟨F, hF⟩ := exists_flatBall hH hNo hxN
  have hnbhd : F.nbhd ⊆ N₀ := by
    intro y hy
    have h := (hF _ (F.mem_nbhd_iff.mp hy).2.2).2.2
    have h' : F.param (F.Φ.toFun ((complexChartAt (n := n) x).val y)) ∈ N₀ := h
    rwa [F.param_chart hy] at h'
  obtain ⟨O, hO, hne, hsub⟩ :=
    exists_isOpen_inter_subset_of_locDimGE F (fun y hy hyA => hN₀sub (hnbhd hy) hyA) hdim
  have hHA := F.inter_nbhd_subset_of_isOpen P (fun w hw => (hF w hw).1) hO hne hsub
  filter_upwards [F.isOpen_nbhd.mem_nhds F.mem_nbhd] with y hy hyH using hHA ⟨hyH, hy⟩

/-- The filling lemma as an equality of germs: `A = H` near `x`. -/
theorem eventually_mem_iff_of_regularAtDim_of_locDimGE {A H : Set M} {x : M} {k : ℕ}
    (hA : IsComplexAnalyticSubset (n := n) A) (hH : RegularAtDim (n := n) H x k)
    (hAH : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ H) (hdim : LocDimGE (n := n) A x k) :
    ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ H := by
  filter_upwards [hAH, eventually_mem_of_locDimGE hA hH hAH hdim] with y h1 h2
  exact ⟨h1, h2⟩

omit [IsComplexManifold n M] in
/-- Two sets agreeing near `x` have the same regular points of each dimension at `x`. -/
theorem regularAtDim_of_eventually_mem_iff {A B : Set M} {x : M} {k : ℕ}
    (hAB : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) (h : RegularAtDim (n := n) A x k) :
    RegularAtDim (n := n) B x k := by
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp hAB
  refine RegularPointDimension.regularAtDim_of_inter_eq hWo hxW ?_ h
  ext y
  exact ⟨fun hy => ⟨(hWsub hy.2).mp hy.1, hy.2⟩, fun hy => ⟨(hWsub hy.2).mpr hy.1, hy.2⟩⟩

omit [IsComplexManifold n M] in
/-- A point of local dimension `≥ q` of a closed set belongs to it. -/
theorem mem_of_locDimGE {A : Set M} (hA : IsClosed A) {x : M} {q : ℕ}
    (h : LocDimGE (n := n) A x q) : x ∈ A :=
  hA.closure_subset (mem_closure_iff_nhds.mpr fun t ht =>
    let ⟨y, hyt, _, _, hy⟩ := h t ht
    ⟨y, hyt, hy.2.1⟩)

/-- **An irreducible analytic subvariety has local dimension `dim V` at each of its points**: its
regular points are dense, and all of dimension `dim V` (pure dimensionality). -/
theorem locDimGE_carrier (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    (hx : x ∈ V.carrier) : LocDimGE (n := n) V.carrier x V.dim := by
  intro t ht
  obtain ⟨y, hyt, j, hy⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds V.analytic hx ht
  exact ⟨y, hyt, j, (PureDimension.eq_dim_of_regularAtDim V hy).ge, hy⟩

/-- **An analytically irreducible set is preconnected**: a separation by two closed sets would write
it as the union of two proper analytic subsets. -/
theorem isPreconnected_of_isComplexAnalyticallyIrreducible {A : Set M}
    (hA : IsComplexAnalyticallyIrreducible (n := n) A) : IsPreconnected A := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hAuv hdisj
  have hpiece : ∀ {s t : Set M}, IsClosed s → IsClosed t → A ⊆ s ∪ t → A ∩ (s ∩ t) = ∅ →
      IsComplexAnalyticSubset (n := n) (A ∩ s) := by
    intro s t hs ht hst hd
    refine AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq hA.analytic
      (hA.analytic.isClosed.inter hs) fun y hy => ⟨tᶜ, ht.isOpen_compl, fun hyt => ?_, ?_⟩
    · have : y ∈ A ∩ (s ∩ t) := ⟨hy.1, hy.2, hyt⟩
      rw [hd] at this
      exact this
    · ext z
      constructor
      · rintro ⟨hzA, hzt⟩
        exact ⟨⟨hzA, (hst hzA).resolve_right hzt⟩, hzt⟩
      · rintro ⟨⟨hzA, -⟩, hzt⟩
        exact ⟨hzA, hzt⟩
  have hB := hpiece hu hv hAuv hdisj
  have hC := hpiece hv hu (by rwa [union_comm]) (by rwa [inter_comm u v] at hdisj)
  have hBC : A = (A ∩ u) ∪ (A ∩ v) := by
    rw [← inter_union_distrib_left]
    exact (inter_eq_left.mpr hAuv).symm
  rcases hA.eq_left_or_eq_right hB hC inter_subset_left inter_subset_left hBC with h | h
  · exact Or.inl fun z hz => (h ▸ hz : z ∈ A ∩ u).2
  · exact Or.inr fun z hz => (h ▸ hz : z ∈ A ∩ v).2

end Fill

/-! ### The support of a marked ideal of maximal order -/

section MaximalOrder

variable {𝔞 : GermIdeal n M} {μ : ℕ}

/-- The zero locus of a coherent ideal is analytic: near each point it is the common zero set of
finitely many local generators.  (Same statement as
`StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus`, re-proved here because that module
lies in the import closure of `Hironaka.RelativePrincipalization`.) -/
theorem isComplexAnalyticSubset_zeroLocus {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) :
    IsComplexAnalyticSubset (n := n) 𝔟.zeroLocus := by
  intro x
  obtain ⟨U, hUo, hxU, N, g, hgd, hgiff⟩ := h𝔟 x
  set e := (complexChartAt (n := n) x).val with he
  have hghol : ∀ i, ∀ y ∈ U, HolomorphicAt n (g i) y := fun i y hy =>
    eventually_of_mem (hUo.mem_nhds hy) fun w hw => (hgd i w hw).mdifferentiableAt (hUo.mem_nhds hw)
  have hzero : ∀ y ∈ U, (y ∈ 𝔟.zeroLocus ↔ ∀ i, g i y = 0) := by
    intro y hy
    constructor
    · intro hyZ i
      exact hyZ (g i) ((hgiff y hy (g i)).mpr (isInSpanAt_of_eq_mul
        ⟨i, rfl⟩ (hghol i y hy) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)))
    · intro h0 f hf
      obtain ⟨-, K, s, a, hs, -, hsum⟩ := (hgiff y hy f).mp hf
      rw [hsum.self_of_nhds]
      refine Finset.sum_eq_zero fun k _ => ?_
      obtain ⟨j, hj⟩ := hs k
      rw [← hj, h0 j, mul_zero]
  exact ⟨{
    generatorCount := N
    generator := fun i z => g i (e.symm z)
    coordinateNeighborhood := e.target ∩ e.symm ⁻¹' U
    isOpen_coordinateNeighborhood := e.isOpen_inter_preimage_symm hUo
    center_mem_coordinateNeighborhood := ⟨e.map_source (mem_complexChartAt_source x), by
      rw [mem_preimage, e.left_inv (mem_complexChartAt_source x)]
      exact hxU⟩
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := fun i => differentiableOn_comp_chartSymm x (hgd i)
    zeroLocus := fun {y} hys hyN => by
      have hyy : e.symm (e y) = y := e.left_inv hys
      have hyU : y ∈ U := by
        have := hyN.2
        rwa [mem_preimage, hyy] at this
      show y ∈ 𝔟.zeroLocus ↔ ∀ i, g i (e.symm (e y)) = 0
      rw [hyy]
      exact hzero y hyU }⟩

/-- **The support of a coherent marked ideal is analytic** (`μ ≥ 1`):
`cosupp(𝔞, μ) = V(𝓓^{μ-1} 𝔞)`. -/
theorem isComplexAnalyticSubset_cosupport (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) :
    IsComplexAnalyticSubset (n := n) (cosupport n univ 𝔞 μ) := by
  obtain ⟨j, rfl⟩ : ∃ j, μ = j + 1 := ⟨μ - 1, by omega⟩
  rw [OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal
    (fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) j]
  exact isComplexAnalyticSubset_zeroLocus (isCoherent_iterDerivIdeal h𝔞 j)

/-- **Near a point of local dimension `n - 1`, an analytic part of the support is the zero set of
any tangent direction** (Wlodarczyk `le:codim1`, analytic form of "open in `V(u)`"): if
`A ⊆ cosupp(𝔞, μ)` is analytic with `dim_x A ≥ n - 1` and `u` is a tangent direction of `(𝔞, μ)` on
`U ∋ x`, then `A = V(u)` near `x`. -/
theorem eventually_mem_iff_of_locDimGE (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hAS : A ⊆ cosupport n univ 𝔞 μ) {U : Set M}
    {u : M → ℂ} (hu : IsTangentDirection 𝔞 μ U u) {x : M} (hxU : x ∈ U)
    (hdim : LocDimGE (n := n) A x (n - 1)) : ∀ᶠ y in 𝓝 x, y ∈ A ↔ u y = 0 := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hxA : x ∈ A := mem_of_locDimGE hA.isClosed hdim
  have hux : u x = 0 := hu.cosupport_inter_subset hhol hμ ⟨hAS hxA, hxU⟩
  have hH : RegularAtDim (n := n) ({y | u y = 0} ∩ U) x (n - 1) :=
    LocalGiraudTransform.regularAtDim_zeroSet hu.isOpen
      (fun y hy => holomorphicAt_of_mem_iterDerivIdeal hhol (μ - 1) y u (hu.mem y hy))
      hu.multiplicity_one hxU hux
  have hAH : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ {y | u y = 0} ∩ U := by
    filter_upwards [hu.isOpen.mem_nhds hxU] with y hyU hyA
    exact ⟨hu.cosupport_inter_subset hhol hμ ⟨hAS hyA, hyU⟩, hyU⟩
  filter_upwards [eventually_mem_iff_of_regularAtDim_of_locDimGE hA hH hAH hdim,
    hu.isOpen.mem_nhds hxU]
    with y h hyU
  rw [h]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, hyU⟩⟩

/-- **A point of local dimension `n - 1` of an analytic part of the support is a regular point of
dimension `n - 1`** (the tangent direction exists near every point of the support). -/
theorem regularAtDim_of_locDimGE (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hAS : A ⊆ cosupport n univ 𝔞 μ)
    {x : M} (hdim : LocDimGE (n := n) A x (n - 1)) : RegularAtDim (n := n) A x (n - 1) := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hxA : x ∈ A := mem_of_locDimGE hA.isClosed hdim
  obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirection h𝔞 hhol hμ hmax (hAS hxA)
  have hux : u x = 0 := hu.cosupport_inter_subset hhol hμ ⟨hAS hxA, hxU⟩
  have hH : RegularAtDim (n := n) ({y | u y = 0} ∩ U) x (n - 1) :=
    LocalGiraudTransform.regularAtDim_zeroSet hu.isOpen
      (fun y hy => holomorphicAt_of_mem_iterDerivIdeal hhol (μ - 1) y u (hu.mem y hy))
      hu.multiplicity_one hxU hux
  refine regularAtDim_of_eventually_mem_iff ?_ hH
  filter_upwards [eventually_mem_iff_of_locDimGE h𝔞 hμ hA hAS hu hxU hdim,
    hu.isOpen.mem_nhds hxU] with y h hyU
  rw [h]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, hyU⟩⟩

/-! ### The codimension-one part of the support -/

variable (𝔞 μ) in
/-- **The codimension-one part of the support**: the points at which `cosupp(𝔞, μ)` is regular of
dimension `n - 1`. -/
def codimOnePart : Set M :=
  regularLocus (n := n) (cosupport n univ 𝔞 μ) (n - 1)

omit [IsComplexManifold n M] in
theorem codimOnePart_subset : codimOnePart 𝔞 μ ⊆ cosupport n univ 𝔞 μ :=
  regularLocus_subset _ _

/-- **The codimension-one part is the set of points of local dimension `n - 1`.** -/
theorem mem_codimOnePart_iff (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    {x : M} : x ∈ codimOnePart 𝔞 μ ↔ LocDimGE (n := n) (cosupport n univ 𝔞 μ) x (n - 1) :=
  ⟨fun h => locDimGE_of_regularAtDim h, fun h =>
    regularAtDim_of_locDimGE h𝔞 hμ hmax (isComplexAnalyticSubset_cosupport h𝔞 hμ) subset_rfl h⟩

/-- Near a point of the codimension-one part, the support is the codimension-one part. -/
theorem eventually_mem_codimOnePart_iff {x : M} (hx : x ∈ codimOnePart 𝔞 μ) :
    ∀ᶠ y in 𝓝 x, y ∈ codimOnePart 𝔞 μ ↔ y ∈ cosupport n univ 𝔞 μ := by
  filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hx] with y hy
  exact ⟨fun h => h.2.1, hy⟩

/-- **The codimension-one part is closed** (Wlodarczyk's "isolated"): a limit of points of local
dimension `n - 1` has local dimension `n - 1`. -/
theorem isClosed_codimOnePart (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ) :
    IsClosed (codimOnePart 𝔞 μ) := by
  refine isClosed_of_closure_subset fun x hx => (mem_codimOnePart_iff h𝔞 hμ hmax).mpr ?_
  intro t ht
  obtain ⟨y, hyt, hyR⟩ := mem_closure_iff_nhds.mp hx t ht
  exact ⟨y, hyt, n - 1, le_rfl, hyR⟩

/-- **The codimension-one part is smooth of pure dimension `n - 1`.** -/
theorem regularAtDim_codimOnePart {x : M} (hx : x ∈ codimOnePart 𝔞 μ) :
    RegularAtDim (n := n) (codimOnePart 𝔞 μ) x (n - 1) :=
  regularAtDim_of_eventually_mem_iff
    (by filter_upwards [eventually_mem_codimOnePart_iff hx] with y h using h.symm) hx

/-- **The codimension-one part is a closed submanifold** (a legitimate blowup centre). -/
theorem isClosedSubmanifold_codimOnePart (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) :
    BlowupSequences.IsClosedSubmanifold n (codimOnePart 𝔞 μ) :=
  ⟨isClosed_codimOnePart h𝔞 hμ hmax, fun _ hx => ⟨n - 1, regularAtDim_codimOnePart hx⟩⟩

/-- **The codimension-one part is open in the support.** -/
theorem exists_isOpen_cosupport_inter_eq_codimOnePart :
    ∃ O : Set M, IsOpen O ∧ cosupport n univ 𝔞 μ ∩ O = codimOnePart 𝔞 μ := by
  refine ⟨interior {y | y ∈ cosupport n univ 𝔞 μ → y ∈ codimOnePart 𝔞 μ}, isOpen_interior,
    Subset.antisymm (fun y hy => interior_subset hy.2 hy.1) fun x hx => ⟨codimOnePart_subset hx,
      mem_interior_iff_mem_nhds.mpr ?_⟩⟩
  filter_upwards [eventually_mem_codimOnePart_iff hx] with y h using h.mpr

/-- **Near a point of the codimension-one part, the support is the zero set of any tangent
direction.** -/
theorem eventually_mem_codimOnePart_iff_eq_zero (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {U : Set M}
    {u : M → ℂ} (hu : IsTangentDirection 𝔞 μ U u) {x : M} (hxU : x ∈ U)
    (hx : x ∈ codimOnePart 𝔞 μ) : ∀ᶠ y in 𝓝 x, y ∈ codimOnePart 𝔞 μ ↔ u y = 0 := by
  filter_upwards [eventually_mem_codimOnePart_iff hx,
    eventually_mem_iff_of_locDimGE h𝔞 hμ (isComplexAnalyticSubset_cosupport h𝔞 hμ) subset_rfl hu
      hxU (locDimGE_of_regularAtDim hx)] with y h1 h2
  rw [h1, h2]

/-- **The rest of the support is closed.** -/
theorem isClosed_cosupport_diff_codimOnePart (h𝔞 : 𝔞.IsCoherent) :
    IsClosed (cosupport n univ 𝔞 μ \ codimOnePart 𝔞 μ) := by
  obtain ⟨O, hO, hSO⟩ := exists_isOpen_cosupport_inter_eq_codimOnePart (𝔞 := 𝔞) (μ := μ)
  have h : cosupport n univ 𝔞 μ \ codimOnePart 𝔞 μ = cosupport n univ 𝔞 μ ∩ Oᶜ := by
    rw [← hSO]
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and]
    exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  rw [h]
  exact (OrderTaylor.isClosed_cosupport h𝔞 μ).inter hO.isClosed_compl

/-- **The rest of the support has codimension at least two**: every regular point of
`cosupp(𝔞, μ) \ codimOnePart` has dimension `< n - 1`. -/
theorem lt_of_regularAtDim_cosupport_diff_codimOnePart (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) {y : M} {j : ℕ}
    (hy : RegularAtDim (n := n) (cosupport n univ 𝔞 μ \ codimOnePart 𝔞 μ) y j) : j < n - 1 := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hyS : y ∈ cosupport n univ 𝔞 μ := hy.2.1.1
  have hyR : y ∉ codimOnePart 𝔞 μ := hy.2.1.2
  have hSy : RegularAtDim (n := n) (cosupport n univ 𝔞 μ) y j := by
    refine RegularPointDimension.regularAtDim_of_inter_eq
      (isClosed_codimOnePart h𝔞 hμ hmax).isOpen_compl hyR ?_ hy
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  obtain ⟨U, u, hyU, hu⟩ := exists_isTangentDirection h𝔞 hhol hμ hmax hyS
  have hux : u y = 0 := hu.cosupport_inter_subset hhol hμ ⟨hyS, hyU⟩
  have hH : RegularAtDim (n := n) ({z | u z = 0} ∩ U) y (n - 1) :=
    LocalGiraudTransform.regularAtDim_zeroSet hu.isOpen
      (fun z hz => holomorphicAt_of_mem_iterDerivIdeal hhol (μ - 1) z u (hu.mem z hz))
      hu.multiplicity_one hyU hux
  have hSU : RegularAtDim (n := n) (cosupport n univ 𝔞 μ ∩ U) y j :=
    RegularPointDimension.regularAtDim_of_inter_eq hu.isOpen hyU (by rw [inter_assoc, inter_self])
      hSy
  have hle : j ≤ n - 1 := BlowupStrictSubmanifold.le_of_regularAtDim_subset hSU hH
    fun z hz => ⟨hu.cosupport_inter_subset hhol hμ hz, hz.2⟩
  refine lt_of_le_of_ne hle fun hj => hyR ?_
  rw [hj] at hSy
  exact hSy

/-- `dim (cosupp(𝔞, μ) \ codimOnePart) ≤ n - 2`. -/
theorem dimLE_cosupport_diff_codimOnePart (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) :
    DimLE (n := n) (cosupport n univ 𝔞 μ \ codimOnePart 𝔞 μ) (n - 2) := fun _ _ hy => by
  have := lt_of_regularAtDim_cosupport_diff_codimOnePart h𝔞 hμ hmax hy
  omega

/-! ### Codimension-one components (`le:codim1`, first half) -/

section Components

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- An analytic subvariety of dimension `n - 1` inside the support lies in the codimension-one
part. -/
theorem carrier_subset_codimOnePart (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ)
    (hdimV : V.dim = n - 1) : V.carrier ⊆ codimOnePart 𝔞 μ := fun _ hx =>
  (mem_codimOnePart_iff h𝔞 hμ hmax).mpr (DimensionMonotone.LocDimGE.mono
    (isComplexAnalyticSubset_cosupport h𝔞 hμ) hVS (hdimV ▸ locDimGE_carrier V hx))

/-- **A codimension-one component is open in `V(u)`** for every tangent direction `u` near each of
its points: `V = V(u)` near `x`. -/
theorem eventually_mem_carrier_iff (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ) (hdimV : V.dim = n - 1) {U : Set M} {u : M → ℂ}
    (hu : IsTangentDirection 𝔞 μ U u) {x : M} (hxU : x ∈ U) (hx : x ∈ V.carrier) :
    ∀ᶠ y in 𝓝 x, y ∈ V.carrier ↔ u y = 0 :=
  eventually_mem_iff_of_locDimGE h𝔞 hμ V.analytic hVS hu hxU (hdimV ▸ locDimGE_carrier V hx)

/-- **A codimension-one component is smooth.** -/
theorem regularAtDim_carrier (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ) (hdimV : V.dim = n - 1) {x : M}
    (hx : x ∈ V.carrier) : RegularAtDim (n := n) V.carrier x (n - 1) :=
  regularAtDim_of_locDimGE h𝔞 hμ hmax V.analytic hVS (hdimV ▸ locDimGE_carrier V hx)

/-- **Near each of its points a codimension-one component is the whole support.** -/
theorem eventually_mem_carrier_iff_mem_cosupport (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ)
    (hdimV : V.dim = n - 1) {x : M} (hx : x ∈ V.carrier) :
    ∀ᶠ y in 𝓝 x, y ∈ V.carrier ↔ y ∈ cosupport n univ 𝔞 μ := by
  have hR : ∀ᶠ y in 𝓝 x, y ∈ codimOnePart 𝔞 μ ↔ y ∈ cosupport n univ 𝔞 μ :=
    eventually_mem_codimOnePart_iff (carrier_subset_codimOnePart h𝔞 hμ hmax hVS hdimV hx)
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirection h𝔞 hhol hμ hmax (hVS hx)
  filter_upwards [eventually_mem_carrier_iff h𝔞 hμ hVS hdimV hu hxU hx,
    hu.isOpen.mem_nhds hxU] with y h hyU
  exact ⟨fun hy => hVS hy, fun hy => h.mpr (hu.cosupport_inter_subset hhol hμ ⟨hy, hyU⟩)⟩

/-- **A codimension-one component is open in the support.** -/
theorem exists_isOpen_cosupport_inter_eq_carrier (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ)
    (hdimV : V.dim = n - 1) :
    ∃ O : Set M, IsOpen O ∧ cosupport n univ 𝔞 μ ∩ O = V.carrier := by
  refine ⟨interior {y | y ∈ cosupport n univ 𝔞 μ → y ∈ V.carrier}, isOpen_interior,
    Subset.antisymm (fun y hy => interior_subset hy.2 hy.1) fun x hx => ⟨hVS hx,
      mem_interior_iff_mem_nhds.mpr ?_⟩⟩
  filter_upwards [eventually_mem_carrier_iff_mem_cosupport h𝔞 hμ hmax hVS hdimV hx] with y h
    using h.mpr

/-- **A codimension-one component is a connected component of the support** (Wlodarczyk's
"isolated"). -/
theorem connectedComponentIn_eq_carrier (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ) (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ)
    (hdimV : V.dim = n - 1) {x : M} (hx : x ∈ V.carrier) :
    connectedComponentIn (cosupport n univ 𝔞 μ) x = V.carrier := by
  obtain ⟨O, hO, hSO⟩ := exists_isOpen_cosupport_inter_eq_carrier h𝔞 hμ hmax hVS hdimV
  refine Subset.antisymm ?_ ((isPreconnected_of_isComplexAnalyticallyIrreducible
    V.irreducible_carrier).subset_connectedComponentIn hx hVS)
  have hVO : V.carrier ⊆ O := fun y hy => (hSO.symm ▸ hy : y ∈ cosupport n univ 𝔞 μ ∩ O).2
  have hcov : connectedComponentIn (cosupport n univ 𝔞 μ) x ⊆ O ∪ V.carrierᶜ := by
    intro y hy
    by_cases hyV : y ∈ V.carrier
    · exact Or.inl (hVO hyV)
    · exact Or.inr hyV
  have hdisj : connectedComponentIn (cosupport n univ 𝔞 μ) x ∩ (O ∩ V.carrierᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun y hy => hy.2.2 ?_
    rw [← hSO]
    exact ⟨connectedComponentIn_subset _ _ hy.1, hy.2.1⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn O
      V.carrierᶜ hO V.isClosed_carrier.isOpen_compl hcov hdisj with h | h
  · intro y hy
    rw [← hSO]
    exact ⟨connectedComponentIn_subset _ _ hy, h hy⟩
  · exact absurd hx (h (mem_connectedComponentIn (hVS hx)))

/-- **A codimension-one component meets no other irreducible component of the support.** -/
theorem disjoint_carrier (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ) (hdimV : V.dim = n - 1)
    {V' : ClosedIrreducibleAnalyticSubvariety n M}
    (hV' : Hironaka.IsIrreducibleComponent V' (cosupport n univ 𝔞 μ))
    (hne : V'.carrier ≠ V.carrier) : Disjoint V.carrier V'.carrier := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxV, hxV'⟩
  have hsub : V'.carrier ⊆ V.carrier := by
    rw [← connectedComponentIn_eq_carrier h𝔞 hμ hmax hVS hdimV hxV]
    exact (isPreconnected_of_isComplexAnalyticallyIrreducible V'.irreducible_carrier
      ).subset_connectedComponentIn hxV' hV'.1
  exact hne (hV'.2 V hsub hVS).symm

/-- **Wlodarczyk `le:codim1`, first half** (Villamayor): every irreducible component `V` of the
support of a coherent marked ideal of maximal order with `dim V = n - 1` is smooth, is open in
`V(u)` for every tangent direction `u` near each of its points, is open in the support, and meets no
other irreducible component of the support. -/
theorem isIrreducibleComponent_codim_one (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (hmax : IsMaximalOrder 𝔞 μ)
    (hV : Hironaka.IsIrreducibleComponent V (cosupport n univ 𝔞 μ))
    (hdimV : V.dim = n - 1) :
    (∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x (n - 1)) ∧
      (∀ x ∈ V.carrier, ∀ (U : Set M) (u : M → ℂ), IsTangentDirection 𝔞 μ U u → x ∈ U →
        ∀ᶠ y in 𝓝 x, y ∈ V.carrier ↔ u y = 0) ∧
      (∃ O : Set M, IsOpen O ∧ cosupport n univ 𝔞 μ ∩ O = V.carrier) ∧
      ∀ V' : ClosedIrreducibleAnalyticSubvariety n M,
        Hironaka.IsIrreducibleComponent V' (cosupport n univ 𝔞 μ) →
          V'.carrier ≠ V.carrier → Disjoint V.carrier V'.carrier :=
  ⟨fun _ hx => regularAtDim_carrier h𝔞 hμ hmax hV.1 hdimV hx,
    fun _ hx _ _ hu hxU => eventually_mem_carrier_iff h𝔞 hμ hV.1 hdimV hu hxU hx,
    exists_isOpen_cosupport_inter_eq_carrier h𝔞 hμ hmax hV.1 hdimV,
    fun _ hV' hne => disjoint_carrier h𝔞 hμ hmax hV.1 hdimV hV' hne⟩

end Components

end MaximalOrder

/-! ### Step 1ba: blowing up the codimension-one part -/

section Blowup

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → X}

/-- **Step 1ba** (Wlodarczyk `le:codim1`, both halves): blowing up the codimension-one part of the
support of a coherent marked ideal of maximal order, the cosupport of the controlled transform does
not meet the exceptional divisor. -/
theorem cosupport_controlledTransform_inter_preimage_codimOnePart_eq_empty {𝔞 : GermIdeal n X}
    {μ : ℕ} (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    (hπ : BlowupSequences.IsBlowupAlong n (codimOnePart 𝔞 μ) π) :
    cosupport n univ (BlowupControlledTransform.controlledTransform hπ 𝔞 μ) μ ∩
      π ⁻¹' codimOnePart 𝔞 μ = ∅ :=
  CodimOneCentre.cosupport_controlledTransform_inter_preimage_eq_empty hπ h𝔞 hμ hmax
    codimOnePart_subset fun _ hx => regularAtDim_codimOnePart hx

/-- **Step 1ba for marked ideals with `N = M`**: the corrected transform along the codimension-one
part has cosupport off the new exceptional divisor. -/
theorem cosupp_geoTransform_inter_preimage_codimOnePart_eq_empty {𝔪 : MarkedIdeals.MarkedIdeal n X}
    (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrder 𝔪.ideal 𝔪.d)
    (hπ : BlowupSequences.IsBlowupAlong n (codimOnePart 𝔪.ideal 𝔪.d) π) :
    (𝔪.geoTransform (codimOnePart 𝔪.ideal 𝔪.d) π).cosupp ∩ π ⁻¹' codimOnePart 𝔪.ideal 𝔪.d = ∅ :=
  CodimOneCentre.cosupp_geoTransform_inter_preimage_eq_empty hN h𝔞 hd hmax hπ
    (fun _ hx => by
      rw [MarkedIdeals.MarkedIdeal.cosupp, hN]
      exact codimOnePart_subset hx)
    fun _ hx => regularAtDim_codimOnePart hx

/-- **Wlodarczyk `le:codim1`, both halves, for one component**: blowing up a codimension-one
irreducible analytic subvariety `V` of the support of a coherent marked ideal of maximal order (for
instance a codimension-one component), the cosupport of the controlled transform does not meet the
exceptional divisor `π⁻¹ V`. -/
theorem cosupport_controlledTransform_inter_preimage_carrier_eq_empty {𝔞 : GermIdeal n X} {μ : ℕ}
    (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) (hmax : IsMaximalOrder 𝔞 μ)
    {V : ClosedIrreducibleAnalyticSubvariety n X} (hVS : V.carrier ⊆ cosupport n univ 𝔞 μ)
    (hdimV : V.dim = n - 1) (hπ : BlowupSequences.IsBlowupAlong n V.carrier π) :
    cosupport n univ (BlowupControlledTransform.controlledTransform hπ 𝔞 μ) μ ∩ π ⁻¹' V.carrier =
      ∅ :=
  CodimOneCentre.cosupport_controlledTransform_inter_preimage_eq_empty hπ h𝔞 hμ hmax hVS
    fun _ hx => regularAtDim_carrier h𝔞 hμ hmax hVS hdimV hx

end Blowup

end

end Hironaka.CodimOneSupport

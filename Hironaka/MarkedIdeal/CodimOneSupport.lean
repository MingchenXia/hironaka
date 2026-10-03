/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.MarkedIdeal.LocalGiraudTransform
import Hironaka.Invariant.OrderTaylor
import Hironaka.MarkedIdeal.CodimOneCentre
import Hironaka.Manifold.ChartDifferentiable
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticDimensionBasics
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.RegularPointDimension
set_option autoImplicit false

/-!
# The codimension-one part of the support of a marked ideal of maximal order

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.7, Lemma `le:codim1` (Villamayor), first half: "Let `(𝓘, μ)`
be the marked ideal of maximal order whose support is of codimension `1`. Then all codimension one components of
`supp(𝓘, μ)` are smooth and isolated." Wlodarczyk's proof: a tangent direction `u ∈ 𝓓^{μ-1}(𝓘)` has a smooth zero
set containing the support.

Analytic adaptation: "a codimension-one component inside the smooth hypersurface `V(u)` is open in
`V(u)`" is an identity-theorem statement, proved here in general:

* `eventually_mem_of_locDimGE` (filling): if an analytic set `A` lies near `x` inside a set `H`
  regular of dimension `k` at `x`, and `dim_x A ≥ k`, then `A = H` near `x`.  Proof: on a flattened
  ball `W` of `H` at `x`, `A ∩ W` has nonempty interior relative to `H ∩ W` (thin-dimension drop,
  `ThinDimensionDrop.lt_of_regularAtDim_of_thin`, applied in the open submanifold `W`), and then
  contains `H ∩ W` (identity theorem on the connected flattened ball,
  `RegularLocusComponent.FlatBall.inter_nbhd_subset_of_isOpen`).

For a coherent marked ideal `(𝔞, μ)` of maximal order (`μ ≥ 1`, orders on the whole manifold), with support `S =
cosupp(𝔞, μ)` (analytic):

* `le:codim1`, first half: an irreducible component `V` of `S` with `dim V = n - 1` lies in the codimension-one
  part, is smooth, equals `V(u)` near each of its points, is a connected component of `S`, and meets no other
  irreducible component of `S`.
* Step 1ba: blowing up the codimension-one part, the cosupport of the controlled transform misses the exceptional
  divisor (from `CodimOneCentre`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.CodimOneSupport

open Hironaka.HolomorphicIdealSheaves AnalyticDimensionBasics RegularLocusComponent GermIdealOrder DerivativeIdeal

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

end Fill

/-! ### The support of a marked ideal of maximal order -/

section MaximalOrder

variable {𝔞 : GermIdeal n M} {μ : ℕ}

/-- The zero locus of a coherent ideal is analytic: near each point it is the common zero set of finitely many local
generators. -/
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

end MaximalOrder

end

end Hironaka.CodimOneSupport

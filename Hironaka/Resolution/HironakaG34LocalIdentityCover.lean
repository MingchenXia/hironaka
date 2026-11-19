import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.ThinDimensionDrop

/-! # Germs of complex submanifolds inside analytic sets: finite covers and filling (local identity theorems)

Lane G34 (run 0080, round 6).  Blueprint: `hironaka-g34-resume-local-identity-cover.tex`.
Route note: `work/hironaka-resume-20261111/G34/DIM3-ROUTE.md` §1 (a), (c).

Two reusable consequences of the held identity theorem on a flattened ball
(`RegularLocusComponent.FlatBall.inter_nbhd_subset_of_isOpen`):

* `exists_open_subset_of_finite_closed_cover` (topology): if a nonempty relatively open part of `S` is
  covered by finitely many closed sets, one of them contains a nonempty relatively open part of `S`.
* `exists_eventually_subset_of_cover` (**identity cover**): a germ `(A, x)` regular of some dimension
  that lies in a finite union of analytic sets lies in one of them.
* `eventually_subset_of_same_dim` (**same-dimension filling**): if `A` is regular of dimension `k` at `x`,
  `B` is regular of dimension `k` at its points near `x`, both analytic, and `A ⊆ B` near `x`, then
  `A = B` near `x` (non-thinness from the held `ThinDimensionDrop.lt_of_regularAtDim_of_thin` in the
  open submanifold of a flat ball of `B`, then the identity theorem). -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold
namespace Hironaka.HironakaG34LocalIdentityCover
noncomputable section
open RegularLocusComponent

/-- **A finite closed cover of a nonempty relatively open set** has a member containing a nonempty
relatively open part. -/
theorem exists_open_subset_of_finite_closed_cover {X ι : Type*} [TopologicalSpace X] (S : Set X)
    (B : ι → Set X) (hB : ∀ l, IsClosed (B l)) (t : Finset ι) :
    ∀ O₀ : Set X, IsOpen O₀ → (O₀ ∩ S).Nonempty → O₀ ∩ S ⊆ ⋃ l ∈ t, B l →
      ∃ l ∈ t, ∃ O : Set X, IsOpen O ∧ (O ∩ S).Nonempty ∧ O ∩ S ⊆ B l := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro O₀ _ hne hsub
    obtain ⟨y, hy⟩ := hne
    obtain ⟨l, hl, -⟩ := mem_iUnion₂.mp (hsub hy)
    exact absurd hl (Finset.notMem_empty l)
  | insert a t _ ih =>
    intro O₀ hO₀ hne hsub
    by_cases h : ((O₀ \ B a) ∩ S).Nonempty
    · obtain ⟨l, hl, O, hO, hOne, hOsub⟩ := ih (O₀ \ B a) (hO₀.sdiff (hB a)) h (by
        intro y hy
        obtain ⟨l, hl, hyl⟩ := mem_iUnion₂.mp (hsub ⟨hy.1.1, hy.2⟩)
        rcases Finset.mem_insert.mp hl with rfl | hl'
        · exact absurd hyl hy.1.2
        · exact mem_iUnion₂.mpr ⟨l, hl', hyl⟩)
      exact ⟨l, Finset.mem_insert_of_mem hl, O, hO, hOne, hOsub⟩
    · refine ⟨a, Finset.mem_insert_self a t, O₀, hO₀, hne, ?_⟩
      intro y hy
      by_contra hya
      exact h ⟨y, ⟨hy.1, hya⟩, hy.2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Identity cover**: a germ regular of some dimension that lies in a finite union of analytic sets
lies in one of them. -/
theorem exists_eventually_subset_of_cover {A : Set M} {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) A x k) {ι : Type*} [Fintype ι] (B : ι → Set M)
    (hB : ∀ l, IsComplexAnalyticSubset (n := n) (B l))
    (hcov : ∀ᶠ y in 𝓝 x, y ∈ A → ∃ l, y ∈ B l) :
    ∃ l, ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ B l := by
  classical
  let P : ∀ l, ComplexAnalyticPresentationAt (n := n) (B l) x := fun l => Classical.choice (hB l x)
  let Nset : Set (ComplexModel n) := ⋂ l, (P l).coordinateNeighborhood
  have hNo : IsOpen Nset := isOpen_iInter_of_finite fun l => (P l).isOpen_coordinateNeighborhood
  have hxN : (complexChartAt (n := n) x).val x ∈ Nset :=
    mem_iInter.mpr fun l => (P l).center_mem_coordinateNeighborhood
  obtain ⟨F, hF⟩ := exists_flatBall hx hNo hxN
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hcov
  obtain ⟨l, -, O, hO, hne, hOsub⟩ := exists_open_subset_of_finite_closed_cover (A ∩ F.nbhd) B
    (fun l => (hB l).isClosed) Finset.univ V hVo ⟨x, hxV, hx.2.1, F.mem_nbhd⟩ (by
      intro y hy
      obtain ⟨l, hl⟩ := hVsub hy.1 hy.2.1
      exact mem_iUnion₂.mpr ⟨l, Finset.mem_univ l, hl⟩)
  refine ⟨l, ?_⟩
  have hsub := F.inter_nbhd_subset_of_isOpen (P l) (fun w hw => mem_iInter.mp (hF w hw) l) hO hne
    hOsub
  filter_upwards [F.isOpen_nbhd.mem_nhds F.mem_nbhd] with y hy hyA
  exact hsub ⟨hyA, hy⟩

/-- **Same-dimension filling**: a germ of dimension `k` inside a set that is regular of dimension `k`
at its points near `x` fills it near `x`. -/
theorem eventually_subset_of_same_dim {A B : Set M} {x : M} {k : ℕ}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B)
    (hxA : RegularAtDim (n := n) A x k)
    (hBk : ∀ᶠ y in 𝓝 x, y ∈ B → RegularAtDim (n := n) B y k)
    (hAB : ∀ᶠ y in 𝓝 x, y ∈ A → y ∈ B) :
    ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A := by
  have hxB : x ∈ B := hAB.self_of_nhds hxA.2.1
  have hxBk : RegularAtDim (n := n) B x k := hBk.self_of_nhds hxB
  let P : ComplexAnalyticPresentationAt (n := n) A x := Classical.choice (hA x)
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (hBk.and hAB)
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  let Nset : Set (ComplexModel n) := P.coordinateNeighborhood ∩
    ((complexChartAt (n := n) x).val.target ∩ (complexChartAt (n := n) x).val.symm ⁻¹' V)
  have hNo : IsOpen Nset := P.isOpen_coordinateNeighborhood.inter
    ((complexChartAt (n := n) x).val.continuousOn_symm.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_target hVo)
  have hxN : (complexChartAt (n := n) x).val x ∈ Nset := by
    refine ⟨P.center_mem_coordinateNeighborhood, (complexChartAt (n := n) x).val.map_source hxs, ?_⟩
    rw [mem_preimage, (complexChartAt (n := n) x).val.left_inv hxs]
    exact hxV
  obtain ⟨F, hF⟩ := exists_flatBall hxBk hNo hxN
  have hNV : F.nbhd ⊆ V := by
    intro y hy
    obtain ⟨hys, hyΦ, hyball⟩ := hy
    have h1 := hF _ hyball
    rw [F.Φ.left_inv _ hyΦ] at h1
    have h2 := h1.2.2
    rwa [mem_preimage, (complexChartAt (n := n) x).val.left_inv hys] at h2
  let U : Opens M := ⟨F.nbhd, F.isOpen_nbhd⟩
  have hxU : x ∈ U := F.mem_nbhd
  have hT : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → M) ⁻¹' B) :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hB U
  have hT'T : (Subtype.val : U → M) ⁻¹' A ⊆ (Subtype.val : U → M) ⁻¹' B := fun y hy =>
    (show _ ∧ _ from hVsub (hNV y.2)).2 hy
  have hdim : AnalyticDimensionBasics.DimLE (n := n) ((Subtype.val : U → M) ⁻¹' B) k := by
    intro y j hy
    have hy' := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hy
    exact (RegularPointDimension.eq_of_regularAtDim hy'
      ((show _ ∧ _ from hVsub (hNV y.2)).1 hy'.2.1)).le
  have hxT' : RegularAtDim (n := n) ((Subtype.val : U → M) ⁻¹' A) (⟨x, hxU⟩ : U) k :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hxA
  have hnot : ¬ ∀ O : Set U, IsOpen O → O ∩ ((Subtype.val : U → M) ⁻¹' B) ⊆
      (Subtype.val : U → M) ⁻¹' A → O ∩ ((Subtype.val : U → M) ⁻¹' B) = ∅ := by
    intro hthin
    exact lt_irrefl _ (ThinDimensionDrop.lt_of_regularAtDim_of_thin hT hT'T hthin hdim hxT')
  push Not at hnot
  obtain ⟨O', hO'o, hO'sub, hO'ne⟩ := hnot
  have hOo : IsOpen ((Subtype.val : U → M) '' O') := U.isOpen.isOpenMap_subtype_val O' hO'o
  have hOsub : (Subtype.val : U → M) '' O' ∩ (B ∩ F.nbhd) ⊆ A := by
    rintro y ⟨⟨z, hz, rfl⟩, hyB, -⟩
    exact hO'sub ⟨hz, hyB⟩
  have hOne : ((Subtype.val : U → M) '' O' ∩ (B ∩ F.nbhd)).Nonempty := by
    obtain ⟨z, hz, hzB⟩ := hO'ne
    exact ⟨z.val, ⟨z, hz, rfl⟩, hzB, z.2⟩
  have hsub := F.inter_nbhd_subset_of_isOpen P (fun w hw => (hF w hw).1) hOo hOne hOsub
  filter_upwards [F.isOpen_nbhd.mem_nhds F.mem_nbhd] with y hy hyB
  exact hsub ⟨hyB, hy⟩

end
end Hironaka.HironakaG34LocalIdentityCover

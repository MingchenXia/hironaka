import Hironaka.Analytic.Unibranch.HironakaG10MwPersistentConsequences
import Hironaka.Analytic.Unibranch.HironakaG10RdStratification
import Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether
import Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction

/-!
# Hironaka Th. 2.4 for a closed non-compact `S`, and finite covers of the non-flat image (lane G10TM)

Plan items G10-03-04.a (`P3′`) and the round cover `hcover` of lane G10RD's
`HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI` / `HironakaG10RdRelativeRounds.exists_flatOverB_of_theoremI`.
Source: H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), Theorem 2.4
(printed p. 526) with its proof's "standard piecing-together method" for a closed `S` with a locally finite family
of local flatteners (p. 527), and its use on the strata `E_{q+r} = s_r ∖ s_{r+1}` inside `V_{q+r} = Y ∖ s_{r+1}`
(p. 544).

* `eventually_mem_support_of_flat` — a local flattener through a point of `A` over which `f` is flat
  relative to `A` contains `A` near that point (no analyticity of `A` used);
* `exists_localFlattener_of_isClosed` — **Th. 2.4 for a closed, possibly non-compact `S = A ∩ W`** in an
  open `W` of a compact base: ONE local flattener on `W` whose support contains `A ∩ W` (locally finite
  gluing in the paracompact `W`, `OriginalRelativelyCompactRestriction.paracompactSpace`);
* `exists_cover_of_frisch`, `exists_relCover_of_frisch`, `hcover_of_frisch`, `relHcover_of_frisch` —
  finitely many local flatteners cover the non-flat image (resp. every relative non-flat set), given the
  two Frisch statements `hF1`, `hF2` of `HironakaG10RdStratification` (finite depth of the strata).

The supports of local flatteners are NOT open, so a finite cover does not follow from compactness alone: for
`Y = {0} ⊔ L → ℂ²` (`L` a line through `0`) the flattener at `0` is `𝔪₀`, while the non-flat image is `L`;
the strata (`s₁ = L`, `s₂ = {0}`) are what make the cover finite.  No named input.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover

open Hironaka HironakaG10HirIdealGerms
open Hironaka.Analytic.Unibranch
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
  Hironaka.Analytic.Unibranch.HironakaG10RdFinish Hironaka.Analytic.Unibranch.HironakaG10RdStratification
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStrataNoether Hironaka.Analytic.Unibranch.HironakaG10TrackedBoundaryCSet
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow

noncomputable section

variable {X Y : SourceReducedComplexSpace}

/-! ### Local containment -/

/-- **A local flattener contains `A` near a point of `A` over which `f` is flat relative to `A`**. -/
theorem eventually_mem_support_of_flat {f : Y ⟶ X} (Z : LocalFlattener f) {A : Set X.obj.left}
    {x : X.obj.left} (hxZ : x ∈ Z.support)
    (hflat : FlatOverAt f x (vanishingIdealAt X.obj.left A x)) :
    ∀ᶠ y in 𝓝 x, y ∈ Z.V ∧ Z.H y ≤ vanishingIdealAt X.obj.left A y := by
  have hle : Z.H x ≤ vanishingIdealAt X.obj.left A x :=
    ((Z.flattener x hxZ.1 hxZ.2) _).mp hflat
  filter_upwards [eventually_le_vanishingIdealAt Z.fg Z.isOpen A hxZ.1 hle,
    Z.isOpen.mem_nhds hxZ.1] with y hy hyV
  exact ⟨hyV, hy⟩

theorem ne_top_of_le_vanishingIdealAt {A : Set X.obj.left} {y : X.obj.left} (hy : y ∈ A)
    {I : Ideal (X.obj.left.presheaf.stalk y)} (h : I ≤ vanishingIdealAt X.obj.left A y) : I ≠ ⊤ :=
  fun htop => (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (top_le_iff.mp ((htop ▸ h).trans (vanishingIdealAt_le_maximalIdeal A hy)))

/-! ### Theorem 2.4 for a closed non-compact `S` -/

/-- **Hironaka Th. 2.4 for a closed `S = A ∩ W`, `A` closed, `W` open, `X` compact** (p. 526–527): if `f` is
flat relative to `A` at every point of `A ∩ W`, ONE local flattener on `W` contains `A ∩ W` in its support. -/
theorem exists_localFlattener_of_isClosed [CompactSpace X.obj.left] (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (W : Set X.obj.left) (hW : IsOpen W)
    (A : Set X.obj.left) (hA : IsClosed A)
    (hflat : ∀ x ∈ A ∩ W, FlatOverAt f x (vanishingIdealAt X.obj.left A x)) :
    ∃ Z : LocalFlattener f, Z.V ⊆ W ∧ A ∩ W ⊆ Z.support := by
  classical
  have : T2Space X.obj.left := X.property.1
  have : ParacompactSpace X.obj.left := X.property.2.1
  let S := A ∩ W
  -- pointwise pieces
  choose Zf hZf using persistentLocalFlattener X Y f hf
  have hpiece : ∀ x : S, ∃ t ∈ 𝓝 x.1, IsClosed t ∧
      t ⊆ {y | y ∈ (Zf x.1).V ∧ y ∈ W ∧ (Zf x.1).H y ≤ vanishingIdealAt X.obj.left A y} := by
    intro x
    have hev := eventually_mem_support_of_flat (Zf x.1) (hZf x.1) (hflat x.1 x.2)
    refine exists_mem_nhds_isClosed_subset ?_
    filter_upwards [hev, hW.mem_nhds x.2.2] with y h1 h2
    exact ⟨h1.1, h2, h1.2⟩
  choose t ht htc hts using hpiece
  -- the paracompact open `W`
  let Wo : Opens X.obj.left := ⟨W, hW⟩
  have hWc : IsCompact (closure (Wo : Set X.obj.left)) := isClosed_closure.isCompact
  have : ParacompactSpace Wo := OriginalRelativelyCompactRestriction.paracompactSpace X Wo hWc
  let ι : Wo → X.obj.left := Subtype.val
  have hι : Topology.IsOpenEmbedding ι := hW.isOpenEmbedding_subtypeVal
  let s' : Set Wo := ι ⁻¹' A
  have hs' : IsClosed s' := hA.preimage continuous_subtype_val
  let u : S → Set Wo := fun k => ι ⁻¹' interior (t k)
  have hu : ∀ k, IsOpen (u k) := fun k => isOpen_interior.preimage continuous_subtype_val
  have hsu : s' ⊆ ⋃ k, u k := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y.1, hy, y.2⟩, mem_interior_iff_mem_nhds.2 (ht ⟨y.1, hy, y.2⟩)⟩
  obtain ⟨v, hvo, hsv, hvlf, hvu⟩ := precise_refinement_set hs' u hu hsu
  -- closures of the pieces lie in the closed neighbourhoods
  have hclv : ∀ k (y : Wo), y ∈ closure (v k) → ι y ∈ t k := by
    intro k y hy
    have h1 : ι y ∈ closure (ι '' v k) := image_closure_subset_closure_image continuous_subtype_val
      ⟨y, hy, rfl⟩
    have h2 : ι '' v k ⊆ t k := by
      rintro _ ⟨z, hz, rfl⟩
      exact interior_subset (hvu k hz)
    exact closure_minimal h2 (htc k) h1
  -- the agreement sets and the bad set
  let N : S → S → Set X.obj.left := fun k l => {y | ∀ᶠ z in 𝓝 y, (Zf k.1).H z = (Zf l.1).H z}
  have hN : ∀ k l, IsOpen (N k l) := fun k l => isOpen_setOfPred_eventually_nhds
  let C : S × S → Set Wo := fun kl => (closure (v kl.1) ∩ closure (v kl.2)) \ ι ⁻¹' N kl.1 kl.2
  have hCc : ∀ kl, IsClosed (C kl) := fun kl =>
    (isClosed_closure.inter isClosed_closure).sdiff ((hN kl.1 kl.2).preimage continuous_subtype_val)
  have hCl : LocallyFinite C := by
    intro y
    obtain ⟨O, hO, hfin⟩ := hvlf.closure y
    refine ⟨O, hO, (hfin.prod hfin).subset ?_⟩
    rintro ⟨k, l⟩ ⟨z, hzC, hzO⟩
    exact ⟨⟨z, hzC.1.1, hzO⟩, ⟨z, hzC.1.2, hzO⟩⟩
  let Bad : Set Wo := ⋃ kl, C kl
  have hBad : IsClosed Bad := hCl.isClosed_iUnion hCc
  let VW : Set Wo := (⋃ k, v k) \ Bad
  have hVW : IsOpen VW := (isOpen_iUnion hvo).sdiff hBad
  let V : Set X.obj.left := ι '' VW
  have hV : IsOpen V := hι.isOpenMap _ hVW
  -- agreement on `V`
  have hagree : ∀ y ∈ VW, ∀ k l, y ∈ v k → y ∈ v l → (Zf k.1).H (ι y) = (Zf l.1).H (ι y) := by
    intro y hy k l hyk hyl
    have hyN : ι y ∈ N k l := by
      by_contra hn
      exact hy.2 (mem_iUnion.2 ⟨(k, l), ⟨subset_closure hyk, subset_closure hyl⟩, hn⟩)
    exact Filter.Eventually.self_of_nhds (p := fun z => (Zf k.1).H z = (Zf l.1).H z) hyN
  -- the glued family
  let H : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) := fun x =>
    if h : ∃ k, ∃ y ∈ v k, ι y = x then (Zf (Classical.choose h).1).H x else ⊤
  have hH : ∀ y ∈ VW, ∀ k, y ∈ v k → H (ι y) = (Zf k.1).H (ι y) := by
    intro y hy k hyk
    have h : ∃ k, ∃ y' ∈ v k, ι y' = ι y := ⟨k, y, hyk, rfl⟩
    simp only [H, dif_pos h]
    obtain ⟨y', hy'k, hy'⟩ := Classical.choose_spec h
    have hyy : y' = y := hι.injective hy'
    subst hyy
    exact hagree y' hy _ k hy'k hyk
  have hvV : ∀ k (y : Wo), y ∈ v k → ι y ∈ (Zf k.1).V := fun k y hy =>
    (hts k (hclv k y (subset_closure hy))).1
  -- `S ⊆ V`
  have hSVW : ∀ x ∈ S, ∃ y ∈ VW, ι y = x := by
    intro x hx
    let y : Wo := ⟨x, hx.2⟩
    have hys : y ∈ s' := hx.1
    refine ⟨y, ⟨hsv hys, ?_⟩, rfl⟩
    intro hbad
    obtain ⟨⟨k, l⟩, ⟨hyk, hyl⟩, hn⟩ := mem_iUnion.1 hbad
    apply hn
    obtain ⟨hk1, -, hk3⟩ := hts k (hclv k y hyk)
    obtain ⟨hl1, -, hl3⟩ := hts l (hclv l y hyl)
    exact (Zf k.1).eventually_eq (Zf l.1) ⟨hk1, ne_top_of_le_vanishingIdealAt hx.1 hk3⟩
      ⟨hl1, ne_top_of_le_vanishingIdealAt hx.1 hl3⟩
  refine ⟨⟨V, hV, H, ?_, ?_⟩, ?_, ?_⟩
  · refine isLocallyFinitelyGeneratedOn_of_local fun x hx => ?_
    obtain ⟨y, hyV, rfl⟩ := hx
    obtain ⟨k, hyk⟩ := mem_iUnion.1 hyV.1
    refine ⟨ι '' (VW ∩ v k), (Zf k.1).V, (Zf k.1).H, hι.isOpenMap _ (hVW.inter (hvo k)),
      ⟨y, ⟨hyV, hyk⟩, rfl⟩, hvV k y hyk, (Zf k.1).fg, ?_⟩
    rintro _ ⟨z, ⟨hzV, hzk⟩, rfl⟩ _
    exact ⟨hvV k z hzk, hH z hzV k hzk⟩
  · rintro _ ⟨y, hyV, rfl⟩ hne
    obtain ⟨k, hyk⟩ := mem_iUnion.1 hyV.1
    rw [hH y hyV k hyk] at hne ⊢
    exact (Zf k.1).flattener _ (hvV k y hyk) hne
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x hx
    obtain ⟨y, hyV, rfl⟩ := hSVW x hx
    refine ⟨⟨y, hyV, rfl⟩, ?_⟩
    obtain ⟨k, hyk⟩ := mem_iUnion.1 hyV.1
    show H (ι y) ≠ ⊤
    rw [hH y hyV k hyk]
    exact ne_top_of_le_vanishingIdealAt hx.1 (hts k (hclv k y (subset_closure hyk))).2.2

/-! ### Finite covers of the non-flat image -/

/-- **Finitely many local flatteners cover the non-flat image**, given Frisch's two statements
(`HironakaG10RdStratification`): the strata of `f` over the whole base are finitely many, and each
difference `s_r ∖ s_{r+1}` lies in ONE local flattener on `X ∖ s_{r+1}` (Th. 2.4, Hironaka p. 544). -/
theorem exists_cover_of_frisch [CompactSpace X.obj.left] (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base)
    (hF1 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A))
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A)) :
    ∃ (m : ℕ) (Z : Fin m → LocalFlattener f), nonflatImage f ⊆ ⋃ p, (Z p).support := by
  have hA := strata_analytic f hF1 (X.isAnalyticSubset_univ)
  obtain ⟨N, hN⟩ := exists_empty_stratum_of_analytic_no_fixed f univ hA
    (strata_succ_ne f hF1 hF2 (X.isAnalyticSubset_univ))
  have hpiece : ∀ r : Fin N, ∃ Z : LocalFlattener f,
      strata f univ r ∩ (strata f univ (r + 1))ᶜ ⊆ Z.support := by
    intro r
    obtain ⟨Z, -, hZ⟩ := exists_localFlattener_of_isClosed f hf (strata f univ (r + 1))ᶜ
      (hA _).isClosed.isOpen_compl (strata f univ r) (hA _).isClosed (by
        intro x hx
        by_contra hnf
        exact hx.2 ⟨hx.1, hnf⟩)
    exact ⟨Z, hZ⟩
  choose Z hZ using hpiece
  refine ⟨N, Z, ?_⟩
  intro x hx
  rw [← relNonflat_univ_eq_nonflatImage] at hx
  have hx1 : x ∈ strata f univ 1 := hx
  obtain ⟨j, -, hxj, hxj'⟩ := exists_last_stratum f univ N hN 1 hx1
  have hjN : j < N := by
    by_contra hle
    have hanti : Antitone (strata f univ) := antitone_nat_of_succ_le (strata_succ_subset f univ)
    have : x ∈ strata f univ N := hanti (not_lt.mp hle) hxj
    rw [hN] at this
    exact this
  exact mem_iUnion.2 ⟨⟨j, hjN⟩, hZ ⟨j, hjN⟩ ⟨hxj, hxj'⟩⟩

/-- Every relative non-flat set lies in the non-flat image, so the same finite family covers it. -/
theorem exists_relCover_of_frisch [CompactSpace X.obj.left] (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base)
    (hF1 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → X.IsAnalyticSubset (relNonflat f A))
    (hF2 : ∀ A : Set X.obj.left, X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat f A))
    (B : Set X.obj.left) :
    ∃ (m : ℕ) (Z : Fin m → LocalFlattener f), relNonflat f B ⊆ ⋃ p, (Z p).support := by
  obtain ⟨m, Z, hZ⟩ := exists_cover_of_frisch f hf hF1 hF2
  exact ⟨m, Z, (relNonflat_subset_nonflatImage f B).trans hZ⟩

/-- **The round cover `hcover` of `HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI`**, from Frisch's
two statements over every compact proper stage. -/
theorem hcover_of_frisch
    (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), nonflatImage s.f ⊆ ⋃ p, (Z p).support :=
  fun s hX hf => exists_cover_of_frisch s.f hf (hFrisch s hX hf).1 (hFrisch s hX hf).2

/-- **The relative round cover of `HironakaG10RdRelativeRounds.exists_flatOverB_of_theoremI`**. -/
theorem relHcover_of_frisch
    (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support :=
  fun s hX hf B _ => exists_relCover_of_frisch s.f hf (hFrisch s hX hf).1 (hFrisch s hX hf).2 B

end

end Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover

import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry
import Hironaka.Resolution.HironakaOriginalFiniteSimultaneousHSException
import Hironaka.Resolution.HironakaOriginalSmoothSubmersionIntrinsicHS
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Analytic.IrreducibleComponentFilling
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaProperValueRangeDescent

set_option autoImplicit false

/-!
# Local finite ranges of the entire original Hilbert--Samuel profile family

Strong induction on the actual analytic carrier dimension works in all
ambient dimensions. Actual denominator exceptions give dimension drop;
the genuine graph and product submersion retain the original profiles under
local embedded resolution. Properness and actual locally finite global
components descend and glue the finite ranges.

Blueprint: `hironaka-original-local-finite-hs-profiles.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaOriginalLocalFiniteHSProfiles

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.NonKahlerLocus HironakaHolomorphicJetChartInvariance
  HironakaOriginalFiniteSimultaneousHSException HironakaActualOpenIntrinsicHS
  HironakaOriginalSmoothSubmersionIntrinsicHS HironakaAuxiliaryGraphGeometry
  HironakaOneDimensionalCanonicalSuperlevels HironakaProperValueRangeDescent
  GlobalComponents RegularLocusComponent AnalyticDimensionBasics

open scoped ProductComplexManifold

private def ProfileRangeBound (ι : Type v) (q : ℕ) : Prop :=
  ∀ (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : ι → GermIdeal n X), (∀ i, (A i).IsCoherent) →
    ∀ W : Set X, IsComplexAnalyticSubset (n := n) W → DimLE (n := n) W q →
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (W ∩ (U : Set X))).Finite

private theorem component_finite_images_glue {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {β : Type*} {C : Set X} (hC : IsComplexAnalyticSubset (n := n) C) (g : X → β)
    (hlocal : ∀ B ∈ globalComponents (n := n) C, ∀ x ∈ B,
      ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (g '' (O ∩ B)).Finite) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ (g '' (C ∩ (U : Set X))).Finite := by
  classical
  obtain ⟨V, hxV, hfin⟩ := locallyFinite_globalComponents hC x
  let T := {B : globalComponents (n := n) C | ((B : Set X) ∩ V).Nonempty}
  have hT : T.Finite := hfin
  have hAll : ∀ B : globalComponents (n := n) C,
      ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (g '' (O ∩ (B : Set X))).Finite := by
    intro B
    by_cases hxB : x ∈ (B : Set X)
    · exact hlocal B B.property x hxB
    · refine ⟨(B : Set X)ᶜ,
        (isComplexAnalyticallyIrreducible_of_mem_globalComponents hC B.property).analytic.isClosed.isOpen_compl,
        hxB, ?_⟩
      simp only [compl_inter_self, image_empty]
      exact finite_empty
  choose O hO hxO hgf using hAll
  let U := interior V ∩ ⋂ B ∈ hT.toFinset, O B
  have hU : IsOpen U := isOpen_interior.inter (isOpen_biInter_finset fun B _ => hO B)
  have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hxV,
    mem_iInter₂.mpr fun B _ => hxO B⟩
  refine ⟨⟨U, hU⟩, hxU, (hT.biUnion fun B _ => hgf B).subset ?_⟩
  rintro _ ⟨y, ⟨hyC, hyU⟩, rfl⟩
  have hyUnion : y ∈ ⋃₀ globalComponents (n := n) C := by
    rw [sUnion_globalComponents hC]
    exact hyC
  obtain ⟨B, hB, hyB⟩ := hyUnion
  let b : globalComponents (n := n) C := ⟨B, hB⟩
  have hbT : b ∈ T := ⟨y, hyB, interior_subset hyU.1⟩
  have hyO : y ∈ O b := mem_iInter₂.mp hyU.2 b (hT.mem_toFinset.mpr hbT)
  exact mem_biUnion hbT ⟨y, ⟨hyO, hyB⟩, rfl⟩

private theorem image_strictTransform_eq {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hproper : IsProperMap π) {W F : Set X} (hW : IsClosed W)
    (hdense : W ⊆ closure (W \ F)) (hiso : IsIsomorphismOver n π Fᶜ) :
    π '' strictTransform n π W = W := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hπ.continuous hW hy
  · have hc : IsClosed (π '' strictTransform n π W) :=
      hproper.isClosedMap _ isClosed_closure
    have hlift : W \ F ⊆ π '' strictTransform n π W := by
      intro x hx
      obtain ⟨y, hyF, hyx⟩ := hiso.1.surjOn hx.2
      have hyE : y ∉ exceptionalLocus n π :=
        fun hy => Set.disjoint_left.mp hiso.2 hyF hy
      exact ⟨y, (HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem
        hπ.continuous hW hyE).mpr (hyx.symm ▸ hx.1), hyx⟩
    exact fun _ hx => closure_minimal hlift hc (hdense hx)

private theorem zero_profile_range_bound (ι : Type v) : ProfileRangeBound.{u,v} ι 0 := by
  intro n X _ _ _ A _hA W hW hd x
  by_cases hx : x ∈ W
  · obtain ⟨U, hU, hxU, hsub⟩ :=
      PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero
        (regularAtDim_zero_of_analytic_dimLE_zero hW hd hx)
    refine ⟨⟨U, hU⟩, hxU,
      (finite_singleton (fun i ℓ => hilbertSamuelAt (A i) x ℓ)).subset ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hsub hy]
    exact mem_singleton _
  · refine ⟨⟨Wᶜ, hW.isClosed.isOpen_compl⟩, hx, ?_⟩
    change ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (W ∩ Wᶜ)).Finite
    simp only [inter_compl_self, image_empty]
    exact finite_empty

private theorem smooth_finite_profile_window {ι : Type v} [Fintype ι]
    (q : ℕ) (ih : ProfileRangeBound.{u,v} ι (q-1))
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : ι → GermIdeal n X) (hA : ∀ i, (A i).IsCoherent)
    {S : Set X} (hS : IsComplexAnalyticSubset (n := n) S)
    (hreg : ∀ x ∈ S, RegularAtDim (n := n) S x q) (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (S ∩ (U : Set X))).Finite := by
  classical
  by_cases hx : x ∈ S
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (hreg x hx).1
    obtain ⟨D, hxD, E, hE, _hES, _hthin, hdim, _hdense, profile, hprofile⟩ :=
      exists_original_finite_simultaneous_intrinsic_hs_exception S hS x (hreg x hx) A hA
    let P : ι → GermIdeal (q+t) D :=
      fun i => GermIdeal.pullback (m := q+t) (Subtype.val : D → X) (A i)
    have hP : ∀ i, (P i).IsCoherent :=
      fun i => GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hA i)
    have hdE : DimLE (n := q+t) E (q-1) :=
      fun y k hy => Nat.le_pred_of_lt (hdim y k hy)
    obtain ⟨O, hxO, hfin⟩ := ih (q+t) D P hP E hE hdE ⟨x, hxD⟩
    let U : Set X := (Subtype.val : D → X) '' (O : Set D)
    have hU : IsOpen U := D.isOpen.isOpenMap_subtype_val _ O.isOpen
    refine ⟨⟨U, hU⟩, ⟨⟨x, hxD⟩, hxO, rfl⟩, (hfin.insert profile).subset ?_⟩
    rintro _ ⟨y, ⟨hyS, p, hpO, hpy⟩, rfl⟩
    by_cases hpE : p ∈ E
    · apply mem_insert_of_mem
      refine ⟨p, ⟨hpE, hpO⟩, ?_⟩
      funext i ℓ
      change hilbertSamuelAt (GermIdeal.pullback (m := q+t)
        (Subtype.val : D → X) (A i)) p ℓ = hilbertSamuelAt (A i) y ℓ
      rw [hilbertSamuelAt_actual_open_pullback (A i) (hA i) D p, hpy]
    · apply mem_insert_iff.mpr
      left
      funext i ℓ
      rw [← hpy]
      exact hprofile i p (hpy.symm ▸ hyS) hpE ℓ
  · refine ⟨⟨Sᶜ, hS.isClosed.isOpen_compl⟩, hx, ?_⟩
    change ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (S ∩ Sᶜ)).Finite
    simp only [inter_compl_self, image_empty]
    exact finite_empty

private theorem composed_smooth_finite_profile_window {ι : Type v} [Fintype ι]
    (q : ℕ) (ih : ProfileRangeBound.{u,v} ι (q-1))
    {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X} (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (A : ι → GermIdeal n X) (hA : ∀ i, (A i).IsCoherent)
    {S : Set Y} (hS : IsComplexAnalyticSubset (n := m) S)
    (hreg : ∀ y ∈ S, RegularAtDim (n := m) S y q) (y : Y) :
    ∃ U : Opens Y, y ∈ U ∧
      ((fun z i ℓ => hilbertSamuelAt (A i) (f z) ℓ) '' (S ∩ (U : Set Y))).Finite := by
  classical
  let P : ι → GermIdeal (n+m) (X × Y) :=
    fun i => GermIdeal.pullback (m := n+m) (Prod.fst : X × Y → X) (A i)
  have hP : ∀ i, (P i).IsCoherent :=
    fun i => GermIdealPullbackCalculus.isCoherent_pullback ProductComplexManifold.contMDiff_fst (hA i)
  have hG : IsClosedSubmanifold (n+m) (HironakaAuxiliaryGraphGeometry.graphOn f S) :=
    isClosedSubmanifold_graph hf ⟨hS.isClosed, fun z hz => ⟨q, hreg z hz⟩⟩
  have hGreg : ∀ p ∈ HironakaAuxiliaryGraphGeometry.graphOn f S,
      RegularAtDim (n := n+m) (HironakaAuxiliaryGraphGeometry.graphOn f S) p q := by
    rintro ⟨x, z⟩ ⟨hzS, hxz⟩
    change x = f z at hxz
    subst x
    exact regularAtDim_graph hf (hreg z hzS)
  obtain ⟨V, hyV, hfin⟩ := smooth_finite_profile_window q ih P hP
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hG) hGreg (f y, y)
  let γ : Y → X × Y := fun z => (f z, z)
  have hγ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (n+m)) ∞ γ :=
    ProductComplexManifold.contMDiff_prodMk hf contMDiff_id
  let U : Opens Y := ⟨γ ⁻¹' (V : Set (X × Y)), V.isOpen.preimage hγ.continuous⟩
  have hfini : ((fun z i ℓ => hilbertSamuelAt (P i) (γ z) ℓ) '' (S ∩ (U : Set Y))).Finite := by
    apply hfin.subset
    rintro _ ⟨z, ⟨hzS, hzU⟩, rfl⟩
    exact ⟨γ z, ⟨⟨hzS, rfl⟩, hzU⟩, rfl⟩
  have hsub : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+m))
      𝓘(ℂ, ComplexModel n) ∞ (Prod.fst : X × Y → X) :=
    HironakaAuxiliaryGraphGeometry.isSubmersion_fst
  refine ⟨U, hyV, finite_image_of_eq_reflection hfini ?_⟩
  intro a _ha b _hb hab
  funext i ℓ
  apply (hilbertSamuelAt_original_submersion_entire_profile_eq_iff
    hsub (A i) (hA i) (γ a) (γ b)).mp ?_ ℓ
  intro k
  exact congrArg (fun p => p i k) hab

private theorem irreducible_finite_profile_window {ι : Type v} [Fintype ι]
    (q : ℕ) (ih : ProfileRangeBound.{u,v} ι (q-1))
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hVdim : V.dim = q)
    (A : ι → GermIdeal n X) (hA : ∀ i, (A i).IsCoherent) (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (V.carrier ∩ (U : Set X))).Finite := by
  classical
  obtain ⟨D, hxD, Y, i1, i2, i3, π, hπ, E, _hE, _hexc, _hsupp, hiso, hS, hreg, _hnc⟩ :=
    HironakaEmbeddedResolutionLocal.exists_embeddedResolution_local V
      (K := {x}) isCompact_singleton
  let W : Set D := (Subtype.val : D → X) ⁻¹' V.carrier
  let F : Set D := (Subtype.val : D → X) ⁻¹' singularLocus V
  let S : Set Y := strictTransform n π W
  have hWc : IsClosed W := V.isClosed_carrier.preimage continuous_subtype_val
  have hdense : W ⊆ closure (W \ F) := by
    intro p hp
    have h := HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V hp
    have he := (D.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (V.carrier ∩ EmbeddedFromResolution.regularOpen V)
    change p ∈ closure ((Subtype.val : D → X) ⁻¹'
      (V.carrier ∩ EmbeddedFromResolution.regularOpen V))
    exact (Set.ext_iff.mp he p).mp h
  have hproper := HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hπ
  have himage : π '' S = W := image_strictTransform_eq hπ.contMDiff hproper hWc hdense hiso
  have hregS : ∀ y ∈ S, RegularAtDim (n := n) S y q := by
    intro y hy
    simpa only [hVdim] using hreg y hy
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : D → X) ∘ π) :=
    (HironakaBaseChange.isOpenHoloEmbedding_val (n := n) D).contMDiff.comp hπ.contMDiff
  let g : D → ι → ℕ → ℕ := fun p i ℓ => hilbertSamuelAt (A i) (p : X) ℓ
  have hlocal : ∀ y ∈ S, ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧
      ((g ∘ π) '' (S ∩ O)).Finite := by
    intro y _hy
    obtain ⟨O, hyO, hfin⟩ := composed_smooth_finite_profile_window q ih hf A hA
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hS) hregS y
    exact ⟨O, O.isOpen, hyO, hfin⟩
  obtain ⟨O, hO, hxO, hfin⟩ := exists_isOpen_finite_image_of_isProperMap hproper hS.1 g hlocal ⟨x, hxD (mem_singleton x)⟩
  rw [himage] at hfin
  let U : Set X := (Subtype.val : D → X) '' O
  have hU : IsOpen U := D.isOpen.isOpenMap_subtype_val _ hO
  refine ⟨⟨U, hU⟩, ⟨⟨x, hxD (mem_singleton x)⟩, hxO, rfl⟩, hfin.subset ?_⟩
  rintro _ ⟨z, ⟨hzV, p, hpO, hpz⟩, rfl⟩
  refine ⟨p, ⟨?_, hpO⟩, ?_⟩
  · change (p : X) ∈ V.carrier
    exact hpz.symm ▸ hzV
  · change (fun i ℓ => hilbertSamuelAt (A i) (p : X) ℓ) =
      (fun i ℓ => hilbertSamuelAt (A i) z ℓ)
    rw [hpz]

private theorem all_profile_range_bounds (ι : Type v) [Fintype ι] (q : ℕ) :
    ProfileRangeBound.{u,v} ι q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq : q = 0
    · subst q
      exact zero_profile_range_bound ι
    · have hprev : ProfileRangeBound.{u,v} ι (q-1) :=
        ih (q-1) (Nat.sub_lt (Nat.pos_of_ne_zero hq) (by decide))
      intro n X _ _ _ A hA W hW hd x
      apply component_finite_images_glue hW (fun y i ℓ => hilbertSamuelAt (A i) y ℓ) ?_ x
      intro B hB p _hpB
      obtain ⟨c, ⟨k, hc⟩, hBC⟩ := hB
      let V := IrreducibleComponentFilling.componentSubvariety hW hc
      have hBV : B = V.carrier := hBC
      have hlocalV : ∃ O : Opens X, p ∈ O ∧
          ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (V.carrier ∩ (O : Set X))).Finite := by
        by_cases hk : k < q
        · have hdV : DimLE (n := n) V.carrier k := by
            intro y j hy
            exact Nat.le_of_eq (AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V hy)
          exact ih k hk n X A hA V.carrier V.analytic hdV p
        · have hkq : V.dim = q := Nat.le_antisymm (hd c k hc) (Nat.le_of_not_lt hk)
          exact irreducible_finite_profile_window q hprev V hkq A hA p
      obtain ⟨O, hpO, hfin⟩ := hlocalV
      refine ⟨O, O.isOpen, hpO, ?_⟩
      rw [hBV, inter_comm]
      exact hfin

/-- Only the actual finite original coherent family and actual analytic
carrier produce a genuine finite range of ENTIRE original HS tuples on an
actual open neighbourhood. No range, cutoff or variation equations are inputs. -/
theorem exists_original_entire_hs_finite_profile_window
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type v} [Fintype ι] (A : ι → GermIdeal n X) (hA : ∀ i, (A i).IsCoherent)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' (W ∩ (U : Set X))).Finite :=
  all_profile_range_bounds ι n n X A hA W hW (fun _ _ hx => hx.1) x

end

end Hironaka.HironakaOriginalLocalFiniteHSProfiles

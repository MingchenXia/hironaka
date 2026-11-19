import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.ConstantRankImage
import Hironaka.Analytic.GlobalComponents
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-! Geometry only. Blueprint FIRST: hironaka-g10-simultaneous-prime-support-neighborhood.tex.
Every regular component and its closure are formed on the prescribed final
ambient. Existing analytic engines are reused with zero duplicate engine credit.
Native module filtrations and full-map continuation are separate consumers. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSimultaneousPrimeSupportNeighborhood
open Hironaka.HolomorphicIdealSheaves
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  AnalyticGermDecomposition RegularLocusComponent

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def chartSet (W : Set M) (p : M) : Set (ComplexModel n) :=
  {z | z + (chartAt (ComplexModel n) p) p ∈
    (chartAt (ComplexModel n) p).target ∩ (chartAt (ComplexModel n) p).symm ⁻¹' W}

/-- Both directions retain original representatives on the actual chart domain. -/
private theorem wholeChart_eq_set_germ (W : Set M) (p : M) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) W) p p (mem_chart_source (ComplexModel n) p) =
      AnalyticGermDecomposition.vanishingIdeal (chartSet (n := n) W p) := by
  let e := chartAt (ComplexModel n) p
  let q := e p
  have hpS : p ∈ e.source := mem_chart_source (ComplexModel n) p
  have hqT : q ∈ e.target := e.map_source hpS
  have htAdd : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    exact (continuous_add_const q).tendsto' 0 q (zero_add q)
  have htInv : Tendsto e.symm (𝓝 q) (𝓝 p) := by
    have h := (e.continuousAt_symm hqT).tendsto
    change Tendsto e.symm (𝓝 q) (𝓝 (e.symm (e p))) at h
    rw [e.left_inv hpS] at h
    exact h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hfW,rfl⟩
    change HolGerm.mk (fun z => f (e.symm (z+q)))
      (translated_holomorphic q (CartanLocalReduction.holAt_comp_chart_symm hpS hf)) ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have ht := (htInv.comp htAdd).eventually hfW.2
    filter_upwards [ht] with z hz hzA
    exact hz hzA.2
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    have hv := AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg
    let F : M → ℂ := fun x => f (e x-q)
    have htSub : Tendsto (fun w : ComplexModel n => w-q) (𝓝 q) (𝓝 0) := by
      have hc : Continuous (fun w : ComplexModel n => w-q) := continuous_id.sub continuous_const
      exact hc.tendsto' q 0 (sub_self q)
    have hfd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ (fun z => f (z-q)) w := by
      filter_upwards [htSub.eventually hf] with w hw
      exact hw.comp w (differentiableAt_id.sub_const q)
    have hF : HolomorphicAt n F p := CartanLocalReduction.holomorphicAt_comp_chart hpS hfd
    have htChart : Tendsto (fun x : M => e x-q) (𝓝 p) (𝓝 0) := by
      have hc : ContinuousAt (fun _ : M => q) p := continuousAt_const
      have h := ((e.continuousAt hpS).sub hc).tendsto
      change Tendsto (fun x : M => e x-q) (𝓝 p) (𝓝 (e p-q)) at h
      simpa only [q,sub_self] using h
    have hFW : (vanishingIdeal (n := n) W).mem p F := by
      refine ⟨hF,?_⟩
      filter_upwards [htChart.eventually hv,e.open_source.mem_nhds hpS] with x hx hxs hxW
      apply hx
      change e x-q+q ∈ e.target ∩ e.symm ⁻¹' W
      rw [sub_add_cancel]
      exact ⟨e.map_source hxs,by simpa only [mem_preimage,e.left_inv hxs] using hxW⟩
    have he : chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) F hF = HolGerm.mk f hf := by
      unfold chartTranslatedGerm translatedGerm
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [htAdd.eventually (e.open_target.mem_nhds hqT)] with z hz
      change f (e (e.symm (z+q))-q) = f z
      rw [e.right_inv hz,add_sub_cancel_right]
    exact Ideal.subset_span ⟨F,hF,hFW,he.symm⟩

private theorem chartSet_irreducible (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (p : M) (hP : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime) :
    IsIrreducibleGerm (chartSet (n := n) W p) := by
  have hA : IsAnalyticGerm (chartSet (n := n) W p) :=
    ClosureDifferenceAnalytic.isAnalyticGerm_chart_translate (hW p).some
  let : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime := hP
  have hPrime : (Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p)).IsPrime :=
    Ideal.map_isPrime_of_equiv (actualStalkChartEquiv (n := n) p)
  rw [map_actualWholeSheafStalkIdeal,wholeChart_eq_set_germ] at hPrime
  exact (isIrreducibleGerm_iff_isPrime hA).mpr hPrime

/-- The component below is GLOBAL on M; the auxiliary O is used only for germ equality. -/
private theorem global_component_germ (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (p : M) (hpW : p ∈ W)
    (hP : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime) :
    ∃ (d : ℕ) (c : M) (_hc : RegularAtDim (n := n) W c d)
      (O : Opens M), p ∈ O ∧
      closure (component (n := n) W c) ∈ GlobalComponents.globalComponents (n := n) W ∧
      W ∩ (O : Set M) = closure (component (n := n) W c) ∩ (O : Set M) := by
  classical
  let e := chartAt (ComplexModel n) p
  let q := e p
  let A := chartSet (n := n) W p
  have hpS : p ∈ e.source := mem_chart_source (ComplexModel n) p
  obtain ⟨d,Δ,G,hΔ,h0Δ,_hAN,hGA,hGc,hDense,_hAvoid,hReg⟩ :=
    IrreducibleGermConnected.exists_connected_nhds (chartSet_irreducible W hW p hP)
      (fun j : Fin 0 => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (show (univ : Set (ComplexModel n)) ∈ 𝓝 0 from univ_mem)
  let T : ComplexModel n → M := fun z => e.symm (z+q)
  let L : M → ComplexModel n := fun x => e x-q
  let O : Set M := e.source ∩ L ⁻¹' Δ
  let H : Set M := T '' G
  have hOo : IsOpen O := e.isOpen_inter_preimage
    (hΔ.preimage (continuous_id.sub continuous_const))
  have hpO : p ∈ O := ⟨hpS,by change e p-q ∈ Δ; simpa only [q,sub_self] using h0Δ⟩
  have hTc : ContinuousOn T G := e.continuousOn_symm.comp
    (continuous_id.add continuous_const).continuousOn (fun z hz => (hGA hz).1.1)
  have hHc : IsPreconnected H := hGc.image T hTc
  have hHO : H ⊆ W ∩ O := by
    rintro _ ⟨z,hz,rfl⟩
    have hzA := (hGA hz).1
    refine ⟨hzA.2,e.map_target hzA.1,?_⟩
    change e (e.symm (z+q))-q ∈ Δ
    rw [e.right_inv hzA.1,add_sub_cancel_right]
    exact (hGA hz).2
  have hHr (x : M) (hx : x ∈ H) : RegularAtDim (n := n) W x d := by
    obtain ⟨z,hz,rfl⟩ := hx
    have hzA := (hGA hz).1
    let Q : Set (ComplexModel n) := {w | w-q ∈ Δ}
    have hQo : IsOpen Q := hΔ.preimage (continuous_id.sub continuous_const)
    have hzQ : z+q ∈ Q := by change z+q-q ∈ Δ; simpa only [add_sub_cancel_right] using (hGA hz).2
    have heq : {w : ComplexModel n | w-q ∈ A ∩ Δ} = (e.target ∩ e.symm ⁻¹' W) ∩ Q := by
      ext w
      change ((w-q+q ∈ e.target ∧ e.symm (w-q+q) ∈ W) ∧ w-q ∈ Δ) ↔
        ((w ∈ e.target ∧ e.symm w ∈ W) ∧ w-q ∈ Δ)
      rw [sub_add_cancel]
    have ht := (AnalyticLocalStatement.regularAtDim_translate_iff q (z+q)).mpr
      (by simpa only [add_sub_cancel_right] using hReg z hz)
    rw [heq] at ht
    have hr := (AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff hQo hzQ).mp ht
    apply LocalStatementConnected.ConnectedParts.regularAtDim_of_chart
      (p := p) (e.map_target hzA.1)
    change RegularAtDim (n := n) (e.target ∩ e.symm ⁻¹' W) (e (e.symm (z+q))) d
    rw [e.right_inv hzA.1]
    exact hr
  have hHD : W ∩ O ⊆ closure H := by
    rintro x ⟨hxW,hxs,hxΔ⟩
    have hz : L x ∈ A ∩ Δ := by
      refine ⟨?_,hxΔ⟩
      change e x-q+q ∈ e.target ∩ e.symm ⁻¹' W
      rw [sub_add_cancel]
      exact ⟨e.map_source hxs,by simpa only [mem_preimage,e.left_inv hxs] using hxW⟩
    have hTz : ContinuousAt T (L x) :=
      (e.continuousAt_symm (by change e x-q+q ∈ e.target; rw [sub_add_cancel]; exact e.map_source hxs)).comp
        (continuous_id.add continuous_const).continuousAt
    have hh := hTz.continuousWithinAt.mem_closure_image (hDense hz)
    change T (L x) ∈ closure H at hh
    have he : T (L x) = x := by
      change e.symm (e x-q+q) = x
      rw [sub_add_cancel,e.left_inv hxs]
    exact he ▸ hh
  obtain ⟨c,hcH⟩ := Set.Nonempty.of_closure (⟨p,hHD ⟨hpW,hpO⟩⟩ : (closure H).Nonempty)
  have hc := hHr c hcH
  have hHK : H ⊆ component (n := n) W c := subset_component_of_isPreconnected hHc
    (fun x hx => ⟨d,hHr x hx⟩) ⟨c,hcH,mem_component_self hc⟩
  have hBW : closure (component (n := n) W c) ⊆ W :=
    closure_minimal (component_subset (n := n) W c) hW.isClosed
  refine ⟨d,c,hc,⟨O,hOo⟩,hpO,GlobalComponents.closure_component_mem_globalComponents hc,?_⟩
  exact Subset.antisymm (fun x hx => ⟨closure_mono hHK (hHD hx),hx.2⟩)
    (fun x hx => ⟨hBW hx.1,hx.2⟩)

/-- An ACTUAL whole prime stalk selects a GLOBAL component on this original open. -/
theorem exists_global_regular_component_eq_on_nhds (D : Opens (ComplexModel n))
    (W : Set D) (hW : IsComplexAnalyticSubset (n := n) W) (p : D) (hpW : p ∈ W)
    (hP : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime) :
    ∃ (d : ℕ) (c : D) (_hc : RegularAtDim (n := n) W c d) (O : Opens D), p ∈ O ∧
      closure (component (n := n) W c) ∈ GlobalComponents.globalComponents (n := n) W ∧
      W ∩ (O : Set D) = closure (component (n := n) W c) ∩ (O : Set D) :=
  global_component_germ W hW p hpW hP

private theorem prime_vanishing_open (W : Set M) (p : M)
    (hP : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime)
    (U : Opens M) (hpU : p ∈ U) :
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W))
      (⟨p,hpU⟩ : U)).IsPrime := by
  let : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p).IsPrime := hP
  have hC : (wholeChartStalkIdeal (vanishingIdeal (n := n) W) p p
      (mem_chart_source (ComplexModel n) p)).IsPrime := by
    have h : (Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) p)).IsPrime :=
      Ideal.map_isPrime_of_equiv (actualStalkChartEquiv (n := n) p)
    rwa [map_actualWholeSheafStalkIdeal] at h
  have hUC : (wholeChartStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W))
      (⟨p,hpU⟩ : U) ⟨p,hpU⟩ (mem_chart_source (ComplexModel n) (⟨p,hpU⟩ : U))).IsPrime := by
    rw [HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open]
    exact hC
  rw [actualWholeSheafStalkIdeal_eq_map_chart]
  let : (wholeChartStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W))
      (⟨p,hpU⟩ : U) ⟨p,hpU⟩ (mem_chart_source (ComplexModel n) (⟨p,hpU⟩ : U))).IsPrime := hUC
  exact Ideal.map_isPrime_of_equiv (actualStalkChartEquiv (n := n) (⟨p,hpU⟩ : U)).symm

/-- All global components are selected on the prescribed N BEFORE the one
analytic-complement deletion. No later arbitrary restriction is used. -/
theorem exists_simultaneous_prime_support_neighborhood (D : Opens (ComplexModel n))
    (p : D) (r : ℕ) (W : Fin r → Set D)
    (hW : ∀ i, IsComplexAnalyticSubset (n := n) (W i)) (hpW : ∀ i, p ∈ W i)
    (hP : ∀ i, (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (W i)) p).IsPrime)
    (N : Opens D) (hpN : p ∈ N) :
    let A : Fin r → Set N := fun i => (Subtype.val : N → D) ⁻¹' W i
    let pN : N := ⟨p,hpN⟩
    ∃ (d : Fin r → ℕ) (c : Fin r → N),
      (∀ i, RegularAtDim (n := n) (A i) (c i) (d i)) ∧
      let B : Fin r → Set N := fun i => closure (component (n := n) (A i) (c i))
      let Zs : Fin r → Set N := fun i => closure (A i \ B i)
      let Z : Set N := ⋃ i, Zs i
      (∀ i, B i ∈ GlobalComponents.globalComponents (n := n) (A i)) ∧
      (∀ i, ∃ O : Opens N, pN ∈ O ∧ A i ∩ (O : Set N) = B i ∩ (O : Set N)) ∧
      (∀ i, IsComplexAnalyticSubset (n := n) (Zs i) ∧ pN ∉ Zs i) ∧
      IsComplexAnalyticSubset (n := n) Z ∧ pN ∉ Z ∧
      ∃ (U : Opens D) (_hpU : p ∈ U) (_hUN : U ≤ N),
        (U : Set D) = (Subtype.val : N → D) '' Zᶜ ∧
        ∀ i, ∃ (k : ℕ) (a : U),
          RegularAtDim (n := n) ((Subtype.val : U → D) ⁻¹' W i) a k ∧
          (Subtype.val : U → D) ⁻¹' W i =
            closure (component (n := n) ((Subtype.val : U → D) ⁻¹' W i) a) ∧
          IsComplexAnalyticallyIrreducible (n := n) ((Subtype.val : U → D) ⁻¹' W i) := by
  classical
  let A : Fin r → Set N := fun i => (Subtype.val : N → D) ⁻¹' W i
  let pN : N := ⟨p,hpN⟩
  have hA (i : Fin r) : IsComplexAnalyticSubset (n := n) (A i) :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (hW i) N
  have hpA (i : Fin r) : pN ∈ A i := hpW i
  have hPA (i : Fin r) : (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (A i)) pN).IsPrime :=
    prime_vanishing_open (W i) p (hP i) N hpN
  choose d c hc O hpO hBmem hlocal using fun i => global_component_germ (A i) (hA i) pN (hpA i) (hPA i)
  let B : Fin r → Set N := fun i => closure (component (n := n) (A i) (c i))
  let Zs : Fin r → Set N := fun i => closure (A i \ B i)
  let Z : Set N := ⋃ i, Zs i
  have hB (i : Fin r) : IsComplexAnalyticSubset (n := n) (B i) :=
    isComplexAnalyticSubset_closure_component (hA i) (hc i)
  have hpB (i : Fin r) : pN ∈ B i := ((hlocal i).subset ⟨hpA i,hpO i⟩).1
  have hZs (i : Fin r) : IsComplexAnalyticSubset (n := n) (Zs i) ∧ pN ∉ Zs i := by
    refine ⟨ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff (hA i) (hB i),?_⟩
    intro hcl
    obtain ⟨x,hxO,hx⟩ := mem_closure_iff.mp hcl (O i) (O i).isOpen (hpO i)
    exact hx.2 ((hlocal i).subset ⟨hx.1,hxO⟩).1
  have hZ : IsComplexAnalyticSubset (n := n) Z := by
    simpa only [Finset.mem_univ,iUnion_true] using
      (ConstantRankImage.isComplexAnalyticSubset_biUnion (Finset.univ : Finset (Fin r))
        (fun i _ => (hZs i).1))
  have hpZ : pN ∉ Z := by
    intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    exact (hZs i).2 hi
  let U : Opens D := ⟨(Subtype.val : N → D) '' Zᶜ,
    N.isOpen.isOpenMap_subtype_val _ hZ.isClosed.isOpen_compl⟩
  have hpU : p ∈ U := ⟨pN,hpZ,rfl⟩
  have hUN : U ≤ N := by
    rintro _ ⟨y,_,rfl⟩
    exact y.property
  refine ⟨d,c,hc,hBmem,?_,hZs,hZ,hpZ,U,hpU,hUN,rfl,?_⟩
  · intro i
    exact ⟨O i,hpO i,hlocal i⟩
  · intro i
    let K : Set N := component (n := n) (A i) (c i)
    let H : Set N := K \ Z
    have hKZ : ¬ K ⊆ Z := by
      intro h
      have hb : B i ⊆ Z := closure_minimal h hZ.isClosed
      exact hpZ (hb (hpB i))
    have hComp := ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
      (hA i) hZ (hc i) hKZ
    have hClH : closure H = B i := Subset.antisymm
      (closure_minimal (fun x hx => subset_closure hx.1) isClosed_closure)
      (closure_minimal hComp.2 isClosed_closure)
    let H0 : Set D := (Subtype.val : N → D) '' H
    let HU : Set U := (Subtype.val : U → D) ⁻¹' H0
    have hH0U : H0 ⊆ (U : Set D) := by
      rintro _ ⟨y,hy,rfl⟩
      exact ⟨y,hy.2,rfl⟩
    have hRange : H0 ⊆ range (Subtype.val : U → D) := fun x hx => ⟨⟨x,hH0U hx⟩,rfl⟩
    have hImage : (Subtype.val : U → D) '' HU = H0 := image_preimage_eq_of_subset hRange
    have hClHU : closure HU = (Subtype.val : U → D) ⁻¹' closure H0 :=
      (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image HU).trans
        (congrArg (fun S : Set D => (Subtype.val : U → D) ⁻¹' closure S) hImage)
    have hH0c : IsPreconnected H0 := hComp.1.image (Subtype.val : N → D)
      continuous_subtype_val.continuousOn
    have hHUc : IsPreconnected HU := IsPreconnected.preimage_of_isOpenMap hH0c Subtype.val_injective
      (show IsOpenMap (Subtype.val : U → D) from U.isOpen.isOpenMap_subtype_val) hRange
    have hHUs : HU ⊆ (Subtype.val : U → D) ⁻¹' W i := by
      intro x hx
      obtain ⟨y,hy,hyx⟩ := hx
      have hyW : y.val ∈ W i := component_subset (n := n) (A i) (c i) hy.1
      change x.val ∈ W i
      exact hyx ▸ hyW
    have hDense : (Subtype.val : U → D) ⁻¹' W i ⊆ closure HU := by
      rw [hClHU]
      intro x hxW
      have hxU : x.val ∈ (Subtype.val : N → D) '' Zᶜ := x.property
      obtain ⟨y,hyNZ,hyx⟩ := hxU
      have hyA : y ∈ A i := by
        change y.val ∈ W i
        rw [hyx]
        exact hxW
      have hyB : y ∈ B i := by
        by_contra hy
        have hbad : y ∈ Zs i := subset_closure ⟨hyA,hy⟩
        exact hyNZ (mem_iUnion.mpr ⟨i,hbad⟩)
      have hyCl : y ∈ closure H := hClH.symm ▸ hyB
      have him : y.val ∈ closure H0 :=
        (continuous_subtype_val : Continuous (Subtype.val : N → D)).continuousAt.continuousWithinAt.mem_closure_image hyCl
      change x.val ∈ closure H0
      exact hyx ▸ him
    have hHUr (x : U) (hx : x ∈ HU) :
        RegularAtDim (n := n) ((Subtype.val : U → D) ⁻¹' W i) x (d i) := by
      obtain ⟨y,hy,hyx⟩ := hx
      have hRN := regularAtDim_of_mem_component (hc i) hy.1
      have hRD : RegularAtDim (n := n) (W i) y.val (d i) :=
        AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hRN
      apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
      exact hyx ▸ hRD
    have hWU : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → D) ⁻¹' W i) :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val (hW i) U
    obtain ⟨a,haH⟩ := Set.Nonempty.of_closure
      (⟨⟨p,hpU⟩,hDense (show (⟨p,hpU⟩ : U) ∈ (Subtype.val : U → D) ⁻¹' W i from hpW i)⟩ :
        (closure HU).Nonempty)
    have ha := hHUr a haH
    have hHK : HU ⊆ component (n := n) ((Subtype.val : U → D) ⁻¹' W i) a :=
      subset_component_of_isPreconnected hHUc (fun x hx => ⟨d i,hHUr x hx⟩)
        ⟨a,haH,mem_component_self ha⟩
    have heq : (Subtype.val : U → D) ⁻¹' W i =
        closure (component (n := n) ((Subtype.val : U → D) ⁻¹' W i) a) :=
      Subset.antisymm (fun x hx => closure_mono hHK (hDense hx))
        (closure_minimal (component_subset (n := n) ((Subtype.val : U → D) ⁻¹' W i) a) hWU.isClosed)
    refine ⟨d i,a,ha,heq,?_⟩
    exact Eq.mpr (congrArg (fun S : Set U => IsComplexAnalyticallyIrreducible (n := n) S) heq)
      (isComplexAnalyticallyIrreducible_closure_component hWU ha)

end Hironaka.HironakaSimultaneousPrimeSupportNeighborhood

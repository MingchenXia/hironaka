import Hironaka.Resolution.HironakaG4OrderOneTransverseCoordinates
import Hironaka.Analytic.RankDegeneracy

set_option autoImplicit false

/-!
# Actual boundary differentials and sharp normal crossings

All boundary equations are whole ideal generators. Restricted differentials
are computed on the actual smooth carrier tangent space. The nonreduced
intersection equations are retained throughout.
Blueprint: `hironaka-g4-boundary-differential-criterion.tex`.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4BoundaryDifferentialCriterion

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense BlowupTowers NormalCrossings SimultaneousNormalCrossings
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpNestedNormalCrossingsInheritance
  HironakaG4OrderOneTransverseCoordinates RankDegeneracy BlowupFlatCoordinates
  RelativePrincipalizationSpan InvertibleIdealQuotient DerivativeIdeal BlowupSNCTransform

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual function differential read in the preferred ambient chart. -/
def chartDifferential (f : X → ℂ) (x : X) : ComplexModel n →L[ℂ] ℂ :=
  fderiv ℂ (fun w => f ((complexChartAt (n := n) x).val.symm w))
    ((complexChartAt (n := n) x).val x)

/-- Restriction of the actual differential to the actual whole-ideal tangent
space of the smooth carrier. -/
def restrictedDifferential (W : Set X) (f : X → ℂ) (x : X) :
    tangentSpaceIn (complexChartAt (n := n) x) W x →L[ℂ] ℂ :=
  (chartDifferential f x).comp (tangentSpaceIn (complexChartAt (n := n) x) W x).subtypeL

private theorem chartDifferential_eq_smul_of_eventually_mul
    {f g a : X → ℂ} {x : X} (_hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) (ha : HolomorphicAt n a x)
    (hg0 : g x = 0) (heq : f =ᶠ[𝓝 x] fun y => a y * g y) :
    chartDifferential f x = a x • chartDifferential g x := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hT : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
    have h := e.val.continuousAt_symm (e.val.map_source hx)
    simpa only [ContinuousAt, e.val.left_inv hx] using h
  have hloc : (fun w => f (e.val.symm w)) =ᶠ[𝓝 (e.val x)]
      fun w => a (e.val.symm w) * g (e.val.symm w) := hT.eventually heq
  have had := (eventually_differentiableAt_comp_symm e hx ha).self_of_nhds
  have hgd := (eventually_differentiableAt_comp_symm e hx hg).self_of_nhds
  have hprod : HasFDerivAt (fun w => a (e.val.symm w) * g (e.val.symm w))
      (a x • chartDifferential g x) (e.val x) := by
    apply (had.hasFDerivAt.mul hgd.hasFDerivAt).congr_fderiv
    ext v
    simp only [add_apply, smul_apply,
      Function.comp_apply, e.val.left_inv hx, hg0, smul_eq_mul, zero_mul, add_zero]
    rfl
  exact hloc.fderiv_eq.trans hprod.fderiv

/-- Two actual whole-ideal generators have differentials differing by a
nonzero scalar; nonreduced zero-set substitutes are not used. -/
theorem exists_nonzero_smul_differential_of_same_generator
    {I : GermIdeal n X} {f g : X → ℂ} {x : X}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hf0 : f x = 0) (hg0 : g x = 0)
    (hF : ∀ v, I.mem x v ↔ IsInSpanAt (n := n) (· = f) x v)
    (hG : ∀ v, I.mem x v ↔ IsInSpanAt (n := n) (· = g) x v)
    (hdg : chartDifferential g x ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ chartDifferential f x = c • chartDifferential g x := by
  have hfI := (hF f).mpr (isInSpanAt_self rfl hf)
  have hgI := (hG g).mpr (isInSpanAt_self rfl hg)
  obtain ⟨_hf,a,ha,hfa⟩ := isInSpanAt_eq_iff.mp ((hG f).mp hfI)
  obtain ⟨_hg,b,hb,hgb⟩ := isInSpanAt_eq_iff.mp ((hF g).mp hgI)
  have hdf := chartDifferential_eq_smul_of_eventually_mul hf hg ha hg0 hfa
  have hdg' := chartDifferential_eq_smul_of_eventually_mul hg hf hb hf0 hgb
  refine ⟨a x, ?_, hdf⟩
  intro hzero
  have hdf0 : chartDifferential f x = 0 := by
    ext v
    have h := DFunLike.congr_fun hdf v
    simpa only [smul_apply, hzero, smul_eq_mul, zero_mul, zero_apply] using h
  apply hdg
  ext v
  have h := DFunLike.congr_fun hdg' v
  simpa only [smul_apply, hdf0, zero_apply,
    smul_eq_mul, mul_zero] using h

/-- Actual finite independent holomorphic germs are retained as exact
coordinate functions of a genuine local holomorphic equivalence. -/
theorem exists_coordinates_of_holomorphicAt_independent
    {ι : Type*} [Fintype ι] (f : ι → X → ℂ) {x : X}
    (hf : ∀ i, HolomorphicAt n (f i) x) (hf0 : ∀ i, f i x = 0)
    (hli : LinearIndependent ℂ (fun i => chartDifferential (f i) x)) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
      (σ : ι ↪ Fin n),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
          ∀ i, Φ.toFun ((complexChartAt (n := n) x).val y) (σ i) = f i y := by
  classical
  let e := complexChartAt (n := n) x
  let R := Fintype.card ι
  let a : ι ≃ Fin R := Fintype.equivFin ι
  let g : Fin R → ComplexModel n → ℂ := fun i w => f (a.symm i) (e.val.symm w)
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hR : R ≤ n := by
    have h := hli.fintype_card_le_finrank
    simpa only [finrank_strongDual_complexModel] using h
  have hge : ∀ᶠ w in 𝓝 (e.val x), ∀ i, DifferentiableAt ℂ (g i) w := by
    apply eventually_all.mpr
    intro i
    exact eventually_differentiableAt_comp_symm e hx (hf (a.symm i))
  obtain ⟨N,hNsub,hNo,hxN⟩ := mem_nhds_iff.mp
    (hge.and (e.val.open_target.mem_nhds (e.val.map_source hx)))
  have hgN : ∀ i, DifferentiableOn ℂ (g i) N :=
    fun i w hw => ((hNsub hw).1 i).differentiableWithinAt
  have hg0 : ∀ i, g i (e.val x) = 0 := by
    intro i
    simpa only [g, e.val.left_inv hx] using hf0 (a.symm i)
  have hgli : LinearIndependent ℂ (fun i => fderiv ℂ (g i) (e.val x)) :=
    hli.comp a.symm a.symm.injective
  obtain ⟨φ,hφd,hφ0,hφg,_hφplane,hinj⟩ :=
    exists_coordinates_of_linearIndependent hR hNo hxN hgN hg0 hgli
  obtain ⟨Φ,hΦN,hΦF,_hΦinj⟩ :=
    exists_localHolomorphicEquivAt hNo hxN (differentiableOn_assemble hφd) hinj
  let σ : ι ↪ Fin n :=
    { toFun := fun i => ⟨n - R + (a i).val, by have := (a i).isLt; omega⟩
      inj' := by
        intro i j h
        apply a.injective
        apply Fin.ext
        have hh := congrArg Fin.val h
        dsimp at hh
        omega }
  refine ⟨Φ,σ,fun z hz => (hNsub (hΦN hz)).2,?_,?_⟩
  · rw [hΦF]
    ext k
    exact hφ0 k
  · intro y hy hyΦ i
    rw [hΦF]
    change φ (σ i) (e.val y) = f i y
    have hh := congrFun (hφg (a i)) (e.val y)
    change φ (σ i) (e.val y) = g (a i) (e.val y) at hh
    rw [hh]
    simp only [g, a.symm_apply_apply, e.val.left_inv hy]

private theorem independent_append_of_independent_restrictions
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {α β : Type*} [Fintype α] [Fintype β] (S : Submodule ℂ V)
    (L : α → V →L[ℂ] ℂ) (F : β → V →L[ℂ] ℂ)
    (hL : LinearIndependent ℂ L)
    (hR : LinearIndependent ℂ (fun b => (F b).comp S.subtypeL))
    (hzero : ∀ a, ∀ v : S, L a v = 0) :
    LinearIndependent ℂ (Sum.elim L F) := by
  classical
  rw [Fintype.linearIndependent_iff] at hL hR ⊢
  intro c hc
  have hsumR : (∑ b, c (Sum.inr b) • (F b).comp S.subtypeL) = 0 := by
    ext v
    have hh := DFunLike.congr_fun hc (v : V)
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      add_apply, sum_apply, smul_apply, hzero, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      zero_add, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      zero_apply] using hh
  have hzR := hR (fun b => c (Sum.inr b)) hsumR
  have hsumL : (∑ a, c (Sum.inl a) • L a) = 0 := by
    ext v
    have hh := DFunLike.congr_fun hc v
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      add_apply, sum_apply, smul_apply, hzR, smul_eq_mul, zero_mul,
      Finset.sum_const_zero, add_zero, zero_apply] using hh
  have hzL := hL (fun a => c (Sum.inl a)) hsumL
  intro i
  cases i with
  | inl a => exact hzL a
  | inr b => exact hzR b

/-- Actual preferred-chart differential of a true flattening coordinate. -/
theorem chartDifferential_flatCoord {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (j : Fin n) :
    chartDifferential (flatCoord Φ j) x =
      (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ Φ.toFun ((complexChartAt (n := n) x).val x)) := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hloc : (fun w => flatCoord Φ j (e.val.symm w)) =ᶠ[𝓝 (e.val x)]
      fun w => Φ.toFun w j := by
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hx)] with w hw
    change Φ.toFun (e.val (e.val.symm w)) j = Φ.toFun w j
    rw [e.val.right_inv hw]
  have hd := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  exact hloc.fderiv_eq.trans
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hd.hasFDerivAt).fderiv

private theorem independent_normal_differentials {x : X} {k : ℕ} (hk : k ≤ n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)) :
    LinearIndependent ℂ (fun i : Fin (n-k) =>
      chartDifferential (flatCoord Φ ⟨k+i.val, by have := i.isLt; omega⟩) x) := by
  classical
  let j : Fin (n-k) → Fin n := fun i => ⟨k+i.val, by have := i.isLt; omega⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp [j] at hh
    omega
  have hsurj := GeneratorMultiplicityOne.surjective_fderiv_toFun Φ Φ.center_mem_source
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  obtain ⟨v,hv⟩ := hsurj (EuclideanSpace.single (j a) (1 : ℂ))
  have hval : ∀ i : Fin (n-k), chartDifferential (flatCoord Φ (j i)) x v =
      if i = a then 1 else 0 := by
    intro i
    rw [chartDifferential_flatCoord, ContinuousLinearMap.comp_apply, hv]
    change (EuclideanSpace.single (j a) (1 : ℂ)) (j i) = _
    by_cases hi : i = a
    · subst i
      simp
    · have hji : j i ≠ j a := fun h => hi (hj h)
      simp [hi, hji]
  have hh := DFunLike.congr_fun hc v
  change (∑ i, c i • chartDifferential (flatCoord Φ (j i)) x) v = (0 : ComplexModel n →L[ℂ] ℂ) v at hh
  simpa only [sum_apply, smul_apply, hval, zero_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh

private theorem exists_unit_factor_of_same_generator
    {I : GermIdeal n X} {f g : X → ℂ} {x : X}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hf0 : f x = 0) (hg0 : g x = 0)
    (hF : ∀ v, I.mem x v ↔ IsInSpanAt (n := n) (· = f) x v)
    (hG : ∀ v, I.mem x v ↔ IsInSpanAt (n := n) (· = g) x v)
    (hdg : chartDifferential g x ≠ 0) :
    ∃ a : X → ℂ, HolomorphicAt n a x ∧ a x ≠ 0 ∧
      f =ᶠ[𝓝 x] fun y => a y * g y := by
  have hfI := (hF f).mpr (isInSpanAt_self rfl hf)
  have hgI := (hG g).mpr (isInSpanAt_self rfl hg)
  obtain ⟨_hf,a,ha,hfa⟩ := isInSpanAt_eq_iff.mp ((hG f).mp hfI)
  obtain ⟨_hg,b,hb,hgb⟩ := isInSpanAt_eq_iff.mp ((hF g).mp hgI)
  have hdf := chartDifferential_eq_smul_of_eventually_mul hf hg ha hg0 hfa
  have hdg' := chartDifferential_eq_smul_of_eventually_mul hg hf hb hf0 hgb
  refine ⟨a,ha,?_,hfa⟩
  intro hzero
  have hdf0 : chartDifferential f x = 0 := by
    ext v
    have hh := DFunLike.congr_fun hdf v
    simpa only [smul_apply, hzero, smul_eq_mul, zero_mul, zero_apply] using hh
  apply hdg
  ext v
  have hh := DFunLike.congr_fun hdg' v
  simpa only [smul_apply, hdf0, zero_apply, smul_eq_mul, mul_zero] using hh

private theorem eventually_mem_iff_generator_zero (hn : 0 < n)
    {E : List (Set X)} (hE : IsSNCDivisor n E) {x : X}
    (i : Fin E.length) (hxi : x ∈ E.get i) (f : X → ℂ)
    (hf : HolomorphicAt n f x)
    (hgen : ∀ v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = f) x v) :
    ∀ᶠ y in 𝓝 x, y ∈ E.get i ↔ f y = 0 := by
  obtain ⟨Φ,σ,_hsrc,_h0,_hinj,hA⟩ := MonomialCase.exists_snc_chart hn hE x
  have hxD := mem_flatDomain_self Φ
  let g := flatCoord Φ (σ i)
  have hg : HolomorphicAt n g x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hG : ∀ v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = g) x v :=
    fun v => MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ (hA i hxi) hxD v
  have hg0 : g x = 0 := (hA i hxi hxD.1 hxD.2).mp hxi
  have hfI := (hgen f).mpr (isInSpanAt_self rfl hf)
  have hf0 : f x = 0 := hfI.2.self_of_nhds hxi
  have hdg : chartDifferential g x ≠ 0 := by
    obtain ⟨v,hv⟩ := MemberPullback.exists_chartDeriv_flatCoord_ne_zero Φ (σ i) hxD
    intro hzero
    apply hv
    change chartDifferential g x v = 0
    rw [hzero]
    rfl
  obtain ⟨a,ha,hax,hfa⟩ := exists_unit_factor_of_same_generator hf hg hf0 hg0 hgen hG hdg
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD, hfa,
    ha.self_of_nhds.continuousAt.eventually_ne hax] with y hyD hyfa hya
  rw [hyfa, mul_eq_zero, or_iff_right hya]
  exact hA i hxi hyD.1 hyD.2

/-- Independent actual restricted boundary differentials construct the
literal native simultaneous-coordinate normal-crossings witness. -/
theorem normalCrossingsAt_of_independent_boundary_differentials (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) {x : X} (hxW : x ∈ W)
    (f : Fin E.length → X → ℂ) (hf : ∀ i, HolomorphicAt n (f i) x)
    (hgen : ∀ i v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = f i) x v)
    (hli : LinearIndependent ℂ (fun i : {i : Fin E.length // x ∈ E.get i} =>
      restrictedDifferential W (f i.val) x)) :
    normalCrossingsAt (n := n) W E x := by
  classical
  let e := complexChartAt (n := n) x
  let I := {i : Fin E.length // x ∈ E.get i}
  obtain ⟨k,hkn,_hx,Ψ,hΨsrc,hΨ0,hflat⟩ := hW.2 x hxW
  let j : Fin (n-k) → Fin n := fun a => ⟨k+a.val, by have := a.isLt; omega⟩
  let N : Fin (n-k) → X → ℂ := fun a => flatCoord Ψ (j a)
  let F : I → X → ℂ := fun i => f i.val
  have hxD := mem_flatDomain_self Ψ
  have hLN : LinearIndependent ℂ (fun a => chartDifferential (N a) x) :=
    independent_normal_differentials hkn Ψ
  have hzero : ∀ a, ∀ v : tangentSpaceIn e W x, chartDifferential (N a) x v = 0 := by
    intro a v
    exact (mem_tangentSpaceIn.mp v.property) (N a)
      (flatCoord_mem_vanishingIdeal Ψ hflat (show k ≤ (j a).val by dsimp [j]; omega) hxD)
  let H : Fin (n-k) ⊕ I → X → ℂ := Sum.elim N F
  have hLI : LinearIndependent ℂ (fun i => chartDifferential (H i) x) := by
    have heq : (fun i => chartDifferential (H i) x) =
        Sum.elim (fun a => chartDifferential (N a) x) (fun i => chartDifferential (F i) x) := by
      funext i
      cases i <;> rfl
    rw [heq]
    exact independent_append_of_independent_restrictions (tangentSpaceIn e W x)
      (fun a => chartDifferential (N a) x) (fun i => chartDifferential (F i) x)
      hLN hli hzero
  have hHhol : ∀ i, HolomorphicAt n (H i) x := by
    rintro (a | i)
    · exact holomorphicAt_flatCoord Ψ (j a) hxD
    · exact hf i.val
  have hH0 : ∀ i, H i x = 0 := by
    rintro (a | i)
    · change Ψ.toFun (e.val x) (j a) = 0
      exact congrArg (fun v : ComplexModel n => v (j a)) hΨ0
    · have hFi := (hgen i.val (f i.val)).mpr (isInSpanAt_self rfl (hf i.val))
      exact hFi.2.self_of_nhds i.property
  obtain ⟨Θ,σ,hΘsrc,hΘ0,hΘeq⟩ :=
    exists_coordinates_of_holomorphicAt_independent H hHhol hH0 hLI
  have hsup : ∀ᶠ y in 𝓝 x, ∀ i : I, y ∈ E.get i.val ↔ f i.val y = 0 := by
    apply eventually_all.mpr
    intro i
    exact eventually_mem_iff_generator_zero hn hE i.val i.property (f i.val)
      (hf i.val) (hgen i.val)
  obtain ⟨O,hOsub,hOo,hxO⟩ := mem_nhds_iff.mp hsup
  let s : Set (ComplexModel n) := Ψ.source ∩ (e.val.target ∩ e.val.symm ⁻¹' O)
  have hs : IsOpen s := Ψ.isOpen_source.inter (e.val.isOpen_inter_preimage_symm hOo)
  have hxs : e.val x ∈ Θ.source ∩ s := by
    refine ⟨Θ.center_mem_source, Ψ.center_mem_source, e.val.map_source (mem_complexChartAt_source x), ?_⟩
    change e.val.symm (e.val x) ∈ O
    rw [e.val.left_inv (mem_complexChartAt_source x)]
    exact hxO
  let Θ' := Θ.restrict s hs (e.val x) hxs
  let S₀ : Finset (Fin n) := Finset.univ.image fun a : Fin (n-k) => σ (Sum.inl a)
  let S : Fin E.length → Finset (Fin n) := fun i =>
    if hi : x ∈ E.get i then {σ (Sum.inr ⟨i,hi⟩)} else ∅
  refine ⟨S₀,S,⟨Θ',fun z hz => hΘsrc hz.1,hΘ0,?_⟩,?_⟩
  · rintro (_ | i) hxi y hy hyΘ
    · change y ∈ W ↔ Θ.toFun (e.val y) ∈ coordSubspace S₀
      have hyΨ : e.val y ∈ Ψ.source := hyΘ.2.1
      constructor
      · intro hyW r hr
        obtain ⟨a,_ha,rfl⟩ := Finset.mem_image.mp hr
        rw [hΘeq hy hyΘ.1]
        exact (hflat hy hyΨ).mp hyW (j a) (by dsimp [j]; omega)
      · intro hyN
        apply (hflat hy hyΨ).mpr
        intro r hr
        let a : Fin (n-k) := ⟨r.val-k, by have := r.isLt; omega⟩
        have hja : j a = r := Fin.ext (by dsimp [j,a]; omega)
        have hh := hyN (σ (Sum.inl a))
          (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)
        rw [hΘeq hy hyΘ.1] at hh
        change flatCoord Ψ (j a) y = 0 at hh
        rw [hja] at hh
        exact hh
    · change y ∈ E.get i ↔ Θ.toFun (e.val y) ∈ coordSubspace (S i)
      change x ∈ E.get i at hxi
      have hyO : y ∈ O := by
        have hh : e.val.symm (e.val y) ∈ O := hyΘ.2.2.2
        rwa [e.val.left_inv hy] at hh
      have hSi : S i = {σ (Sum.inr ⟨i,hxi⟩)} := by simp only [S, dif_pos hxi]
      rw [hSi, mem_coordSubspace_singleton, hΘeq hy hyΘ.1]
      exact hOsub hyO ⟨i,hxi⟩
  · intro i hi
    simp only [S, dif_pos hi, Finset.card_singleton]

/-- Every free actual carrier coordinate has its genuine native tangent basis vector. -/
theorem exists_tangent_free_coordinate_vector {W : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (S₀ : Finset (Fin n))
    (hflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ W ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace S₀))
    (j : Fin n) (hj : j ∉ S₀) :
    ∃ v : tangentSpaceIn (complexChartAt (n := n) x) W x,
      ∀ r : Fin n, chartDifferential (flatCoord Φ r) x v =
        (EuclideanSpace.single j (1 : ℂ)) r := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := h0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hdi := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)
  let v₀ := fderiv ℂ Φ.invFun 0 (EuclideanSpace.single j (1 : ℂ))
  have hv : v₀ ∈ tangentSpaceIn e W x := by
    apply mem_tangentSpaceIn.mpr
    intro g hg
    have hge := (eventually_differentiableAt_comp_symm e hx hg.1).self_of_nhds
    have hge' : DifferentiableAt ℂ (g ∘ e.val.symm) (Φ.invFun 0) := by
      rw [hinv0]
      exact hge
    let P : ℂ → X := fun τ => e.val.symm (Φ.invFun (τ • EuclideanSpace.single j (1 : ℂ)))
    have hline : Tendsto (fun τ : ℂ => τ • EuclideanSpace.single j (1 : ℂ)) (𝓝 0) (𝓝 0) := by
      have hh := (continuous_id.smul continuous_const :
        Continuous fun τ : ℂ => τ • EuclideanSpace.single j (1 : ℂ)).tendsto 0
      change Tendsto (fun τ : ℂ => τ • EuclideanSpace.single j (1 : ℂ))
        (𝓝 0) (𝓝 ((0 : ℂ) • EuclideanSpace.single j (1 : ℂ))) at hh
      rw [zero_smul] at hh
      exact hh
    have hPi : Tendsto (fun z => e.val.symm (Φ.invFun z)) (𝓝 0) (𝓝 x) := by
      have hec := e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))
      have hh := hec.tendsto.comp hdi.continuousAt.tendsto
      change Tendsto (fun z => e.val.symm (Φ.invFun z)) (𝓝 0)
        (𝓝 (e.val.symm (Φ.invFun 0))) at hh
      rw [hinv0, e.val.left_inv hx] at hh
      exact hh
    have hP : Tendsto P (𝓝 0) (𝓝 x) := hPi.comp hline
    have hzero : (fun τ => g (P τ)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hline.eventually (Φ.isOpen_target.mem_nhds h0t), hP.eventually hg.2]
        with τ hτ hgτ
      apply hgτ
      have hzΦ := Φ.mapsTo_invFun hτ
      have hze := hsrc hzΦ
      apply (hflat (e.val.map_target hze) (by rw [e.val.right_inv hze]; exact hzΦ)).mpr
      rw [e.val.right_inv hze, Φ.right_inv _ hτ]
      intro r hr
      have hrj : r ≠ j := fun h => hj (h ▸ hr)
      simp [hrj]
    have hdline : HasDerivAt (fun τ : ℂ => τ • EuclideanSpace.single j (1 : ℂ))
        (EuclideanSpace.single j (1 : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const (EuclideanSpace.single j (1 : ℂ))
    have hgf := hge'.hasFDerivAt.comp 0 hdi.hasFDerivAt
    have hgf' : HasFDerivAt ((g ∘ e.val.symm) ∘ Φ.invFun)
        ((fderiv ℂ (g ∘ e.val.symm) (Φ.invFun 0)).comp (fderiv ℂ Φ.invFun 0))
        ((0 : ℂ) • EuclideanSpace.single j (1 : ℂ)) := by
      rw [zero_smul]
      exact hgf
    have hcomp := hgf'.comp_hasDerivAt 0 hdline
    have hconst : HasDerivAt (fun τ => g (P τ)) 0 0 :=
      (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero
    have hh := hcomp.unique hconst
    change fderiv ℂ (g ∘ e.val.symm) (e.val x)
      (fderiv ℂ Φ.invFun 0 (EuclideanSpace.single j (1 : ℂ))) = 0
    simpa only [ContinuousLinearMap.comp_apply, hinv0] using hh
  have hdo := Φ.toFun_holomorphic.differentiableAt
    (Φ.isOpen_source.mem_nhds (Φ.mapsTo_invFun h0t))
  have hloc : (Φ.toFun ∘ Φ.invFun) =ᶠ[𝓝 (0 : ComplexModel n)] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t] with w hw
    exact Φ.right_inv w hw
  have hright : (fderiv ℂ Φ.toFun (e.val x)).comp (fderiv ℂ Φ.invFun 0) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    have hh := (hdo.hasFDerivAt.comp 0 hdi.hasFDerivAt).fderiv
    rw [hloc.fderiv_eq, fderiv_id] at hh
    simpa only [hinv0] using hh.symm
  refine ⟨⟨v₀,hv⟩, ?_⟩
  intro r
  rw [chartDifferential_flatCoord, ContinuousLinearMap.comp_apply]
  have hh := congrArg (fun w : ComplexModel n => w r)
    (DFunLike.congr_fun hright (EuclideanSpace.single j (1 : ℂ)))
  exact hh

/-- The literal original normal-crossings predicate is equivalent to
independence of all actual incident boundary differentials on the actual
carrier tangent space. Every equation generates the whole original ideal. -/
theorem normalCrossingsAt_iff_independent_boundary_differentials (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    {x : X} (hxW : x ∈ W)
    (f : Fin E.length → X → ℂ) (hf : ∀ i, HolomorphicAt n (f i) x)
    (hgen : ∀ i v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = f i) x v) :
    normalCrossingsAt (n := n) W E x ↔
      LinearIndependent ℂ (fun i : {i : Fin E.length // x ∈ E.get i} =>
        restrictedDifferential W (f i.val) x) := by
  classical
  constructor
  · intro hNC
    have hnot : ∀ i : Fin E.length, x ∈ E.get i →
        ¬∀ᶠ y in 𝓝 x, y ∈ W → y ∈ E.get i := by
      intro i _hi hcontains
      have hfreq := mem_closure_iff_frequently.mp (hdense hxW)
      obtain ⟨y,⟨hyW,hyE⟩,hyH⟩ := (hfreq.and_eventually hcontains).exists
      exact hyE (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hyH hyW⟩)
    obtain ⟨S₀,S,⟨Φ,hsrc,h0,hfam⟩,hfree⟩ :=
      exists_actual_free_family_of_germ_noncontainment hxW hNC hnot
    let pick : Finset (Fin n) → Fin n := fun s =>
      if h : s.Nonempty then s.min' h else ⟨0,hn⟩
    have hpick : ∀ s : Finset (Fin n), s.card = 1 → s = {pick s} := by
      intro s hs
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hs
      simp [pick]
    let p : Fin E.length → Fin n := fun i => pick (S i)
    have hSi : ∀ i, x ∈ E.get i → S i = {p i} := fun i hi => hpick (S i) (hfree i hi).1
    have hp : ∀ i, x ∈ E.get i → p i ∉ S₀ := by
      intro i hi
      have hh := (hfree i hi).2
      rw [hSi i hi] at hh
      exact Finset.disjoint_singleton_left.mp hh
    have hxD := mem_flatDomain_self Φ
    have hA : ∀ i, x ∈ E.get i → ∀ {y : X},
        y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) (p i) = 0) := by
      intro i hi y hy hyΦ
      have hh := hfam (some i) hi hy hyΦ
      change (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i)) at hh
      rwa [hSi i hi, mem_coordSubspace_singleton] at hh
    have hpinj : Set.InjOn p {i | x ∈ E.get i} := by
      intro i hi j hj hpij
      apply eq_of_eventually_mem_iff hE hi hj
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y hy
      rw [hA i hi hy.1 hy.2, hA j hj hy.1 hy.2, hpij]
    let I := {i : Fin E.length // x ∈ E.get i}
    have hscalar : ∀ i : I, ∃ c : ℂ, c ≠ 0 ∧
        chartDifferential (f i.val) x = c • chartDifferential (flatCoord Φ (p i.val)) x := by
      intro i
      have hg := holomorphicAt_flatCoord Φ (p i.val) hxD
      have hfI := (hgen i.val (f i.val)).mpr (isInSpanAt_self rfl (hf i.val))
      have hf0 := hfI.2.self_of_nhds i.property
      have hg0 : flatCoord Φ (p i.val) x = 0 :=
        (hA i.val i.property hxD.1 hxD.2).mp i.property
      have hdg : chartDifferential (flatCoord Φ (p i.val)) x ≠ 0 := by
        obtain ⟨v,hv⟩ := MemberPullback.exists_chartDeriv_flatCoord_ne_zero Φ (p i.val) hxD
        intro hzero
        apply hv
        change chartDifferential (flatCoord Φ (p i.val)) x v = 0
        rw [hzero]
        rfl
      exact exists_nonzero_smul_differential_of_same_generator (hf i.val) hg hf0 hg0
        (hgen i.val) (fun v => MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ
          (hA i.val i.property) hxD v) hdg
    choose c hc hdf using hscalar
    rw [Fintype.linearIndependent_iff]
    intro a ha i₀
    obtain ⟨v,hv⟩ := exists_tangent_free_coordinate_vector Φ hsrc h0 S₀
      (hfam none hxW) (p i₀.val) (hp i₀.val i₀.property)
    have heval : ∀ i : I, restrictedDifferential W (f i.val) x v =
        if i = i₀ then c i else 0 := by
      intro i
      change chartDifferential (f i.val) x v = _
      rw [hdf i, smul_apply, hv (p i.val)]
      by_cases hii : i = i₀
      · subst i
        simp only [smul_eq_mul]
        simp
      · have hpi : p i.val ≠ p i₀.val := by
          intro hh
          exact hii (Subtype.ext (hpinj i.property i₀.property hh))
        simp [hii, hpi, smul_eq_mul]
    let ev : (tangentSpaceIn (complexChartAt (n := n) x) W x →L[ℂ] ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun L => L v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hh := congrArg ev ha
    simp only [map_sum, map_smul, map_zero] at hh
    change (∑ i : I, a i * restrictedDifferential W (f i.val) x v) = 0 at hh
    have haz : a i₀ * c i₀ = 0 := by
      rw [Finset.sum_eq_single i₀] at hh
      · simpa only [heval, if_true] using hh
      · intro i _hi hne
        rw [heval, if_neg hne, mul_zero]
      · simp
    exact (mul_eq_zero.mp haz).resolve_right (hc i₀)
  · exact normalCrossingsAt_of_independent_boundary_differentials hn hW hE hxW f hf hgen

end

end Hironaka.HironakaG4BoundaryDifferentialCriterion

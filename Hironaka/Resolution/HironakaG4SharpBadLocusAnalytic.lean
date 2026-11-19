import Hironaka.Resolution.HironakaG4BoundaryDifferentialCriterion
import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.Analytic.ConstantRankImage
import Hironaka.Resolution.HironakaSharpOriginalAllBoundaryCentre

set_option autoImplicit false

/-!
# The entire actual original sharp bad locus is analytic

The exact finite-subset formula retains the original whole boundary ideal
functions and their differentials on the actual carrier tangent space. Genuine
SNC charts produce all local whole-ideal dictionaries. Native analytic rank
loci then recognize the literal sharp bad locus in arbitrary smooth dimension.
Blueprint: `hironaka-g4-sharp-bad-locus-analytic.tex`.
No transformed invariant or termination statement is asserted here.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SharpBadLocusAnalytic

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4BoundaryDifferentialCriterion RankDegeneracy BlowupFlatCoordinates
  AnalyticDimensionBasics AnalyticSubsetOpens BlowupRestrictOpen
  InvertibleIdealQuotient MemberPullback RelativePrincipalizationSpan

variable {n : ℕ} {X : CMfd.{u} n}


/-- Coordinate functionals detect exactly the full actual linear-map rank. -/
theorem independent_coordinates_iff_finrank_range
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {r : ℕ} (L : V →L[ℂ] ComplexModel r) :
    LinearIndependent ℂ (fun j : Fin r => (EuclideanSpace.proj j).comp L) ↔
      Module.finrank ℂ (LinearMap.range L.toLinearMap) = r := by
  let rows : Fin r → V →L[ℂ] ℂ := fun j => (EuclideanSpace.proj j).comp L
  have hker : (⨅ j, LinearMap.ker (rows j).toLinearMap : Submodule ℂ V) =
      LinearMap.ker L.toLinearMap := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h
      ext j
      exact h j
    · intro h j
      exact congrArg (fun w : ComplexModel r => w j) h
  have hrow := finrank_span_add_finrank_iInf_ker rows
  rw [hker] at hrow
  have hrange := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
  have heq : Module.finrank ℂ (Submodule.span ℂ (range rows)) =
      Module.finrank ℂ (LinearMap.range L.toLinearMap) := by omega
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin r) = Module.finrank ℂ (Submodule.span ℂ (range rows)) ↔ _
  rw [Fintype.card_fin, heq, eq_comm]

/-- Native whole-ideal SNC equations on one genuine common neighbourhood. -/
theorem exists_actual_local_boundary_generators (hn : 0 < n)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (x : X) :
    ∃ (U : Opens X) (f : Fin E.length → X → ℂ), x ∈ U ∧
      (∀ y ∈ U, ∀ i, HolomorphicAt n (f i) y) ∧
      ∀ y ∈ U, ∀ i v, (vanishingIdeal (n := n) (E.get i)).mem y v ↔
        IsInSpanAt (n := n) (· = f i) y v := by
  classical
  obtain ⟨S,⟨Φ,hsrc,_h0,hflat⟩,hcard,_hinj⟩ := hE.2 x
  let pick : Fin E.length → Fin n := fun i =>
    if h : (S i).Nonempty then (S i).min' h else ⟨0,hn⟩
  have hpick : ∀ i, x ∈ E.get i → S i = {pick i} := by
    intro i hi
    have h1 := hcard i hi
    have hne : (S i).Nonempty := Finset.card_pos.mp (by omega)
    have hm : pick i ∈ S i := by simp only [pick, dif_pos hne]; exact Finset.min'_mem _ _
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
    have : pick i = a := by simpa only [ha,Finset.mem_singleton] using hm
    simp only [this,ha]
  obtain ⟨O,hOsub,hOo,hxO⟩ := mem_nhds_iff.mp
    (eventually_incident_subset (fun i : Fin E.length => E.get i)
      (fun i => hE.1 _ (List.get_mem E i)) x)
  let U : Opens X := ⟨flatDomain Φ ∩ O,(isOpen_flatDomain Φ).inter hOo⟩
  let f : Fin E.length → X → ℂ := fun i =>
    if x ∈ E.get i then flatCoord Φ (pick i) else fun _ => 1
  refine ⟨U,f,⟨mem_flatDomain_self Φ,hxO⟩,?_,?_⟩
  · intro y hy i
    dsimp only [f]
    split_ifs
    · exact holomorphicAt_flatCoord Φ _ hy.1
    · exact holomorphicAt_const 1
  · intro y hy i v
    dsimp only [f]
    split_ifs with hi
    · apply vanishingIdeal_mem_iff_flatCoord Φ ?_ hy.1 v
      intro z hz hzΦ
      have hh := hflat i hi hz hzΦ
      rw [hpick i hi] at hh
      change (z ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ coordSubspace {pick i}) at hh
      simpa only [coordSubspace,mem_ofPred_eq,Finset.mem_singleton,forall_eq] using hh
    · rw [isInSpanAt_one_iff]
      refine ⟨fun hv => hv.1, fun hv => ⟨hv,?_⟩⟩
      have hyi : y ∉ E.get i := fun hyi => hi (hOsub hy.2 i hyi)
      filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hyi] with z hz hzi
      exact False.elim (hz hzi)

/-- Actual restricted coordinate differentials have full rank exactly when the map does. -/
theorem independent_restricted_coordinates_iff_rank_eq {r : ℕ}
    (W : Set X) (F : X → ComplexModel r) {x : X}
    (hF : MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) F x) :
    LinearIndependent ℂ (fun j : Fin r =>
      restrictedDifferential W (fun y => F y j) x) ↔
      rankAt (n := n) (n' := r) F W x = r := by
  let e := complexChartAt (n := n) x
  let T := tangentSpaceIn e W x
  let D : ComplexModel n →L[ℂ] ComplexModel r :=
    fderiv ℂ (fun w => F (e.val.symm w)) (e.val x)
  let L := D.comp T.subtypeL
  have hFd := differentiableAt_chartReading e (complexChartAt (n := r) (F x))
    (mem_complexChartAt_source x) (mem_complexChartAt_source (F x)) hF
  change DifferentiableAt ℂ (fun w => F (e.val.symm w)) (e.val x) at hFd
  have hcoords : (fun j : Fin r => restrictedDifferential W (fun y => F y j) x) =
      (fun j : Fin r => (EuclideanSpace.proj j).comp L) := by
    funext j
    have hc := ((EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt.comp (e.val x)
      hFd.hasFDerivAt).fderiv
    change fderiv ℂ (fun w => F (e.val.symm w) j) (e.val x) =
      (EuclideanSpace.proj j).comp D at hc
    change (fderiv ℂ (fun w => F (e.val.symm w) j) (e.val x)).comp T.subtypeL = _
    rw [hc]
    rfl
  have hmap : T.map D.toLinearMap = LinearMap.range L.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w,hw,hv⟩
      exact ⟨⟨w,hw⟩,hv⟩
    · rintro ⟨w,hw⟩
      exact ⟨w,w.property,hw⟩
  rw [hcoords,independent_coordinates_iff_finrank_range]
  change Module.finrank ℂ (LinearMap.range L.toLinearMap) = r ↔
    Module.finrank ℂ (T.map D.toLinearMap) = r
  rw [hmap]

/-- The actual finite map formed from the original selected boundary functions. -/
def subsetBoundaryMap {I : Type*} [DecidableEq I] (f : I → X → ℂ) (J : Finset I) :
    X → ComplexModel J.card := fun y =>
  WithLp.toLp 2 (fun j => f (J.equivFin.symm j).val y)

private theorem mdifferentiableAt_of_coordinates {r : ℕ} {F : X → ComplexModel r} {x : X}
    (h : ∀ i, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun y => F y i) x) :
    MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) F x := by
  have hF : F = fun p => ∑ i, (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))) (F p i) := by
    funext p
    ext l
    simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
      WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      EuclideanSpace.single]
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  rw [hF]
  have heq : (fun p => ∑ i, (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))) (F p i)) =
      ∑ i, fun p => (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
        (EuclideanSpace.single i (1 : ℂ))) (F p i) := by funext p; simp
  rw [heq]
  exact MDifferentiableAt.sum fun i _ =>
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (EuclideanSpace.single i (1 : ℂ))).mdifferentiableAt.comp x (h i)

private theorem independent_subset_iff_rank_eq {I : Type*} [DecidableEq I]
    (W : Set X) (f : I → X → ℂ) (J : Finset I) {x : X}
    (hf : ∀ i, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i) x) :
    LinearIndependent ℂ (fun i : J => restrictedDifferential W (f i.val) x) ↔
      rankAt (n := n) (n' := J.card) (subsetBoundaryMap f J) W x = J.card := by
  have hF : MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel J.card)
      (subsetBoundaryMap f J) x := mdifferentiableAt_of_coordinates fun j => hf _
  have heq := independent_restricted_coordinates_iff_rank_eq W (subsetBoundaryMap f J) hF
  have hli := linearIndependent_equiv (R := ℂ) J.equivFin.symm
    (f := fun i : J => restrictedDifferential W (f i.val) x)
  exact hli.symm.trans heq

private theorem rankAt_le_target {r : ℕ} (F : X → ComplexModel r) (W : Set X) (x : X) :
    rankAt (n := n) (n' := r) F W x ≤ r := by
  unfold rankAt rankIn
  exact (Submodule.finrank_le _).trans_eq (by simp)

/-- Both inclusions of the exact finite-subset rank-degeneracy formula.
The selected equations are the original whole ideal generators. -/
theorem originalSharpBadLocus_eq_rank_union (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    (q : ℕ) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x q)
    (f : Fin E.length → X → ℂ) (hf : ∀ i x, HolomorphicAt n (f i) x)
    (hgen : ∀ x i v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = f i) x v) :
    originalSharpBadLocus (n := n) W E =
      ⋃ J : Finset (Fin E.length), BoundaryCount.memberInter E J ∩
        rankDegeneracyLocus n J.card (subsetBoundaryMap f J) W q J.card := by
  classical
  ext x
  constructor
  · rintro ⟨hxW,hbad⟩
    let J : Finset (Fin E.length) := Finset.univ.filter fun i => x ∈ E.get i
    have hnc := normalCrossingsAt_iff_independent_boundary_differentials
      hn hW hE hdense hxW f (fun i => hf i x) (hgen x)
    have hdep : ¬LinearIndependent ℂ (fun i : J => restrictedDifferential W (f i.val) x) := by
      intro hli
      apply hbad
      apply hnc.mpr
      let e : {i : Fin E.length // x ∈ E.get i} → J := fun i =>
        ⟨i.val,by simp only [J,Finset.mem_filter,Finset.mem_univ,true_and]; exact i.property⟩
      exact hli.comp e (fun i j h => Subtype.ext
        (congrArg (fun z : J => z.val) h))
    have hne : rankAt (n := n) (n' := J.card) (subsetBoundaryMap f J) W x ≠ J.card :=
      fun h => hdep ((independent_subset_iff_rank_eq W f J (fun i => (hf i x).self_of_nhds)).mpr h)
    have hlt : rankAt (n := n) (n' := J.card) (subsetBoundaryMap f J) W x < J.card :=
      lt_of_le_of_ne (rankAt_le_target _ _ _) hne
    refine mem_iUnion.mpr ⟨J,?_,Or.inr ⟨hreg x hxW,hlt⟩⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    obtain ⟨J,hJ,hdeg⟩ := mem_iUnion.mp hx
    have hxW := rankDegeneracyLocus_subset (subsetBoundaryMap f J) W q J.card hdeg
    have hlt : rankAt (n := n) (n' := J.card) (subsetBoundaryMap f J) W x < J.card := by
      rcases hdeg with hs | hr
      · exact False.elim (hs.2 (hreg x hxW))
      · exact hr.2
    refine ⟨hxW,?_⟩
    intro hNC
    have hli := (normalCrossingsAt_iff_independent_boundary_differentials
      hn hW hE hdense hxW f (fun i => hf i x) (hgen x)).mp hNC
    let e : J → {i : Fin E.length // x ∈ E.get i} := fun i => ⟨i.val,hJ i.val i.property⟩
    have hliJ : LinearIndependent ℂ (fun i : J => restrictedDifferential W (f i.val) x) :=
      hli.comp e (fun i j h => Subtype.ext
        (congrArg (fun z : {i : Fin E.length // x ∈ E.get i} => z.val) h))
    have hr := (independent_subset_iff_rank_eq W f J (fun i => (hf i x).self_of_nhds)).mp hliJ
    omega

private theorem analytic_sharpBad_of_entire_generators (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    (q : ℕ) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x q)
    (f : Fin E.length → X → ℂ) (hf : ∀ i x, HolomorphicAt n (f i) x)
    (hgen : ∀ x i v, (vanishingIdeal (n := n) (E.get i)).mem x v ↔
      IsInSpanAt (n := n) (· = f i) x v) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W E) := by
  classical
  rw [originalSharpBadLocus_eq_rank_union hn hW hE hdense q hreg f hf hgen]
  have hA := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW
  have hpure : IsPureDim (n := n) W q := fun y k hy =>
    RegularPointDimension.eq_of_regularAtDim hy (hreg y hy.2.1)
  have hp (J : Finset (Fin E.length)) :
      IsComplexAnalyticSubset (n := n) (BoundaryCount.memberInter E J ∩
        rankDegeneracyLocus n J.card (subsetBoundaryMap f J) W q J.card) := by
    apply (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (BoundaryCount.isClosedSubmanifold_memberInter hn hE J)).inter
    apply isComplexAnalyticSubset_rankDegeneracyLocus hA hpure
    intro y
    exact mdifferentiableAt_of_coordinates fun j => (hf _ y).self_of_nhds
  have hu := ConstantRankImage.isComplexAnalyticSubset_biUnion
    (Finset.univ : Finset (Finset (Fin E.length))) (fun J _ => hp J)
  simpa only [Finset.mem_univ,iUnion_true] using hu

/-- The entire literal original sharp bad locus is analytic, in arbitrary smooth
carrier dimension and for every finite genuine SNC boundary. -/
theorem isComplexAnalyticSubset_originalSharpBadLocus (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    (q : ℕ) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x q) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W E) := by
  classical
  apply isComplexAnalyticSubset_of_forall_opens
  intro x
  obtain ⟨U,f,hxU,hf,hgen⟩ := exists_actual_local_boundary_generators hn hE x
  let WU : Set U := (Subtype.val : U → X) ⁻¹' W
  let EU : List (Set U) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let c : Fin EU.length → Fin E.length := Fin.cast (List.length_map _)
  let fU : Fin EU.length → U → ℂ := fun i => f (c i) ∘ Subtype.val
  have hWU : IsClosedSubmanifold n WU := isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val U) continuous_subtype_val hE
  have htotal : (Subtype.val : U → X) ⁻¹' (⋃ A ∈ E, A) = ⋃ A ∈ EU, A := by
    ext y
    constructor
    · intro hy
      obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨(Subtype.val : U → X) ⁻¹' A,
        List.mem_map.mpr ⟨A,hA,rfl⟩,hyA⟩
    · intro hy
      obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hy
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hA
      exact mem_iUnion₂.mpr ⟨B,hB,hyA⟩
  have hDenseU : WU ⊆ closure (WU \ ⋃ A ∈ EU, A) := by
    intro y hy
    have hcl : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ A ∈ E, A) := hdense hy
    have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ A ∈ E, A)
    have hlocal := (Set.ext_iff.mp he y).mp hcl
    rw [preimage_sdiff] at hlocal
    change y ∈ closure (WU \ (Subtype.val : U → X) ⁻¹' (⋃ A ∈ E, A)) at hlocal
    rw [htotal] at hlocal
    exact hlocal
  have hRegU : ∀ y ∈ WU, RegularAtDim (n := n) WU y q :=
    fun y hy => regularAtDim_preimage_val_iff.mpr (hreg y hy)
  have hfU : ∀ i y, HolomorphicAt n (fU i) y := fun i y =>
    (holomorphicAt_comp_val_iff U).mpr (hf y y.property (c i))
  have hgenU : ∀ y i v, (vanishingIdeal (n := n) (EU.get i)).mem y v ↔
      IsInSpanAt (n := n) (· = fU i) y v := by
    intro y i v
    change (vanishingIdeal (n := n)
      ((E.map ((Subtype.val : U → X) ⁻¹' ·)).get i)).mem y v ↔ _
    rw [get_map_preimage,←SmoothCentreHomogeneity.pullback_val_vanishingIdeal U]
    exact pullback_mem_iff_of_generator contMDiff_subtype_val
      (hf y y.property (c i)) (hgen y y.property (c i)) v
  have ha := analytic_sharpBad_of_entire_generators (X := CMfd.of (n := n) U)
    hn hWU hEU hDenseU q hRegU fU hfU hgenU
  have heq : originalSharpBadLocus (n := n) WU EU =
      (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
    ext y
    exact and_congr Iff.rfl (not_congr HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff)
  exact ⟨U,hxU,heq ▸ ha⟩

/-- Actual density makes the literal bad locus thin in the actual pure carrier. -/
theorem dimLE_originalSharpBadLocus
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hdense : W ⊆ closure (W \ ⋃ A ∈ E, A))
    (q : ℕ) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x q) :
    DimLE (n := n) (originalSharpBadLocus (n := n) W E) (q-1) := by
  have hsub := originalSharpBadLocus_subset_boundary (E := E) hW
  apply ThinDimensionDrop.dimLE_pred_of_thin
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW)
    (hsub.trans inter_subset_left)
  · intro O hO hOW
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxO,hxW⟩
    obtain ⟨y,hyO,hyW,hyE⟩ := mem_closure_iff.mp (hdense hxW) O hO hxO
    exact hyE (hsub (hOW ⟨hyO,hyW⟩)).2
  · intro x k hx
    exact (RegularPointDimension.eq_of_regularAtDim hx (hreg x hx.2.1)).le

end

end Hironaka.HironakaG4SharpBadLocusAnalytic

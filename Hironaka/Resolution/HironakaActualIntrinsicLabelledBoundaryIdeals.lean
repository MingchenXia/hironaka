import Hironaka.Resolution.HironakaActualIntrinsicCarrierDerivationTransport
import Hironaka.Invariant.MemberPullback

/-! The ENTIRE original labelled boundary ideal images on the TRUE native carrier stalk. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicLabelledBoundaryIdeals
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.RegularLocusDense HolGerm
  BlowupTowers NormalCrossings BlowupFlatCoordinates RelativePrincipalizationSpan GiraudAlong
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualOpenIntrinsicHS HironakaActualAnalyticSubspaceIntrinsicHS
  HironakaActualIntrinsicLogQuotientDictionary HironakaActualIntrinsicCarrierDerivationTransport
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaReducedComplexAnalyticSpaces

variable {n : ℕ} {X : CMfd.{0} n}

/-- The actual Cartier-restriction ideal is the IMAGE of the original ambient ideal,
along the TRUE native inclusion; its index is the FULL original boundary list. -/
def actualLabelledBoundaryTraceIdeal (N : Set X) (E : List (Set X))
    (i : Fin E.length) (p : N) : Ideal (((actualSubspaceSheaf (n := n) N).presheaf.stalk p).carrier) :=
  Ideal.map ((actualSubspaceInclusion (n := n) N).stalkMap p).hom
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val)

/-- Every original label is retained; an active off-divisor label has the SAME shifted unit germ. -/
def labelledParameterBoundaryGerm {l k : ℕ} (τ : Fin l → Option (Fin k))
    (v : ComplexModel k) (i : Fin l) : HolGerm (ComplexModel k) :=
  match τ i with
  | none => 1
  | some j => HolGerm.constHom (v j) + coordinateGerm j

/-- The PUBLIC coordinate-hyperplane membership mother yields the ENTIRE actual native ideal. -/
theorem actualWholeHyperplaneStalkIdeal_eq_span {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {A : Set X} {t : Fin n}
    (hflat : ∀ p ∈ flatDomain Φ, p ∈ A ↔ flatCoord Φ t p = 0)
    (p : X) (hp : p ∈ flatDomain Φ) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) p =
      Ideal.span {actualOriginalFunctionGerm p (flatCoord Φ t) (holomorphicAt_flatCoord Φ t hp)} := by
  let G : Fin 1 → X → ℂ := fun _ => flatCoord Φ t
  have hG : ∀ i, HolomorphicAt n (G i) p := fun _ => holomorphicAt_flatCoord Φ t hp
  have hgen : ∀ g, (vanishingIdeal (n := n) A).mem p g ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) p g := by
    intro g
    exact (MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ
      (fun hy hΦ => hflat _ ⟨hy,hΦ⟩) hp g).trans
      (MemberPullback.isInSpanAt_range_one_iff (flatCoord Φ t) g).symm
  rw [actualWholeSheafStalkIdeal_eq_map_chart,
    wholeChartStalkIdeal_eq_actual_generator_span _ p G hG hgen,
    Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  calc
    _ = Set.range (fun _ : Fin 1 =>
        actualOriginalFunctionGerm p (flatCoord Φ t) (holomorphicAt_flatCoord Φ t hp)) := by
      apply congrArg Set.range
      funext i
      apply (actualStalkChartEquiv (n := n) p).injective
      change actualStalkChartEquiv (n := n) p
        ((actualStalkChartEquiv (n := n) p).symm
          (chartTranslatedGerm p p (mem_chart_source _ p) (G i) (hG i))) = _
      rw [RingEquiv.apply_symm_apply,actualOriginalFunctionGerm_chart]
    _ = _ := by simp

/-- The actual native parameter pullback of an original flat coordinate is its full shifted germ. -/
theorem parameter_flatCoord_germ {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hk : k ≤ n) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (v : parameterOpen Φ k) (j : Fin k) :
    parameterGermPullback Φ k hsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (flatCoord Φ (j.castLE hk))
        (holomorphicAt_flatCoord Φ (j.castLE hk)
          (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1)) =
      HolGerm.constHom (v.val j) + coordinateGerm j := by
  have hcoord : HolomorphicAt k (fun w : ComplexModel k => w j) v.val :=
    Eventually.of_forall fun w => mdifferentiableAt_iff_differentiableAt.mpr
      (PiLp.proj 2 (fun _ : Fin k => ℂ) j).differentiableAt
  have hcoordOn := hcoord.comp_contMDiff
    (Eventually.of_forall fun _ => (contMDiff_subtype_val :
      ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞
        (Subtype.val : parameterOpen Φ k → ComplexModel k)).contMDiffAt)
  have hval := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : parameterOpen Φ k → ComplexModel k)) contMDiff_subtype_val v
    (fun w : ComplexModel k => w j) hcoord
  rw [actualHolomorphicGermPullback_val] at hval
  change actualStalkChartEquiv (n := k) v
    ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k)
      (parameterMapOn_contMDiff Φ k hsrc)).stalkMap v _) = _
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function]
  calc
    _ = chartTranslatedGerm v v (mem_chart_source _ v)
        ((fun w : ComplexModel k => w j) ∘ Subtype.val) hcoordOn := by
      apply chartTranslatedGerm_congr_original
      apply Eventually.of_forall
      intro w
      have h := congrArg (fun q : ComplexModel n => q (j.castLE hk))
        (parameterMap_flat_dictionary Φ k hsrc w.val w.property).2
      simpa [flatCoord,flatMap,parameterMapOn,Function.comp_apply,coordinateInclusion_apply,j.isLt] using h
    _ = chartTranslatedGerm v.val v.val (mem_chart_source _ v.val)
        (fun w : ComplexModel k => w j) hcoord := by simpa using hval.symm
    _ = HolGerm.constHom (v.val j) + coordinateGerm j := by
      have hshift : ∀ᶠ z in 𝓝 (0 : ComplexModel k),
          DifferentiableAt ℂ (fun z : ComplexModel k => (z + v.val) j) z :=
        Eventually.of_forall fun z => by
          have hpj : DifferentiableAt ℂ (fun w : ComplexModel k => w j) (z + v.val) :=
            (PiLp.proj 2 (fun _ : Fin k => ℂ) j).differentiableAt
          have ht : DifferentiableAt ℂ (fun w : ComplexModel k => w + v.val) z :=
            differentiableAt_id.add_const v.val
          exact hpj.comp z ht
      change HolGerm.mk (fun z : ComplexModel k => (z + v.val) j) hshift =
        HolGerm.constHom (v.val j) + coordinateGerm j
      rw [coordinateGerm,HolGerm.constHom_apply,←HolGerm.mk_add]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by simp [add_comm]

private def intrinsicSlot {k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) : Option (Fin k) :=
  match s with
  | none => none
  | some j => some ⟨j.val,hs j rfl⟩

private theorem intrinsicSlot_value {k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) :
    Option.map Fin.val (intrinsicSlot s hs) = Option.map Fin.val s := by
  cases s <;> rfl

private theorem intrinsicSlot_ambient {k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) (hk : k ≤ n) :
    s = Option.map (fun j : Fin k => j.castLE hk) (intrinsicSlot s hs) := by
  cases s with
  | none => rfl
  | some j =>
    apply congrArg some
    exact Fin.ext rfl

private theorem actual_whole_vanishing_eq_top_of_local_absence {x : X}
    (A U : Set X) (hU : IsOpen U) (hx : x ∈ U) (habs : ∀ p ∈ U, p ∉ A) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x = ⊤ := by
  have hf : HolomorphicAt n (fun _ : X => (1 : ℂ)) x := holomorphicAt_const 1
  have hm : (vanishingIdeal (n := n) A).mem x (fun _ => (1 : ℂ)) := by
    refine ⟨hf,?_⟩
    filter_upwards [hU.mem_nhds hx] with p hp hpa
    exact (habs p hp hpa).elim
  have hone : actualOriginalFunctionGerm x (fun _ : X => (1 : ℂ)) hf = 1 := by
    apply (actualStalkChartEquiv (n := n) x).injective
    rw [actualOriginalFunctionGerm_chart,map_one]
    rfl
  apply (Ideal.eq_top_iff_one _).mpr
  rw [←hone]
  exact Ideal.subset_span ⟨fun _ => (1 : ℂ),hf,hm,rfl⟩

/-- ONLY original SNC/transversality data internally choose ONE chart and native algebra dictionary,
before ALL points and ALL FULL original boundary labels, including unit and zero-dimensional cases. -/
theorem exists_actual_intrinsic_labelled_boundary_ideal_dictionary
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x ∈ N) :
    ∃ k ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
      (τ : Fin E.length → Option (Fin k)),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ i, Option.map Fin.val (τ i) = Option.map Fin.val (κ i)) ∧
      (k = 0 → ∀ i, τ i = none) ∧
      (∀ p ∈ flatDomain Φ,
        (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
        ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
      (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
      ∀ v : parameterOpen Φ k,
        ∃ hp : parameterMapOn Φ k v ∈ N,
          ∃ e : ((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier ≃ₐ[ℂ]
              HolGerm (ComplexModel k),
            (∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩ r) =
                parameterGermPullback Φ k hsrc v r) ∧
            ∀ i : Fin E.length,
              Ideal.map e.toRingHom (actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩) =
                Ideal.span {labelledParameterBoundaryGerm τ v.val i} ∧
              (IsUnit (labelledParameterBoundaryGerm τ v.val i) ↔ parameterMapOn Φ k v ∉ E.get i) := by
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hpoint,hall⟩ :=
    exists_actual_intrinsic_carrier_algebra_dictionary hE hT x hx
  let τ : Fin E.length → Option (Fin k) := fun i => intrinsicSlot (κ i) (hκ i)
  have hτambient (i : Fin E.length) : κ i = Option.map (fun j : Fin k => j.castLE hk) (τ i) :=
    intrinsicSlot_ambient (κ i) (hκ i) hk
  refine ⟨k,hk,Φ,κ,hsrc,τ,h0,hκ,hinj,?_,?_,hcharts,hpoint,?_⟩
  · intro i
    exact intrinsicSlot_value (κ i) (hκ i)
  · intro hk0 i
    have hempty : IsEmpty (Fin k) := by rw [hk0]; infer_instance
    cases hτ : τ i with
    | none => rfl
    | some j => exact (hempty.false j).elim
  · intro v
    obtain ⟨hp,e,he⟩ := hall v
    refine ⟨hp,e,he,?_⟩
    intro i
    have hd := parameterMap_flat_dictionary Φ k hsrc v.val v.property
    have hemaps : e.toRingHom.comp
        ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩).hom =
          parameterGermPullback Φ k hsrc v := by
      apply RingHom.ext
      intro r
      exact he r
    cases hτ : τ i with
    | none =>
      have hκi : κ i = none := by simpa [hτ] using hτambient i
      have habs : ∀ p ∈ flatDomain Φ, p ∉ E.get i := by
        intro p hpΦ hpE
        obtain ⟨j,hj,_⟩ := ((hcharts p hpΦ).2 i).mp hpE
        simp [hκi] at hj
      have hI : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i))
          (parameterMapOn Φ k v) = ⊤ :=
        actual_whole_vanishing_eq_top_of_local_absence (E.get i) (flatDomain Φ)
          (isOpen_flatDomain Φ) hd.1 habs
      constructor
      · rw [actualLabelledBoundaryTraceIdeal,Ideal.map_map,hemaps]
        change Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) (parameterMapOn Φ k v)) = _
        rw [hI,Ideal.map_top]
        simp [labelledParameterBoundaryGerm,hτ]
      · constructor
        · intro _
          exact habs _ hd.1
        · intro _
          simp [labelledParameterBoundaryGerm,hτ]
    | some j =>
      have hκi : κ i = some (j.castLE hk) := by simpa [hτ] using hτambient i
      have hflat : ∀ p ∈ flatDomain Φ, p ∈ E.get i ↔ flatCoord Φ (j.castLE hk) p = 0 := by
        intro p hpΦ
        rw [(hcharts p hpΦ).2 i]
        constructor
        · rintro ⟨j',hj',hz⟩
          have hjj : j' = j.castLE hk := Option.some.inj (hj'.symm.trans hκi)
          subst j'
          exact hz
        · intro hz
          exact ⟨j.castLE hk,hκi,hz⟩
      have hvalue : flatCoord Φ (j.castLE hk) (parameterMapOn Φ k v) = v.val j := by
        change flatMap Φ (parameterMap Φ k v.val) (j.castLE hk) = v.val j
        rw [hd.2]
        simp [coordinateInclusion_apply,j.isLt]
      have hmem : parameterMapOn Φ k v ∈ E.get i ↔ v.val j = 0 := by
        rw [hflat (parameterMapOn Φ k v) hd.1,hvalue]
      constructor
      · rw [actualLabelledBoundaryTraceIdeal,Ideal.map_map,hemaps]
        change Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) (parameterMapOn Φ k v)) = _
        rw [actualWholeHyperplaneStalkIdeal_eq_span Φ hflat (parameterMapOn Φ k v) hd.1,Ideal.map_span]
        simp only [Set.image_singleton]
        rw [parameter_flatCoord_germ Φ k hk hsrc v j]
        simp [labelledParameterBoundaryGerm,hτ]
      · have hu : IsUnit (labelledParameterBoundaryGerm τ v.val i) ↔ v.val j ≠ 0 := by
          rw [labelledParameterBoundaryGerm,hτ,HolGerm.isUnit_iff_eval_ne_zero]
          simp [coordinateGerm]
        exact hu.trans (not_congr hmem).symm

end
end Hironaka.HironakaActualIntrinsicLabelledBoundaryIdeals

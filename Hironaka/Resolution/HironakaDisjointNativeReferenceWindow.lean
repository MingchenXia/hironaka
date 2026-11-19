import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! Actual native reference windows on original histories, conditional only
on the existing geometry-only lift. Entire records, no value certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointNativeReferenceWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaActualRawRecordPullbacks SubmanifoldChartedSpace NormalCrossings

variable {n k : ℕ} {X : CMfd.{0} n} (hk : k≤n) (W : Set X)
  (hW : ∀x∈W,RegularAtDim (n := n) W x k)

/-- The actual native inverse image of an ambient reference open. -/
def nativeWindow (O : Opens X) : Opens (nativeManifold hk W hW) :=
  ⟨(Subtype.val : W→X) ⁻¹' O,O.isOpen.preimage continuous_subtype_val⟩

/-- The literal source inclusion into the SAME ambient reference open. -/
def sourceInclusion (O : Opens X) : nativeWindow hk W hW O → O :=
  fun p=>⟨p.val.val,p.property⟩

private def sourceHomeomorph (O : Opens X) :
    nativeWindow hk W hW O ≃ₜ ((Subtype.val : O→X) ⁻¹' W) where
  toFun p:=⟨sourceInclusion hk W hW O p,p.val.property⟩
  invFun p:=⟨⟨p.val.val,p.property⟩,p.val.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun p : {w : W // w.val∈(O : Set X)}=>p.val.val)
    fun_prop
  continuous_invFun:=by fun_prop

/-- The source map is a genuine holomorphic CLOSED embedding with exact
whole section image, including the case of an empty reference open. -/
theorem source_geometry (hWc : IsClosed W) (O : Opens X) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (sourceInclusion hk W hW O) ∧
    Topology.IsClosedEmbedding (sourceInclusion hk W hW O) ∧
    range (sourceInclusion hk W hW O)=(Subtype.val : O→X) ⁻¹' W := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hval : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : W→X) := contMDiff_val hk hW
  have hhol : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (sourceInclusion hk W hW O) := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    exact hval.comp contMDiff_subtype_val
  have hclosed : IsClosed ((Subtype.val : O→X) ⁻¹' W):=hWc.preimage continuous_subtype_val
  have hEmb :=hclosed.isClosedEmbedding_subtypeVal.comp (sourceHomeomorph hk W hW O).isClosedEmbedding
  refine ⟨hhol,hEmb,?_⟩
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact q.val.property
  · intro hp
    exact ⟨⟨⟨p.val,hp⟩,p.property⟩,rfl⟩

variable {hk W hW} {hWc : IsClosed W} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/-- Endpoint inclusion on the literal original restricted native tower;
its ambient window condition is DERIVED from the actual lift square. -/
def endpointInclusion (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    openPreimage Q (nativeWindow hk W hW O) → openPreimage T O := fun p=>
  ⟨p.val.val,by
    change T.proj p.val.val∈O
    rw [h.square p.val]
    exact p.property⟩

private def endpointHomeomorph (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    openPreimage Q (nativeWindow hk W hW O) ≃ₜ
      ((Subtype.val : openPreimage T O→Y) ⁻¹' V) where
  toFun p:=⟨endpointInclusion h O p,p.val.property⟩
  invFun p:=⟨⟨p.val.val,p.property⟩,by
    change (Q.proj ⟨p.val.val,p.property⟩).val∈O
    rw [←h.square ⟨p.val.val,p.property⟩]
    exact p.val.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun p : {v : V // (Q.proj v).val∈(O : Set X)}=>p.val.val)
    fun_prop
  continuous_invFun:=by fun_prop

/-- Geometry, exact whole image, projection square and retained length on
both actual restricted histories, without any source/target test premise. -/
theorem endpoint_geometry (h : Lift hk W hWc hW E T V hVc hV Q) (O : Opens X) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (endpointInclusion h O) ∧
    Topology.IsClosedEmbedding (endpointInclusion h O) ∧
    range (endpointInclusion h O)=(Subtype.val : openPreimage T O→Y) ⁻¹' V ∧
    (∀p : openPreimage Q (nativeWindow hk W hW O),
      (restrict O T).proj (endpointInclusion h O p)=
        sourceInclusion hk W hW O ((restrict (nativeWindow hk W hW O) Q).proj p)) ∧
    (restrict (nativeWindow hk W hW O) Q).length=(restrict O T).length := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hval : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : V→Y) := contMDiff_val hk hV
  have hhol : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (endpointInclusion h O) := by
    apply (ContMDiff.subtypeVal_comp_iff (openPreimage T O) _).mp
    exact hval.comp contMDiff_subtype_val
  have hclosed : IsClosed ((Subtype.val : openPreimage T O→Y) ⁻¹' V):=
    hVc.preimage continuous_subtype_val
  have hEmb :=hclosed.isClosedEmbedding_subtypeVal.comp (endpointHomeomorph h O).isClosedEmbedding
  refine ⟨hhol,hEmb,?_,?_,?_⟩
  · ext p
    constructor
    · rintro ⟨q,rfl⟩
      exact q.val.property
    · intro hp
      refine ⟨⟨⟨p.val,hp⟩,?_⟩,rfl⟩
      change (Q.proj ⟨p.val,hp⟩).val∈O
      rw [←h.square ⟨p.val,hp⟩]
      exact p.property
  · intro p
    apply Subtype.ext
    simpa only [sourceInclusion,endpointInclusion,proj_restrict] using h.square p.val
  · rw [length_restrict,length_restrict,h.length]

private theorem raw_marked_comp {a b c : ℕ} {A B C : Type}
    [TopologicalSpace A] [ChartedSpace (ComplexModel a) A] [IsComplexManifold a A]
    [TopologicalSpace B] [ChartedSpace (ComplexModel b) B] [IsComplexManifold b B]
    [TopologicalSpace C] [ChartedSpace (ComplexModel c) C] [IsComplexManifold c C]
    {f : B→A} {g : C→B}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel c) 𝓘(ℂ,ComplexModel b) ∞ g)
    (M : MarkedIdeal a A) (hhol : ∀x v,M.ideal.mem x v → HolomorphicAt a v x) :
    markedPullback (m := c) g (markedPullback (m := b) f M)=
      markedPullback (m := c) (f ∘ g) M := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · simp only [markedPullback,List.map_map,Function.comp_def]
    rfl
  · exact (whole_pullback_comp hf hg M.ideal hhol).symm
  · rfl

/-- Whole N/E/I/d equality on the SAME actual original restricted towers.
Every mark and all raw holomorphic ideals are allowed; neither tower's
admissibility/canonicality or a desired record comparison is assumed. -/
theorem actual_masked_records (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E)
    (O : Opens X) (M : MarkedIdeal n X) (hME : M.E=E) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) :
    geoTransformAlong
      (markedPullback (m := k) (sourceInclusion hk W hW O)
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→X) M)) (restrict (nativeWindow hk W hW O) Q)=
      markedPullback (m := k) (endpointInclusion h O)
        (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→X) M) (restrict O T)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hWval : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : W→X):=contMDiff_val hk hW
  have hVval : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : V→Y):=contMDiff_val hk hV
  have hSource:=(source_geometry hk W hW hWc O).1
  have hEnd:=(endpoint_geometry h O).1
  have hInitial : markedPullback (m := k) (sourceInclusion hk W hW O)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→X) M)=
        MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW)
          (nativePullback hk W hW M) := by
    calc
      _=markedPullback (m := k) ((Subtype.val : O→X) ∘ sourceInclusion hk W hW O) M :=
        raw_marked_comp contMDiff_subtype_val hSource M hhol
      _=markedPullback (m := k)
          ((Subtype.val : W→X) ∘ (Subtype.val : nativeWindow hk W hW O→nativeManifold hk W hW)) M:=rfl
      _=_ := (raw_marked_comp hWval contMDiff_subtype_val M hhol).symm
  have hNativeHol : ∀x g,(nativePullback hk W hW M).ideal.mem x g → HolomorphicAt k g x:=
    fun _ _ hg=>hg.1
  rw [hInitial,geoTransformAlong_restrict_of_hhol (nativePullback hk W hW M) hNativeHol
    (nativeWindow hk W hW O) Q,h.whole_records hn hE hTrans M hME hMN hhol,
    geoTransformAlong_restrict_of_hhol M hhol O T]
  have hCurrent:=holomorphic_geoTransformAlong M hhol T
  change markedPullback (m := k)
      (Subtype.val : openPreimage Q (nativeWindow hk W hW O)→nativeManifold hk V hV)
      (markedPullback (m := k) (Subtype.val : V→Y) (geoTransformAlong M T))=
    markedPullback (m := k) (endpointInclusion h O)
      (markedPullback (m := n) (Subtype.val : openPreimage T O→Y) (geoTransformAlong M T))
  rw [raw_marked_comp hVval contMDiff_subtype_val _ hCurrent,
    raw_marked_comp contMDiff_subtype_val hEnd _ hCurrent]
  rfl

/-- Every ORIGINAL reference cut has actual restricted head/tail maps and
whole raw records on every ambient open at that head. The full current
boundary, including all born-before-cut members, is retained. -/
theorem exists_original_cut_masked_records
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (hn : 0<n) (hE : IsSNCDivisor n E) (hTrans : IsTransverse n W E) (j : ℕ) :
    ∃(P : Set (BlowupTowerSplit.split T j).1)(hPc : IsClosed P)
      (hP : ∀x∈P,RegularAtDim (n := n) P x k)
      (e : (BlowupTowerSplit.split Q j).1=nativeManifold hk P hP),
      Lift hk W hWc hW E (BlowupTowerSplit.head T j) P hPc hP
        (recastTarget e (BlowupTowerSplit.head Q j)) ∧
      ∃hTail : Lift hk P hPc hP (boundary E (BlowupTowerSplit.head T j))
        (BlowupTowerSplit.tail T j) V hVc hV (recastSource e (BlowupTowerSplit.tail Q j)),
      ∀(O : Opens (BlowupTowerSplit.split T j).1)
        (L : MarkedIdeal n (BlowupTowerSplit.split T j).1),
        L.E=boundary E (BlowupTowerSplit.head T j) → L.N⊆P →
        (∀x g,L.ideal.mem x g → HolomorphicAt n g x) →
        geoTransformAlong
          (markedPullback (m := k) (sourceInclusion hk P hP O)
            (MarkedIdealBiholomorphism.MarkedIdeal.pullback
              (Subtype.val : O→(BlowupTowerSplit.split T j).1) L))
          (restrict (nativeWindow hk P hP O) (recastSource e (BlowupTowerSplit.tail Q j)))=
        markedPullback (m := k) (endpointInclusion hTail O)
          (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback
            (Subtype.val : O→(BlowupTowerSplit.split T j).1) L)
            (restrict O (BlowupTowerSplit.tail T j))) := by
  obtain ⟨P,hPc,hP,e,hHead,hTail⟩:=HironakaActualNativeSectionOriginalCuts.Lift.original_head_tails h j
  obtain ⟨hE₀,hT₀⟩:=hHead.geometry hn hE hTrans
  exact ⟨P,hPc,hP,e,hHead,hTail,fun O L hLE hLN hhol=>
    actual_masked_records hTail hn hE₀ hT₀ O L hLE hLN hhol⟩

end
end Hironaka.HironakaDisjointNativeReferenceWindow

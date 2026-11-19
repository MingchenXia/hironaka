import Hironaka.Resolution.HironakaG1RatioGraphFiniteTestClass
import Hironaka.Resolution.HironakaG1CrossAmbientNativeComparison

/-! Canonical comparison on the literal graph-supported records. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphSupportedComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  ResolutionDriver CanonicalCentres CoefficientIdealRestriction
  HironakaG11PresLineState HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal
  HironakaBaseChange HironakaG1RatioSectionBlowup HironakaSmoothSubmersionCoefficientIdeals
  HironakaG1RatioGraphNativeSource HironakaG1RatioGraphFiniteTower HironakaG1RatioGraphFiniteTestClass
  HironakaG1CrossAmbientNativeComparison HironakaG1NativeChartCanonicalComparison
  HironakaActualNativeSectionFiniteHistory HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaG8LocalHistory HironakaG1NativeChartValueOrder

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- An actual cylinder test determines a native chart realization of the
carrier-reset invariant. The original normalized source-open record is
literal, and the full padded endpoint contributes its exact cosupport
and all old and born boundary slots in the same order. -/
theorem exists_ratioGraph_supported_canonical_read
    {n t : ℕ} (hn : 0 < n) {U : Opens (ComplexModel n)} {X Y : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    {C : Set U} {H : ℕ → ℕ} (hState : NativeHSState (X := CMfd.of (n := n) U) Q C H)
    (T : BlowupTower X Y) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let S := withN P (P.N ∩ sectionSupport e f)
    let U₀ := sectionBaseOpen (O := O) hf
    let A := CMfd.of (n := n) U₀
    let Q₀ := markedPullback (m := n) (Subtype.val : U₀ → U) Q
    let hpos := hn.trans_le (Nat.le_add_right n t)
    ∀ (_hT : P.IsGeoTestTower T),
      ∃ (Z : CMfd.{0} n) (B : BlowupTower A Z) (i : Z → Y),
        B.length = T.length ∧ Q₀.IsGeoTestTower B ∧ Function.Injective i ∧
        (∀ z, T.proj (i z) = (sectionBaseEquiv b hb hf (B.proj z)).val) ∧
        (geoTransformAlong Q₀ B).d = Q.d ∧
        (geoTransformAlong Q₀ B).E = (geoTransformAlong P T).E.map (i ⁻¹' ·) ∧
        (geoTransformAlong Q₀ B).cosupp = i ⁻¹' (geoTransformAlong P T).cosupp ∧
        i '' (geoTransformAlong Q₀ B).cosupp = (geoTransformAlong P T).cosupp ∧
        (IsCanonical Q₀ ((invFamily hn n).inv Q₀) B ↔
          IsCanonical S ((invFamily hpos ((n+t-n)+n)).inv S) T) ∧
        (IsCanonical Q₀ ((invFamily hn n).inv Q₀) B →
          (∀ z ∈ (geoTransformAlong Q₀ B).cosupp,
            (invFamily hpos ((n+t-n)+n)).inv S T (i z) =
              familyDimensionMap (n+t-n) n ((invFamily hn n).inv Q₀ B z)) ∧
          maxLocus ((invFamily hn n).inv Q₀ B) (geoTransformAlong Q₀ B).cosupp =
            i ⁻¹' maxLocus ((invFamily hpos ((n+t-n)+n)).inv S T) (geoTransformAlong S T).cosupp ∧
          i '' maxLocus ((invFamily hn n).inv Q₀ B) (geoTransformAlong Q₀ B).cosupp =
            maxLocus ((invFamily hpos ((n+t-n)+n)).inv S T) (geoTransformAlong S T).cosupp) := by
  intro P S U₀ A Q₀ hpos hT
  let he : IsOpenHoloEmbedding (n+t) e := ⟨O,b,hb⟩
  let W := sectionSupport e f
  let hW := sectionSupport_regular he hf
  let WN := nativeManifold (Nat.le_add_right n t) W hW
  let c := sectionBaseEquiv b hb hf
  obtain ⟨V,hVc,hV,B,hLift,hLen,hNative,hSource,hSquare,hRecord,hMark,hE,hCos,hRestrict⟩ :=
    exists_ratioGraph_finite_tower_of_cylinder hpos b hb hf Q hQ hState T hT
  let ZN := nativeManifold (Nat.le_add_right n t) V hV
  let B₀ := transport (X := WN) (X' := A) c B
  have hIso := transport_isTowerIso (X := WN) (X' := A) c B
  let i (z : B₀.target) : Y := (B₀.back z).val
  obtain ⟨_,hS,hTr⟩ := ratioGraph_supported_domains b hb hf Q hQ hState
  have hNW : S.N ⊆ W := inter_subset_right
  have hReset : nativePullback (Nat.le_add_right n t) W hW S =
      nativePullback (Nat.le_add_right n t) W hW P :=
    nativePullback_withN_inter _ hW P
  have hRead := original_native_chart_comparison hpos hn S hS hNW hTr hLift c B₀.tower B₀.back hIso
  dsimp only at hRead
  rw [hReset,hSource] at hRead
  obtain ⟨_,hCan,hEndpoint⟩ := hRead
  let N₀ := nativePullback (Nat.le_add_right n t) W hW P
  have hNCo := HironakaActualNativeInvariantDomain.isInvDomain_nativePullback hpos
    (Nat.le_add_right n t) hW S hS hNW hTr
  rw [hReset] at hNCo
  have hRec := IsTowerIso.geoTransformAlong_eq (X := WN) (X' := A) (Y := ZN) (Y' := B₀.target) c (𝔪 := N₀) hNCo.isWellFormed.isClosedSubmanifold_N
    hNCo.isWellFormed.isCoherent hIso hNative
  rw [hSource] at hRec
  have hNative₀ := IsTowerIso.isGeoTestTower_iff (X := WN) (X' := A) (Y := ZN) (Y' := B₀.target) c (𝔪 := N₀) hNCo.isWellFormed.isClosedSubmanifold_N
    hNCo.isWellFormed.isCoherent hIso
  rw [hSource] at hNative₀
  have hCos₀ := IsTowerIso.cosupp_geoTransformAlong (X := WN) (X' := A) (Y := ZN) (Y' := B₀.target) c (𝔪 := N₀) hNCo.isWellFormed.isClosedSubmanifold_N
    hNCo.isWellFormed.isCoherent hIso hNative
  rw [hSource,hCos] at hCos₀
  have hCosA : (geoTransformAlong Q₀ B₀.tower).cosupp = i ⁻¹' (geoTransformAlong P T).cosupp := hCos₀
  have hWeak := (ratioGraph_sameTestClass b hb hf Q hQ).wEquiv
  have hPadCos : (geoTransformAlong P T).cosupp = (geoTransformAlong S T).cosupp :=
    (hWeak.2 T).2 hT
  have hRange : (geoTransformAlong P T).cosupp ⊆ range i := by
    intro y hy
    rw [hPadCos] at hy
    have hyV := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift S hNW
      ((geoTransformAlong S T).cosupp_subset_N hy)
    exact ⟨B₀.back.symm ⟨y,hyV⟩,congrArg Subtype.val (B₀.back.apply_symm_apply ⟨y,hyV⟩)⟩
  refine ⟨B₀.target,B₀.tower,i,hIso.length_eq.trans hLen,hNative₀.mpr hNative,Subtype.val_injective.comp B₀.back.injective,?_,?_,?_,hCosA,?_,hCan,?_⟩
  · intro z
    exact (hSquare (B₀.back z)).trans (congrArg Subtype.val (hIso.proj_comm z).symm)
  · rw [hRec]
    exact hMark
  · rw [hRec]
    change (geoTransformAlong N₀ B).E.map (B₀.back ⁻¹' ·) = _
    rw [hE,List.map_map]
    rfl
  · rw [hCosA, image_preimage_eq_inter_range]
    exact inter_eq_left.mpr hRange
  · intro hc
    obtain ⟨_,_,hValue,hMax₁,hMax₂⟩ := hEndpoint (hCan.mp hc)
    refine ⟨fun z hz => hValue z ?_,hMax₁,hMax₂⟩
    rw [hCosA] at hz
    change i z ∈ (geoTransformAlong P T).cosupp at hz
    change i z ∈ (geoTransformAlong S T).cosupp
    rwa [← hPadCos]


/-- On the common strict endpoint cut, any strictly monotone recoding
preserves and reflects the full two-point comparison. The alignment
premise concerns the two supported invariants on that cut. -/
theorem supportedEndpoint_order_iff
    {A B Y L R L' R' : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder L'] [LinearOrder R']
    {D : Set Y} {i : A → Y} {j : B → Y}
    (f : A → L) (g : B → R) (F : Y → L') (G : Y → R')
    (l : L → L') (r : R → R') (hl : StrictMono l) (hr : StrictMono r)
    (hF : ∀ x, i x ∈ D → F (i x) = l (f x))
    (hG : ∀ x, j x ∈ D → G (j x) = r (g x))
    (hAlign : ∀ y ∈ D, ∀ z ∈ D, F y < F z ↔ G y < G z)
    {x x' : A} {y y' : B} (hx : i x ∈ D) (hx' : i x' ∈ D)
    (hPair : j y = i x) (hPair' : j y' = i x') :
    f x < f x' ↔ g y < g y' := by
  have hy : j y ∈ D := hPair.symm ▸ hx
  have hy' : j y' ∈ D := hPair'.symm ▸ hx'
  have h₁ := hAlign (i x) hx (i x') hx'
  rw [← hPair, ← hPair',hG y hy,hG y' hy'] at h₁
  rw [hPair,hPair',hF x hx,hF x' hx'] at h₁
  exact hl.lt_iff_lt.symm.trans (h₁.trans hr.lt_iff_lt)

/-- Aligned supported endpoint orders give the same maximal locus on the
common cut. Thus the two actual native maximum loci have the same image
when the respective native-to-supported comparison formulas apply. -/
theorem supportedEndpoint_maximum_image_eq
    {A B Y L R L' R' : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder L'] [LinearOrder R']
    {D : Set Y} {i : A → Y} {j : B → Y}
    (f : A → L) (g : B → R) (F : Y → L') (G : Y → R')
    (l : L → L') (r : R → R') (hl : StrictMono l) (hr : StrictMono r)
    (hi : D ⊆ range i) (hj : D ⊆ range j)
    (hF : ∀ x, i x ∈ D → F (i x) = l (f x))
    (hG : ∀ x, j x ∈ D → G (j x) = r (g x))
    (hAlign : ∀ y ∈ D, ∀ z ∈ D, F y < F z ↔ G y < G z) :
    i '' maxLocus f (i ⁻¹' D) = j '' maxLocus g (j ⁻¹' D) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,⟨hx,hMax⟩,rfl⟩
    obtain ⟨y,hy⟩ := hj hx
    refine ⟨y,⟨(show j y ∈ D from hy.symm ▸ hx),?_⟩,hy⟩
    intro y' hy'
    obtain ⟨x',hx'⟩ := hi hy'
    have hDom : i x' ∈ D := hx'.symm ▸ hy'
    have hp := supportedEndpoint_order_iff f g F G l r hl hr hF hG hAlign hx hDom hy hx'.symm
    exact not_lt.mp (hp.not.mp (not_lt.mpr (hMax x' hDom)))
  · rintro _ ⟨y,⟨hy,hMax⟩,rfl⟩
    obtain ⟨x,hx⟩ := hi hy
    refine ⟨x,⟨(show i x ∈ D from hx.symm ▸ hy),?_⟩,hx⟩
    intro x' hx'
    obtain ⟨y',hy'⟩ := hj hx'
    have hDom : j y' ∈ D := hy'.symm ▸ hx'
    have hp := supportedEndpoint_order_iff f g F G l r hl hr hF hG hAlign
      (hx.symm ▸ hy) hx' hx.symm hy'
    exact not_lt.mp (hp.not.mpr (not_lt.mpr (hMax y' hDom)))


/-- The two exact strict embeddings induce a bijection of the unpadded
endpoint cuts. If their supported orders align, this bijection induces
an order isomorphism between the attained unpadded values. -/
theorem exists_supportedEndpoint_valueOrderIso
    {A B Y L R L' R' : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder L'] [LinearOrder R']
    {D : Set Y} {i : A → Y} {j : B → Y}
    (f : A → L) (g : B → R) (F : Y → L') (G : Y → R')
    (l : L → L') (r : R → R') (hl : StrictMono l) (hr : StrictMono r)
    (hi : D ⊆ range i) (hj : D ⊆ range j)
    (hii : Function.Injective i) (hjj : Function.Injective j)
    (hF : ∀ x, i x ∈ D → F (i x) = l (f x))
    (hG : ∀ x, j x ∈ D → G (j x) = r (g x))
    (hAlign : ∀ y ∈ D, ∀ z ∈ D, F y < F z ↔ G y < G z) :
    ∃ e : (i ⁻¹' D) ≃ (j ⁻¹' D),
      (∀ x, j (e x).val = i x.val) ∧
      let f₀ := fun x : i ⁻¹' D => f x.val
      let g₀ := fun x : i ⁻¹' D => g (e x).val
      ∃ o : range f₀ ≃o range g₀, ∀ x, (o ⟨f₀ x,mem_range_self x⟩ : R) = g₀ x := by
  let il (x : i ⁻¹' D) : D := ⟨i x.val,x.property⟩
  let jr (y : j ⁻¹' D) : D := ⟨j y.val,y.property⟩
  have hIl : Function.Bijective il := by
    refine ⟨fun _ _ h => Subtype.ext (hii (congrArg Subtype.val h)),?_⟩
    intro y
    obtain ⟨x,hx⟩ := hi y.property
    exact ⟨⟨x,show i x ∈ D from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
  have hJr : Function.Bijective jr := by
    refine ⟨fun _ _ h => Subtype.ext (hjj (congrArg Subtype.val h)),?_⟩
    intro y
    obtain ⟨x,hx⟩ := hj y.property
    exact ⟨⟨x,show j x ∈ D from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
  let el := Equiv.ofBijective il hIl
  let er := Equiv.ofBijective jr hJr
  let e := el.trans er.symm
  have hPair (x : i ⁻¹' D) : j (e x).val = i x.val :=
    congrArg Subtype.val (er.apply_symm_apply (el x))
  let f₀ := fun x : i ⁻¹' D => f x.val
  let g₀ := fun x : i ⁻¹' D => g (e x).val
  have hLt (x x' : i ⁻¹' D) : f₀ x < f₀ x' ↔ g₀ x < g₀ x' :=
    supportedEndpoint_order_iff f g F G l r hl hr hF hG hAlign
      x.property x'.property (hPair x) (hPair x')
  exact ⟨e,hPair,attainedValueOrderIso f₀ g₀ hLt,attainedValueOrderIso_apply f₀ g₀ hLt⟩

end
end Hironaka.HironakaG1RatioGraphSupportedComparison

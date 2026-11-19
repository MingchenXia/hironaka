import Hironaka.Resolution.HironakaG1LiteralRatioFullSupport
import Hironaka.Resolution.HironakaOriginalAllStepOneEtaleValues
import Hironaka.Resolution.HironakaG1NativeFiniteProductHSValues

/-! Composition of the original recursive dimension embeddings. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG1FiniteNativePaddingComposition
open CanonicalCentres MonomialInvariant
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaOriginalAllStepOneEtaleValues

private theorem dimensionValue_chain (s t : ℕ) (v : WithBot Val) :
    dimensionValue s (dimensionValue t v) = dimensionValue (s+t) v := by
  cases v using WithBot.recBotCoe with
  | bot => rfl
  | coe w =>
    change (dimensionKey s (dimensionKey t w) : WithBot Val) = dimensionKey (s+t) w
    have he : (ofLex w).1 + t + s = (ofLex w).1 + (s+t) := by omega
    simp only [dimensionKey,ofLex_toLex,he]

universe u v w

private theorem generalStep_chain {α : Type u} {β : Type v} {γ δ : Type w}
    (s t : ℕ) (h : γ = δ) (f : α → β) (g : β → γ) (p : α → δ)
    (hp : ∀ x, cast h (g (f x)) = p x)
    (v : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop α))) :
    cast (congrArg (fun A => ℕ ×ₗ (WithBot Val ⊕ₗ WithTop (ℕ ×ₗ WithTop A))) h)
      (generalDimensionMap s (stepDimensionMap g)
        (generalDimensionMap t (stepDimensionMap f) v)) =
      generalDimensionMap (s+t) (stepDimensionMap p) v := by
  subst δ
  have hp' : g ∘ f = p := funext hp
  subst p
  change ℕ × (WithBot Val ⊕ WithTop (ℕ × WithTop α)) at v
  obtain ⟨a,b⟩ := v
  cases b using Sum.rec with
  | inl w =>
    exact congrArg (fun x => toLex (a,toLex (Sum.inl x))) (dimensionValue_chain s t w)
  | inr w =>
    cases w using WithTop.recTopCoe with
    | top => rfl
    | coe v =>
      obtain ⟨c,d⟩ := v
      cases d using WithTop.recTopCoe <;> rfl

private theorem seedDimension_chain (s t x : ℕ) :
    cast (congrArg ValTy (Nat.add_assoc s t 0).symm)
      (familyDimensionMap s t (seedDimension t x)) = seedDimension (s+t) x := by
  cases t <;> rfl

/-- Successive supported dimension embeddings compose by adding their
actual offsets, with only associativity transporting the recursive type. -/
theorem familyDimensionMap_chain (s t k : ℕ) (v : ValTy k) :
    cast (congrArg ValTy (Nat.add_assoc s t k).symm)
      (familyDimensionMap s (t+k) (familyDimensionMap t k v)) =
      familyDimensionMap (s+t) k v := by
  induction k with
  | zero => exact seedDimension_chain s t v
  | succ k ih =>
    exact generalStep_chain s t (congrArg ValTy (Nat.add_assoc s t k).symm)
      (familyDimensionMap t k) (familyDimensionMap s (t+k)) (familyDimensionMap (s+t) k) ih v


open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver HironakaG1CrossAmbientNativeComparison
  HironakaG1RatioGraphSupportedComparison

/-- Two genuinely realized supported chart paddings have the same
canonical clock. At that clock the original source values recode by
the sum of the two normal offsets, and its maximum maps to the final
supported maximum through the actual endpoint maps. -/
theorem realized_padding_chain {m d k q : ℕ} {A Z : CMfd.{0} k}
    {C : MarkedIdeal k A} {S : BlowupTower A Z}
    (L : NativeChartRealization C S m q)
    (R : NativeChartRealization L.record L.tower d ((m-k)+q))
    (hk : 0 < k) :
    let hm := hk.trans_le L.dimLE
    let s := d-m
    let t := m-k
    let i := R.endpointMap ∘ L.endpointMap
    let f := (invFamily hk q).inv C S
    let g := R.ambientInvariant hm R.tower
    let D := (geoTransformAlong C S).cosupp
    let E := (geoTransformAlong R.record R.tower).cosupp
    (IsCanonical C ((invFamily hk q).inv C) S ↔
      IsCanonical R.record (R.ambientInvariant hm) R.tower) ∧
    (IsCanonical C ((invFamily hk q).inv C) S →
      D = i ⁻¹' E ∧ i '' D = E ∧
      (∀ z ∈ D, cast (congrArg ValTy (Nat.add_assoc s t q).symm) (g (i z)) =
        familyDimensionMap (s+t) q (f z)) ∧
      maxLocus f D = i ⁻¹' maxLocus g E ∧
      i '' maxLocus f D = maxLocus g E) := by
  intro hm s t i f g D E
  obtain ⟨hCanL,hDataL⟩ := L.compare hk
  obtain ⟨hCanR,hDataR⟩ := R.compare hm
  refine ⟨hCanL.trans hCanR,fun h => ?_⟩
  obtain ⟨hImgL,hPreL,hValueL,hMaxPreL,hMaxL⟩ := hDataL (hCanL.mp h)
  obtain ⟨hImgR,hPreR,hValueR,hMaxPreR,hMaxR⟩ := hDataR (hCanR.mp (hCanL.mp h))
  refine ⟨hPreL.trans (congrArg (L.endpointMap ⁻¹' ·) hPreR),?_,?_,
    hMaxPreL.trans (congrArg (L.endpointMap ⁻¹' ·) hMaxPreR),?_⟩
  · change (R.endpointMap ∘ L.endpointMap) '' D = E
    calc
      _ = R.endpointMap '' (L.endpointMap '' D) := (Set.image_image R.endpointMap L.endpointMap _).symm
      _ = E := (congrArg (R.endpointMap '' ·) hImgL).trans hImgR
  · intro z hz
    have hmid : L.endpointMap z ∈ (geoTransformAlong L.record L.tower).cosupp := by
      rw [← hImgL]
      exact mem_image_of_mem _ hz
    change cast (congrArg ValTy (Nat.add_assoc s t q).symm)
      (R.ambientInvariant hm R.tower (R.endpointMap (L.endpointMap z))) = _
    have hv := hValueR _ hmid
    change R.ambientInvariant hm R.tower (R.endpointMap (L.endpointMap z)) =
      familyDimensionMap s (t+q) (L.ambientInvariant hk L.tower (L.endpointMap z)) at hv
    rw [hv,hValueL _ hz]
    exact familyDimensionMap_chain s t q (f z)
  · change (R.endpointMap ∘ L.endpointMap) '' maxLocus f D = maxLocus g E
    calc
      _ = R.endpointMap '' (L.endpointMap '' maxLocus f D) := (Set.image_image R.endpointMap L.endpointMap _).symm
      _ = _ := (congrArg (R.endpointMap '' ·) hMaxL).trans hMaxR


open TopologicalSpace
open scoped Manifold ContDiff
open HironakaG11PresLineState HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal
  CoefficientIdealRestriction HironakaBaseChange HironakaSmoothSubmersionCoefficientIdeals
  HironakaG1RatioSectionBlowup HironakaG1RatioGraphNativeSource HironakaG1RatioGraphFiniteTower
  HironakaG1RatioGraphFiniteTestClass HironakaActualNativeSectionFiniteHistory
  BlowupTowerIsomorphism MarkedIdealTowerTransport MarkedIdealBiholomorphism

set_option backward.isDefEq.respectTransparency false in
/-- The actual ratio window supplies the first supported realization for
the composition theorem, on the literal upper tower and the exact
normalized source-open record. The independent second realization can
be supplied over this data. -/
theorem exists_ratio_supported_nativeChartRealization
    {n t : ℕ} (hpos : 0 < n+t) {U : Opens (ComplexModel n)} {X Y : CMfd.{0} (n+t)}
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
    ∀ (_hT : P.IsGeoTestTower T),
      ∃ (Z : CMfd.{0} n) (B : BlowupTower A Z)
        (L : NativeChartRealization Q₀ B (n+t) n),
        L.base = X ∧ L.target = Y ∧ HEq L.record S ∧ HEq L.tower T ∧
        B.length = T.length := by
  intro P S U₀ A Q₀ hT
  let he : IsOpenHoloEmbedding (n+t) e := ⟨O,b,hb⟩
  let W := sectionSupport e f
  let hW := sectionSupport_regular he hf
  let WN := nativeManifold (Nat.le_add_right n t) W hW
  let c := sectionBaseEquiv b hb hf
  obtain ⟨V,hVc,hV,B,hLift,hLen,_,hSource,_⟩ :=
    exists_ratioGraph_finite_tower_of_cylinder hpos b hb hf Q hQ hState T hT
  let B₀ := transport (X := WN) (X' := A) c B
  have hIso := transport_isTowerIso (X := WN) (X' := A) c B
  obtain ⟨_,hS,hTr⟩ := ratioGraph_supported_domains b hb hf Q hQ hState
  have hReset : nativePullback (Nat.le_add_right n t) W hW S =
      nativePullback (Nat.le_add_right n t) W hW P :=
    nativePullback_withN_inter _ hW P
  have hSource' : MarkedIdeal.pullback c (nativePullback (Nat.le_add_right n t) W hW S) = Q₀ :=
    (congrArg (MarkedIdeal.pullback c) hReset).trans hSource
  let L : NativeChartRealization Q₀ B₀.tower (n+t) n :=
    ⟨X,Y,S,hS,T,Nat.le_add_right n t,W,sectionSupport_closed he hf,hW,inter_subset_right,hTr,
      V,hVc,hV,B,hLift,c,B₀.back,hIso,hSource'⟩
  exact ⟨B₀.target,B₀.tower,L,rfl,rfl,HEq.rfl,HEq.rfl,hIso.length_eq.trans hLen⟩


/-- In actual nested dimensions, the total offset is the difference
between the top dimension and the original native dimension. -/
theorem familyDimensionMap_chain_offsets (k m d q : ℕ)
    (hkm : k ≤ m) (hmd : m ≤ d) (v : ValTy q) :
    cast (congrArg ValTy (show (d-m)+((m-k)+q) = (d-k)+q by omega))
      (familyDimensionMap (d-m) ((m-k)+q) (familyDimensionMap (m-k) q v)) =
      familyDimensionMap (d-k) q v := by
  have h : (d-m)+(m-k) = d-k := by omega
  have hmap {a b : ℕ} (e : a = b) :
      cast (congrArg ValTy (congrArg (· + q) e)) (familyDimensionMap a q v) =
        familyDimensionMap b q v := by
    cases e
    rfl
  calc
    _ = cast (congrArg ValTy (congrArg (· + q) h))
      (cast (congrArg ValTy (Nat.add_assoc (d-m) (m-k) q).symm)
        (familyDimensionMap (d-m) ((m-k)+q) (familyDimensionMap (m-k) q v))) := by rw [cast_cast]
    _ = cast (congrArg ValTy (congrArg (· + q) h))
      (familyDimensionMap ((d-m)+(m-k)) q v) :=
        congrArg _ (familyDimensionMap_chain (d-m) (m-k) q v)
    _ = _ := hmap h


open HironakaG1NativeFiniteProductState HironakaG1NativeFiniteProductHSValues

/-- Free Cartesian stabilization of two copies of one nonzero native
profile cannot both equalize different ambient dimensions and preserve
equality of the literal stabilized profiles. The rank is detected in
degree one. -/
theorem dimension_eq_of_equal_free_product_profiles (n m r s : ℕ) (H : ℕ → ℕ)
    (hH : 0 < H 0) (hd : n+r = m+s)
    (hHS : finiteProductHS r H = finiteProductHS s H) : n = m := by
  have he := congrFun hHS 1
  rw [finiteProductHS_one,finiteProductHS_one] at he
  have hm : r * H 0 = s * H 0 := by omega
  have hr : r = s := Nat.eq_of_mul_eq_mul_right hH hm
  omega

end Hironaka.HironakaG1FiniteNativePaddingComposition

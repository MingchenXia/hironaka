import TranscendentalNakamaye.Pending.HironakaActualZeroSectionContactNeighbourhood

/-!
# Whole closed-section differential ideals on the genuine open models

The ORIGINAL carrier is only closed regular IN an original open U. The actual
ambient model is p⁻¹U with its actual open-subspace charts. A true closed section,
projection and product flattening are constructed; inverse-coordinate section
identities are proved on the TRUE chart target, using no invalid global inverse
extension identity. The genuine fderiv chain rule and the SAME finite generators
then give both whole along-derivative inclusions and every actual iterate. These
are the open models required after a genuine recursive contact restriction.
Canonical cross-ambient values, matching centres/histories and proper intrinsic
descent are not assumed or asserted.
Blueprint: `hironaka-actual-open-zero-section-differentials-extension.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaActualOpenZeroSectionDifferentials
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  DerivativeIdealAlongCoherent BlowupFlatCoordinates GiraudAlong DerivativeIdealAlong DerivativeIdeal
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
variable {n : ℕ}

def productOpen (U : Opens (ComplexModel n)) : Opens (ComplexModel (n+1)) :=
  ⟨tangentProjection n 1 ⁻¹' U,U.isOpen.preimage (tangentProjection n 1).continuous⟩

def zeroSection (U : Opens (ComplexModel n)) (x : U) : productOpen U :=
  ⟨tangentInclusion n 1 x,by
    change tangentProjection n 1 (tangentInclusion n 1 x)∈U
    rw [tangentProjection_tangentInclusion]
    exact x.property⟩

def projection (U : Opens (ComplexModel n)) (z : productOpen U) : U :=
  ⟨tangentProjection n 1 z,z.property⟩

def liftedCarrier {U : Opens (ComplexModel n)} (A : Set U) : Set (productOpen U) :=
  {z | projection U z∈A ∧ actualJointNormalProjection n 1 z.val=0}

theorem zeroSection_contMDiff (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (zeroSection U) := by
  apply (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp
  exact (tangentInclusion n 1).contMDiff.comp contMDiff_subtype_val

theorem projection_contMDiff (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (projection U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (tangentProjection n 1).contMDiff.comp contMDiff_subtype_val

private theorem projection_section (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem section_mem_liftedCarrier {U : Opens (ComplexModel n)} (A : Set U) (x : U) :
    zeroSection U x∈liftedCarrier A ↔ x∈A := by
  change (projection U (zeroSection U x)∈A ∧ actualJointNormalProjection n 1 (tangentInclusion n 1 x)=0) ↔ x∈A
  rw [projection_section]
  simp

private theorem chart_apply {m : ℕ} (U : Opens (ComplexModel m)) (x y : U) :
    chartAt (ComplexModel m) x y=y.val := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

private theorem chart_source {m : ℕ} (U : Opens (ComplexModel m)) (x y : U) :
    y∈(chartAt (ComplexModel m) x).source :=
  AnalyticSubsetOpens.mem_chartAt_opens_source.mpr (by simp)

private theorem mem_chart_target {m : ℕ} (U : Opens (ComplexModel m)) (x : U) (v : ComplexModel m) :
    v∈(chartAt (ComplexModel m) x).target ↔ v∈U := by
  constructor
  · intro hv
    have h := (chartAt (ComplexModel m) x).right_inv hv
    rw [chart_apply] at h
    exact h ▸ ((chartAt (ComplexModel m) x).symm v).property
  · intro hv
    have h := AnalyticSubsetOpens.chart_mem_opens_target (n := m) (x := x) (y := ⟨v,hv⟩) (by simp)
    simpa using h

def productFlat (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    LocalHolomorphicEquivAt (n := n+1)
      (chartAt (ComplexModel (n+1)) (zeroSection U x) (zeroSection U x)) where
  source := tangentProjection n 1 ⁻¹' Φ.source
  target := tangentProjection n 1 ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage (tangentProjection n 1).continuous
  isOpen_target := Φ.isOpen_target.preimage (tangentProjection n 1).continuous
  center_mem_source := by
    change tangentProjection n 1 (tangentInclusion n 1 x.val)∈Φ.source
    rw [tangentProjection_tangentInclusion]
    simpa only [chart_apply] using Φ.center_mem_source
  toFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.toFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z)
  invFun := fun z => HironakaActualIntrinsicStableAmbientIso.join
    (Φ.invFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z)
  toFun_holomorphic := by
    intro z hz
    have hΦ := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)
    exact (((tangentInclusion n 1).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n 1).differentiableAt)).add
        ((actualJointNormalInclusion n 1).differentiableAt.comp z
          (actualJointNormalProjection n 1).differentiableAt)).differentiableWithinAt
  invFun_holomorphic := by
    intro z hz
    have hΦ := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
    exact (((tangentInclusion n 1).differentiableAt.comp z
      (hΦ.comp z (tangentProjection n 1).differentiableAt)).add
        ((actualJointNormalInclusion n 1).differentiableAt.comp z
          (actualJointNormalProjection n 1).differentiableAt)).differentiableWithinAt
  mapsTo_toFun := by
    intro z hz
    change tangentProjection n 1 (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.toFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z))∈Φ.target
    rw [first_join]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro z hz
    change tangentProjection n 1 (HironakaActualIntrinsicStableAmbientIso.join
      (Φ.invFun (tangentProjection n 1 z)) (actualJointNormalProjection n 1 z))∈Φ.source
    rw [first_join]
    exact Φ.mapsTo_invFun hz
  left_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.left_inv _ hz,join_projections]
  right_inv := by
    intro z hz
    simp only [first_join,second_join,Φ.right_inv _ hz,join_projections]

private theorem productFlat_source (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target) :
    (productFlat U x Φ).source⊆(chartAt (ComplexModel (n+1)) (zeroSection U x)).target := by
  intro z hz
  apply (mem_chart_target (productOpen U) (zeroSection U x) z).mpr
  change tangentProjection n 1 z∈U
  exact (mem_chart_target U x _).mp (hΦsrc hz)

private theorem productFlat_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (v : ComplexModel n) :
    (productFlat U x Φ).toFun (tangentInclusion n 1 v)=tangentInclusion n 1 (Φ.toFun v) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

private theorem productFlat_inverse_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (v : ComplexModel n) :
    (productFlat U x Φ).invFun (tangentInclusion n 1 v)=tangentInclusion n 1 (Φ.invFun v) := by
  simp [productFlat,HironakaActualIntrinsicStableAmbientIso.join,tangentProjection_tangentInclusion]

private theorem join_plane_iff (a : ComplexModel n) (b : ComplexModel 1) {k : ℕ} (hk : k≤n) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈complexCoordinatePlane (n+1) k ↔
      a∈complexCoordinatePlane n k ∧ b=0 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro i hi
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.castAdd 1) hi
    · ext i
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.natAdd n) (by simp;omega)
  · rintro ⟨ha,hb⟩ i hi
    refine Fin.addCases (fun j hj => ?_) (fun j _hj => ?_) i hi
    · simpa [HironakaActualIntrinsicStableAmbientIso.join] using ha j hj
    · simp [HironakaActualIntrinsicStableAmbientIso.join,hb]

private theorem productFlat_carrier (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {A : Set U} {k : ℕ} (hk : k≤n)
    (hflat : ∀ {y : U},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Φ.source →
      (y∈A ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈complexCoordinatePlane n k))
    {z : productOpen U} (hz : chartAt (ComplexModel (n+1)) (zeroSection U x) z∈(productFlat U x Φ).source) :
    z∈liftedCarrier A ↔ (productFlat U x Φ).toFun
      (chartAt (ComplexModel (n+1)) (zeroSection U x) z)∈complexCoordinatePlane (n+1) k := by
  have hΦ : chartAt (ComplexModel n) x (projection U z)∈Φ.source := by
    change tangentProjection n 1 z.val∈Φ.source
    change tangentProjection n 1 z.val∈Φ.source at hz
    exact hz
  have h := hflat (chart_source U x _) hΦ
  simp only [chart_apply] at h ⊢
  change (projection U z∈A ∧ actualJointNormalProjection n 1 z.val=0) ↔
    HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 z.val))
      (actualJointNormalProjection n 1 z.val)∈complexCoordinatePlane (n+1) k
  rw [join_plane_iff _ _ hk]
  exact and_congr_left fun _ => h

theorem liftedCarrier_closed_submanifold {U : Opens (ComplexModel n)} {A : Set U}
    (hA : IsClosedSubmanifold n A) : IsClosedSubmanifold (n+1) (liftedCarrier A) := by
  refine ⟨(hA.1.preimage (projection_contMDiff U).continuous).inter
    (isClosed_eq ((actualJointNormalProjection n 1).continuous.comp continuous_subtype_val) continuous_const),?_⟩
  intro z hz
  let x := projection U z
  have hx : x∈A := hz.1
  have hsec : zeroSection U x=z := by
    apply Subtype.ext
    change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
    have hq : actualJointNormalProjection n 1 z.val=0 := hz.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
      using join_projections (n := n) (m := 1) z.val
  obtain ⟨k,hkn,_hx,Φ,hsrc,h0,hflat⟩ := hA.2 x hx
  have hreg : RegularAtDim (n := n+1) (liftedCarrier A) (zeroSection U x) k := by
    refine ⟨by omega,(section_mem_liftedCarrier A x).mpr hx,productFlat U x Φ,
      productFlat_source U x Φ hsrc,?_,?_⟩
    · change (productFlat U x Φ).toFun (tangentInclusion n 1 x.val)=0
      rw [productFlat_section]
      have hΦ0 : Φ.toFun x.val=0 := by simpa only [complexChartAt,chart_apply] using h0
      rw [hΦ0,map_zero]
    · intro y _hy hyΦ
      exact productFlat_carrier U x Φ hkn hflat hyΦ
  exact ⟨k,by simpa only [hsec] using hreg⟩

private theorem productFlat_domain (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (z : productOpen U) :
    z∈flatDomain (productFlat U x Φ) ↔ projection U z∈flatDomain Φ := by
  constructor
  · rintro ⟨_,hz⟩
    refine ⟨chart_source U x _,?_⟩
    change tangentProjection n 1 z.val∈Φ.source at hz ⊢
    exact hz
  · rintro ⟨_,hz⟩
    refine ⟨chart_source (productOpen U) (zeroSection U x) _,?_⟩
    change tangentProjection n 1 z.val∈Φ.source at hz ⊢
    exact hz

private theorem flatMap_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (y : U) :
    flatMap (productFlat U x Φ) (zeroSection U y)=tangentInclusion n 1 (flatMap Φ y) := by
  change (productFlat U x Φ).toFun (chartAt (ComplexModel (n+1)) (zeroSection U x) (zeroSection U y))=
    tangentInclusion n 1 (Φ.toFun (chartAt (ComplexModel n) x y))
  simpa only [chart_apply,zeroSection] using productFlat_section U x Φ y.val

private theorem flatInv_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (v : ComplexModel n) (hv : v∈Φ.target) :
    flatInv (productFlat U x Φ) (tangentInclusion n 1 v)=zeroSection U (flatInv Φ v) := by
  have hΓtar : tangentInclusion n 1 v∈(productFlat U x Φ).target := by
    change tangentProjection n 1 (tangentInclusion n 1 v)∈Φ.target
    rwa [tangentProjection_tangentInclusion]
  have hB := (chartAt (ComplexModel n) x).right_inv (hΦsrc (Φ.mapsTo_invFun hv))
  have hB' : (flatInv Φ v).val=Φ.invFun v := by
    simpa only [flatInv,chart_apply] using hB
  have hΓsrc := productFlat_source U x Φ hΦsrc
  have hG := (chartAt (ComplexModel (n+1)) (zeroSection U x)).right_inv
    (hΓsrc ((productFlat U x Φ).mapsTo_invFun hΓtar))
  have hG' : (flatInv (productFlat U x Φ) (tangentInclusion n 1 v)).val=
      (productFlat U x Φ).invFun (tangentInclusion n 1 v) := by
    simpa only [flatInv,chart_apply] using hG
  apply Subtype.ext
  change (flatInv (productFlat U x Φ) (tangentInclusion n 1 v)).val=
    tangentInclusion n 1 (flatInv Φ v).val
  rw [hG',productFlat_inverse_section,hB']

private theorem section_single (i : Fin n) :
    tangentInclusion n 1 (EuclideanSpace.single i 1)=EuclideanSpace.single (i.castAdd 1) 1 := by
  ext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp
  · have hne : k.natAdd n≠i.castAdd 1 := by
      intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at h
      omega
    simp [hne]

theorem product_partial_zero_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    {y : U} (hy : y∈flatDomain Φ) (g : productOpen U → ℂ)
    (hg : HolomorphicAt (n+1) g (zeroSection U y)) (i : Fin n) :
    flatPartial (productFlat U x Φ) (i.castAdd 1) g (zeroSection U y)=
      flatPartial Φ i (g ∘ zeroSection U) y := by
  have hsy : zeroSection U y∈flatDomain (productFlat U x Φ) := by
    apply (productFlat_domain U x Φ _).mpr
    rwa [projection_section]
  have hcomp : HolomorphicAt n (g ∘ zeroSection U) y :=
    hg.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)
  rw [flatPartial_eq hsy hg,flatPartial_eq hy hcomp]
  have hΓsrc := productFlat_source U x Φ hΦsrc
  have hgd := differentiableAt_comp_flatInv (flatMap_mem_target hsy) hΓsrc
    (show HolomorphicAt (n+1) g (flatInv (productFlat U x Φ)
      (flatMap (productFlat U x Φ) (zeroSection U y))) by
        rw [flatInv_flatMap hsy];exact hg)
  rw [flatMap_section] at hgd
  have heq : (g ∘ flatInv (productFlat U x Φ)) ∘ tangentInclusion n 1
      =ᶠ[𝓝 (flatMap Φ y)] (g ∘ zeroSection U) ∘ flatInv Φ := by
    filter_upwards [Φ.isOpen_target.mem_nhds (flatMap_mem_target hy)] with v hv
    simp only [Function.comp_apply,flatInv_section U x Φ hΦsrc v hv]
  have hc := (hgd.hasFDerivAt.comp (flatMap Φ y) (tangentInclusion n 1).hasFDerivAt).fderiv
  rw [heq.fderiv_eq] at hc
  have h := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
  simp only [ContinuousLinearMap.comp_apply,section_single] at h
  rw [flatMap_section]
  exact h.symm

private theorem product_partial_eventually (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (g : productOpen U → ℂ) (hg : HolomorphicAt (n+1) g (zeroSection U x)) (i : Fin n) :
    flatPartial (productFlat U x Φ) (i.castAdd 1) g ∘ zeroSection U
      =ᶠ[𝓝 x] flatPartial Φ i (g ∘ zeroSection U) := by
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
    (zeroSection_contMDiff U).continuous.continuousAt.eventually hg.eventually] with y hy hgy
  exact product_partial_zero_section U x Φ hΦsrc hy g hgy i

private theorem coord_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (i : Fin n) :
    flatCoord (productFlat U x Φ) (i.castAdd 1) ∘ zeroSection U=flatCoord Φ i := by
  funext y
  change flatMap (productFlat U x Φ) (zeroSection U y) (i.castAdd 1)=flatMap Φ y i
  rw [flatMap_section]
  simp

private theorem added_coord_section (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (i : Fin 1) :
    flatCoord (productFlat U x Φ) (i.natAdd n) ∘ zeroSection U=fun _ => 0 := by
  funext y
  change flatMap (productFlat U x Φ) (zeroSection U y) (i.natAdd n)=0
  rw [flatMap_section]
  simp

private theorem pullback_span_iff {ι : Type*} (U : Opens (ComplexModel n))
    (J : GermIdeal (n+1) (productOpen U)) (x : U) (G : ι → productOpen U → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (zeroSection U x))
    (hgen : ∀ a,J.mem (zeroSection U x) a ↔
      IsInSpanAt (n := n+1) (·∈range G) (zeroSection U x) a) (F : U → ℂ) :
    (GermIdeal.pullback (m := n) (zeroSection U) J).mem x F ↔
      IsInSpanAt (n := n) (·∈range fun i => G i ∘ zeroSection U) x F := by
  constructor
  · intro h
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp h)
    rintro _ ⟨a,ha,rfl⟩
    apply IsInSpanAt.mono ?_ (isInSpanAt_comp (zeroSection_contMDiff U) ((hgen a).mp ha))
    rintro _ ⟨b,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro h
    apply GermIdeal.mem_pullback_iff.mpr
    apply IsInSpanAt.mono ?_ h
    rintro _ ⟨i,rfl⟩
    exact ⟨G i,(hgen _).mpr (isInSpanAt_self ⟨i,rfl⟩ (hG i)),rfl⟩

private theorem zero_mem_span {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] (x : M) (S : (M → ℂ) → Prop) :
    IsInSpanAt (n := m) S x (fun _ => 0) := by
  refine ⟨holomorphicAt_const 0,0,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),?_⟩
  exact Eventually.of_forall fun _ => by simp

private def liftFamilyIndex {r : ℕ} :
    Fin r ⊕ Fin n ⊕ (Fin r × Fin n) → Fin r ⊕ Fin (n+1) ⊕ (Fin r × Fin (n+1))
  | .inl i => .inl i
  | .inr (.inl j) => .inr (.inl (j.castAdd 1))
  | .inr (.inr (i,j)) => .inr (.inr (i,j.castAdd 1))

private theorem family_holomorphic {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M] (x : M)
    (Φ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) x x))
    (k : ℕ) {r : ℕ} (G : Fin r → M → ℂ)
    (hG : ∀ i,HolomorphicAt m (G i) x) (c : Fin r ⊕ Fin m ⊕ (Fin r × Fin m)) :
    HolomorphicAt m (derivFamilyAlong Φ k G c) x := by
  rcases c with i | j | ⟨i,j⟩
  · exact hG i
  · by_cases hj : k≤j.val
    · simpa only [derivFamilyAlong,if_pos hj] using holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)
    · simpa only [derivFamilyAlong,if_neg hj] using (holomorphicAt_const (n := m) (x := x) (0 : ℂ))
  · by_cases hj : j.val<k
    · simpa only [derivFamilyAlong,if_pos hj] using holomorphicAt_flatPartial j (mem_flatDomain_self Φ) (hG i)
    · simpa only [derivFamilyAlong,if_neg hj] using (holomorphicAt_const (n := m) (x := x) (0 : ℂ))

private theorem lifted_family_base (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (k : ℕ) {r : ℕ} (G : Fin r → productOpen U → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (zeroSection U x))
    (c : Fin r ⊕ Fin n ⊕ (Fin r × Fin n)) :
    derivFamilyAlong (productFlat U x Φ) k G (liftFamilyIndex c) ∘ zeroSection U
      =ᶠ[𝓝 x] derivFamilyAlong Φ k (fun i => G i ∘ zeroSection U) c := by
  rcases c with i | j | ⟨i,j⟩
  · exact Filter.EventuallyEq.rfl
  · by_cases hj : k≤j.val
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_pos hj]
      exact Eventually.of_forall fun y => congrFun (coord_section U x Φ j) y
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_neg hj]
      exact Filter.EventuallyEq.rfl
  · by_cases hj : j.val<k
    · simpa only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_pos hj] using
        product_partial_eventually U x Φ hΦsrc (G i) (hG i) j
    · simp only [liftFamilyIndex,derivFamilyAlong,Fin.val_castAdd,if_neg hj]
      exact Filter.EventuallyEq.rfl

private theorem restricted_family_span_iff (U : Opens (ComplexModel n)) (x : U)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    {k : ℕ} (hk : k≤n) {r : ℕ} (G : Fin r → productOpen U → ℂ)
    (hG : ∀ i,HolomorphicAt (n+1) (G i) (zeroSection U x)) (F : U → ℂ) :
    IsInSpanAt (n := n)
      (·∈range fun c => derivFamilyAlong (productFlat U x Φ) k G c ∘ zeroSection U) x F ↔
    IsInSpanAt (n := n) (·∈range (derivFamilyAlong Φ k (fun i => G i ∘ zeroSection U))) x F := by
  have hcomp (i : Fin r) : HolomorphicAt n (G i ∘ zeroSection U) x :=
    (hG i).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)
  have hB := family_holomorphic x Φ k (fun i => G i ∘ zeroSection U) hcomp
  have hS (c : Fin r ⊕ Fin (n+1) ⊕ (Fin r × Fin (n+1))) : HolomorphicAt n
      (derivFamilyAlong (productFlat U x Φ) k G c ∘ zeroSection U) x :=
    (family_holomorphic _ (productFlat U x Φ) k G hG c).comp_contMDiff
      (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)
  constructor
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    rcases c with i | j | ⟨i,j⟩
    · exact isInSpanAt_self ⟨.inl i,rfl⟩ (hcomp i)
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact isInSpanAt_congr (isInSpanAt_self ⟨.inr (.inl j),rfl⟩ (hB _))
          (lifted_family_base U x Φ hΦsrc k G hG (.inr (.inl j))).symm
      · have hj : k≤(j.natAdd n).val := by simp;omega
        simp only [derivFamilyAlong,if_pos hj]
        rw [added_coord_section]
        exact zero_mem_span _ _
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact isInSpanAt_congr (isInSpanAt_self ⟨.inr (.inr (i,j)),rfl⟩ (hB _))
          (lifted_family_base U x Φ hΦsrc k G hG (.inr (.inr (i,j)))).symm
      · have hj : ¬(j.natAdd n).val<k := by simp;omega
        simp only [derivFamilyAlong,if_neg hj,Function.comp_def]
        exact zero_mem_span _ _
  · intro h
    refine IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    exact isInSpanAt_congr (isInSpanAt_self ⟨liftFamilyIndex c,rfl⟩ (hS _))
      (lifted_family_base U x Φ hΦsrc k G hG c)

/-- Whole functional derivative ideals compare on the ACTUAL OPEN models,
with the original carrier closed regular only in its genuine open manifold. -/
theorem zero_section_derivIdealAlong (U : Opens (ComplexModel n)) {A : Set U}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) :
    GermIdeal.pullback (m := n) (zeroSection U) (derivIdealAlong (liftedCarrier A) J)=
      derivIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) := by
  apply GermIdeal.ext
  funext x F
  apply propext
  by_cases hx : x∈A
  · obtain ⟨k,hkn,_hx,Φ,hΦsrc,_h0,hflat⟩ := hA.2 x hx
    obtain ⟨O₀,hO₀,hxO₀,r,G,hG,hgen⟩ := hJ (zeroSection U x)
    let O := O₀ ∩ flatDomain (productFlat U x Φ)
    have hO : IsOpen O := hO₀.inter (isOpen_flatDomain _)
    have hxO : zeroSection U x∈O := ⟨hxO₀,mem_flatDomain_self _⟩
    have hGh : ∀ i z,z∈O → HolomorphicAt (n+1) (G i) z :=
      fun i z hz => holomorphicAt_of_mdifferentiableOn hO₀ (hG i) hz.1
    have hΓsrc := productFlat_source U x Φ hΦsrc
    have hΓflat : ∀ {z : productOpen U},
        z∈(chartAt (ComplexModel (n+1)) (zeroSection U x)).source →
        chartAt (ComplexModel (n+1)) (zeroSection U x) z∈(productFlat U x Φ).source →
        (z∈liftedCarrier A ↔ (productFlat U x Φ).toFun
          (chartAt (ComplexModel (n+1)) (zeroSection U x) z)∈complexCoordinatePlane (n+1) k) := by
      intro z _ hz
      exact productFlat_carrier U x Φ hkn hflat hz
    have hD : ∀ a,(derivIdealAlong (liftedCarrier A) J).mem (zeroSection U x) a ↔
        IsInSpanAt (n := n+1) (·∈range (derivFamilyAlong (productFlat U x Φ) k G))
          (zeroSection U x) a :=
      fun a => derivIdealAlong_mem_iff_of_generators hΓsrc hΓflat hO (fun _ hz => hz.2)
        (fun i => (hG i).mono fun _ hz => hz.1) (fun z hz => hgen z hz.1) hxO a
    have hDf := family_holomorphic (zeroSection U x) (productFlat U x Φ) k G
      (fun i => hGh i _ hxO)
    let W := zeroSection U ⁻¹' O
    have hW : IsOpen W := hO.preimage (zeroSection_contMDiff U).continuous
    have hxW : x∈W := hxO
    have hWΦ : W⊆flatDomain Φ := by
      intro z hz
      have h := (productFlat_domain U x Φ _).mp hz.2
      rwa [projection_section] at h
    have hfat : ∀ {z : U},∀ᶠ w in 𝓝 z,
        ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (zeroSection U) w :=
      fun {_} => Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt
    have hGW : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
        (G i ∘ zeroSection U) W := by
      intro i z hz
      exact ((hGh i _ hz).comp_contMDiff hfat).self_of_nhds.mdifferentiableWithinAt
    have hgenW : ∀ z∈W,∀ a,
        (GermIdeal.pullback (m := n) (zeroSection U) J).mem z a ↔
          IsInSpanAt (n := n) (·∈range fun i => G i ∘ zeroSection U) z a := by
      intro z hz a
      exact FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation hfat J G
        (fun i => hGh i _ hz) (hgen _ hz.1) a
    have hBase := derivIdealAlong_mem_iff_of_generators hΦsrc hflat hW hWΦ hGW hgenW hxW F
    exact (pullback_span_iff U (derivIdealAlong (liftedCarrier A) J) x
      (derivFamilyAlong (productFlat U x Φ) k G) hDf hD F).trans
        ((restricted_family_span_iff U x Φ hΦsrc hkn G (fun i => hGh i _ hxO) F).trans hBase.symm)
  · constructor
    · intro h
      exact derivIdealAlong_mem_of_notMem hA.1 hx (GermIdeal.mem_pullback_iff.mp h).holomorphicAt
    · intro h
      have hF : HolomorphicAt n F x := h.holomorphicAt
      have hsx : zeroSection U x∉liftedCarrier A := by rwa [section_mem_liftedCarrier]
      have hunit : (derivIdealAlong (liftedCarrier A) J).mem (zeroSection U x) (fun _ => 1) :=
        derivIdealAlong_mem_of_notMem (liftedCarrier_closed_submanifold hA).1 hsx (holomorphicAt_const 1)
      apply GermIdeal.mem_pullback_iff.mpr
      exact isInSpanAt_of_eq_mul ⟨fun _ => 1,hunit,rfl⟩ hF hF
        (Eventually.of_forall fun _ => (mul_one _).symm)

/-- All actual iterated derivatives remain on the SAME true open models. -/
theorem zero_section_iterDerivIdealAlong (U : Opens (ComplexModel n)) {A : Set U}
    (hA : IsClosedSubmanifold n A) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (q : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U) (iterDerivIdealAlong (liftedCarrier A) J q)=
      iterDerivIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [iterDerivIdealAlong,zero_section_derivIdealAlong U hA _
      (isCoherent_iterDerivIdealAlong hJ (liftedCarrier_closed_submanifold hA) q),ih,iterDerivIdealAlong]

end
end TranscendentalNakamaye.Pending.HironakaActualOpenZeroSectionDifferentials

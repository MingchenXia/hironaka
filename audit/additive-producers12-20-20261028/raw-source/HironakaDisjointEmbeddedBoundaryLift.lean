import TranscendentalNakamaye.Pending.HironakaDisjointActualBoundaryLift
import TranscendentalNakamaye.Pending.HironakaDisjointMatchedControlledTrace
import TranscendentalNakamaye.Pending.SimultaneousNormalCrossings
import TranscendentalNakamaye.Pending.RegularPointDimension
import TranscendentalNakamaye.Pending.CodimOneAdmissibleAlong

/-!
# Intrinsic-to-ambient whole boundary normal crossings

The actual native centre is supplied only with its literal whole traced
boundary NC. Ambient transversality supplies the contact chart; native
matching, an actual product transition and a genuine finite-neighbourhood
restriction produce NC with every original ambient boundary position.
Positive ambient dimension is explicit. No ambient centre NC or desired
joint-chart certificate is input; no blowup/history conclusion is claimed.
Blueprint: `hironaka-disjoint-embedded-boundary-lift-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaDisjointEmbeddedBoundaryLift
noncomputable section
open FirstPass FirstPass.BlowupSequences NormalCrossings BlowupSNCTransform
  SimultaneousNormalCrossings RegularPointDimension RegularPatchPullback
  GiraudAlong BlowupFlatCoordinates TangentDirectionAlong RegularAtDimTransport
  RegularPatchPushforward HironakaActualSingularChartTransport HironakaRelativeNormalIdeal
  HironakaActualZeroSectionCentreGeometry SubmanifoldChartedSpace

private theorem plane_min {n : ℕ} (b : ℕ) :
    complexCoordinatePlane n (min n b) = complexCoordinatePlane n b := by
  ext z
  constructor
  · intro h j hj
    exact h j (by omega)
  · intro h j hj
    exact h j (by have := j.isLt; omega)

private theorem sub_plane {n b : ℕ} {z c : ComplexModel n}
    (hc : c ∈ complexCoordinatePlane n b) :
    z-c ∈ complexCoordinatePlane n b ↔ z ∈ complexCoordinatePlane n b := by
  constructor
  · intro h j hj
    have he := h j hj
    simpa only [PiLp.sub_apply, hc j hj, sub_zero] using he
  · intro h j hj
    change z j-c j=0
    rw [h j hj, hc j hj, sub_self]

/-- Transversality itself yields a centered actual-dimension native flattening. -/
private theorem centred_transverse {n d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (hn : 0<n) {N : Set X} {E : List (Set X)} {x : X}
    (hN : RegularAtDim (n := n) N x d) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) :
    ∃ (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n),
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ i, x∈E.get i → (s i).val<d) ∧ Set.InjOn s {i | x∈E.get i} ∧
      ∀ z∈flatDomain Θ,
        (z∈N ↔ flatMap Θ z∈complexCoordinatePlane n d) ∧
        ∀ i, x∈E.get i → (z∈E.get i ↔ flatCoord Θ (s i) z=0) := by
  obtain ⟨a,b,Φ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.rfl : N⊆N) hE hT
      hT.hasNormalCrossings hN.2.1
  let c := flatMap Φ x
  have hxD := mem_flatDomain_self Φ
  have hcN : c∈complexCoordinatePlane n b := (hflat hxD.1 hxD.2).2.1.mp hN.2.1
  have hcE : ∀ i,x∈E.get i → c (s i)=0 :=
    fun i hi => (hflat hxD.1 hxD.2).2.2 i hi |>.mp hi
  let Θ := subConst Φ c
  have hΘsrc : Θ.source⊆(chartAt (ComplexModel n) x).target := hsrc
  have hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0 := sub_self _
  have hflatN : ∀ {z : X}, z∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z∈Θ.source →
      (z∈N ↔ Θ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n b) := by
    intro z hz hzΘ
    exact (hflat hz hzΘ).2.1.trans (sub_plane hcN).symm
  have hNb : RegularAtDim (n := n) N x (min n b) := by
    refine ⟨Nat.min_le_left _ _,hN.2.1,Θ,hΘsrc,hΘ0,?_⟩
    intro z hz hzΘ
    rw [plane_min]
    exact hflatN hz hzΘ
  have hb : min n b=d := eq_of_regularAtDim hNb hN
  refine ⟨Θ,s,hΘsrc,hΘ0,?_,hinj,?_⟩
  · intro i hi
    have hiN := (s i).isLt
    have hiB := hs i hi
    omega
  · intro z hz
    constructor
    · rw [←hb,plane_min]
      exact hflatN hz.1 hz.2
    · intro i hi
      have he := (hflat hz.1 hz.2).2.2 i hi
      change (z∈E.get i ↔ (Φ.toFun (chartAt (ComplexModel n) x z)-c) (s i)=0)
      simpa only [PiLp.sub_apply,hcE i hi,sub_zero] using he

private theorem forward_near {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {x : X}
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    Tendsto (flatMap Φ) (𝓝 x) (𝓝 0) := by
  have hc : ContinuousAt (flatMap Φ) x :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.comp
      ((chartAt (ComplexModel n) x).continuousAt (mem_chart_source _ x))
  simpa only [flatMap,h0] using hc.tendsto

private theorem inverse_near {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {x : X}
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    Tendsto (inverseCoordinates Φ) (𝓝 0) (𝓝 x) := by
  have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
  rw [h0] at h
  exact h

private theorem inverse_chart_event {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {x : X}
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    ∀ᶠ u in 𝓝 (0 : ComplexModel n),
      inverseCoordinates Φ u ∈ flatDomain Φ ∧
      chartAt (ComplexModel n) x (inverseCoordinates Φ u)=Φ.invFun u ∧
      flatMap Φ (inverseCoordinates Φ u)=u := by
  have ht : (0 : ComplexModel n)∈Φ.target := h0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hi0 : Φ.invFun 0=chartAt (ComplexModel n) x x := by
    rw [←h0]; exact Φ.left_inv _ Φ.center_mem_source
  have hi : Tendsto Φ.invFun (𝓝 0) (𝓝 (chartAt (ComplexModel n) x x)) := by
    have hc := Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds ht)
    simpa only [hi0] using hc.tendsto
  have he := hi.eventually ((chartAt (ComplexModel n) x).open_target.mem_nhds (mem_chart_target _ x))
  filter_upwards [Φ.isOpen_target.mem_nhds ht,he] with u hu he
  have hchart : chartAt (ComplexModel n) x (inverseCoordinates Φ u)=Φ.invFun u :=
    (chartAt (ComplexModel n) x).right_inv he
  refine ⟨⟨(chartAt (ComplexModel n) x).map_target he,?_⟩,hchart,?_⟩
  · change chartAt (ComplexModel n) x (inverseCoordinates Φ u) ∈ Φ.source
    rw [hchart]
    exact Φ.mapsTo_invFun hu
  · change Φ.toFun (chartAt (ComplexModel n) x (inverseCoordinates Φ u))=u
    rw [hchart]
    exact Φ.right_inv u hu

private theorem coordinate_family_of_eventual {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type*} [Finite ι] (A : ι → Set X) (S : ι → Finset (Fin n)) (x : X)
    (Γ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Γ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Γ.toFun (chartAt (ComplexModel n) x x)=0)
    (h : ∀ i, x∈A i → ∀ᶠ y in 𝓝 x, y∈A i ↔ flatMap Γ y∈coordSubspace (S i)) :
    IsCoordinateFamilyAt n A S x := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i, x∈A i →
      (y∈A i ↔ flatMap Γ y∈coordSubspace (S i)) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x∈A i
    · exact (h i hi).mono fun y hy _ => hy
    · exact Eventually.of_forall fun _ hi' => (hi hi').elim
  obtain ⟨O,hOsub,hOo,hxO⟩ := mem_nhds_iff.mp he
  let e := chartAt (ComplexModel n) x
  let V := e.target ∩ e.symm ⁻¹' O
  have hVo : IsOpen V := e.continuousOn_symm.isOpen_inter_preimage e.open_target hOo
  have hxV : e x∈V := ⟨mem_chart_target _ x, by simpa only [mem_preimage,e.left_inv (mem_chart_source _ x)] using hxO⟩
  let Γ' := Γ.restrict V hVo (e x) ⟨Γ.center_mem_source,hxV⟩
  refine ⟨Γ',fun u hu => hsrc hu.1,h0,?_⟩
  intro i hi y hy hyΓ
  have hyO : y∈O := by
    have hh : e.symm (e y)∈O := hyΓ.2.2
    simpa only [e.left_inv hy] using hh
  exact hOsub hyO i hi

private def liftMask (d t : ℕ) (S : Finset (Fin d)) : Finset (Fin (d+t)) :=
  S.map ⟨fun j => j.castAdd t, Fin.castAdd_injective d t⟩

private def normalMask (d t : ℕ) : Finset (Fin (d+t)) :=
  Finset.univ.filter fun j => d ≤ j.val

private theorem product_tangent {d t : ℕ} (x : ComplexModel d)
    (Φ : LocalHolomorphicEquivAt (n := d) x) (z : ComplexModel (d+t)) (j : Fin d) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z (j.castAdd t) =
      Φ.toFun (tangentProjection d t z) j := by
  change (tangentInclusion d t (Φ.toFun (tangentProjection d t z)) +
    (z - tangentInclusion d t (tangentProjection d t z))) (j.castAdd t) = _
  simp

private theorem product_normal {d t : ℕ} (x : ComplexModel d)
    (Φ : LocalHolomorphicEquivAt (n := d) x) (z : ComplexModel (d+t)) (j : Fin t) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z (j.natAdd d) = z (j.natAdd d) := by
  change (tangentInclusion d t (Φ.toFun (tangentProjection d t z)) +
    (z - tangentInclusion d t (tangentProjection d t z))) (j.natAdd d) = _
  simp

private theorem mem_liftMask {d t : ℕ} (S : Finset (Fin d))
    (x : ComplexModel d) (Φ : LocalHolomorphicEquivAt (n := d) x)
    (z : ComplexModel (d+t)) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z ∈ coordSubspace (liftMask d t S) ↔
      Φ.toFun (tangentProjection d t z) ∈ coordSubspace S := by
  simp only [coordSubspace, Set.mem_ofPred_eq, liftMask, Finset.mem_map]
  constructor
  · intro h j hj
    simpa only [product_tangent] using h (j.castAdd t) ⟨j, hj, rfl⟩
  · rintro h _ ⟨j, hj, rfl⟩
    change (actual_zeroSection_localEquiv d t x Φ).toFun z (j.castAdd t) = 0
    rw [product_tangent]
    exact h j hj

private theorem mem_centreMask {d t : ℕ} (S : Finset (Fin d))
    (x : ComplexModel d) (Φ : LocalHolomorphicEquivAt (n := d) x)
    (z : ComplexModel (d+t)) :
    (actual_zeroSection_localEquiv d t x Φ).toFun z ∈
        coordSubspace (liftMask d t S ∪ normalMask d t) ↔
      Φ.toFun (tangentProjection d t z) ∈ coordSubspace S ∧
        z ∈ complexCoordinatePlane (d+t) d := by
  have hu : ∀ w : ComplexModel (d+t),
      w ∈ coordSubspace (liftMask d t S ∪ normalMask d t) ↔
      w ∈ coordSubspace (liftMask d t S) ∧ w ∈ coordSubspace (normalMask d t) := by
    intro w
    simp only [coordSubspace, Set.mem_ofPred_eq, Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
    · rintro ⟨h₁, h₂⟩ j (hj | hj)
      · exact h₁ j hj
      · exact h₂ j hj
  rw [hu, mem_liftMask]
  apply and_congr_right
  intro _
  change (∀ j ∈ normalMask d t, _) ↔ ∀ j : Fin (d+t), d ≤ j.val → z j = 0
  constructor
  · intro h j hj
    let l : Fin t := ⟨j.val-d, by omega⟩
    have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
    have hh := h j (by simp [normalMask, hj])
    rw [he, product_normal] at hh
    simpa only [he] using hh
  · intro h j hj
    have hd : d ≤ j.val := (Finset.mem_filter.mp hj).2
    let l : Fin t := ⟨j.val-d, by omega⟩
    have he : j = l.natAdd d := Fin.ext (by dsimp [l]; omega)
    rw [he, product_normal]
    exact h _ (by simp)


/-- Intrinsic NC lifts to the entire actual ambient boundary, in the native atlas. -/
theorem hasNormalCrossings_native_image {d t : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    {N : Set X} (hS : ∀ p∈N, RegularAtDim (n := d+t) N p d)
    (hn : 0<d+t) {E : List (Set X)} (hE : IsSNCDivisor (d+t) E)
    (hT : IsTransverse (d+t) N E) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (D : Set N), HasNormalCrossings d D (E.map fun H => (Subtype.val : N → X) ⁻¹' H) →
      HasNormalCrossings (d+t) ((Subtype.val : N → X) '' D) E := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro D hD
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨Θ,s,hΘsrc,hΘ0,hs,hinj,hΘflat⟩ := centred_transverse hn (hS p.val p.property) hE hT
  have hflatN : ∀ z, z∈(chartAt (ComplexModel (d+t)) p.val).source →
      chartAt (ComplexModel (d+t)) p.val z∈Θ.source →
      (z∈N ↔ Θ.toFun (chartAt (ComplexModel (d+t)) p.val z)∈complexCoordinatePlane (d+t) d) :=
    fun z hz hzΘ => (hΘflat z ⟨hz,hzΘ⟩).1
  obtain ⟨Ψ,hΨ0,hmatch⟩ := HironakaDisjointMatchedControlledTrace.exists_matched_coordinates
    hS p Θ hΘsrc hΘ0 hflatN (Diffeomorph.refl 𝓘(ℂ,ComplexModel d) N ∞)
  obtain ⟨S₀,S,⟨Φ,hΦsrc,hΦ0,hΦflat⟩,hcard⟩ := hD p hp
  have hΨtarget : (0 : ComplexModel d)∈Ψ.target := hΨ0 ▸ Ψ.mapsTo_toFun Ψ.center_mem_source
  have hΨinv0 : Ψ.invFun 0=chartAt (ComplexModel d) p p := by
    rw [←hΨ0]; exact Ψ.left_inv _ Ψ.center_mem_source
  let F := LocalHolomorphicEquivAt.comp (symmAt Ψ hΨtarget) Φ hΨinv0
  have hF0 : F.toFun 0=0 := by
    change Φ.toFun (Ψ.invFun 0)=0
    rw [hΨinv0]
    exact hΦ0
  let P := actual_zeroSection_localEquiv d t 0 F
  let Γ := LocalHolomorphicEquivAt.comp Θ P (by simpa only [map_zero] using hΘ0)
  have hΓsrc : Γ.source⊆(chartAt (ComplexModel (d+t)) p.val).target :=
    fun _ hz => hΘsrc hz.1
  have hΓ0 : Γ.toFun (chartAt (ComplexModel (d+t)) p.val p.val)=0 := by
    change P.toFun (Θ.toFun (chartAt (ComplexModel (d+t)) p.val p.val))=0
    rw [hΘ0]
    change tangentInclusion d t (F.toFun (tangentProjection d t 0)) +
      (0-tangentInclusion d t (tangentProjection d t 0))=0
    simp only [map_zero,hF0,sub_self,add_zero]
  let u : X → ComplexModel d := fun y => tangentProjection d t (flatMap Θ y)
  let q : X → N := fun y => inverseCoordinates Ψ (u y)
  have hu : Tendsto u (𝓝 p.val) (𝓝 0) := by
    have hh := (tangentProjection d t).continuous.tendsto (0 : ComplexModel (d+t))
    simpa only [u, Function.comp_def, map_zero] using hh.comp (forward_near Θ hΘ0)
  have hq : Tendsto q (𝓝 p.val) (𝓝 p) := (inverse_near Ψ hΨ0).comp hu
  have hsu : Tendsto (fun y => tangentInclusion d t (u y)) (𝓝 p.val) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d) |>.comp hu
  have hΘtarget : (0 : ComplexModel (d+t))∈Θ.target := hΘ0 ▸ Θ.mapsTo_toFun Θ.center_mem_source
  have hevent : ∀ᶠ y in 𝓝 p.val,
      y∈flatDomain Θ ∧ q y∈flatDomain Φ ∧
      chartAt (ComplexModel d) p (q y)=Ψ.invFun (u y) ∧
      (q y).val=inverseCoordinates Θ (tangentInclusion d t (u y)) ∧
      tangentInclusion d t (u y)∈Θ.target := by
    filter_upwards [(isOpen_flatDomain Θ).mem_nhds (mem_flatDomain_self Θ),
      hq.eventually ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)),
      hu.eventually (inverse_chart_event Ψ hΨ0), hu.eventually hmatch,
      hsu.eventually (Θ.isOpen_target.mem_nhds hΘtarget)] with y hy hqΦ hqΨ hm ht
    exact ⟨hy,hqΦ,hqΨ.2.1,hm,ht⟩
  let j : Fin E.length → Fin (E.map fun H => (Subtype.val : N → X) ⁻¹' H).length :=
    fun i => ⟨i.val,by simp only [List.length_map]; exact i.isLt⟩
  let S' : Fin E.length → Finset (Fin (d+t)) := fun i => liftMask d t (S (j i))
  refine ⟨liftMask d t S₀ ∪ normalMask d t,S',?_,?_⟩
  · apply coordinate_family_of_eventual _ _ p.val Γ hΓsrc hΓ0
    intro o ho
    filter_upwards [hevent] with y hy
    obtain ⟨hyΘ,hqΦ,hqchart,hmatchy,hsut⟩ := hy
    have hqΘ : (q y).val∈flatDomain Θ := by
      rw [hmatchy]
      exact (flatInverse_mem Θ hsut hΘsrc).1
    have hqcoords : flatMap Θ (q y).val=tangentInclusion d t (u y) := by
      rw [hmatchy]
      exact (flatInverse_mem Θ hsut hΘsrc).2
    have hFq : F.toFun (u y)=flatMap Φ (q y) := by
      change Φ.toFun (Ψ.invFun (u y))=Φ.toFun (chartAt (ComplexModel d) p (q y))
      rw [hqchart]
    have hqeq (hplane : flatMap Θ y∈complexCoordinatePlane (d+t) d) : (q y).val=y := by
      rw [hmatchy]
      have hpcoords : tangentInclusion d t (u y)=flatMap Θ y :=
        tangentInclusion_projection_eq_of_mem_plane d t hplane
      rw [hpcoords]
      exact flatInverse_flat Θ hyΘ
    cases o with
    | none =>
      have himage : y∈(Subtype.val : N → X) '' D ↔
          q y∈D ∧ flatMap Θ y∈complexCoordinatePlane (d+t) d := by
        constructor
        · rintro ⟨z,hz,hzy⟩
          have hplane := (hΘflat y hyΘ).1.mp (hzy ▸ z.property)
          have hqz : q y=z := Subtype.ext ((hqeq hplane).trans hzy.symm)
          exact ⟨hqz ▸ hz,hplane⟩
        · rintro ⟨hDq,hplane⟩
          exact ⟨q y,hDq,hqeq hplane⟩
      change y∈(Subtype.val : N → X) '' D ↔
        Γ.toFun (chartAt (ComplexModel (d+t)) p.val y)∈coordSubspace (liftMask d t S₀ ∪ normalMask d t)
      change y∈(Subtype.val : N → X) '' D ↔
        P.toFun (flatMap Θ y)∈coordSubspace (liftMask d t S₀ ∪ normalMask d t)
      rw [mem_centreMask,hFq,himage]
      exact and_congr_left fun _ => hΦflat none hp hqΦ.1 hqΦ.2
    | some i =>
      have hget : (E.map fun H => (Subtype.val : N → X) ⁻¹' H).get (j i)=
          (Subtype.val : N → X) ⁻¹' E.get i := by simp [j]
      have hi : p.val∈E.get i := ho
      have hsame : y∈E.get i ↔ (q y).val∈E.get i := by
        rw [(hΘflat y hyΘ).2 i hi,(hΘflat (q y).val hqΘ).2 i hi]
        change flatMap Θ y (s i)=0 ↔ flatMap Θ (q y).val (s i)=0
        rw [hqcoords]
        let a : Fin d := ⟨(s i).val,hs i hi⟩
        have ha : a.castAdd t=s i := Fin.ext rfl
        rw [←ha,tangentInclusion_tangent]
        rfl
      have hi' : p∈(E.map fun H => (Subtype.val : N → X) ⁻¹' H).get (j i) := by
        rw [hget]; exact hi
      have hphi := hΦflat (some (j i)) hi' hqΦ.1 hqΦ.2
      change y∈E.get i ↔ P.toFun (flatMap Θ y)∈coordSubspace (liftMask d t (S (j i)))
      rw [mem_liftMask,hFq]
      exact hsame.trans (by simpa only [Option.elim_some,hget,mem_preimage,flatMap,complexChartAt] using hphi)
  · intro i hi
    have hget : (E.map fun H => (Subtype.val : N → X) ⁻¹' H).get (j i)=
        (Subtype.val : N → X) ⁻¹' E.get i := by simp [j]
    have hi' : p∈(E.map fun H => (Subtype.val : N → X) ⁻¹' H).get (j i) := by
      rw [hget]; exact hi
    simpa only [S',liftMask,Finset.card_map] using hcard (j i) hi'

end
end TranscendentalNakamaye.Pending.HironakaDisjointEmbeddedBoundaryLift

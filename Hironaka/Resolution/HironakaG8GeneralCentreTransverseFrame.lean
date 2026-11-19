import Hironaka.Resolution.HironakaG8GeneralCentreTransverseTrace
import Hironaka.Blowup.NormalCrossings

set_option autoImplicit false

/-!
# A local transverse boundary coordinate preserving nested smooth carriers

The inverse function theorem replaces one centre coordinate by an ordinary
local holomorphic defining equation whose differential is nonzero on the
centre tangent space. All normal coordinates of both nested carriers remain
unchanged. No simultaneous carrier/boundary frame is an input.

This is a local frame producer, not a residual successor or a completed
original Hironaka goal. Extraction of the scalar transversality witness from
the actual source SNC data is a separate consumer step.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8GeneralCentreTransverseFrame

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates
  NestedFlattening RegularAtDimTransport

noncomputable section

variable {n : ℕ}

private def replaceCoordinate (f : ComplexModel n → ℂ) (i : Fin n)
    (z : ComplexModel n) : ComplexModel n :=
  z + (f z - z i) • EuclideanSpace.single i (1 : ℂ)

private theorem replaceCoordinate_apply (f : ComplexModel n → ℂ) (i j : Fin n)
    (z : ComplexModel n) :
    replaceCoordinate f i z j = if j = i then f z else z j := by
  by_cases hji : j = i
  · subst j
    simp [replaceCoordinate]
  · simp [replaceCoordinate, hji]

private theorem replaceCoordinate_mem_plane_iff (f : ComplexModel n → ℂ)
    {i : Fin n} {k : ℕ} (hi : i.val < k) (z : ComplexModel n) :
    replaceCoordinate f i z ∈ complexCoordinatePlane n k ↔
      z ∈ complexCoordinatePlane n k := by
  have hcoord : ∀ j : Fin n, k ≤ j.val → replaceCoordinate f i z j = z j := by
    intro j hj
    have hji : j ≠ i := by intro h; subst j; omega
    rw [replaceCoordinate_apply, if_neg hji]
  exact ⟨fun hz j hj => (hcoord j hj).symm.trans (hz j hj),
    fun hz j hj => (hcoord j hj).trans (hz j hj)⟩

/-- Replace an actual centre coordinate by a local scalar submersion, using
the holomorphic inverse function theorem. Every plane with larger dimension
is preserved because none of its normal coordinates changes. -/
theorem exists_coordinate_replacement {f : ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (h0U : (0 : ComplexModel n) ∈ U)
    (hf : DifferentiableOn ℂ f U) (hf0 : f 0 = 0) {kC : ℕ}
    (htrans : ∃ v ∈ complexCoordinatePlane n kC, fderiv ℂ f 0 v ≠ 0) :
    ∃ (i : Fin n) (Ψ : LocalHolomorphicEquivAt (n := n) 0),
      i.val < kC ∧ Ψ.source ⊆ U ∧ Ψ.toFun 0 = 0 ∧
      (∀ z, Ψ.toFun z i = f z) ∧
      ∀ k, kC ≤ k → ∀ z,
        (z ∈ complexCoordinatePlane n k ↔ Ψ.toFun z ∈ complexCoordinatePlane n k) := by
  classical
  let D := fderiv ℂ f 0
  obtain ⟨v, hv, hDv⟩ := htrans
  obtain ⟨i, hi, hDi⟩ : ∃ i : Fin n, i.val < kC ∧ D (EuclideanSpace.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    have hvsum : v = ∑ j : Fin n, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    apply hDv
    change D v = 0
    rw [hvsum, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul]
    by_cases hj : j.val < kC
    · rw [h j hj, smul_zero]
    · rw [hv j (Nat.le_of_not_lt hj), zero_smul]
  let eᵢ : ComplexModel n := EuclideanSpace.single i (1 : ℂ)
  let L : ComplexModel n →L[ℂ] ComplexModel n :=
    ContinuousLinearMap.id ℂ _ + (D - EuclideanSpace.proj i).smulRight eᵢ
  have hFd : DifferentiableOn ℂ (replaceCoordinate f i) U :=
    differentiableOn_id.add ((hf.sub (EuclideanSpace.proj i).differentiableOn).smul_const eᵢ)
  have hFL : HasFDerivAt (replaceCoordinate f i) L 0 :=
    (hasFDerivAt_id 0).add
      (((hf.differentiableAt (hU.mem_nhds h0U)).hasFDerivAt.sub
        (EuclideanSpace.proj i).hasFDerivAt).smul_const eᵢ)
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hcoords : ∀ j : Fin n, j ≠ i → w j = 0 := by
      intro j hji
      have hj := congrArg (fun z : ComplexModel n => z j) hw
      simpa [L, eᵢ, hji] using hj
    have hwi : w = w i • eᵢ := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [eᵢ]
      · simp [eᵢ, hji, hcoords j hji]
    have hDzero : D w = 0 := by
      have hiw := congrArg (fun z : ComplexModel n => z i) hw
      simpa [L, eᵢ] using hiw
    have hcoeff : w i = 0 := by
      rw [hwi, map_smul] at hDzero
      exact (smul_eq_zero.mp hDzero).resolve_right hDi
    rw [hwi, hcoeff, zero_smul]
  have hFinj : Function.Injective (fderiv ℂ (replaceCoordinate f i) 0) := by
    rw [hFL.fderiv]
    exact hLinj
  obtain ⟨Ψ, hΨU, hΨF, -⟩ := exists_localHolomorphicEquivAt hU h0U hFd hFinj
  refine ⟨i, Ψ, hi, hΨU, ?_, ?_, ?_⟩
  · rw [hΨF]
    simp [replaceCoordinate, hf0]
  · intro z
    rw [hΨF, replaceCoordinate_apply, if_pos rfl]
  · intro k hk z
    rw [hΨF]
    exact (replaceCoordinate_mem_plane_iff f (hi.trans_le hk) z).symm

section Manifold

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Nested regular carriers and an ordinary transverse local defining
function produce an actual qualified common frame. The transversality input
is nonvanishing of the equation's differential on an actual centre tangent
vector, rather than an assumed simultaneous coordinate frame. -/
theorem exists_transverse_nested_flattening {C P H : Set X} {x : X} {kC kP : ℕ}
    (hC : RegularAtDim (n := n) C x kC) (hP : RegularAtDim (n := n) P x kP)
    (hCP : C ⊆ P) {f : X → ℂ} (hf : HolomorphicAt n f x)
    (hH : ∀ᶠ y in 𝓝 x, y ∈ H ↔ f y = 0) (hxH : x ∈ H)
    (htrans : ∃ ξ ∈ tangentSpace n C x, germDiff n f x ξ ≠ 0) :
    ∃ (i : Fin n)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      i.val < kC ∧ Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x y ∈ Θ.source →
          (y ∈ C ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kC) ∧
          (y ∈ P ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kP) ∧
          (y ∈ H ↔ Θ.toFun (chartAt (ComplexModel n) x y) i = 0) := by
  have hkCP : kC ≤ kP := le_of_regularAtDim_subset hC hP hCP
  obtain ⟨Φ, hΦsrc, hΦ0, hΦflat⟩ := exists_nested_flattening hkCP hC hP hCP
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Φ
  change Φ.toFun (chartAt (ComplexModel n) x x) = 0 at hΦ0
  have hxΦ : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  let F : ComplexModel n → ℂ := fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z))
  have h0T : (0 : ComplexModel n) ∈ Φ.target := hΦ0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hInv : Tendsto (fun z => (chartAt (ComplexModel n) x).symm (Φ.invFun z))
      (𝓝 (0 : ComplexModel n)) (𝓝 x) := by
    simpa only [hΦ0] using tendsto_flatInverse Φ hxΦ
  have hFd : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0T, hInv.eventually hf.eventually] with z hz hfz
    have hzChart := hΦsrc (Φ.mapsTo_invFun hz)
    exact (differentiableAt_comp_chart_symm hzChart hfz.mdifferentiableAt).comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
  have hF0 : F 0 = 0 := by
    have hfx : f x = 0 := hH.self_of_nhds.mp hxH
    have hInv0 : (chartAt (ComplexModel n) x).symm (Φ.invFun 0) = x := by
      rw [← hΦ0]
      exact flatInverse_flat Φ hxΦ
    simpa only [F, hInv0] using hfx
  have hHflat : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      (chartAt (ComplexModel n) x).symm (Φ.invFun z) ∈ H ↔ F z = 0 := hInv.eventually hH
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Φ.target ∧
      DifferentiableAt ℂ F z ∧
      ((chartAt (ComplexModel n) x).symm (Φ.invFun z) ∈ H ↔ F z = 0) := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0T, hFd, hHflat] with z hz hdz hHz
    exact ⟨hz, hdz, hHz⟩
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp hnear
  obtain ⟨ξ, hξC, hξf⟩ := htrans
  let A := fderiv ℂ (flatMap Φ x) (chartAt (ComplexModel n) x x)
  have hAsurj : Function.Surjective A := fun v =>
    ⟨flatVec Φ x v, fderiv_flatMap_flatVec hΦsrc hxΦ v⟩
  have hAinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective (f := (A : ComplexModel n →ₗ[ℂ] ComplexModel n))).mpr hAsurj
  have hξflat : flatVec Φ x (A ξ) = ξ := by
    apply hAinj
    exact fderiv_flatMap_flatVec hΦsrc hxΦ (A ξ)
  have hAξC : A ξ ∈ complexCoordinatePlane n kC := by
    intro j hj
    have hzero := (mem_tangentSpace_iff hΦsrc
      (fun hy hyΦ => (hΦflat hy hyΦ).1) hxΦ hC.2.1).mp hξC j hj
    rw [germDiff_flatCoord hΦsrc hxΦ, ContinuousLinearMap.comp_apply] at hzero
    exact hzero
  have hFtrans : ∃ v ∈ complexCoordinatePlane n kC, fderiv ℂ F 0 v ≠ 0 := by
    refine ⟨A ξ, hAξC, ?_⟩
    have hchain := germDiff_flatVec hΦsrc hxΦ hf (A ξ)
    rw [hξflat, hΦ0] at hchain
    rw [← hchain]
    exact hξf
  obtain ⟨i, Ψ, hi, hΨU, hΨ0, hΨi, hΨplane⟩ :=
    exists_coordinate_replacement hUopen h0U (fun z hz => (hUsub hz).2.1.differentiableWithinAt)
      hF0 hFtrans
  let Θ := LocalHolomorphicEquivAt.comp Φ Ψ hΦ0
  refine ⟨i, Θ, hi, fun z hz => hΦsrc hz.1, ?_, ?_⟩
  · change Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x x)) = 0
    rw [hΦ0, hΨ0]
  · intro y hy hyΘ
    change chartAt (ComplexModel n) x y ∈ Φ.source ∩ Φ.toFun ⁻¹' Ψ.source at hyΘ
    have hflat := hΦflat hy hyΘ.1
    have hyU := hUsub (hΨU hyΘ.2)
    have hInvy : (chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x y))) = y :=
      flatInverse_flat Φ ⟨hy, hyΘ.1⟩
    refine ⟨hflat.1.trans (hΨplane kC le_rfl _),
      hflat.2.trans (hΨplane kP hkCP _), ?_⟩
    change y ∈ H ↔ Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x y)) i = 0
    rw [hΨi]
    simpa only [F, hInvy] using hyU.2.2

private theorem flatVec_mem_tangentSpace_of_coordinate_subspace
    {C : Set X} {x : X}
    (Ω : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΩsrc : Ω.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΩ0 : Ω.toFun (chartAt (ComplexModel n) x x) = 0)
    (S : Finset (Fin n))
    (hΩC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ C ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈ NormalCrossings.coordSubspace S))
    (v : ComplexModel n) (hv : ∀ j ∈ S, v j = 0) :
    flatVec Ω x v ∈ tangentSpace n C x := by
  have hxΩ : x ∈ flatDomain Ω := mem_flatDomain_self Ω
  have h0T : (0 : ComplexModel n) ∈ Ω.target := hΩ0 ▸ Ω.mapsTo_toFun Ω.center_mem_source
  have hInv0 : Ω.invFun 0 = chartAt (ComplexModel n) x x := by
    rw [← hΩ0]
    exact Ω.left_inv _ Ω.center_mem_source
  have hInv : Tendsto (fun z => (chartAt (ComplexModel n) x).symm (Ω.invFun z))
      (𝓝 (0 : ComplexModel n)) (𝓝 x) := by
    simpa only [hΩ0] using tendsto_flatInverse Ω hxΩ
  have hline : Tendsto (fun τ : ℂ => τ • v) (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
    have hlim : Tendsto (fun τ : ℂ => τ • v) (𝓝 0) (𝓝 ((0 : ℂ) • v)) :=
      (continuous_id.smul continuous_const : Continuous fun τ : ℂ => τ • v).tendsto 0
    simpa only [zero_smul] using hlim
  apply mem_tangentSpace.mpr
  intro g hg
  let G : ComplexModel n → ℂ := fun z => g ((chartAt (ComplexModel n) x).symm (Ω.invFun z))
  have hGd : DifferentiableAt ℂ G 0 := by
    have h₁ : DifferentiableAt ℂ (g ∘ (chartAt (ComplexModel n) x).symm) (Ω.invFun 0) := by
      rw [hInv0]
      exact differentiableAt_germ hg.1
    exact h₁.comp 0 (Ω.invFun_holomorphic.differentiableAt (Ω.isOpen_target.mem_nhds h0T))
  have hGvan : ∀ᶠ τ : ℂ in 𝓝 0, G (τ • v) = 0 := by
    filter_upwards [hline.eventually (Ω.isOpen_target.mem_nhds h0T),
      (hInv.comp hline).eventually hg.2] with τ hτ hgv
    obtain ⟨hyΩ, hcoords⟩ := flatInverse_mem Ω hτ hΩsrc
    apply hgv
    apply (hΩC hyΩ.1 hyΩ.2).mpr
    rw [hcoords]
    intro j hj
    simp only [PiLp.smul_apply, hv j hj, smul_zero]
  have hlineD : HasDerivAt (fun τ : ℂ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hGD : HasFDerivAt G (fderiv ℂ G 0) ((0 : ℂ) • v) := by
    simpa using hGd.hasFDerivAt
  have hGlineD := hGD.comp_hasDerivAt (0 : ℂ) hlineD
  have hGline0 : HasDerivAt (fun τ : ℂ => G (τ • v)) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hGvan
  have hDzero := hGlineD.unique hGline0
  rw [germDiff_flatVec hΩsrc hxΩ hg.1 v, hΩ0]
  exact hDzero

/-- The actual local C/H normal-crossing coordinates provide the scalar
equation and its nonzero centre derivative in the transverse branch. The
larger carrier need not be adapted to this initial chart. -/
theorem local_equation_transverse_of_coordinate_crossings {C H : Set X} {x : X}
    (Ω : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΩsrc : Ω.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΩ0 : Ω.toFun (chartAt (ComplexModel n) x x) = 0)
    (S : Finset (Fin n)) (h : Fin n) (hh : h ∉ S)
    (hΩC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ C ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈ NormalCrossings.coordSubspace S))
    (hΩH : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ H ↔ flatCoord Ω h y = 0)) :
    ∃ f : X → ℂ, HolomorphicAt n f x ∧
      (∀ᶠ y in 𝓝 x, y ∈ H ↔ f y = 0) ∧
      ∃ ξ ∈ tangentSpace n C x, germDiff n f x ξ ≠ 0 := by
  let eₕ : ComplexModel n := EuclideanSpace.single h (1 : ℂ)
  have hxΩ : x ∈ flatDomain Ω := mem_flatDomain_self Ω
  refine ⟨flatCoord Ω h, holomorphicAt_flatCoord Ω h hxΩ, ?_,
    flatVec Ω x eₕ, ?_, ?_⟩
  · filter_upwards [(isOpen_flatDomain Ω).mem_nhds hxΩ] with y hy
    exact hΩH hy.1 hy.2
  · apply flatVec_mem_tangentSpace_of_coordinate_subspace Ω hΩsrc hΩ0 S hΩC eₕ
    intro j hj
    have hjh : j ≠ h := fun heq => hh (heq ▸ hj)
    simp [eₕ, hjh]
  · rw [germDiff_flatCoord_flatVec hΩsrc hxΩ]
    simp [eₕ]

/-- Construct the qualified native chart from ordinary local geometry and
apply the checked moving-base total-trace theorem on that actual chart. -/
theorem frequently_exceptional_strict_not_boundary_of_local_equation
    {C : Set X} [Fact (IsClosedSubmanifold n C)]
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hHclosed : IsClosed H)
    {p : BlowupConstruction.BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (BlowupConstruction.blowupProj n C) C P)
    (hpC : p.base ∈ C) (hpH : p.base ∈ H) {f : X → ℂ}
    (hf : HolomorphicAt n f p.base)
    (hH : ∀ᶠ y in 𝓝 p.base, y ∈ H ↔ f y = 0)
    (htrans : ∃ ξ ∈ tangentSpace n C p.base, germDiff n f p.base ξ ≠ 0) :
    ∃ᶠ q in 𝓝 p, q.base ∈ C ∧
      q ∈ geoStrictTransform (BlowupConstruction.blowupProj n C) C P ∧
      q ∉ geoStrictTransform (BlowupConstruction.blowupProj n C) C H := by
  obtain ⟨kC, hkC⟩ := (Fact.out : IsClosedSubmanifold n C).2 p.base hpC
  obtain ⟨kP, hkP⟩ := hP.2 p.base (hCP hpC)
  obtain ⟨i, Θ, hi, hΘsrc, -, hΘflat⟩ :=
    exists_transverse_nested_flattening hkC hkP hCP hf hH hpH htrans
  have hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) p.base).source →
      chartAt (ComplexModel n) p.base y ∈ Θ.source →
        (y ∈ C ↔ Θ.toFun (chartAt (ComplexModel n) p.base y) ∈ complexCoordinatePlane n kC) :=
    fun hy hyΘ => (hΘflat hy hyΘ).1
  have hnot := p.dirVec_not_mem hpC
  rw [mem_tangentSpace_iff hΘsrc hflatC (mem_flatDomain_self Θ) hpC] at hnot
  push Not at hnot
  obtain ⟨j, hj, hne⟩ := hnot
  let c : BlowupConstruction.FlatChart n C := ⟨p.base, kC, Θ, hΘsrc, hflatC, j, hj⟩
  have hps : p ∈ c.source := by
    refine ⟨mem_flatDomain_self Θ, ?_⟩
    change BlowupConstruction.extVal (flatCoord Θ j) p ≠ 0
    rw [BlowupConstruction.extVal_of_mem hpC]
    exact hne
  exact HironakaG8GeneralCentreTransverseTrace.frequently_exceptional_strict_not_boundary
    c hP hCP (fun hy hyΘ => (hΘflat hy hyΘ).2.1) i hi hHclosed
    (fun hy hyΘ => (hΘflat hy hyΘ).2.2) hp hps hpC hpH

end Manifold

end

end Hironaka.HironakaG8GeneralCentreTransverseFrame

import Hironaka.Analytic.PshCodimTwoLocal
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Analytic.LocalPotentialIndependence
import Hironaka.Analytic.PotentialTheory.EnvelopesBasic
import Hironaka.Manifold.HolomorphicMaps
import Hironaka.Analytic.UscRegularizationContinuous

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Theta-plurisubharmonic functions extend across codimension-two submanifolds

Let `K` be a closed subset of a complex manifold `M` which near each of its points is carried by a
holomorphic flattening into a coordinate plane of codimension `≥ 2`, and let `θ` be a smooth real
form with local potentials.  If `v` is `θ`-plurisubharmonic off `K` (in every chart, near every
point off `K`), then its upper semicontinuous regularization across `K`
(`extensionAcross K v`) is `θ`-plurisubharmonic on `M` and equals `v` off `K`
(`thetaPlurisubharmonic_extensionAcross`).

In a chart near a point of `K`, add a local potential `ρ` of `θ` and apply
`PshCodimTwoLocal.plurisubharmonicOn_of_regularization` to the biholomorphism
`Φ ∘ (chart transition)`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ThetaPshCodimTwoExtension

open Hironaka Hironaka.HolomorphicMaps PshCodimTwoExtension PshCodimTwoLocal
  BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

variable {K : Set M} {v : M → EReal}

open scoped Classical in
/-- The upper semicontinuous regularization of `v` across `K`. -/
def extensionAcross (K : Set M) (v : M → EReal) : M → EReal :=
  uscRegularization fun y => if y ∈ K then ⊥ else v y

/-- Passing to a manifold chart commutes with the upper regularization used
for `extensionAcross`.  Thus the chart expression of the global extension is
the coordinate extension across the chart preimage of the exceptional set.
This is the regularization compatibility needed to transport the proved
coordinate-hyperplane theorem to a locally flattened analytic hypersurface. -/
theorem chartFunction_extensionAcross_eq_extension_preimage
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target) :
    chartFunction (extensionAcross K v) e z =
      extension (e.val.symm ⁻¹' K) (chartFunction v e) z := by
  classical
  rw [extensionAcross]
  rw [← uscRegularization_chartFunction_apply
    (fun y => if y ∈ K then (⊥ : EReal) else v y) e hz]
  rfl

/-- An extended-real function plus a continuous real function. -/
theorem upperSemicontinuousAt_add_real {X : Type*} [TopologicalSpace X] {f : X → EReal}
    {g : X → ℝ} {x : X} (hf : UpperSemicontinuousAt f x) (hg : ContinuousAt g x) :
    UpperSemicontinuousAt (fun y => f y + (g y : EReal)) x :=
  hf.add' (continuous_coe_real_ereal.continuousAt.comp hg).upperSemicontinuousAt
    (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))

theorem upperSemicontinuousAt_of_add_real {X : Type*} [TopologicalSpace X] {f : X → EReal}
    {g : X → ℝ} {x : X} (hf : UpperSemicontinuousAt (fun y => f y + (g y : EReal)) x)
    (hg : ContinuousAt g x) : UpperSemicontinuousAt f x := by
  have h := upperSemicontinuousAt_add_real hf hg.neg
  have heq : ∀ y, f y + (g y : EReal) + ((-g y : ℝ) : EReal) = f y := fun y => by
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  intro c hc
  have h' := h c (by simp only [Pi.neg_apply, heq]; exact hc)
  filter_upwards [h'] with y hy
  simpa only [Pi.neg_apply, heq] using hy

variable [IsComplexManifold n M]
variable {θ : SmoothRealForm n M 2}

/-- `θ`-plurisubharmonicity off `K`. -/
def ThetaPshOff (θ : SmoothRealForm n M 2) (K : Set M) (v : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target → e.val.symm z ∉ K →
    ∃ W ρ, z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction v e y + (ρ y : EReal)) W

theorem upperSemicontinuousAt_of_thetaPshOff (hv : ThetaPshOff θ K v) {y : M} (hy : y ∉ K) :
    UpperSemicontinuousAt v y := by
  set e := complexChartAt (n := n) y
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hye
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hv e (e.val y) hz (by rwa [e.val.left_inv hye])
  have h1 : UpperSemicontinuousAt (fun w => chartFunction v e w + (ρ w : EReal)) (e.val y) := by
    intro c hc
    have := hpsh.discPshOn.upperSemicontinuousOn _ hzW c hc
    rwa [nhdsWithin_eq_nhds.mpr (hρ.1.mem_nhds hzW)] at this
  have h2 : UpperSemicontinuousAt (chartFunction v e) (e.val y) :=
    upperSemicontinuousAt_of_add_real h1
      ((hρ.2.2.1.continuousOn _ hzW).continuousAt (hρ.1.mem_nhds hzW))
  intro c hc
  have h3 := h2 c (by simpa [chartFunction, e.val.left_inv hye] using hc)
  filter_upwards [(e.val.continuousAt hye).eventually h3, e.val.open_source.mem_nhds hye]
    with y' h1' h2'
  simpa [chartFunction, e.val.left_inv h2'] using h1'

theorem extensionAcross_eq_of_notMem (hK : IsClosed K) (hv : ThetaPshOff θ K v) {y : M}
    (hy : y ∉ K) : extensionAcross K v y = v y := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have husc := upperSemicontinuousAt_of_thetaPshOff hv hy c hc
    have hU : {y' | y' ∉ K ∧ v y' < c} ∈ 𝓝 y := Filter.inter_mem (hK.isOpen_compl.mem_nhds hy) husc
    refine (uscRegularization_le_localSup _ hU).trans (iSup₂_le fun y' hy' => ?_)
    simp only [if_neg hy'.1]
    exact hy'.2.le
  · have := le_uscRegularization (fun y => if y ∈ K then ⊥ else v y) y
    simp only [if_neg hy] at this
    exact this


/-- A bound for the regularization at a chart point from a bound off `K` nearby. -/
theorem extensionAcross_le_of_chart {e : ComplexChart n M} {w : ComplexModel n}
    (hw : w ∈ e.val.target) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 w) {b : EReal}
    (hb : ∀ w' ∈ N, w' ∈ e.val.target → e.val.symm w' ∉ K → chartFunction v e w' ≤ b) :
    extensionAcross K v (e.val.symm w) ≤ b := by
  classical
  obtain ⟨N', hN'sub, hN'o, hwN'⟩ := mem_nhds_iff.mp (Filter.inter_mem hN (e.val.open_target.mem_nhds hw))
  have hU : IsOpen (e.val.symm '' N') :=
    e.val.symm.isOpen_image_of_subset_source hN'o fun w' hw' => (hN'sub hw').2
  refine (uscRegularization_le_localSup _ (hU.mem_nhds ⟨w, hwN', rfl⟩)).trans
    (iSup₂_le fun y hy => ?_)
  obtain ⟨w', hw', rfl⟩ := hy
  by_cases hyK : e.val.symm w' ∈ K
  · simp [hyK]
  · simp only [if_neg hyK]
    exact hb w' (hN'sub hw').1 (hN'sub hw').2 hyK

theorem ereal_lt_sub_of_add_lt {a : EReal} {ρ r : ℝ} (h : a + (ρ : EReal) < (r : EReal)) :
    a < ((r - ρ : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact EReal.bot_lt_coe _
  | top => simp at h
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
    exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- Flattenings of `K` into coordinate planes of codimension `≥ 2`. -/
def HasCodimTwoFlattenings (K : Set M) : Prop :=
  ∀ p ∈ K, ∃ k : ℕ, k + 2 ≤ n ∧
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p),
      Φ.source ⊆ (chartAt (ComplexModel n) p).target ∧
      ∀ y ∈ flatDomain Φ, y ∈ K →
        Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n k

/-- **Extension across a codimension-two set.** -/
theorem thetaPlurisubharmonic_extensionAcross (hK : IsClosed K) (hflat : HasCodimTwoFlattenings (n := n) K)
    (hθ : HasSmoothLocalPotentials θ) (hv : ThetaPshOff θ K v) :
    ThetaPlurisubharmonic θ (extensionAcross K v) := by
  classical
  intro e z hz
  set ψ := extensionAcross K v
  by_cases hzK : e.val.symm z ∈ K
  swap
  · obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hv e z hz hzK
    set W' := W ∩ (e.val.target ∩ e.val.symm ⁻¹' Kᶜ)
    have hW' : IsOpen W' := hρ.1.inter (e.val.isOpen_inter_preimage_symm hK.isOpen_compl)
    refine ⟨W', ρ, ⟨hzW, hz, hzK⟩, hρ.mono hW' inter_subset_left, fun w hw => ?_⟩
    refine (hpsh w hw.1).congr ?_
    filter_upwards [hW'.mem_nhds hw] with w' hw'
    simp only [chartFunction, ψ, extensionAcross_eq_of_notMem hK hv hw'.2.2]
  -- near a point of `K`
  set x := e.val.symm z
  obtain ⟨k, hk, Φ, hsrc, hflatK⟩ := hflat x hzK
  obtain ⟨W₀, ρ, hzW₀, hρ⟩ := hθ e z hz
  set d := complexChartAt (n := n) x
  have hxd : x ∈ d.val.source := mem_complexChartAt_source x
  -- the chart transition and the flattening
  set T := chartTransition e d
  have hTapp : ∀ w, T w = d.val (e.val.symm w) := fun w => rfl
  have hTsrc : ∀ w, w ∈ T.source ↔ w ∈ e.val.target ∧ e.val.symm w ∈ d.val.source := fun w => by
    simp [T, chartTransition]
  set O : Set (ComplexModel n) := W₀ ∩ (T.source ∩ T ⁻¹' Φ.source)
  have hO : IsOpen O := hρ.1.inter (T.isOpen_inter_preimage Φ.isOpen_source)
  have hOt : ∀ w ∈ O, w ∈ e.val.target := fun w hw => ((hTsrc w).mp hw.2.1).1
  have hzO : z ∈ O := ⟨hzW₀, (hTsrc z).mpr ⟨hz, hxd⟩, Φ.center_mem_source⟩
  set H : ComplexModel n → ComplexModel n := fun w => Φ.toFun (T w)
  set G : ComplexModel n → ComplexModel n := fun b => T.symm (Φ.invFun b)
  set B : Set (ComplexModel n) := Φ.target ∩ Φ.invFun ⁻¹' (T.target ∩ T.symm ⁻¹' O)
  have hB : IsOpen B :=
    Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
      (T.isOpen_inter_preimage_symm hO)
  have hTsymm : ⇑T.symm = ⇑(chartTransition d e) := by
    simp [T, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  have hTtgt : T.target = (chartTransition d e).source := by
    simp [T, chartTransition]
  have hH : DifferentiableOn ℂ H O := fun w hw =>
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hw.2.2)).comp w
      ((chartTransition_contDiffAt e d hw.2.1).differentiableAt (by simp))).differentiableWithinAt
  have hG : DifferentiableOn ℂ G B := fun b hb => by
    have h1 : DifferentiableAt ℂ (chartTransition d e) (Φ.invFun b) :=
      (chartTransition_contDiffAt d e (hTtgt ▸ hb.2.1)).differentiableAt (by simp)
    have h2 : DifferentiableAt ℂ Φ.invFun b :=
      Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hb.1)
    show DifferentiableWithinAt ℂ (fun b => T.symm (Φ.invFun b)) B b
    rw [hTsymm]
    exact (h1.comp b h2).differentiableWithinAt
  have hHO : MapsTo H O B := fun w hw => by
    refine ⟨Φ.mapsTo_toFun hw.2.2, ?_⟩
    show Φ.invFun (Φ.toFun (T w)) ∈ T.target ∩ T.symm ⁻¹' O
    rw [Φ.left_inv _ hw.2.2]
    exact ⟨T.map_source hw.2.1, by rw [mem_preimage, T.left_inv hw.2.1]; exact hw⟩
  have hGB : MapsTo G B O := fun b hb => hb.2.2
  have hGH : ∀ w ∈ O, G (H w) = w := fun w hw => by
    show T.symm (Φ.invFun (Φ.toFun (T w))) = w
    rw [Φ.left_inv _ hw.2.2, T.left_inv hw.2.1]
  have hHG : ∀ b ∈ B, H (G b) = b := fun b hb => by
    show Φ.toFun (T (T.symm (Φ.invFun b))) = b
    rw [T.right_inv hb.2.1, Φ.right_inv b hb.1]
  have hn : 2 ≤ n := by omega
  set i : Fin n := ⟨n - 2, by omega⟩
  set j : Fin n := ⟨n - 1, by omega⟩
  have hij : i ≠ j := fun h => by
    have := congrArg Fin.val h; simp [i, j] at this; omega
  set S : Set (ComplexModel n) := e.val.symm ⁻¹' K
  have hSO : IsOpen (O \ S) := by
    have : O \ S = O ∩ (e.val.target ∩ e.val.symm ⁻¹' Kᶜ) := by
      ext w; constructor
      · rintro ⟨hw, hwS⟩; exact ⟨hw, hOt w hw, hwS⟩
      · rintro ⟨hw, -, hwS⟩; exact ⟨hw, hwS⟩
    rw [this]; exact hO.inter (e.val.isOpen_inter_preimage_symm hK.isOpen_compl)
  have hS : ∀ w ∈ O, w ∈ S → H w ∈ coordPlane i j := fun w hw hwS => by
    have hwd := ((hTsrc w).mp hw.2.1).2
    have hflat' := hflatK (e.val.symm w) ⟨hwd, hw.2.2⟩ hwS
    exact ⟨hflat' i (by simp [i]; omega), hflat' j (by simp [j]; omega)⟩
  set u : ComplexModel n → EReal := fun w => chartFunction v e w + (ρ w : EReal)
  have hu : PlurisubharmonicOn u (O \ S) := fun w hw => by
    obtain ⟨W', σ, hwW', hσ, hpsh'⟩ := hv e w (hOt w hw.1) hw.2
    set V := W' ∩ W₀
    have hV : IsOpen V := hσ.1.inter hρ.1
    have h := (_root_.Hironaka.smoothLocalPotential_psh_iff θ e V σ ρ (hσ.mono hV inter_subset_left)
      (hρ.mono hV inter_subset_right) (chartFunction v e)).1 (hpsh'.mono inter_subset_left)
    exact h w ⟨hwW', hw.1.1⟩
  set F : ComplexModel n → EReal := fun w => chartFunction ψ e w + (ρ w : EReal)
  have hFeq : EqOn F u (O \ S) := fun w hw => by
    simp only [F, u, chartFunction, ψ, extensionAcross_eq_of_notMem hK hv hw.2]
  have hFusc : UpperSemicontinuousOn F O := fun w hw => by
    have hψ : UpperSemicontinuous ψ := upperSemicontinuous_uscRegularization _
    have h1 : UpperSemicontinuousAt (chartFunction ψ e) w := by
      intro c hc
      exact (e.val.continuousAt_symm (hOt w hw)).eventually (hψ _ c hc)
    exact (upperSemicontinuousAt_add_real h1
      ((hρ.2.2.1.continuousOn w hw.1).continuousAt (hρ.1.mem_nhds hw.1))).upperSemicontinuousWithinAt O
  have hFle : ∀ w ∈ O, ∀ c : EReal, (∀ᶠ w' in 𝓝 w, w' ∉ S → u w' < c) → F w ≤ c := by
    intro w hw c hc
    have hwt := hOt w hw
    have hρc : ContinuousAt ρ w := (hρ.2.2.1.continuousOn w hw.1).continuousAt (hρ.1.mem_nhds hw.1)
    induction c using EReal.rec with
    | top => exact le_top
    | bot =>
      have h := extensionAcross_le_of_chart (K := K) (v := v) hwt hc (b := ⊥)
        fun w' hw' _ hw'K => absurd (hw' hw'K) (not_lt_bot)
      show ψ (e.val.symm w) + (ρ w : EReal) ≤ ⊥
      have h' : ψ (e.val.symm w) = ⊥ := le_bot_iff.mp h
      rw [h', EReal.bot_add]
    | coe r =>
      have hψle : ψ (e.val.symm w) ≤ ((r - ρ w : ℝ) : EReal) := by
        refine le_of_forall_gt_imp_ge_of_dense fun c' hc' => ?_
        induction c' using EReal.rec with
        | bot => exact absurd hc' (not_lt_bot)
        | top => exact le_top
        | coe r' =>
          have hε : 0 < r' - (r - ρ w) := by
            have := EReal.coe_lt_coe_iff.mp hc'; linarith
          have hN : {w' | (w' ∉ S → u w' < r) ∧ ρ w - (r' - (r - ρ w)) < ρ w'} ∈ 𝓝 w :=
            Filter.inter_mem hc (hρc.eventually (lt_mem_nhds (by linarith)))
          refine extensionAcross_le_of_chart hwt hN fun w' hw' _ hw'K => ?_
          have h1 := ereal_lt_sub_of_add_lt (hw'.1 hw'K)
          refine h1.le.trans (EReal.coe_le_coe_iff.mpr ?_)
          linarith [hw'.2]
      show ψ (e.val.symm w) + (ρ w : EReal) ≤ (r : EReal)
      calc ψ (e.val.symm w) + (ρ w : EReal) ≤ ((r - ρ w : ℝ) : EReal) + (ρ w : EReal) := by
            gcongr
        _ = (r : EReal) := by rw [← EReal.coe_add]; congr 1; ring
  have hpsh := plurisubharmonicOn_of_regularization hO hB hH hG hHO hGB hGH hHG hij hSO hS hu
    hFeq hFusc hFle
  exact ⟨O, ρ, hzO, hρ.mono hO inter_subset_left, hpsh⟩

end

end Hironaka.ThetaPshCodimTwoExtension

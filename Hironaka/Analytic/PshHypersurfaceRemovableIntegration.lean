import Hironaka.Analytic.PshAmbientExtensionLineControl
import Hironaka.Analytic.GrauertRemmertExtension
import Hironaka.Analytic.PshExtensionEquivariance
import Hironaka.Analytic.RegularAtDimChart
import Hironaka.Analytic.PshAnalyticCodimTwoRemovable

set_option autoImplicit false

/-!
# Integrating transverse-line removability with the Grauert--Remmert reduction

The punctured-line development now proves the ambient upper-regularized
extension is plurisubharmonic across a coordinate hyperplane.  This module
feeds that local theorem into the Grauert--Remmert reduction.

A `HasCoordinateHyperplaneSliceModels` witness is local geometric data, not a
removability axiom: after adding an actual local potential, the prescribed
candidate agrees on a chart neighbourhood with a coordinate-hyperplane
extension whose branch is plurisubharmonic and locally bounded above away from
that hyperplane.  The line-level conclusion is no longer assumed: it follows
from `PshAmbientExtensionLineControl`.  The final theorem feeds these local
conclusions into the verified codimension-two-core reduction of
`GrauertRemmertExtension`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PshHypersurfaceRemovableIntegration

open Hironaka
open PshCodimTwoExtension
open PshHypersurfaceRemovable
open PshPuncturedLineRemovable
open PshAnalyticSetExtension
open GrauertRemmertExtension
open ThetaPshCodimTwoExtension
open PshExtensionEquivariance
open PshAnalyticCodimTwoRemovable

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {A Z S : Set M} {theta : SmoothRealForm n M 2} {u : M → EReal}

/-- Fixing one smooth local potential does not lose the PSH information in
`ThetaPshOff`: at each point outside the exceptional set, compare that fixed
potential with the potential supplied by the off-set hypothesis on their open
intersection.  This gives one ordinary PSH branch on the whole punctured
neighbourhood and is the input needed before flattening a regular
hypersurface. -/
theorem plurisubharmonicOn_chartFunction_add_fixedPotential_off
    (hoff : ThetaPshOff theta A u) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) :
    PlurisubharmonicOn (fun y => chartFunction u e y + (rho y : EReal))
      (W \ e.val.symm ⁻¹' A) := by
  intro x hx
  obtain ⟨V, sigma, hxV, hsigma, hpsh⟩ :=
    hoff e x (hrho.2.1 hx.1) hx.2
  let Q := W ∩ V
  have hQ : IsOpen Q := hrho.1.inter hsigma.1
  have hxQ : x ∈ Q := ⟨hx.1, hxV⟩
  have hfixed : PlurisubharmonicOn
      (fun y => chartFunction u e y + (rho y : EReal)) Q :=
    (_root_.Hironaka.smoothLocalPotential_psh_iff theta e Q rho sigma
      (hrho.mono hQ inter_subset_left) (hsigma.mono hQ inter_subset_right)
      (chartFunction u e)).mpr (hpsh.mono inter_subset_right)
  exact hfixed x hxQ

/-- The locally bounded-above branch condition transports into a chart after
adding a fixed smooth local potential.  The bound is genuinely local: pull
back the neighbourhood from the manifold, then use continuity of the finite
potential to enlarge its constant by one. -/
theorem locallyBoundedAboveOff_chartFunction_add_fixedPotential
    (hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u)
    {e : ComplexChart n M} {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) :
    LocallyBoundedAboveOff (e.val.symm ⁻¹' A) W
      (fun y => chartFunction u e y + (rho y : EReal)) := by
  intro x hxW
  obtain ⟨U, hU, C, hC⟩ := hbound (e.val.symm x)
  have hxt : x ∈ e.val.target := hrho.2.1 hxW
  have hpre : e.val.symm ⁻¹' U ∈ 𝓝 x :=
    (e.val.continuousAt_symm hxt).preimage_mem_nhds hU
  have hrhoc : ContinuousAt rho x :=
    (hrho.2.2.1.continuousOn x hxW).continuousAt (hrho.1.mem_nhds hxW)
  have hrhoup : {y | rho y < rho x + 1} ∈ 𝓝 x :=
    hrhoc (gt_mem_nhds (by linarith))
  refine ⟨e.val.symm ⁻¹' U ∩ {y | rho y < rho x + 1},
    inter_mem hpre hrhoup, C + rho x + 1, ?_⟩
  intro y hy hyA
  have huy : u (e.val.symm y) ≤ (C : EReal) :=
    hC (e.val.symm y) hy.1 hyA
  change u (e.val.symm y) + (rho y : EReal) ≤ ((C + rho x + 1 : ℝ) : EReal)
  calc u (e.val.symm y) + (rho y : EReal) ≤ (C : EReal) + (rho y : EReal) := by
        gcongr
    _ ≤ (C : EReal) + ((rho x + 1 : ℝ) : EReal) := by
        gcongr
        exact hy.2.le
    _ = ((C + rho x + 1 : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring

/-- A local biholomorphic flattening of an analytic hypersurface gives the
chartwise closure required at its centre.  Unlike
`HasCoordinateHyperplaneSliceModels`, this theorem constructs the target
branch, its punctured PSH property, its local upper bound, and the equality
with the prescribed upper-regularized candidate from the actual local data.
It is therefore the direct regular-hypersurface step in the
Grauert--Remmert reduction. -/
theorem thetaPshLocalClosure_of_locally_flattened_coordHyperplane
    (hoff : ThetaPshOff theta A u)
    (hglobalBound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u)
    {e : ComplexChart n M} {z : ComplexModel n}
    (_hz : z ∈ e.val.target) {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hzW : z ∈ W) (hrho : IsSmoothLocalPotential theta e W rho)
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p) (i : Fin n)
    (hzPhi : z ∈ Phi.source)
    (hflat : ∀ y ∈ W ∩ Phi.source,
      y ∈ e.val.symm ⁻¹' A ↔ Phi.toFun y ∈ coordHyperplane i) :
    ∃ U rho, z ∈ U ∧ IsSmoothLocalPotential theta e U rho ∧
      PlurisubharmonicOn
        (fun y => chartFunction (extensionAcross A u) e y + (rho y : EReal)) U := by
  let S : Set (ComplexModel n) := e.val.symm ⁻¹' A
  let f : ComplexModel n → EReal := fun y => chartFunction u e y + (rho y : EReal)
  let O : Set (ComplexModel n) := W ∩ Phi.source
  have hO : IsOpen O := hrho.1.inter Phi.isOpen_source
  have hzO : z ∈ O := ⟨hzW, hzPhi⟩
  have hpshW : PlurisubharmonicOn f (W \ S) :=
    plurisubharmonicOn_chartFunction_add_fixedPotential_off hoff hrho
  have hboundW : LocallyBoundedAboveOff S W f :=
    locallyBoundedAboveOff_chartFunction_add_fixedPotential hglobalBound hrho
  have hpshO : PlurisubharmonicOn f (O \ S) := by
    intro y hy
    exact hpshW y ⟨hy.1.1, hy.2⟩
  have hboundO : LocallyBoundedAboveOff S O f := by
    intro y hy
    exact hboundW y hy.1
  have hflatO : ∀ y ∈ O, y ∈ S ↔ Phi.toFun y ∈ coordHyperplane i := by
    intro y hy
    exact hflat y hy
  let B : Set (ComplexModel n) := Phi.target ∩ Phi.invFun ⁻¹' O
  let psi : ComplexModel n → EReal := fun b => f (Phi.invFun b)
  have hB : IsOpen B :=
    Phi.invFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_target hO
  have hH : IsClosed (coordHyperplane i) := by
    change IsClosed {x : ComplexModel n | x i = 0}
    exact isClosed_singleton.preimage (PiLp.continuous_apply 2 _ i)
  have hBA : IsOpen (B \ coordHyperplane i) := hB.sdiff hH
  have hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i) :=
    plurisubharmonicOn_comp_localHolomorphicEquivAt_inv Phi i S O f hO hpshO hflatO
  have hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi :=
    locallyBoundedAboveOff_comp_localHolomorphicEquivAt_inv Phi i S O f hO hboundO hflatO
  have hfg : EqOn f (psi ∘ Phi.toFun) O := by
    intro y hy
    change f y = f (Phi.invFun (Phi.toFun y))
    rw [Phi.left_inv y hy.2]
  let U : Set (ComplexModel n) := O ∩ (Phi.source ∩ Phi.toFun ⁻¹' B)
  have hU : IsOpen U :=
    hO.inter (Phi.toFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_source hB)
  have hzB : Phi.toFun z ∈ B := by
    refine ⟨Phi.mapsTo_toFun hzPhi, ?_⟩
    change Phi.invFun (Phi.toFun z) ∈ O
    rw [Phi.left_inv z hzPhi]
    exact hzO
  have hzU : z ∈ U := ⟨hzO, hzPhi, hzB⟩
  have hext : PlurisubharmonicOn (extension S f) U :=
    plurisubharmonicOn_extension_of_locally_flattened_coordHyperplane_on
      Phi i B S O f psi hO hflatO hfg hB hbound hpsi hBA
  refine ⟨U, rho, hzU, hrho.mono hU (fun y hy => hy.1.1), ?_⟩
  intro y hy
  apply (hext y hy).congr
  filter_upwards [hU.mem_nhds hy] with y hy'
  have hyt : y ∈ e.val.target := hrho.2.1 hy'.1.1
  have hrhoc : ContinuousAt rho y :=
    (hrho.2.2.1.continuousOn y hy'.1.1).continuousAt (hrho.1.mem_nhds hy'.1.1)
  have hchart := chartFunction_extensionAcross_eq_extension_preimage
    (K := A) (v := u) hyt
  have hadd := extension_add_coe_continuousAt_apply S (chartFunction u e) hrhoc
  change extension S f y = chartFunction (extensionAcross A u) e y + (rho y : EReal)
  change extension S (fun w => chartFunction u e w + (rho w : EReal)) y = _
  rw [hadd, ← hchart]

/-- A complex coordinate plane of codimension one is a coordinate
hyperplane.  The existential formulation avoids choosing a distinguished
coordinate before the ambient dimension is known to be positive. -/
theorem exists_complexCoordinatePlane_pred_eq_coordHyperplane (hn : 0 < n) :
    ∃ i : Fin n, complexCoordinatePlane n (n - 1) = coordHyperplane i := by
  let i : Fin n := ⟨n - 1, by omega⟩
  refine ⟨i, ?_⟩
  ext z
  constructor
  · intro hz
    exact hz i (by simp [i])
  · intro hz j hj
    have hjn : j.1 < n := j.isLt
    have hji : j = i := Fin.ext (by simp [i]; omega)
    rw [hji]
    exact hz

/-- At a regular point of complex dimension `n - 1`, the flattening supplied
by `RegularAtDim` automatically supplies the local coordinate-hyperplane
data required by `thetaPshLocalClosure_of_locally_flattened_coordHyperplane`.
Thus no separate slice-model interface is needed at the regular
hypersurface stratum. -/
theorem thetaPshLocalClosure_of_regularAtDim
    (htheta : HasSmoothLocalPotentials theta)
    (hoff : ThetaPshOff theta A u)
    (hglobalBound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u)
    {e : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ e.val.target) (hn : 0 < n)
    (hregular : RegularAtDim (n := n) A (e.val.symm z) (n - 1)) :
    ∃ U rho, z ∈ U ∧ IsSmoothLocalPotential theta e U rho ∧
      PlurisubharmonicOn
        (fun y => chartFunction (extensionAcross A u) e y + (rho y : EReal)) U := by
  set flatMap : LocalHolomorphicEquivAt (n := n)
      ((complexChartAt (n := n) (e.val.symm z)).val (e.val.symm z)) :=
    Classical.choose hregular.2.2
  have hflatMap : ∀ {q : M},
      q ∈ (complexChartAt (n := n) (e.val.symm z)).val.source →
      (complexChartAt (n := n) (e.val.symm z)).val q ∈ flatMap.source →
      (q ∈ A ↔ flatMap.toFun ((complexChartAt (n := n) (e.val.symm z)).val q) ∈
        complexCoordinatePlane n (n - 1)) := by
    dsimp [flatMap]
    exact (Classical.choose_spec hregular.2.2).2.2
  have hxd : e.val.symm z ∈ (complexChartAt (n := n) (e.val.symm z)).val.source :=
    mem_complexChartAt_source _
  set T := chartTransition e (complexChartAt (n := n) (e.val.symm z))
  have hTsrc : T.source = e.val.target ∩ e.val.symm ⁻¹'
      (complexChartAt (n := n) (e.val.symm z)).val.source := by
    simp [T, chartTransition]
  have hTapp : ∀ w, T w = (complexChartAt (n := n) (e.val.symm z)).val (e.val.symm w) :=
    fun w => rfl
  have hzT : z ∈ T.source := by
    rw [hTsrc]
    exact ⟨hz, hxd⟩
  have hTz : T z = (complexChartAt (n := n) (e.val.symm z)).val (e.val.symm z) := by
    rw [hTapp]
  let Psi := RegularAtDimChart.precomp T
    (RegularPatchNeighborhood.differentiableOn_chartTransition e
      (complexChartAt (n := n) (e.val.symm z)))
    (RegularPatchNeighborhood.differentiableOn_chartTransition_symm e
      (complexChartAt (n := n) (e.val.symm z))) hzT hTz flatMap
  have hzPsi : z ∈ Psi.source := Psi.center_mem_source
  obtain ⟨W, rho, hzW, hrho⟩ := htheta e z hz
  obtain ⟨i, hplane⟩ := exists_complexCoordinatePlane_pred_eq_coordHyperplane hn
  apply thetaPshLocalClosure_of_locally_flattened_coordHyperplane
    hoff hglobalBound hz hzW hrho Psi i hzPsi
  intro y hy
  change y ∈ e.val.symm ⁻¹' A ↔ flatMap.toFun (T y) ∈ coordHyperplane i
  have hyPsi : y ∈ T.source ∩ T ⁻¹' flatMap.source := hy.2
  have hyTsrc := hyPsi.1
  rw [hTsrc] at hyTsrc
  have hy_d : e.val.symm y ∈ (complexChartAt (n := n) (e.val.symm z)).val.source :=
    hyTsrc.2
  have hyFlat : T y ∈ flatMap.source := hyPsi.2
  have hyFlat' : (complexChartAt (n := n) (e.val.symm z)).val (e.val.symm y) ∈
      flatMap.source := by
    rw [← hTapp y]
    exact hyFlat
  have horig : e.val.symm y ∈ A ↔
      flatMap.toFun ((complexChartAt (n := n) (e.val.symm z)).val (e.val.symm y)) ∈
        complexCoordinatePlane n (n - 1) :=
    hflatMap hy_d hyFlat'
  rw [hTapp y]
  simpa only [mem_preimage, hplane] using horig

/-- The pointwise regular-hypersurface theorem assembles into the exact local
closure predicate used by the Grauert--Remmert codimension-two reduction. -/
theorem thetaPshLocalClosureOn_of_regularAtDim
    (htheta : HasSmoothLocalPotentials theta)
    (hoff : ThetaPshOff theta A u)
    (hglobalBound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u)
    (hn : 0 < n)
    (hregular : ∀ x ∈ S, RegularAtDim (n := n) A x (n - 1)) :
    ThetaPshLocalClosureOn theta (extensionAcross A u) S := by
  intro e z hz hzS
  exact thetaPshLocalClosure_of_regularAtDim htheta hoff hglobalBound hz hn
    (hregular (e.val.symm z) hzS)

/-- The fully verified hypersurface assembly: the final transverse-line
submean conclusion gives the ambient coordinate-hyperplane extension. -/
theorem plurisubharmonicOn_coordinateExtension_of_forall_hasDiscSubmean
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B)
    (hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff
      (coordHyperplane i) B psi)
    (hline : ∀ (x v : ComplexModel n), v i ≠ 0 →
      HasDiscSubmeanOn (fun z => extension (coordHyperplane i) psi
        (x + affineLine v z)) (transverseLineDomain B x v)) :
    PlurisubharmonicOn (extension (coordHyperplane i) psi) B := by
  apply plurisubharmonicOn_extensionAcross_coordHyperplane_of_transverseSlices hB hbound
  exact (hasTransverseLineSlices_iff_forall_hasDiscSubmean hB hbound).mpr hline

/-- The same line-level conclusion also discharges the ambient-versus-intrinsic
regularization comparison at every puncture lying in the line domain.  This
uses the already-proved puncture comparison theorem, rather than adding a
second compatibility hypothesis. -/
theorem transverseLineRegularizationCompatible_of_forall_hasDiscSubmean
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hBA : IsOpen (B \ coordHyperplane i))
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff
      (coordHyperplane i) B psi)
    (hline : ∀ (x v : ComplexModel n), v i ≠ 0 →
      HasDiscSubmeanOn (fun z => extension (coordHyperplane i) psi
        (x + affineLine v z)) (transverseLineDomain B x v))
    (x v : ComplexModel n) (hv : v i ≠ 0)
    (hpole : -(x i) / v i ∈ transverseLineDomain B x v) :
    TransverseLineRegularizationCompatible i B psi x v := by
  have hslices : HasTransverseLineSlices i (extension (coordHyperplane i) psi) B :=
    (hasTransverseLineSlices_iff_forall_hasDiscSubmean hB hbound).mpr hline
  exact transverseLineRegularizationCompatible_of_hasTransverseLineSlices
    hB hBA hpsi hslices x v hv hpole

/-- Local chart data which genuinely arise from the transverse-hypersurface
argument.  The equality is on `W`, so it transports actual PSH germs, with all
pole values retained.  The branch PSH condition is precisely the hypothesis of
the proved coordinate-hyperplane removable theorem. -/
def HasCoordinateHyperplaneSliceModels (theta : SmoothRealForm n M 2)
    (A : Set M) (u : M → EReal) (S : Set M) : Prop :=
  ∀ e z, z ∈ e.val.target → e.val.symm z ∈ S →
    ∃ (i : Fin n) (B : Set (ComplexModel n)) (psi : ComplexModel n → EReal)
      (W : Set (ComplexModel n)) (rho : ComplexModel n → ℝ),
      IsOpen B ∧
      PshHypersurfaceRemovable.LocallyBoundedAboveOff (coordHyperplane i) B psi ∧
      PlurisubharmonicOn psi (B \ coordHyperplane i) ∧
      IsOpen (B \ coordHyperplane i) ∧
      z ∈ W ∧ IsSmoothLocalPotential theta e W rho ∧ W ⊆ B ∧
      EqOn (fun y => chartFunction (extensionAcross A u) e y + (rho y : EReal))
        (extension (coordHyperplane i) psi) W

/-- Coordinate-hyperplane slice models produce the local closure package on
exactly the stratum they cover. -/
theorem thetaPshLocalClosureOn_of_coordinateHyperplaneSliceModels
    (hmodels : HasCoordinateHyperplaneSliceModels theta A u S) :
    ThetaPshLocalClosureOn theta (extensionAcross A u) S := by
  intro e z hz hzS
  obtain ⟨i, B, psi, W, rho, hB, hbound, hpsi, hBA, hzW, hrho, hWB, heq⟩ :=
    hmodels e z hz hzS
  refine ⟨W, rho, hzW, hrho, ?_⟩
  have hpshB : PlurisubharmonicOn (extension (coordHyperplane i) psi) B :=
    PshAmbientExtensionLineControl.plurisubharmonicOn_extension_of_punctured_plurisubharmonic
      hB hbound hpsi hBA
  have hpshW : PlurisubharmonicOn (extension (coordHyperplane i) psi) W :=
    hpshB.mono hWB
  intro w hw
  apply (hpshW w hw).congr
  filter_upwards [hrho.1.mem_nhds hw] with w' hw'
  exact (heq hw').symm

/-- **Full stratified integration.**  A closed codimension-two core is handled
by the verified codimension-two theorem.  At every point outside that core,
actual chartwise coordinate-hyperplane data plus the transverse-line submean
conclusion produce the needed local closure.  Hence the existing
`AnalyticRemovableThetaPsh` interface follows without any global
removability assumption. -/
theorem analyticRemovableThetaPsh_of_coordinateHyperplaneSliceCore
    (htheta : HasSmoothLocalPotentials theta)
    (hcore : ∀ (_hanalytic : IsComplexAnalyticSubset (n := n) A) (_hproper : A ≠ univ)
      (_hoff : ThetaPshOff theta A u)
      (_hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u),
      ∃ Z : Set M, IsClosed Z ∧ Z ⊆ A ∧ HasCodimTwoFlattenings (n := n) Z ∧
        HasCoordinateHyperplaneSliceModels theta A u (A \ Z)) :
    AnalyticRemovableThetaPsh theta A u := by
  apply analyticRemovableThetaPsh_of_codimTwoCore htheta
  intro hanalytic hproper hoff hbound
  obtain ⟨Z, hZ, hZA, hflat, hmodels⟩ := hcore hanalytic hproper hoff hbound
  refine ⟨Z, hZ, hZA, hflat, ?_⟩
  exact thetaPshLocalClosureOn_of_coordinateHyperplaneSliceModels hmodels

/-- A formulation of the full analytic reduction whose regular-stratum input
is stated solely in the intrinsic language of `RegularAtDim`.  The analytic
stratification theorem which produces the closed codimension-two core remains
separate; once supplied, no coordinate-slice-model hypothesis remains. -/
theorem analyticRemovableThetaPsh_of_regularHypersurfaceCore
    (htheta : HasSmoothLocalPotentials theta) (hn : 0 < n)
    (hcore : ∀ (_hanalytic : IsComplexAnalyticSubset (n := n) A) (_hproper : A ≠ univ)
      (_hoff : ThetaPshOff theta A u)
      (_hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u),
      ∃ Z : Set M, IsClosed Z ∧ Z ⊆ A ∧ HasCodimTwoFlattenings (n := n) Z ∧
        ∀ x ∈ A \ Z, RegularAtDim (n := n) A x (n - 1)) :
    AnalyticRemovableThetaPsh theta A u := by
  apply analyticRemovableThetaPsh_of_codimTwoCore htheta
  intro hanalytic hproper hoff hbound
  obtain ⟨Z, hZ, hZA, hflat, hregular⟩ := hcore hanalytic hproper hoff hbound
  refine ⟨Z, hZ, hZA, hflat, ?_⟩
  exact thetaPshLocalClosureOn_of_regularAtDim htheta hoff hbound hn hregular

/-- The regular-hypersurface closure also supplies the complementary-stratum
input for the valid recursive analytic-core reduction.  In contrast to the
preceding special-case theorem, the analytic core may be singular: it is
handled by its own removability interface rather than by an invalid global
smooth flattening assertion. -/
theorem analyticRemovableThetaPsh_of_regularHypersurfaceAnalyticCore
    (htheta : HasSmoothLocalPotentials theta) (hn : 0 < n)
    (hcore : ∀ (_hanalytic : IsComplexAnalyticSubset (n := n) A) (_hproper : A ≠ univ)
      (_hoff : ThetaPshOff theta A u)
      (_hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u),
      ∃ Z : Set M, IsComplexAnalyticSubset (n := n) Z ∧ Z ⊆ A ∧
        AnalyticRemovableThetaPsh theta Z (extensionAcross A u) ∧
        PshAnalyticSetExtension.LocallyBoundedAboveOff Z (extensionAcross A u) ∧
        ∀ x ∈ A \ Z, RegularAtDim (n := n) A x (n - 1)) :
    AnalyticRemovableThetaPsh theta A u := by
  apply PshAnalyticCodimTwoRemovable.analyticRemovableThetaPsh_of_analyticCore
  intro hanalytic hproper hoff hbound
  obtain ⟨Z, hZanalytic, hZA, hZremovable, hZbound, hregular⟩ :=
    hcore hanalytic hproper hoff hbound
  refine ⟨Z, hZanalytic, hZA, hZremovable, hZbound, ?_⟩
  exact thetaPshLocalClosureOn_of_regularAtDim htheta hoff hbound hn hregular

end

end Hironaka.PshHypersurfaceRemovableIntegration

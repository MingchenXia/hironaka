import Hironaka.Analytic.PshHypersurfaceRemovable
import Hironaka.Analytic.PotentialTheory.LogPole
import Hironaka.Analytic.PshConvexCone
import Hironaka.Analytic.HarmonicCircleApproximation

set_option autoImplicit false

/-!
# Verified data on a transverse punctured complex line

This module records the parts of the hypersurface-to-line reduction which do
not use the classical one-dimensional removable-singularity theorem.  A
transverse affine line meets the coordinate hypersurface at a single parameter
value.  On the complementary punctured line, the prescribed upper
regularization agrees with the original plurisubharmonic branch; it is upper
semicontinuous and locally bounded above on the entire line domain.  Thus the
remaining direct target is exactly its one-dimensional disc-submean field.

For a formulation using the intrinsic line upper regularization, there is one
additional comparison at the puncture: ambient regularization can a priori be
larger than a restriction regularized only along the line.  Both gaps are
exposed as propositions or equivalences, never supplied as an axiom here.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.PshPuncturedLineRemovable

open Hironaka
open PshCodimTwoExtension
open PshHypersurfaceRemovable

noncomputable section

variable {n : ℕ}

/-- The domain of a transverse affine line inside an ambient coordinate domain. -/
def transverseLineDomain (B : Set (ComplexModel n)) (x v : ComplexModel n) : Set ℂ :=
  (fun z => x + affineLine v z) ⁻¹' B

/-- The transverse line domain is open whenever the ambient coordinate domain is open. -/
theorem isOpen_transverseLineDomain {B : Set (ComplexModel n)} (hB : IsOpen B)
    (x v : ComplexModel n) :
    IsOpen (transverseLineDomain B x v) := by
  exact hB.preimage (continuous_const.add (affineLine v).continuous)

/-- Off the unique hyperplane-intersection parameter, the regularized branch
is exactly the original branch. -/
theorem extension_comp_affineLine_eq_off_pole
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) {z : ℂ}
    (hzB : z ∈ transverseLineDomain B x v)
    (hz : z ≠ -(x i) / v i) :
    extension (coordHyperplane i) psi (x + affineLine v z) =
      psi (x + affineLine v z) := by
  apply extension_eq hpsi hBA
  refine ⟨hzB, ?_⟩
  intro hzH
  have hz' : z ∈ (fun w : ℂ => x + affineLine v w) ⁻¹' coordHyperplane i := hzH
  rw [preimage_coordHyperplane_eq_singleton hv] at hz'
  exact hz hz'

/-- The regularized transverse restriction is upper semicontinuous. -/
theorem upperSemicontinuous_extension_comp_affineLine
    {i : Fin n} {psi : ComplexModel n → EReal} (x v : ComplexModel n) :
    UpperSemicontinuous (fun z : ℂ => extension (coordHyperplane i) psi
      (x + affineLine v z)) := by
  intro z
  exact (upperSemicontinuous_extension (coordHyperplane i) psi _).comp
    (continuous_const.add (affineLine v).continuous).continuousAt

/-- Pulling a local upper bound back to a transverse affine line gives a local
upper bound on the complete line domain, including the puncture. -/
theorem exists_transverseLine_local_upper_bound
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hbound : LocallyBoundedAboveOn (extension (coordHyperplane i) psi) B)
    (x v : ComplexModel n) {z : ℂ} (hz : z ∈ transverseLineDomain B x v) :
    ∃ V : Set ℂ, V ∈ 𝓝 z ∧ ∃ C : ℝ, ∀ w ∈ V,
      extension (coordHyperplane i) psi (x + affineLine v w) ≤ (C : EReal) := by
  obtain ⟨U, hU, C, hC⟩ := hbound (x + affineLine v z) hz
  refine ⟨(fun w : ℂ => x + affineLine v w) ⁻¹' U,
    (continuous_const.add (affineLine v).continuous).continuousAt.preimage_mem_nhds hU,
    C, ?_⟩
  intro w hw
  exact hC _ hw

/-- The exact non-removable data on each transverse line: an open planar
punctured domain, a plurisubharmonic branch there, equality with the prescribed
upper regularization away from its sole puncture, and local upper bounds for
that regularization on the full line domain. -/
theorem transverseLine_punctured_data
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hBA : IsOpen (B \ coordHyperplane i))
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (x v : ComplexModel n) (hv : v i ≠ 0) :
    IsOpen (transverseLineDomain B x v) ∧
      PlurisubharmonicOn (fun z => psi (x + affineLine v z))
        (transverseLineDomain B x v \ {-(x i) / v i}) ∧
      (∀ z ∈ transverseLineDomain B x v, z ≠ -(x i) / v i →
        extension (coordHyperplane i) psi (x + affineLine v z) =
          psi (x + affineLine v z)) ∧
      UpperSemicontinuous (fun z => extension (coordHyperplane i) psi
        (x + affineLine v z)) ∧
      (∀ z ∈ transverseLineDomain B x v, ∃ V : Set ℂ, V ∈ 𝓝 z ∧ ∃ C : ℝ,
        ∀ w ∈ V, extension (coordHyperplane i) psi (x + affineLine v w) ≤ (C : EReal)) := by
  refine ⟨isOpen_transverseLineDomain hB x v, ?_, ?_,
    upperSemicontinuous_extension_comp_affineLine x v, ?_⟩
  · simpa only [transverseLineDomain] using
      plurisubharmonicOn_comp_transverseLine_off_coordHyperplane hpsi x v hv
  · intro z hzB hz
    exact extension_comp_affineLine_eq_off_pole hpsi hBA x v hv hzB hz
  · intro z hz
    exact exists_transverseLine_local_upper_bound
      (locallyBoundedAboveOn_extension hbound) x v hz

open scoped Classical in
/-- The raw function on a transverse line: it is the original branch on the
punctured line domain and `-∞` both at the missing parameter and outside the
line domain.  This spelling is needed to compare the *ambient* upper
regularization with the intrinsic one-dimensional upper regularization. -/
def transverseLineRaw (i : Fin n) (B : Set (ComplexModel n))
    (psi : ComplexModel n → EReal) (x v : ComplexModel n) : ℂ → EReal :=
  fun z => if z ∈ transverseLineDomain B x v ∧ z ≠ -(x i) / v i then
    psi (x + affineLine v z) else ⊥

/-- The ambient upper regularization is an upper-semicontinuous majorant of
the raw transverse-line function.  The reverse comparison at the missing
parameter is a real compatibility issue: upper semicontinuity alone permits a
strict upward spike there. -/
theorem transverseLineRaw_le_extension
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) :
    transverseLineRaw i B psi x v ≤ fun z =>
      extension (coordHyperplane i) psi (x + affineLine v z) := by
  intro z
  classical
  by_cases hz : z ∈ transverseLineDomain B x v ∧ z ≠ -(x i) / v i
  · rw [transverseLineRaw, if_pos hz]
    change psi (x + affineLine v z) ≤
      extension (coordHyperplane i) psi (x + affineLine v z)
    rw [extension_comp_affineLine_eq_off_pole hpsi hBA x v hv hz.1 hz.2]
  · rw [transverseLineRaw, if_neg hz]
    exact bot_le

/-- Intrinsic upper regularization of the raw transverse-line function never
exceeds the ambient upper regularization restricted to that line. -/
theorem uscRegularization_transverseLineRaw_le_extension
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) :
    uscRegularization (transverseLineRaw i B psi x v) ≤ fun z =>
      extension (coordHyperplane i) psi (x + affineLine v z) := by
  apply uscRegularization_le
    (upperSemicontinuous_extension_comp_affineLine x v)
  exact transverseLineRaw_le_extension hpsi hBA x v hv

/-- Away from the unique missing parameter, the intrinsic and ambient
regularizations agree with the original transverse branch. -/
theorem uscRegularization_transverseLineRaw_eq_off_pole
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) {z : ℂ}
    (hzB : z ∈ transverseLineDomain B x v)
    (hz : z ≠ -(x i) / v i) :
    uscRegularization (transverseLineRaw i B psi x v) z =
      psi (x + affineLine v z) := by
  apply le_antisymm
  · calc uscRegularization (transverseLineRaw i B psi x v) z ≤
        extension (coordHyperplane i) psi (x + affineLine v z) :=
          uscRegularization_transverseLineRaw_le_extension hpsi hBA x v hv z
      _ = psi (x + affineLine v z) :=
          extension_comp_affineLine_eq_off_pole hpsi hBA x v hv hzB hz
  · rw [← show transverseLineRaw i B psi x v z = psi (x + affineLine v z) by
      simp [transverseLineRaw, hzB, hz]]
    exact le_uscRegularization _ z

/-- The sole comparison still needed to identify the given ambient
regularization with the intrinsic one-dimensional regularization at the
puncture.  It is intentionally just an inequality, and contains no
plurisubharmonic conclusion. -/
def TransverseLineRegularizationCompatible (i : Fin n)
    (B : Set (ComplexModel n)) (psi : ComplexModel n → EReal)
    (x v : ComplexModel n) : Prop :=
  extension (coordHyperplane i) psi (x + affineLine v (-(x i) / v i)) ≤
    uscRegularization (transverseLineRaw i B psi x v) (-(x i) / v i)

/-- Under the explicit puncture comparison, the two regularizations agree on
the full transverse-line domain.  This theorem separates that comparison from
the classical planar submean/removability theorem. -/
theorem eqOn_extension_comp_affineLine_uscRegularization_transverseLineRaw
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0)
    (hcompat : TransverseLineRegularizationCompatible i B psi x v) :
    EqOn (fun z => extension (coordHyperplane i) psi (x + affineLine v z))
      (uscRegularization (transverseLineRaw i B psi x v))
      (transverseLineDomain B x v) := by
  intro z hzB
  by_cases hz : z = -(x i) / v i
  · subst z
    apply le_antisymm
    · exact hcompat
    · exact uscRegularization_transverseLineRaw_le_extension hpsi hBA x v hv _
  · change extension (coordHyperplane i) psi (x + affineLine v z) =
      uscRegularization (transverseLineRaw i B psi x v) z
    rw [uscRegularization_transverseLineRaw_eq_off_pole hpsi hBA x v hv hzB hz,
      extension_comp_affineLine_eq_off_pole hpsi hBA x v hv hzB hz]

/-- On a transverse line all parts of `DiscPshOn` except its submean field
are already verified from the punctured branch and its local upper bounds.
Consequently `HasDiscSubmeanOn` below is the exact remaining analytic
obligation; this equivalence does not postulate the desired conclusion. -/
theorem discPshOn_extension_comp_affineLine_iff_hasDiscSubmean
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (x v : ComplexModel n) :
    DiscPshOn (fun z => extension (coordHyperplane i) psi (x + affineLine v z))
      (transverseLineDomain B x v) ↔
    HasDiscSubmeanOn (fun z => extension (coordHyperplane i) psi
      (x + affineLine v z)) (transverseLineDomain B x v) := by
  constructor
  · exact fun h => h.submean
  · intro hsub
    refine ⟨?_,
      (upperSemicontinuous_extension_comp_affineLine x v).upperSemicontinuousOn _, hsub⟩
    intro z hz
    obtain ⟨V, hV, C, hC⟩ := exists_transverseLine_local_upper_bound
      (locallyBoundedAboveOn_extension hbound) x v hz
    exact ne_top_of_le_ne_top (EReal.coe_ne_top C) (hC z (mem_of_mem_nhds hV))

/-- Exact slice-level reformulation of the hypersurface closure target.  Once
the displayed one-dimensional disc-submean statement is proved for every
transverse line, `HasTransverseLineSlices` follows with no further analytic
input. -/
theorem hasTransverseLineSlices_iff_forall_hasDiscSubmean
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi) :
    HasTransverseLineSlices i (extension (coordHyperplane i) psi) B ↔
    ∀ (x v : ComplexModel n), v i ≠ 0 →
      HasDiscSubmeanOn (fun z => extension (coordHyperplane i) psi
        (x + affineLine v z)) (transverseLineDomain B x v) := by
  constructor
  · intro hslices x v hv
    exact (hslices x v hv).discPshOn.submean
  · intro hslice x v hv
    exact (discPshOn_extension_comp_affineLine_iff_hasDiscSubmean
      hbound x v).mpr (hslice x v hv) |>.plurisubharmonicOn
        (isOpen_transverseLineDomain hB x v)

/-- A genuine one-dimensional PSH extension cannot carry an artificial upward
spike at the removed point.  More precisely, if it agrees off that point with
`raw`, then its value at the point is bounded by the intrinsic upper
regularization of `raw`.  The proof uses the closed-disc maximum principle on
a small disc contained in each neighborhood occurring in the regularization.

This is the reverse comparison which was not available from upper
semicontinuity alone.  It is a consequence of the sought planar extension,
not an additional independent analytic input. -/
theorem le_uscRegularization_of_plurisubharmonicOn_eqOff_singleton
    {raw u : ℂ → EReal} {U : Set ℂ} {a : ℂ}
    (hU : IsOpen U) (ha : a ∈ U) (hu : PlurisubharmonicOn u U)
    (heq : EqOn u raw (U \ {a})) :
    u a ≤ uscRegularization raw a := by
  apply le_of_forall_gt
  intro b hab
  obtain ⟨q, hq₁, hq₂⟩ := EReal.exists_rat_btwn_of_lt hab
  have hq₁' : uscRegularization raw a < (((q : ℝ) : EReal)) := by
    exact_mod_cast hq₁
  have hq₂' : ((q : ℝ) : EReal) < b := by
    simpa using hq₂
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hq₁'
  obtain ⟨haN, hNq⟩ := iInf_lt_iff.mp hN
  obtain ⟨W, hWsub, hWopen, haW⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem haN (hU.mem_nhds ha))
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hWopen a haW
  have hr : 0 < R / 2 := half_pos hR
  have hclosed : closedBall a (R / 2) ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hdisc : closedBall a (R / 2) ⊆ U := fun z hz => (hWsub (hclosed hz)).2
  have hsphere : ∀ z ∈ sphere a (R / 2), u z ≤ (((q : ℝ) : EReal)) := by
    intro z hz
    have hzW : z ∈ W := hclosed (sphere_subset_closedBall hz)
    have hzN : z ∈ N := (hWsub hzW).1
    have hzU : z ∈ U := (hWsub hzW).2
    have hzne : z ≠ a := by
      intro hza
      subst z
      have hzero : R / 2 = 0 := by simpa using (mem_sphere.mp hz).symm
      exact hr.ne' hzero
    rw [heq ⟨hzU, by simp [hzne]⟩]
    have hsup : raw z ≤ ⨆ y ∈ N, raw y := by
      calc raw z ≤ ⨆ _ : z ∈ N, raw z :=
            le_iSup (fun _ : z ∈ N => raw z) hzN
        _ ≤ ⨆ y : ℂ, ⨆ _ : y ∈ N, raw y :=
            le_iSup (fun y : ℂ => ⨆ _ : y ∈ N, raw y) z
    exact hsup.trans hNq.le
  exact (hu.le_const_on_closedBall_of_le_on_sphere hr hdisc hsphere a
    (mem_closedBall_self hr.le)).trans_lt hq₂'

/-- Once the transverse slice itself has been proved plurisubharmonic, the
ambient and intrinsic upper regularizations agree at its puncture as well.
Thus `TransverseLineRegularizationCompatible` is discharged by the planar
removability theorem rather than being a second closure axiom. -/
theorem transverseLineRegularizationCompatible_of_plurisubharmonicOn
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hBA : IsOpen (B \ coordHyperplane i))
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0)
    (hpole : -(x i) / v i ∈ transverseLineDomain B x v)
    (hslice : PlurisubharmonicOn
      (fun z => extension (coordHyperplane i) psi (x + affineLine v z))
      (transverseLineDomain B x v)) :
    TransverseLineRegularizationCompatible i B psi x v := by
  apply le_uscRegularization_of_plurisubharmonicOn_eqOff_singleton
    (isOpen_transverseLineDomain hB x v) hpole hslice
  intro z hz
  have hzB : z ∈ transverseLineDomain B x v := hz.1
  have hzne : z ≠ -(x i) / v i := by simpa using hz.2
  change extension (coordHyperplane i) psi (x + affineLine v z) =
    transverseLineRaw i B psi x v z
  rw [extension_comp_affineLine_eq_off_pole hpsi hBA x v hv hzB hzne]
  simp [transverseLineRaw, hzB, hzne]

/-- The fully assembled transverse-slice conclusion automatically supplies
the intrinsic-regularization comparison wherever the line meets the ambient
domain. -/
theorem transverseLineRegularizationCompatible_of_hasTransverseLineSlices
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hBA : IsOpen (B \ coordHyperplane i))
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hslices : HasTransverseLineSlices i (extension (coordHyperplane i) psi) B)
    (x v : ComplexModel n) (hv : v i ≠ 0)
    (hpole : -(x i) / v i ∈ transverseLineDomain B x v) :
    TransverseLineRegularizationCompatible i B psi x v :=
  transverseLineRegularizationCompatible_of_plurisubharmonicOn hB hBA hpsi x v hv hpole
    (hslices x v hv)

/-- The closed Euclidean annulus used for the logarithmic-barrier argument. -/
def closedAnnulus (c : ℂ) (r R : ℝ) : Set ℂ :=
  closedBall c R \ ball c r

/- The planar closed annulus is connected because it is the continuous image
of a radius interval times the unit circle.  Keeping the explicit image proof
here avoids importing a specialized annulus-topology result. -/
theorem isPreconnected_closedAnnulus {c : ℂ} {r R : ℝ} (hr : 0 < r) :
    IsPreconnected (closedAnnulus c r R) := by
  let f : ℝ × ℂ → ℂ := fun p => c + p.1 • p.2
  have hf : Continuous f :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have hprod : IsPreconnected (Icc r R ×ˢ sphere (0 : ℂ) 1) :=
    isPreconnected_Icc.prod
      (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) 1)
  suffices himage : f '' (Icc r R ×ˢ sphere (0 : ℂ) 1) = closedAnnulus c r R by
    rw [← himage]
    exact hprod.image f hf.continuousOn
  ext w
  constructor
  · rintro ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩
    have hznorm : ‖z‖ = 1 := by
      simpa [dist_zero_right] using (mem_sphere.mp hz)
    have hdist : dist (c + t • z) c = t := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hr.le.trans ht.1), hznorm, mul_one]
    change c + t • z ∈ closedBall c R ∧ c + t • z ∉ ball c r
    refine ⟨mem_closedBall.mpr (hdist.le.trans ht.2), ?_⟩
    intro hball
    have : t < r := by
      have hlt := mem_ball.mp hball
      rwa [hdist] at hlt
    exact (not_lt_of_ge ht.1) this
  · intro hw
    change w ∈ closedBall c R ∧ w ∉ ball c r at hw
    have htr : r ≤ dist w c := by
      apply le_of_not_gt
      intro h
      exact hw.2 (mem_ball.mpr h)
    let t : ℝ := dist w c
    have htpos : 0 < t := hr.trans_le (by simpa [t] using htr)
    have htnorm : ‖w - c‖ = t := by
      change ‖w - c‖ = dist w c
      exact (dist_eq_norm w c).symm
    have hzunit : (t⁻¹ • (w - c) : ℂ) ∈ sphere 0 1 := by
      rw [mem_sphere, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), htnorm,
        inv_mul_cancel₀ htpos.ne']
    refine ⟨(t, t⁻¹ • (w - c)), ⟨?_, hzunit⟩, ?_⟩
    · exact ⟨(by simpa [t] using htr),
        (by simpa [t] using (mem_closedBall.mp hw.1))⟩
    · change c + t • (t⁻¹ • (w - c)) = w
      rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul,
        ← add_sub_assoc, add_sub_cancel_left]

/-- The maximum principle on a closed annulus.  The only geometric input is
the preconnectedness of that annulus; the analytic proof is derived from the
already verified local strong maximum principle for `DiscPshOn` and compact
upper-semicontinuous maxima.

The intended application takes a PSH branch minus a harmonic boundary
majorant plus a positive multiple of `log ‖z-c‖²`.  That logarithmic term
makes the inner-circle bound automatic as its radius tends to zero. -/
theorem PlurisubharmonicOn.le_const_on_closedAnnulus_of_isPreconnected
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {r R C : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hr : 0 < r) (hrR : r < R)
    (hAnn : closedAnnulus c r R ⊆ Omega)
    (hconn : IsPreconnected (closedAnnulus c r R))
    (houter : ∀ z ∈ sphere c R, u z ≤ (C : EReal))
    (hinner : ∀ z ∈ sphere c r, u z ≤ (C : EReal)) :
    ∀ z ∈ closedAnnulus c r R, u z ≤ (C : EReal) := by
  intro q hq
  by_contra hqC
  have hCq : (C : EReal) < u q := lt_of_not_ge hqC
  have hKcompact : IsCompact (closedAnnulus c r R) := by
    exact (isCompact_closedBall c R).inter_right isOpen_ball.isClosed_compl
  have husc : UpperSemicontinuousOn u (closedAnnulus c r R) :=
    hu.upperSemicontinuousOn.mono hAnn
  obtain ⟨y, hyK, hmax⟩ := husc.exists_isMaxOn ⟨q, hq⟩ hKcompact
  have hytop : u y ≠ ⊤ := (hu y (hAnn hyK)).ne_top
  have hybot : u y ≠ ⊥ := by
    have hygt : (C : EReal) < u y := hCq.trans_le (hmax hq)
    intro hy
    rw [hy] at hygt
    exact (not_lt_of_ge bot_le) hygt
  let M : ℝ := (u y).toReal
  have hyM : u y = (M : EReal) := (EReal.coe_toReal hytop hybot).symm
  have hCM : C < M := by
    rw [← EReal.coe_lt_coe_iff, ← hyM]
    exact hCq.trans_le (hmax hq)
  let A : Set ℂ := ball c R \ closedBall c r
  have hAopen : IsOpen A :=
    isOpen_ball.inter isClosed_closedBall.isOpen_compl
  have hA_sub_K : A ⊆ closedAnnulus c r R := by
    intro z hz
    refine ⟨ball_subset_closedBall hz.1, fun hzball => hz.2 (ball_subset_closedBall hzball)⟩
  let O : Set ℂ := {z | z ∈ A ∧ u z = (M : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨W, hW, hzW, hdisc⟩ := hu z (hAnn (hA_sub_K hz.1))
    have hopen : IsOpen (W ∩ A) := hW.inter hAopen
    have hzopen : z ∈ W ∩ A := ⟨hzW, hz.1⟩
    obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hopen z hzopen
    have hBW : ball z delta ⊆ W := fun w hw => (hball hw).1
    have hMball : ∀ w ∈ ball z delta, u w ≤ (M : EReal) := by
      intro w hw
      exact (hmax (hA_sub_K (hball hw).2)).trans_eq hyM
    have heq := hdisc.eqOn_ball_of_le_of_eq z hBW hMball hz.2
    refine ⟨delta, hdelta, ?_⟩
    intro w hw
    exact ⟨(hball hw).2, heq hw⟩
  have hK : IsCompact (closedAnnulus c r R ∩ u ⁻¹' Ici (M : EReal)) :=
    husc.isCompact_inter_preimage_Ici hKcompact (M : EReal)
  have hOK : O ⊆ closedAnnulus c r R ∩ u ⁻¹' Ici (M : EReal) := by
    intro z hz
    exact ⟨hA_sub_K hz.1, by simp [hz.2]⟩
  have hclosure : closure O ∩ closedAnnulus c r R ⊆ O := by
    intro z hz
    have hzK := closure_minimal hOK hK.isClosed hz.1
    have hzM : u z = (M : EReal) := by
      apply le_antisymm
      · exact (hmax hz.2).trans_eq hyM
      · exact hzK.2
    have hzRle : dist z c ≤ R := (mem_closedBall.mp hz.2.1)
    have hrzle : r ≤ dist z c := by
      by_contra h
      push Not at h
      exact hz.2.2 (mem_ball.mpr h)
    have hzRne : dist z c ≠ R := by
      intro hzR
      have hzS : z ∈ sphere c R := mem_sphere.mpr hzR
      have hzC := houter z hzS
      rw [hzM, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCM
    have hrzne : dist z c ≠ r := by
      intro hzr
      have hzS : z ∈ sphere c r := mem_sphere.mpr hzr
      have hzC := hinner z hzS
      rw [hzM, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCM
    have hzRlt : dist z c < R := lt_of_le_of_ne hzRle hzRne
    have hrlz : r < dist z c := lt_of_le_of_ne hrzle hrzne.symm
    refine ⟨⟨mem_ball.mpr hzRlt, ?_⟩, hzM⟩
    rw [mem_closedBall, not_le]
    exact hrlz
  have hyRle : dist y c ≤ R := mem_closedBall.mp hyK.1
  have hryl : r ≤ dist y c := by
    by_contra h
    push Not at h
    exact hyK.2 (mem_ball.mpr h)
  have hyRne : dist y c ≠ R := by
    intro hyR
    have hyS : y ∈ sphere c R := mem_sphere.mpr hyR
    have hyC := houter y hyS
    rw [hyM, EReal.coe_le_coe_iff] at hyC
    exact (not_lt_of_ge hyC) hCM
  have hryne : dist y c ≠ r := by
    intro hyr
    have hyS : y ∈ sphere c r := mem_sphere.mpr hyr
    have hyC := hinner y hyS
    rw [hyM, EReal.coe_le_coe_iff] at hyC
    exact (not_lt_of_ge hyC) hCM
  have hyA : y ∈ A := by
    refine ⟨mem_ball.mpr (lt_of_le_of_ne hyRle hyRne), ?_⟩
    rw [mem_closedBall, not_le]
    exact lt_of_le_of_ne hryl hryne.symm
  have hnonempty : (closedAnnulus c r R ∩ O).Nonempty :=
    ⟨y, hA_sub_K hyA, hyA, hyM⟩
  have hall : closedAnnulus c r R ⊆ O :=
    hconn.subset_of_closure_inter_subset hO hnonempty hclosure
  let z : ℂ := c + (R : ℂ)
  have hRpos : 0 < R := hr.trans hrR
  have hzS : z ∈ sphere c R := by
    simp [z, abs_of_pos hRpos]
  have hzK : z ∈ closedAnnulus c r R := by
    refine ⟨sphere_subset_closedBall hzS, ?_⟩
    rw [mem_ball, dist_comm]
    simpa [z, abs_of_pos hRpos] using hrR.le
  have hzO := hall hzK
  exact (not_lt_of_ge (by
    have hzC := houter z hzS
    rw [hzO.2, EReal.coe_le_coe_iff] at hzC
    exact hzC)) hCM

/-- The usable planar annular maximum principle.  Its connectivity hypothesis
has been discharged by `isPreconnected_closedAnnulus`, so it applies directly
to logarithmic barriers on every nondegenerate complex annulus. -/
theorem PlurisubharmonicOn.le_const_on_closedAnnulus
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {r R C : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hr : 0 < r) (hrR : r < R)
    (hAnn : closedAnnulus c r R ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (C : EReal))
    (hinner : ∀ z ∈ sphere c r, u z ≤ (C : EReal)) :
    ∀ z ∈ closedAnnulus c r R, u z ≤ (C : EReal) :=
  PlurisubharmonicOn.le_const_on_closedAnnulus_of_isPreconnected hu hr hrR hAnn
    (isPreconnected_closedAnnulus hr) houter hinner

/-- The standard logarithmic pole translated to the point `c`. -/
def logPoleAt (c : ℂ) : ℂ → EReal := fun z => logNormSq (z - c)

/-- Translation preserves the globally available disc-PSH logarithmic pole. -/
theorem plurisubharmonicOn_logPoleAt (c : ℂ) :
    PlurisubharmonicOn (logPoleAt c) univ := by
  change PlurisubharmonicOn (fun y : ℂ => logNormSq (y + -c)) univ
  simpa [add_comm] using
    ((discPshOn_logNormSq (H := ℂ) univ).plurisubharmonicOn isOpen_univ).comp_affine
      (ContinuousLinearMap.id ℂ ℂ) (-c)

/-- On a positive-radius circle the translated logarithmic pole is the
ordinary finite real logarithm of the squared radius. -/
theorem logPoleAt_eq_on_sphere {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ sphere c R) :
    logPoleAt c z = (Real.log (R ^ 2) : EReal) := by
  have hnorm : ‖z - c‖ = R := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  have hne : z - c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hR.ne' hnorm.symm
  rw [logPoleAt, logNormSq_of_ne_zero hne, hnorm]

/-- Every strictly positive real multiple of the translated logarithmic pole
is PSH.  The coefficient is kept explicit because the puncture argument sends
it to zero after applying the annular maximum principle. -/
theorem plurisubharmonicOn_const_mul_logPoleAt (c : ℂ) {e : ℝ} (he : 0 < e) :
    PlurisubharmonicOn (fun z => (e : EReal) * logPoleAt c z) univ :=
  (plurisubharmonicOn_logPoleAt c).const_mul he

/-- The annular logarithmic-barrier estimate with an arbitrary positive
coefficient.  This is the form used before taking the coefficient to zero. -/
theorem PlurisubharmonicOn.le_const_mul_logPoleAt_on_closedAnnulus
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {r R A B e : ℝ}
    (hu : PlurisubharmonicOn u Omega) (he : 0 < e) (hr : 0 < r) (hrR : r < R)
    (hAnn : closedAnnulus c r R ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (A : EReal))
    (hinner : ∀ z ∈ sphere c r, u z ≤ (B : EReal)) :
    ∀ z ∈ closedAnnulus c r R,
      u z + (e : EReal) * logPoleAt c z ≤
        (max (A + e * Real.log (R ^ 2)) (B + e * Real.log (r ^ 2)) : ℝ) := by
  apply PlurisubharmonicOn.le_const_on_closedAnnulus
    (hu.add ((plurisubharmonicOn_const_mul_logPoleAt c he).mono (subset_univ _))) hr hrR hAnn
  · intro z hz
    calc
      u z + (e : EReal) * logPoleAt c z ≤
          (A : EReal) + (e : EReal) * logPoleAt c z :=
        add_le_add (houter z hz) le_rfl
      _ = (A : EReal) + (e : EReal) * (Real.log (R ^ 2) : EReal) := by
        rw [logPoleAt_eq_on_sphere (lt_trans hr hrR) hz]
      _ = (A + e * Real.log (R ^ 2) : ℝ) := by
        rw [← EReal.coe_mul, ← EReal.coe_add]
      _ ≤ (max (A + e * Real.log (R ^ 2)) (B + e * Real.log (r ^ 2)) : ℝ) :=
        EReal.coe_le_coe_iff.mpr (le_max_left _ _)
  · intro z hz
    calc
      u z + (e : EReal) * logPoleAt c z ≤
          (B : EReal) + (e : EReal) * logPoleAt c z :=
        add_le_add (hinner z hz) le_rfl
      _ = (B : EReal) + (e : EReal) * (Real.log (r ^ 2) : EReal) := by
        rw [logPoleAt_eq_on_sphere hr hz]
      _ = (B + e * Real.log (r ^ 2) : ℝ) := by
        rw [← EReal.coe_mul, ← EReal.coe_add]
      _ ≤ (max (A + e * Real.log (R ^ 2)) (B + e * Real.log (r ^ 2)) : ℝ) :=
        EReal.coe_le_coe_iff.mpr (le_max_right _ _)

/-- **Logarithmic-barrier estimate.**  A PSH function bounded above by `A` on
the outer circle and by `B` on the inner circle obeys the displayed bound for
`u + log ‖z-c‖²` throughout the annulus.  In the removable-puncture argument,
`B` comes from the local upper bound while `log(r²) → -∞` makes the inner term
harmless as `r → 0`. -/
theorem PlurisubharmonicOn.le_logPoleAt_on_closedAnnulus
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {r R A B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hr : 0 < r) (hrR : r < R)
    (hAnn : closedAnnulus c r R ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (A : EReal))
    (hinner : ∀ z ∈ sphere c r, u z ≤ (B : EReal)) :
    ∀ z ∈ closedAnnulus c r R,
      u z + logPoleAt c z ≤
        (max (A + Real.log (R ^ 2)) (B + Real.log (r ^ 2)) : ℝ) := by
  apply PlurisubharmonicOn.le_const_on_closedAnnulus
    (hu.add ((plurisubharmonicOn_logPoleAt c).mono (subset_univ _))) hr hrR hAnn
  · intro z hz
    calc
      u z + logPoleAt c z ≤ (A : EReal) + logPoleAt c z :=
        add_le_add (houter z hz) le_rfl
      _ = (A : EReal) + (Real.log (R ^ 2) : EReal) := by
        rw [logPoleAt_eq_on_sphere (lt_trans hr hrR) hz]
      _ = (A + Real.log (R ^ 2) : ℝ) := (EReal.coe_add _ _).symm
      _ ≤ (max (A + Real.log (R ^ 2)) (B + Real.log (r ^ 2)) : ℝ) :=
        EReal.coe_le_coe_iff.mpr (le_max_left _ _)
  · intro z hz
    calc
      u z + logPoleAt c z ≤ (B : EReal) + logPoleAt c z :=
        add_le_add (hinner z hz) le_rfl
      _ = (B : EReal) + (Real.log (r ^ 2) : EReal) := by
        rw [logPoleAt_eq_on_sphere hr hz]
      _ = (B + Real.log (r ^ 2) : ℝ) := (EReal.coe_add _ _).symm
      _ ≤ (max (A + Real.log (R ^ 2)) (B + Real.log (r ^ 2)) : ℝ) :=
        EReal.coe_le_coe_iff.mpr (le_max_right _ _)

/-- A quantitative replacement for the informal limit
`log (r²) → -∞`: below any fixed positive outer radius, one can choose an
inner radius whose logarithmic boundary contribution is no larger than a
prescribed finite outer contribution. -/
theorem exists_radius_log_inner_le_outer {R A B : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      B + Real.log (r ^ 2) ≤ A + Real.log (R ^ 2) := by
  let q : ℝ := (A + Real.log (R ^ 2) - B) / 2
  let r : ℝ := min (R / 2) (Real.exp q)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (Real.exp_pos q)
  have hrR : r < R :=
    (min_le_left _ _).trans_lt (by linarith)
  have hrexp : r ≤ Real.exp q := min_le_right _ _
  have hsq : r ^ 2 ≤ (Real.exp q) ^ 2 :=
    (sq_le_sq₀ hr.le (Real.exp_pos q).le).mpr hrexp
  have hlog : Real.log (r ^ 2) ≤ Real.log ((Real.exp q) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn (sq_pos_of_pos hr)
      (sq_pos_of_pos (Real.exp_pos q)) hsq
  refine ⟨r, hr, hrR, ?_⟩
  have hlogq : Real.log (r ^ 2) ≤ 2 * q :=
    hlog.trans_eq (by
      rw [Real.log_pow, Real.log_exp]
      norm_num)
  calc
    B + Real.log (r ^ 2) ≤ B + (2 * q) := by linarith
    _ = A + Real.log (R ^ 2) := by
      dsimp [q]
      ring

/-- The quantitative inner-radius choice for every positive logarithmic
coefficient.  This is the finite, no-limit form needed before sending that
coefficient to zero. -/
theorem exists_radius_const_mul_log_inner_le_outer {R A B e : ℝ}
    (hR : 0 < R) (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      B + e * Real.log (r ^ 2) ≤ A + e * Real.log (R ^ 2) := by
  let q : ℝ := (A + e * Real.log (R ^ 2) - B) / (2 * e)
  let r : ℝ := min (R / 2) (Real.exp q)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (Real.exp_pos q)
  have hrR : r < R :=
    (min_le_left _ _).trans_lt (by linarith)
  have hrexp : r ≤ Real.exp q := min_le_right _ _
  have hsq : r ^ 2 ≤ (Real.exp q) ^ 2 :=
    (sq_le_sq₀ hr.le (Real.exp_pos q).le).mpr hrexp
  have hlog : Real.log (r ^ 2) ≤ Real.log ((Real.exp q) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn (sq_pos_of_pos hr)
      (sq_pos_of_pos (Real.exp_pos q)) hsq
  have hlogq : Real.log (r ^ 2) ≤ 2 * q :=
    hlog.trans_eq (by
      rw [Real.log_pow, Real.log_exp]
      norm_num)
  refine ⟨r, hr, hrR, ?_⟩
  calc
    B + e * Real.log (r ^ 2) ≤ B + e * (2 * q) := by
      gcongr
    _ = A + e * Real.log (R ^ 2) := by
      dsimp [q]
      field_simp [he.ne']
      ring

/-- A locally bounded-above PSH function on a punctured closed disc admits a
smaller annulus on which the logarithmic barrier is controlled solely by the
outer-circle bound.  The inner-circle estimate is derived from the supplied
ordinary local bound and the quantitative radius choice above. -/
theorem PlurisubharmonicOn.exists_logPoleAt_annular_bound
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R A B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (A : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ z ∈ closedAnnulus c r R,
        u z + logPoleAt c z ≤ (A + Real.log (R ^ 2) : ℝ) := by
  obtain ⟨r, hr, hrR, hrbound⟩ := exists_radius_log_inner_le_outer (A := A) (B := B) hR
  refine ⟨r, hr, hrR, ?_⟩
  have hAnn : closedAnnulus c r R ⊆ Omega := by
    intro z hz
    change z ∈ closedBall c R ∧ z ∉ ball c r at hz
    apply hclosed
    refine ⟨hz.1, ?_⟩
    intro hzc
    subst z
    exact hz.2 (mem_ball_self hr)
  have hinner : ∀ z ∈ sphere c r, u z ≤ (B : EReal) := by
    intro z hz
    have hzclosed : z ∈ closedBall c R :=
      Metric.closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hz)
    have hzne : z ≠ c := by
      intro hzc
      subst z
      have hzero : (0 : ℝ) = r := by simpa using (mem_sphere.mp hz)
      exact hr.ne' hzero.symm
    exact hbound z ⟨hzclosed, by simpa using hzne⟩
  have hbar := PlurisubharmonicOn.le_logPoleAt_on_closedAnnulus
    hu hr hrR hAnn houter hinner
  intro z hz
  rw [max_eq_left hrbound] at hbar
  exact hbar z hz

/-- The preceding punctured-disc barrier with a freely chosen positive
coefficient.  Its outer bound converges to the original outer bound when the
coefficient tends to zero. -/
theorem PlurisubharmonicOn.exists_const_mul_logPoleAt_annular_bound
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R A B e : ℝ}
    (hu : PlurisubharmonicOn u Omega) (he : 0 < e) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (A : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ z ∈ closedAnnulus c r R,
        u z + (e : EReal) * logPoleAt c z ≤
          (A + e * Real.log (R ^ 2) : ℝ) := by
  obtain ⟨r, hr, hrR, hrbound⟩ :=
    exists_radius_const_mul_log_inner_le_outer (A := A) (B := B) hR he
  refine ⟨r, hr, hrR, ?_⟩
  have hAnn : closedAnnulus c r R ⊆ Omega := by
    intro z hz
    change z ∈ closedBall c R ∧ z ∉ ball c r at hz
    apply hclosed
    refine ⟨hz.1, ?_⟩
    intro hzc
    subst z
    exact hz.2 (mem_ball_self hr)
  have hinner : ∀ z ∈ sphere c r, u z ≤ (B : EReal) := by
    intro z hz
    have hzclosed : z ∈ closedBall c R :=
      Metric.closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hz)
    have hzne : z ≠ c := by
      intro hzc
      subst z
      have hzero : (0 : ℝ) = r := by simpa using (mem_sphere.mp hz)
      exact hr.ne' hzero.symm
    exact hbound z ⟨hzclosed, by simpa using hzne⟩
  have hbar := PlurisubharmonicOn.le_const_mul_logPoleAt_on_closedAnnulus
    hu he hr hrR hAnn houter hinner
  intro z hz
  rw [max_eq_left hrbound] at hbar
  exact hbar z hz

/-- The quantitative logarithmic radius can be made smaller than any
prescribed positive threshold.  Taking that threshold to be the distance to a
fixed point is what turns the annular estimate into a pointwise one. -/
theorem exists_radius_const_mul_log_inner_le_outer_lt {R A B e δ : ℝ}
    (hR : 0 < R) (he : 0 < e) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ r < δ ∧
      B + e * Real.log (r ^ 2) ≤ A + e * Real.log (R ^ 2) := by
  let q : ℝ := (A + e * Real.log (R ^ 2) - B) / (2 * e)
  let r : ℝ := min (R / 2) (min (δ / 2) (Real.exp q))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (lt_min (by linarith) (Real.exp_pos q))
  have hrR : r < R :=
    (min_le_left _ _).trans_lt (by linarith)
  have hrδ : r < δ :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hrexp : r ≤ Real.exp q :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsq : r ^ 2 ≤ (Real.exp q) ^ 2 :=
    (sq_le_sq₀ hr.le (Real.exp_pos q).le).mpr hrexp
  have hlog : Real.log (r ^ 2) ≤ Real.log ((Real.exp q) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn (sq_pos_of_pos hr)
      (sq_pos_of_pos (Real.exp_pos q)) hsq
  have hlogq : Real.log (r ^ 2) ≤ 2 * q :=
    hlog.trans_eq (by
      rw [Real.log_pow, Real.log_exp]
      norm_num)
  refine ⟨r, hr, hrR, hrδ, ?_⟩
  calc
    B + e * Real.log (r ^ 2) ≤ B + e * (2 * q) := by
      gcongr
    _ = A + e * Real.log (R ^ 2) := by
      dsimp [q]
      field_simp [he.ne']
      ring

/-- The scaled annular barrier with its inner radius forced below a prescribed
threshold. -/
theorem PlurisubharmonicOn.exists_const_mul_logPoleAt_annular_bound_lt
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R A B e δ : ℝ}
    (hu : PlurisubharmonicOn u Omega) (he : 0 < e) (hR : 0 < R) (hδ : 0 < δ)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (houter : ∀ z ∈ sphere c R, u z ≤ (A : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ r < δ ∧
      ∀ z ∈ closedAnnulus c r R,
        u z + (e : EReal) * logPoleAt c z ≤
          (A + e * Real.log (R ^ 2) : ℝ) := by
  obtain ⟨r, hr, hrR, hrδ, hrbound⟩ :=
    exists_radius_const_mul_log_inner_le_outer_lt (A := A) (B := B) hR he hδ
  refine ⟨r, hr, hrR, hrδ, ?_⟩
  have hAnn : closedAnnulus c r R ⊆ Omega := by
    intro z hz
    change z ∈ closedBall c R ∧ z ∉ ball c r at hz
    apply hclosed
    refine ⟨hz.1, ?_⟩
    intro hzc
    subst z
    exact hz.2 (mem_ball_self hr)
  have hinner : ∀ z ∈ sphere c r, u z ≤ (B : EReal) := by
    intro z hz
    have hzclosed : z ∈ closedBall c R :=
      Metric.closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hz)
    have hzne : z ≠ c := by
      intro hzc
      subst z
      have hzero : (0 : ℝ) = r := by simpa using (mem_sphere.mp hz)
      exact hr.ne' hzero.symm
    exact hbound z ⟨hzclosed, by simpa using hzne⟩
  have hbar := PlurisubharmonicOn.le_const_mul_logPoleAt_on_closedAnnulus
    hu he hr hrR hAnn houter hinner
  intro z hz
  rw [max_eq_left hrbound] at hbar
  exact hbar z hz

/-- Pointwise scaled logarithmic barrier on every noncentral point of the
punctured closed disc.  The proof chooses the inner radius below `dist z c`,
so this is exactly the form needed before the coefficient tends to zero. -/
theorem PlurisubharmonicOn.const_mul_logPoleAt_le_bound_of_mem_closedBall_ne
    {u : ℂ → EReal} {Omega : Set ℂ} {c z : ℂ} {R A B e : ℝ}
    (hu : PlurisubharmonicOn u Omega) (he : 0 < e) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (houter : ∀ w ∈ sphere c R, u w ≤ (A : EReal))
    (hbound : ∀ w ∈ closedBall c R \ {c}, u w ≤ (B : EReal))
    (hz : z ∈ closedBall c R) (hzc : z ≠ c) :
    u z + (e : EReal) * logPoleAt c z ≤
      (A + e * Real.log (R ^ 2) : ℝ) := by
  have hδ : 0 < dist z c := dist_pos.mpr hzc
  obtain ⟨r, hr, hrR, hrδ, hbar⟩ :=
    PlurisubharmonicOn.exists_const_mul_logPoleAt_annular_bound_lt
      hu he hR hδ hclosed houter hbound
  apply hbar z
  change z ∈ closedBall c R ∧ z ∉ ball c r
  refine ⟨hz, ?_⟩
  rw [mem_ball]
  exact not_lt_of_ge hrδ.le

/-- A finite logarithmic error with an arbitrary positive coefficient
may be sent to zero in `EReal` without an analytic limit theorem.  The explicit
choice `e = δ / (|K-L|+1)` reduces the claim to ordinary real inequalities. -/
theorem EReal.le_coe_of_forall_pos_add_mul_le
    {x : EReal} {A L K : ℝ}
    (h : ∀ e : ℝ, 0 < e →
      x + (e : EReal) * (L : EReal) ≤ (A + e * K : ℝ)) :
    x ≤ (A : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | top =>
      exfalso
      have hfalse := h 1 (by norm_num)
      simp at hfalse
      apply EReal.coe_ne_top (A + K)
      simpa only [EReal.coe_add] using hfalse
  | coe x =>
      rw [EReal.coe_le_coe_iff]
      apply le_of_forall_pos_le_add
      intro δ hδ
      let e : ℝ := δ / (|K - L| + 1)
      have hden : 0 < |K - L| + 1 := by positivity
      have he : 0 < e := div_pos hδ hden
      have hreal : x + e * L ≤ A + e * K := by
        have h' := h e he
        norm_cast at h'
      have hsmall : e * (K - L) ≤ δ := by
        calc
          e * (K - L) ≤ e * |K - L| :=
            mul_le_mul_of_nonneg_left (le_abs_self (K - L)) he.le
          _ = δ * (|K - L| / (|K - L| + 1)) := by
            dsimp [e]
            field_simp
          _ ≤ δ * 1 := by
            gcongr
            exact (div_le_one₀ hden).mpr (by linarith)
          _ = δ := by ring
      linarith

/-- **Punctured-disc maximum principle.** A locally bounded-above PSH branch
on a punctured closed disc is bounded by any constant upper bound on its outer
circle.  This is the pointwise removable-singularity core, obtained by the
logarithmic barrier and the preceding coefficient-to-zero lemma. -/
theorem PlurisubharmonicOn.le_const_of_punctured_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} {c z : ℂ} {R A B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (houter : ∀ w ∈ sphere c R, u w ≤ (A : EReal))
    (hbound : ∀ w ∈ closedBall c R \ {c}, u w ≤ (B : EReal))
    (hz : z ∈ closedBall c R) (hzc : z ≠ c) : u z ≤ (A : EReal) := by
  apply EReal.le_coe_of_forall_pos_add_mul_le
  intro e he
  have hbar := PlurisubharmonicOn.const_mul_logPoleAt_le_bound_of_mem_closedBall_ne
    hu he hR hclosed houter hbound hz hzc
  have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
  rw [logPoleAt, logNormSq_of_ne_zero hne] at hbar
  exact hbar

/-- A local ordinary bound controls the value assigned by upper
regularization at its centre.  This packages the precise limsup step needed
at the puncture without assuming the desired removable-singularity theorem. -/
theorem uscRegularization_le_of_eventually_le
    {raw : ℂ → EReal} {a : ℂ} {C : EReal}
    (hC : {z | raw z ≤ C} ∈ 𝓝 a) :
    uscRegularization raw a ≤ C := by
  refine (uscRegularization_le_localSup raw hC).trans (iSup₂_le fun z hz => ?_)
  exact hz

/-- The preceding limsup control with a continuous, nonconstant majorant.
Once a harmonic boundary construction yields a continuous majorant on the
punctured neighbourhood, this theorem transports it rigorously to the
regularized value at the missing centre. -/
theorem uscRegularization_le_of_eventually_le_continuous
    {raw : ℂ → EReal} {a : ℂ} {g : ℂ → EReal}
    (hg : Continuous g) (hfg : {z | raw z ≤ g z} ∈ 𝓝 a) :
    uscRegularization raw a ≤ g a := by
  apply le_of_forall_gt
  intro b hab
  obtain ⟨d, had, hdb⟩ := exists_between hab
  have hgd : {z | g z < d} ∈ 𝓝 a := hg.upperSemicontinuous a d had
  have hU : {z | raw z ≤ g z} ∩ {z | g z < d} ∈ 𝓝 a := inter_mem hfg hgd
  exact ((uscRegularization_le_localSup raw hU).trans
    (iSup_le fun z => iSup_le fun hz => (hz.1.trans (le_of_lt hz.2)))).trans_lt hdb


/-- Continuous real data on an outer circle admits a globally harmonic,
continuous strict majorant there.  The majorant is *constructed* from Fourier
approximation, rather than being an input to the punctured-disc argument. -/
theorem exists_global_harmonic_strict_majorantOn_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere c R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h univ ∧ Continuous h ∧
      ∀ z ∈ sphere c R, g z < h z ∧ h z < g z + 2 * ε := by
  obtain ⟨h, hh, happ⟩ :=
    exists_global_harmonic_uniformApproxOn_sphere c hR hg hε
  have hh' : InnerProductSpace.HarmonicOnNhd (h + fun _ => ε) univ :=
    hh.add (InnerProductSpace.harmonicOnNhd_const ε)
  refine ⟨h + fun _ => ε, hh', ?_, ?_⟩
  · simpa only [continuousOn_univ] using hh'.contDiffOn.continuousOn
  · intro z hz
    obtain ⟨hl, hr⟩ := abs_lt.mp (happ z hz)
    change g z < h z + ε ∧ h z + ε < g z + 2 * ε
    constructor <;> linarith

/-- An extended-real branch below continuous outer-circle data therefore has a
constructed global harmonic outer majorant.  This is the form fed into the
scaled logarithmic annulus estimate after subtracting the harmonic function. -/
theorem exists_global_harmonic_outer_majorantOn_sphere
    {u : ℂ → EReal} (c : ℂ) {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere c R))
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h univ ∧ Continuous h ∧
      ∀ z ∈ sphere c R, u z ≤ (h z : EReal) ∧ h z < g z + 2 * ε := by
  obtain ⟨h, hh, hcont, hbounds⟩ :=
    exists_global_harmonic_strict_majorantOn_sphere c hR hg hε
  refine ⟨h, hh, hcont, ?_⟩
  intro z hz
  refine ⟨(hgu z hz).trans ?_, (hbounds z hz).2⟩
  exact EReal.coe_le_coe_iff.mpr (le_of_lt (hbounds z hz).1)

/-- A continuous real function has a real lower bound on every closed complex
ball.  This supplies the local upper bound for `u - h` after a harmonic
majorant has been constructed from outer-circle data. -/
theorem exists_lower_bound_on_closedBall_of_continuous
    {h : ℂ → ℝ} (hh : Continuous h) (c : ℂ) (R : ℝ) :
    ∃ m : ℝ, ∀ z ∈ closedBall c R, m ≤ h z := by
  obtain ⟨m, hm⟩ :=
    (ProperSpace.isCompact_closedBall c R).bddBelow_image hh.continuousOn
  refine ⟨m, ?_⟩
  intro z hz
  exact hm ⟨z, hz, rfl⟩

/-- **Constructed harmonic majorant on a punctured disc.** Continuous outer
circle data majorizing a locally bounded-above PSH branch produces a global
real harmonic function that majorizes the branch throughout the punctured
closed disc.  No harmonic majorant is assumed: it is obtained from the Fourier
circle approximation and then propagated by the punctured-disc maximum
principle. -/
theorem PlurisubharmonicOn.exists_global_harmonic_majorant_of_punctured_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere c R))
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h univ ∧ Continuous h ∧
      ∀ z ∈ closedBall c R \ {c}, u z ≤ (h z : EReal) := by
  obtain ⟨h, hh, hcont, hbounds⟩ :=
    exists_global_harmonic_outer_majorantOn_sphere c hR hg hgu hε
  obtain ⟨m, hm⟩ := exists_lower_bound_on_closedBall_of_continuous hcont c R
  have hhOmega : InnerProductSpace.HarmonicOnNhd h Omega := hh.mono (subset_univ _)
  have hsub : PlurisubharmonicOn (fun z => u z - (h z : EReal)) Omega :=
    hu.sub_harmonic hhOmega
  have houter_sub : ∀ z ∈ sphere c R, u z - (h z : EReal) ≤ (0 : EReal) := by
    intro z hz
    exact EReal.sub_nonpos.mpr (hbounds z hz).1
  have hbound_sub : ∀ z ∈ closedBall c R \ {c},
      u z - (h z : EReal) ≤ ((B - m : ℝ) : EReal) := by
    intro z hz
    calc
      u z - (h z : EReal) ≤ (B : EReal) - (h z : EReal) :=
        EReal.sub_le_sub (hbound z hz) le_rfl
      _ = ((B - h z : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ ((B - m : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (sub_le_sub le_rfl (hm z hz.1))
  refine ⟨h, hh, hcont, ?_⟩
  intro z hz
  have hmax := Hironaka.PshPuncturedLineRemovable.PlurisubharmonicOn.le_const_of_punctured_closedBall
    hsub hR hclosed houter_sub hbound_sub hz.1 hz.2
  have hmax' : u z - (h z : EReal) ≤ (0 : EReal) := by simpa using hmax
  exact EReal.sub_nonpos.mp hmax'

/-- A global harmonic function whose outer-circle values lie below `g + δ`
has the corresponding centre bound by the harmonic mean-value formula. -/
theorem harmonic_center_le_circleAverage_add_of_le_on_sphere
    {h g : ℂ → ℝ} {c : ℂ} {R δ : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h univ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R))
    (hbound : ∀ z ∈ sphere c R, h z ≤ g z + δ) :
    h c ≤ Real.circleAverage g c R + δ := by
  have hhclosed : InnerProductSpace.HarmonicOnNhd h (closedBall c |R|) :=
    hh.mono (subset_univ _)
  have hcircle_h : CircleIntegrable h c R :=
    (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  have hcircle_g : CircleIntegrable g c R := by
    apply ContinuousOn.circleIntegrable'
    simpa [abs_of_pos hR] using hg
  have hcircle_const : CircleIntegrable (fun _ : ℂ => δ) c R :=
    circleIntegrable_const δ c R
  have hmono : Real.circleAverage h c R ≤
      Real.circleAverage (fun z => g z + δ) c R := by
    apply Real.circleAverage_mono hcircle_h (hcircle_g.add hcircle_const)
    intro z hz
    exact hbound z (by simpa [abs_of_pos hR] using hz)
  rw [hhclosed.circleAverage_eq,
    Real.circleAverage_fun_add hcircle_g hcircle_const,
    Real.circleAverage_const] at hmono
  exact hmono

/-- The constructed punctured-disc harmonic majorant can retain its uniform
outer-circle approximation error.  This strengthened form is what makes its
centre value comparable with the prescribed circle average. -/
theorem PlurisubharmonicOn.exists_global_harmonic_majorant_of_punctured_closedBall_with_error
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere c R))
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h univ ∧ Continuous h ∧
      (∀ z ∈ closedBall c R \ {c}, u z ≤ (h z : EReal)) ∧
      ∀ z ∈ sphere c R, h z < g z + 2 * ε := by
  obtain ⟨h, hh, hcont, hbounds⟩ :=
    exists_global_harmonic_outer_majorantOn_sphere c hR hg hgu hε
  obtain ⟨m, hm⟩ := exists_lower_bound_on_closedBall_of_continuous hcont c R
  have hhOmega : InnerProductSpace.HarmonicOnNhd h Omega := hh.mono (subset_univ _)
  have hsub : PlurisubharmonicOn (fun z => u z - (h z : EReal)) Omega :=
    hu.sub_harmonic hhOmega
  have houter_sub : ∀ z ∈ sphere c R, u z - (h z : EReal) ≤ (0 : EReal) := by
    intro z hz
    exact EReal.sub_nonpos.mpr (hbounds z hz).1
  have hbound_sub : ∀ z ∈ closedBall c R \ {c},
      u z - (h z : EReal) ≤ ((B - m : ℝ) : EReal) := by
    intro z hz
    calc
      u z - (h z : EReal) ≤ (B : EReal) - (h z : EReal) :=
        EReal.sub_le_sub (hbound z hz) le_rfl
      _ = ((B - h z : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ ((B - m : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (sub_le_sub le_rfl (hm z hz.1))
  refine ⟨h, hh, hcont, ?_, ?_⟩
  · intro z hz
    have hmax := Hironaka.PshPuncturedLineRemovable.PlurisubharmonicOn.le_const_of_punctured_closedBall
      hsub hR hclosed houter_sub hbound_sub hz.1 hz.2
    have hmax' : u z - (h z : EReal) ≤ (0 : EReal) := by simpa using hmax
    exact EReal.sub_nonpos.mp hmax'
  · intro z hz
    exact (hbounds z hz).2

/-- The centre value assigned by upper regularization to the function equal to
`u` off a puncture and `-∞` at it is bounded by the circle average of every
continuous outer majorant.  The proof constructs a fresh harmonic majorant for
each positive error and removes that error by the explicit `EReal` endpoint
lemma above. -/
theorem uscRegularization_puncturedFill_le_circleAverage
    {u : ℂ → EReal} {Omega : Set ℂ} {c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere c R))
    (hgu : ∀ z ∈ sphere c R, u z ≤ (g z : EReal))
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    uscRegularization (fun z => if z = c then (⊥ : EReal) else u z) c ≤
      ((Real.circleAverage g c R : ℝ) : EReal) := by
  apply EReal.le_coe_of_forall_pos_add_mul_le (L := 0) (K := 2)
  intro ε hε
  obtain ⟨h, hh, hcont, hmajor, herr⟩ :=
    PlurisubharmonicOn.exists_global_harmonic_majorant_of_punctured_closedBall_with_error
      hu hR hclosed hg hgu hbound hε
  have hlocal : {z | (if z = c then (⊥ : EReal) else u z) ≤ (h z : EReal)} ∈ 𝓝 c := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds c hR)
    intro z hz
    by_cases hzc : z = c
    · simp [hzc]
    · change (if z = c then (⊥ : EReal) else u z) ≤ (h z : EReal)
      rw [if_neg hzc]
      exact hmajor z ⟨ball_subset_closedBall hz, hzc⟩
  have hcontE : Continuous (fun z => (h z : EReal)) :=
    EReal.continuous_coe_iff.mpr hcont
  have husc := uscRegularization_le_of_eventually_le_continuous hcontE hlocal
  have hcenter : h c ≤ Real.circleAverage g c R + 2 * ε :=
    harmonic_center_le_circleAverage_add_of_le_on_sphere hh hR hg
      (fun z hz => (herr z hz).le)
  have hcenterE : (h c : EReal) ≤
      (Real.circleAverage g c R + 2 * ε : ℝ) :=
    EReal.coe_le_coe_iff.mpr hcenter
  simpa [EReal.coe_mul, EReal.coe_add, mul_comm] using husc.trans hcenterE

end

end Hironaka.PshPuncturedLineRemovable

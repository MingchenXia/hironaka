import Hironaka.Analytic.PshPuncturedLineRemovable
import Hironaka.Analytic.DiscPshSupremum
import Hironaka.Analytic.PshDiscLocalGlobal
import Hironaka.Analytic.UscSupremumRecovery
import Hironaka.Analytic.UscRegularizationLocality

set_option autoImplicit false

/-!
# Ambient control of a hypersurface upper regularization along a line

The transverse one-dimensional logarithmic-barrier argument controls the
*intrinsic* upper regularization of a punctured line.  The function used by the
hypersurface theorem is instead the restriction of an **ambient** upper
regularization.  This file closes that gap: recovery points off the hyperplane,
compactness of parallel closed discs, and the intrinsic deficit estimate give
the ambient disc-submean inequality.  It then derives the transverse-slice and
ambient plurisubharmonic extension theorems without identifying the two
regularizations.

The final continuous-majorant lemmas are retained as an independent local
estimate: a continuous function `G` that dominates the original branch on an
ambient punctured neighborhood dominates `extension A ψ` at the centre.  They
are no longer an unresolved prerequisite for the hypersurface theorem.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshAmbientExtensionLineControl


open PshCodimTwoExtension
open PshHypersurfaceRemovable

noncomputable section

variable {n : ℕ}

/-- Upper semicontinuity transports circle deficits from parallel discs with
moving centres to their limiting disc.  Unlike
`Hironaka.circleDeficit_le_liminf_of_moving_centers`, this lemma does not
assume that the approximating functions are disc-PSH: the required submean
information can instead already be recorded as a bound on each moving
deficit.  This is the form needed for ambient upper regularizations, whose
parallel-line restrictions have not yet been shown PSH. -/
theorem circleDeficit_le_liminf_of_moving_centers_of_upperSemicontinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    {w : E → EReal} (husc : UpperSemicontinuous w)
    (x : E) (centers : ℕ → E) (v : E) {r : ℝ}
    (hcenters : Tendsto centers atTop (𝓝 x)) (C : ℝ) :
    circleDeficit w x v r C ≤
      liminf (fun k => circleDeficit w (centers k) v r C) atTop := by
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun t => deficit C (w (centers k + circleMap 0 r t • v)))
      (volume.restrict (Ioc 0 (2 * Real.pi))) := fun k =>
    ((continuous_deficit _).measurable.comp
      (husc.measurable.comp (by fun_prop : Continuous fun t : ℝ =>
        centers k + circleMap 0 r t • v).measurable)).aemeasurable
  have hpointwise : ∀ t : ℝ,
      deficit C (w (x + circleMap 0 r t • v)) ≤
        liminf (fun k => deficit C (w (centers k + circleMap 0 r t • v))) atTop :=
    fun t => by
      have hp : Tendsto (fun k => centers k + circleMap 0 r t • v) atTop
          (𝓝 (x + circleMap 0 r t • v)) :=
        hcenters.add tendsto_const_nhds
      have hls : limsup (fun k => w (centers k + circleMap 0 r t • v)) atTop ≤
          w (x + circleMap 0 r t • v) :=
        (limsup_le_limsup_of_le hp (by isBoundedDefault) (by isBoundedDefault)).trans
          (upperSemicontinuousAt_iff_limsup_le.mp (husc _))
      calc deficit C (w (x + circleMap 0 r t • v))
          ≤ deficit C (limsup (fun k => w (centers k + circleMap 0 r t • v)) atTop) :=
            antitone_deficit _ hls
        _ = liminf (fun k => deficit C (w (centers k + circleMap 0 r t • v))) atTop :=
          (antitone_deficit _).map_limsup_of_continuousAt _
            (continuous_deficit _).continuousAt
  calc
    circleDeficit w x v r C =
        ∫⁻ t in Ioc 0 (2 * Real.pi), deficit C (w (x + circleMap 0 r t • v)) := rfl
    _ ≤ ∫⁻ t in Ioc 0 (2 * Real.pi),
          liminf (fun k => deficit C (w (centers k + circleMap 0 r t • v))) atTop :=
        lintegral_mono hpointwise
    _ ≤ liminf (fun k => circleDeficit w (centers k) v r C) atTop :=
        lintegral_liminf_le' hmeas

/-- A sequence of already-established submean deficit bounds on moving
parallel discs gives the limiting disc submean bound.  The center values may
come from the unregularized ambient branch: only their convergence to the
ambient regularized value is used. -/
theorem circleSubmean_of_moving_center_circleDeficits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    {w : E → EReal} (husc : UpperSemicontinuous w)
    (x : E) (centers : ℕ → E) (v : E) {r : ℝ}
    (hcenters : Tendsto centers atTop (𝓝 x)) (C : ℝ)
    {centerValue : ℕ → EReal}
    (hcenter : Tendsto centerValue atTop (𝓝 (w x)))
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hsub : ∀ k, circleDeficit w (centers k) v r C ≤
      K * ((C : EReal) - centerValue k).toENNReal) :
    circleDeficit w x v r C ≤ K * ((C : EReal) - w x).toENNReal := by
  let d : EReal → ℝ≥0∞ := fun a => ((C : EReal) - a).toENNReal
  have hdcenter : Tendsto (fun k => d (centerValue k)) atTop (𝓝 (d (w x))) :=
    (continuous_finiteDeficit C).continuousAt.tendsto.comp hcenter
  calc
    circleDeficit w x v r C ≤
        liminf (fun k => circleDeficit w (centers k) v r C) atTop :=
      circleDeficit_le_liminf_of_moving_centers_of_upperSemicontinuous husc
        x centers v hcenters C
    _ ≤ liminf (fun k => K * ((C : EReal) - centerValue k).toENNReal) atTop := by
      simp only [liminf_eq_iSup_iInf_of_nat]
      exact iSup_mono fun _ => iInf_mono fun k => iInf_mono fun _ => hsub k
    _ = K * liminf (fun k => d (centerValue k)) atTop :=
      ENNReal.liminf_const_mul_of_ne_top hK
    _ = K * ((C : EReal) - w x).toENNReal := by
      rw [hdcenter.liminf_eq]

/-- The same Fatou transport remains valid when the directions of the test
discs converge as well as their centres.  It is the analytic device for
approximating a tangent punctured disc by strictly smaller discs that leave
the puncture outside. -/
theorem circleDeficit_le_liminf_of_moving_centers_and_vectors_of_upperSemicontinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    {w : E → EReal} (husc : UpperSemicontinuous w)
    (x : E) (centers vectors : ℕ → E) (v : E) {r : ℝ}
    (hcenters : Tendsto centers atTop (𝓝 x))
    (hvectors : Tendsto vectors atTop (𝓝 v)) (C : ℝ) :
    circleDeficit w x v r C ≤
      liminf (fun k => circleDeficit w (centers k) (vectors k) r C) atTop := by
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun t => deficit C (w (centers k + circleMap 0 r t • vectors k)))
      (volume.restrict (Ioc 0 (2 * Real.pi))) := fun k =>
    ((continuous_deficit _).measurable.comp
      (husc.measurable.comp (by fun_prop : Continuous fun t : ℝ =>
        centers k + circleMap 0 r t • vectors k).measurable)).aemeasurable
  have hpointwise : ∀ t : ℝ,
      deficit C (w (x + circleMap 0 r t • v)) ≤
        liminf (fun k => deficit C (w (centers k + circleMap 0 r t • vectors k))) atTop :=
    fun t => by
      have hp : Tendsto (fun k => centers k + circleMap 0 r t • vectors k) atTop
          (𝓝 (x + circleMap 0 r t • v)) :=
        hcenters.add (tendsto_const_nhds.smul hvectors)
      have hls : limsup (fun k => w (centers k + circleMap 0 r t • vectors k)) atTop ≤
          w (x + circleMap 0 r t • v) :=
        (limsup_le_limsup_of_le hp (by isBoundedDefault) (by isBoundedDefault)).trans
          (upperSemicontinuousAt_iff_limsup_le.mp (husc _))
      calc deficit C (w (x + circleMap 0 r t • v))
          ≤ deficit C (limsup (fun k => w (centers k + circleMap 0 r t • vectors k)) atTop) :=
            antitone_deficit _ hls
        _ = liminf (fun k => deficit C (w (centers k + circleMap 0 r t • vectors k))) atTop :=
          (antitone_deficit _).map_limsup_of_continuousAt _
            (continuous_deficit _).continuousAt
  calc
    circleDeficit w x v r C =
        ∫⁻ t in Ioc 0 (2 * Real.pi), deficit C (w (x + circleMap 0 r t • v)) := rfl
    _ ≤ ∫⁻ t in Ioc 0 (2 * Real.pi),
          liminf (fun k => deficit C (w (centers k + circleMap 0 r t • vectors k))) atTop :=
        lintegral_mono hpointwise
    _ ≤ liminf (fun k => circleDeficit w (centers k) (vectors k) r C) atTop :=
        lintegral_liminf_le' hmeas

/-- A moving-centre, moving-direction sequence of deficit bounds transfers
to its limiting disc whenever the centre values converge. -/
theorem circleSubmean_of_moving_center_vector_circleDeficits
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    {w : E → EReal} (husc : UpperSemicontinuous w)
    (x : E) (centers vectors : ℕ → E) (v : E) {r : ℝ}
    (hcenters : Tendsto centers atTop (𝓝 x))
    (hvectors : Tendsto vectors atTop (𝓝 v)) (C : ℝ)
    {centerValue : ℕ → EReal}
    (hcenter : Tendsto centerValue atTop (𝓝 (w x)))
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hsub : ∀ k, circleDeficit w (centers k) (vectors k) r C ≤
      K * ((C : EReal) - centerValue k).toENNReal) :
    circleDeficit w x v r C ≤ K * ((C : EReal) - w x).toENNReal := by
  let d : EReal → ℝ≥0∞ := fun a => ((C : EReal) - a).toENNReal
  have hdcenter : Tendsto (fun k => d (centerValue k)) atTop (𝓝 (d (w x))) :=
    (continuous_finiteDeficit C).continuousAt.tendsto.comp hcenter
  calc
    circleDeficit w x v r C ≤
        liminf (fun k => circleDeficit w (centers k) (vectors k) r C) atTop :=
      circleDeficit_le_liminf_of_moving_centers_and_vectors_of_upperSemicontinuous husc
        x centers vectors v hcenters hvectors C
    _ ≤ liminf (fun k => K * ((C : EReal) - centerValue k).toENNReal) atTop := by
      simp only [liminf_eq_iSup_iInf_of_nat]
      exact iSup_mono fun _ => iInf_mono fun k => iInf_mono fun _ => hsub k
    _ = K * liminf (fun k => d (centerValue k)) atTop :=
      ENNReal.liminf_const_mul_of_ne_top hK
    _ = K * ((C : EReal) - w x).toENNReal := by
      rw [hdcenter.liminf_eq]

/-- Restricting before taking an upper regularization can only decrease the
result.  This elementary functoriality is the valid direction of comparison
between an intrinsic line fill and the actual ambient extension. -/
theorem uscRegularization_comp_continuous_le
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (raw : Y → EReal) (L : X → Y) (hL : Continuous L) (z : X) :
    uscRegularization (raw ∘ L) z ≤ uscRegularization raw (L z) := by
  apply uscRegularization_le
    ((upperSemicontinuous_uscRegularization raw).comp hL)
  intro y
  exact le_uscRegularization raw (L y)

open scoped Classical in
/-- Applied to an affine complex line, intrinsic regularization of the
ambient raw branch is bounded by the actual ambient extension.  This lemma
uses neither plurisubharmonicity of the line restriction nor the desired
ambient/intrinsic equality. -/
theorem uscRegularization_ambientRaw_comp_affineLine_le_extension
    {i : Fin n} {psi : ComplexModel n → EReal} {x v : ComplexModel n} (z : ℂ) :
    uscRegularization
        ((fun y : ComplexModel n => if y ∈ coordHyperplane i then (⊥ : EReal) else psi y) ∘
          fun ζ : ℂ => x + affineLine v ζ) z ≤
      extension (coordHyperplane i) psi (x + affineLine v z) := by
  rw [extension_eq_uscRegularization]
  simpa [Function.comp_def] using
    (uscRegularization_comp_continuous_le
      (fun y : ComplexModel n => if y ∈ coordHyperplane i then (⊥ : EReal) else psi y)
      (fun ζ : ℂ => x + affineLine v ζ) (by fun_prop) z)

/-- At every finite value of an ambient extension, the defining branch has a
recovering sequence entirely outside the exceptional set.  The exclusion is
not an extra hypothesis: values of the raw function on the exceptional set
are `⊥`, whereas the sequence converges to a finite real value.  These are
the parallel off-hypersurface centres used in the moving-disc argument. -/
theorem exists_sequence_tendsto_branch_of_extension_eq_coe
    {A : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    {a : ComplexModel n} {q : ℝ} (hvalue : extension A psi a = (q : EReal)) :
    ∃ centers : ℕ → ComplexModel n,
      Tendsto centers atTop (𝓝 a) ∧ (∀ k, centers k ∉ A) ∧
        Tendsto (fun k => psi (centers k)) atTop (𝓝 (q : EReal)) := by
  classical
  let raw : ComplexModel n → EReal := fun y => if y ∈ A then ⊥ else psi y
  rw [extension_eq_uscRegularization] at hvalue
  have hrawvalue : uscRegularization raw a = (q : EReal) := by
    simpa [raw] using hvalue
  obtain ⟨ys, hys, hvals⟩ :=
    Hironaka.exists_sequence_tendsto_uscRegularization_eq_coe hrawvalue
  have hpositive : ∀ᶠ k : ℕ in atTop, (⊥ : EReal) < raw (ys k) := by
    apply hvals.eventually
    exact Ioi_mem_nhds (by simp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpositive
  have hnot : ∀ k, ys (k + N) ∉ A := by
    intro k hk
    have hbot : (⊥ : EReal) < raw (ys (k + N)) := hN (k + N) (by omega)
    simp [raw, hk] at hbot
  refine ⟨fun k => ys (k + N),
    (tendsto_add_atTop_iff_nat N).mpr hys, hnot, ?_⟩
  · have hshift : Tendsto (fun k => raw (ys (k + N))) atTop (𝓝 (q : EReal)) :=
      (tendsto_add_atTop_iff_nat N).mpr hvals
    convert hshift using 1
    funext k
    simp [raw, hnot]

/-- Maximum principle on an off-centre punctured closed disc.  The
preconnectedness and the existence of an outer-boundary point outside the
inner hole are kept as explicit geometric inputs.  Analytically this is the
same strong-maximum argument as the concentric annulus lemma, but its outer
and inner boundary circles may have different centres.  It is the maximum
principle needed to upgrade the puncture-centred barrier to arbitrary test
discs. -/
theorem PlurisubharmonicOn.le_const_on_closedBall_diff_ball_of_isPreconnected
    {u : ℂ → EReal} {Omega : Set ℂ} {a c : ℂ} {r R C : ℝ}
    (hu : PlurisubharmonicOn u Omega)
    (hK : closedBall a R \ ball c r ⊆ Omega)
    (hconn : IsPreconnected (closedBall a R \ ball c r))
    (houter : ∀ z ∈ sphere a R, u z ≤ (C : EReal))
    (hinner : ∀ z ∈ sphere c r, u z ≤ (C : EReal))
    (houter_nonempty : ∃ z ∈ sphere a R, z ∉ ball c r) :
    ∀ z ∈ closedBall a R \ ball c r, u z ≤ (C : EReal) := by
  intro q hq
  by_contra hqC
  have hCq : (C : EReal) < u q := lt_of_not_ge hqC
  have hKcompact : IsCompact (closedBall a R \ ball c r) :=
    (isCompact_closedBall a R).inter_right isOpen_ball.isClosed_compl
  have husc : UpperSemicontinuousOn u (closedBall a R \ ball c r) :=
    hu.upperSemicontinuousOn.mono hK
  obtain ⟨y, hyK, hmax⟩ := husc.exists_isMaxOn ⟨q, hq⟩ hKcompact
  have hytop : u y ≠ ⊤ := (hu y (hK hyK)).ne_top
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
  let A : Set ℂ := ball a R \ closedBall c r
  have hAopen : IsOpen A :=
    isOpen_ball.inter isClosed_closedBall.isOpen_compl
  have hA_sub_K : A ⊆ closedBall a R \ ball c r := by
    intro z hz
    refine ⟨ball_subset_closedBall hz.1, fun hzball => hz.2 (ball_subset_closedBall hzball)⟩
  let O : Set ℂ := {z | z ∈ A ∧ u z = (M : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨W, hW, hzW, hdisc⟩ := hu z (hK (hA_sub_K hz.1))
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
  have hcompactMax : IsCompact ((closedBall a R \ ball c r) ∩ u ⁻¹' Ici (M : EReal)) :=
    husc.isCompact_inter_preimage_Ici hKcompact (M : EReal)
  have hOK : O ⊆ (closedBall a R \ ball c r) ∩ u ⁻¹' Ici (M : EReal) := by
    intro z hz
    exact ⟨hA_sub_K hz.1, by simp [hz.2]⟩
  have hclosure : closure O ∩ (closedBall a R \ ball c r) ⊆ O := by
    intro z hz
    have hzMax := closure_minimal hOK hcompactMax.isClosed hz.1
    have hzM : u z = (M : EReal) := by
      apply le_antisymm
      · exact (hmax hz.2).trans_eq hyM
      · exact hzMax.2
    have hzRle : dist z a ≤ R := mem_closedBall.mp hz.2.1
    have hrzle : r ≤ dist z c := by
      by_contra h
      push Not at h
      exact hz.2.2 (mem_ball.mpr h)
    have hzRne : dist z a ≠ R := by
      intro hzR
      have hzS : z ∈ sphere a R := mem_sphere.mpr hzR
      have hzC := houter z hzS
      rw [hzM, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCM
    have hrzne : dist z c ≠ r := by
      intro hzr
      have hzS : z ∈ sphere c r := mem_sphere.mpr hzr
      have hzC := hinner z hzS
      rw [hzM, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCM
    have hzRlt : dist z a < R := lt_of_le_of_ne hzRle hzRne
    have hrlz : r < dist z c := lt_of_le_of_ne hrzle hrzne.symm
    refine ⟨⟨mem_ball.mpr hzRlt, ?_⟩, hzM⟩
    rw [mem_closedBall, not_le]
    exact hrlz
  have hyRle : dist y a ≤ R := mem_closedBall.mp hyK.1
  have hryl : r ≤ dist y c := by
    by_contra h
    push Not at h
    exact hyK.2 (mem_ball.mpr h)
  have hyRne : dist y a ≠ R := by
    intro hyR
    have hyS : y ∈ sphere a R := mem_sphere.mpr hyR
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
  have hnonempty : ((closedBall a R \ ball c r) ∩ O).Nonempty :=
    ⟨y, hA_sub_K hyA, hyA, hyM⟩
  have hall : closedBall a R \ ball c r ⊆ O :=
    hconn.subset_of_closure_inter_subset hO hnonempty hclosure
  obtain ⟨z, hzS, hznot⟩ := houter_nonempty
  have hzK : z ∈ closedBall a R \ ball c r := ⟨sphere_subset_closedBall hzS, hznot⟩
  have hzO := hall hzK
  exact (not_lt_of_ge (by
    have hzC := houter z hzS
    rw [hzO.2, EReal.coe_le_coe_iff] at hzC
    exact hzC)) hCM

/-- If the inner closed disc is strictly inside the outer open disc in the
metric radius sense, every point of the outer boundary avoids the inner open
disc.  This is the outer-boundary input for the off-centre annular maximum
principle. -/
theorem sphere_subset_compl_ball_of_add_dist_lt
    {a c : ℂ} {r R : ℝ} (hinside : r + dist c a < R) :
    sphere a R ⊆ (ball c r)ᶜ := by
  intro z hz hzc
  have hzR : dist z a = R := mem_sphere.mp hz
  have hzC : dist z c < r := mem_ball.mp hzc
  have hcontra : R < R := by
    calc
      R = dist z a := hzR.symm
      _ ≤ dist z c + dist c a := dist_triangle _ _ _
      _ < r + dist c a := by linarith
      _ < R := hinside
  exact lt_irrefl R hcontra

/-- The outer boundary of a nondegenerate disc has a point outside every
strictly contained inner disc.  The preceding inclusion gives the avoidance;
we use a real radial point only to witness that the outer sphere is nonempty. -/
theorem exists_mem_sphere_diff_ball_of_add_dist_lt
    {a c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hinside : r + dist c a < R) :
    ∃ z ∈ sphere a R, z ∉ ball c r := by
  have hR : 0 < R := (add_nonneg hr dist_nonneg).trans_lt hinside
  have hzSphere : a + (R : ℂ) ∈ sphere a R := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
  exact ⟨a + (R : ℂ), hzSphere,
    sphere_subset_compl_ball_of_add_dist_lt hinside hzSphere⟩

/-- A closed complex disc with a strictly interior open disc removed is path
connected.  Each point is joined radially to the inner boundary circle, and
that circle is path connected in real dimension two.  This supplies the
previously explicit geometric input to the off-centre maximum principle. -/
theorem isPathConnected_closedBall_diff_ball_of_add_dist_lt
    {a c : ℂ} {r R : ℝ} (hr : 0 < r) (hinside : r + dist c a < R) :
    IsPathConnected (closedBall a R \ ball c r) := by
  have hinner : closedBall c r ⊆ ball a R := closedBall_subset_ball' hinside
  have hSphere_sub : sphere c r ⊆ closedBall a R \ ball c r := by
    intro z hz
    refine ⟨ball_subset_closedBall (hinner (sphere_subset_closedBall hz)), ?_⟩
    intro hzball
    have hzr : dist z c = r := mem_sphere.mp hz
    have hlt : dist z c < r := mem_ball.mp hzball
    exact (lt_irrefl r) (hzr.symm.trans_lt hlt)
  let q0 : ℂ := c + (r : ℂ)
  have hq0Sphere : q0 ∈ sphere c r := by
    dsimp [q0]
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have hq0 : q0 ∈ closedBall a R \ ball c r := hSphere_sub hq0Sphere
  have hSphereConnected : IsPathConnected (sphere c r) :=
    isPathConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c hr.le
  refine ⟨q0, hq0, ?_⟩
  intro y hy
  let d : ℝ := dist y c
  have hrd : r ≤ d := by
    apply le_of_not_gt
    intro hlt
    exact hy.2 (mem_ball.mpr (by simpa [d] using hlt))
  have hd : 0 < d := hr.trans_le hrd
  have hnorm : ‖y - c‖ = d := by
    exact (dist_eq_norm y c).symm
  let w : ℂ := d⁻¹ • (y - c)
  have hwSphere : w ∈ sphere (0 : ℂ) 1 := by
    dsimp [w]
    rw [mem_sphere, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hd.le), hnorm,
      inv_mul_cancel₀ hd.ne']
  have hwnorm : ‖w‖ = 1 := by
    simpa [dist_zero_right] using (mem_sphere.mp hwSphere)
  let q : ℂ := c + r • w
  have hqSphere : q ∈ sphere c r := by
    dsimp [q]
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le, hwnorm, mul_one]
  have hq : q ∈ closedBall a R \ ball c r := hSphere_sub hqSphere
  have hy_eq : y = c + d • w := by
    dsimp [w]
    have hdinv : (d : ℂ) * ((d⁻¹ : ℝ) : ℂ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hd.ne'
    rw [← mul_assoc, hdinv, one_mul,
      ← add_sub_assoc, add_sub_cancel_left]
  have houter_segment : segment ℝ q y ⊆ closedBall a R :=
    (convex_closedBall a R).segment_subset hq.1 hy.1
  have hinner_segment : segment ℝ q y ⊆ (ball c r)ᶜ := by
    rw [segment_subset_iff]
    intro alpha beta halpha hbeta hab
    let s : ℝ := alpha * r + beta * d
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      positivity
    have hs_lower : r ≤ s := by
      calc
        r = (alpha + beta) * r := by rw [hab, one_mul]
        _ = alpha * r + beta * r := add_mul _ _ _
        _ ≤ alpha * r + beta * d := by gcongr
    have hlinear : alpha • q + beta • y - c = s • w := by
      have hq_mul : q = c + (r : ℂ) * w := by rfl
      have hy_mul : y = c + (d : ℂ) * w := by
        dsimp [w]
        have hdinv : (d : ℂ) * ((d⁻¹ : ℝ) : ℂ) = 1 := by
          exact_mod_cast mul_inv_cancel₀ hd.ne'
        rw [← mul_assoc, hdinv, one_mul,
          ← add_sub_assoc, add_sub_cancel_left]
      have hab' : (alpha : ℂ) + (beta : ℂ) = 1 := by exact_mod_cast hab
      change (alpha : ℂ) * q + (beta : ℂ) * y - c = (s : ℂ) * w
      rw [hq_mul, hy_mul]
      dsimp [s]
      push_cast
      calc
        (alpha : ℂ) * (c + (r : ℂ) * w) + (beta : ℂ) * (c + (d : ℂ) * w) - c =
            (((alpha : ℂ) + (beta : ℂ) - 1) * c) +
              ((alpha : ℂ) * (r : ℂ) + (beta : ℂ) * (d : ℂ)) * w := by ring
        _ = ((alpha : ℂ) * (r : ℂ) + (beta : ℂ) * (d : ℂ)) * w := by rw [hab']; simp
    intro hzball
    have hdist : dist (alpha • q + beta • y) c = s := by
      rw [dist_eq_norm, hlinear, norm_smul, Real.norm_of_nonneg hs_nonneg,
        hwnorm, mul_one]
    have hlt : dist (alpha • q + beta • y) c < r := mem_ball.mp hzball
    exact (not_lt_of_ge hs_lower) (by rwa [hdist] at hlt)
  have hradial : JoinedIn (closedBall a R \ ball c r) q y :=
    JoinedIn.of_segment_subset fun z hz => ⟨houter_segment hz, hinner_segment hz⟩
  exact (hSphereConnected.joinedIn q0 hq0Sphere q hqSphere).mono hSphere_sub |>.trans hradial

/-- The preconnected form used by the off-centre maximum principle. -/
theorem isPreconnected_closedBall_diff_ball_of_add_dist_lt
    {a c : ℂ} {r R : ℝ} (hr : 0 < r) (hinside : r + dist c a < R) :
    IsPreconnected (closedBall a R \ ball c r) :=
  (isPathConnected_closedBall_diff_ball_of_add_dist_lt hr hinside).isConnected.isPreconnected

/-- On a closed punctured disc, inserting `⊥` outside the punctured branch
does not change the regularized centre value.  This is the local bridge from
the established punctured-fill estimate to a domain-cut-off raw function. -/
theorem uscRegularization_restrictedPuncturedFill_eq_at_center
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega] {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hclosed : closedBall c R \ {c} ⊆ Omega) :
    uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) c =
      uscRegularization (fun z => if z = c then (⊥ : EReal) else u z) c := by
  apply Hironaka.uscRegularization_congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds c hR] with z hz
  by_cases hzc : z = c
  · simp [hzc]
  · have hzOmega : z ∈ Omega := hclosed ⟨ball_subset_closedBall hz, hzc⟩
    simp [hzOmega, hzc]

/-- At an off-puncture point of the domain, cutting the raw function off by
`⊥` outside the domain turns relative upper semicontinuity into ordinary upper
semicontinuity. -/
theorem upperSemicontinuousAt_restrictedPuncturedFill_off_center
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c z : ℂ} (hzOmega : z ∈ Omega) (hzc : z ≠ c)
    (hu : UpperSemicontinuousWithinAt u Omega z) :
    UpperSemicontinuousAt (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) z := by
  intro b hzb
  change (if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) < b at hzb
  rw [if_pos ⟨hzOmega, hzc⟩] at hzb
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hu b hzb)
  apply Filter.mem_of_superset hV
  intro y hyV
  by_cases hyOmega : y ∈ Omega
  · by_cases hyc : y = c
    · simpa [hyc] using (bot_le.trans_lt hzb)
    · simpa [hyOmega, hyc] using hsub ⟨hyV, hyOmega⟩
  · simpa [hyOmega] using (bot_le.trans_lt hzb)

/-- The domain-cut-off punctured fill agrees with the original branch at every
off-puncture domain point after upper regularization. -/
theorem uscRegularization_restrictedPuncturedFill_eq_off_center
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c z : ℂ} (hzOmega : z ∈ Omega) (hzc : z ≠ c)
    (hu : UpperSemicontinuousWithinAt u Omega z) :
    uscRegularization (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) z = u z := by
  apply le_antisymm
  · have hle := Hironaka.uscRegularization_le_of_eventually_le
      (f := fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal))
      (g := fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal))
      (upperSemicontinuousAt_restrictedPuncturedFill_off_center hzOmega hzc hu)
      (Filter.Eventually.of_forall fun _ => le_rfl)
    simpa [hzOmega, hzc] using hle
  · calc
      u z = (if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) := by simp [hzOmega, hzc]
      _ ≤ uscRegularization (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) z :=
        le_uscRegularization (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) z

/-- The cut-off punctured fill satisfies the exact deficit submean inequality
at the centre of a closed disc.  Boundary upper regularization is identified
with the PSH branch by the preceding off-centre lemma, then the established
continuous-majorant centre estimate is passed through usc sup-convolution. -/
theorem circleSubmean_restrictedPuncturedFill_of_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c : ℂ} {R B : ℝ} (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) c 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) c).toENNReal := by
  let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
  let F : ℂ → EReal := uscRegularization raw
  let K : Set ℂ := sphere c R
  have hKne : K.Nonempty := by
    refine ⟨c + (R : ℂ), ?_⟩
    simp [K, abs_of_pos hR]
  have hF_eq : ∀ z ∈ K, F z = u z := by
    intro z hz
    apply uscRegularization_restrictedPuncturedFill_eq_off_center
    · exact hclosed ⟨sphere_subset_closedBall hz, by
        intro h
        subst z
        have : R = 0 := by simpa using (mem_sphere.mp hz).symm
        exact hR.ne' this⟩
    · intro h
      subst z
      have : R = 0 := by simpa using (mem_sphere.mp hz).symm
      exact hR.ne' this
    · exact hu.upperSemicontinuousOn _ (hclosed ⟨sphere_subset_closedBall hz, by
        intro h
        subst z
        have : R = 0 := by simpa using (mem_sphere.mp hz).symm
        exact hR.ne' this⟩)
  have hFtop : ∀ z ∈ K, F z ≠ ⊤ := fun z hz => by
    rw [hF_eq z hz]
    exact (hu z (hclosed ⟨sphere_subset_closedBall hz, by
      intro h
      subst z
      have : R = 0 := by simpa using (mem_sphere.mp hz).symm
      exact hR.ne' this⟩)).ne_top
  have hFbound : ∀ z ∈ K, F z ≤ (B : EReal) := fun z hz => by
    rw [hF_eq z hz]
    exact hbound z ⟨sphere_subset_closedBall hz, by
      intro h
      subst z
      have : R = 0 := by simpa using (mem_sphere.mp hz).symm
      exact hR.ne' this⟩
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K F B n
  have hg : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne hFtop hFbound n
  have hgu : ∀ n z, z ∈ K → F z ≤ (g n z : EReal) := fun n z hz =>
    le_coe_uscSupConvolution hKne hFtop hFbound n hz
  have hgB : ∀ n z, g n z ≤ B := fun n z =>
    uscSupConvolution_le hKne hFtop hFbound n z
  have hganti : ∀ z, Antitone fun n => g n z := fun z =>
    uscSupConvolution_antitone hKne hFtop hFbound z
  have hginf : ∀ z, z ∈ K → (⨅ n : ℕ, (g n z : EReal)) = F z :=
    fun z hz => iInf_coe_uscSupConvolution hKne
      ((upperSemicontinuous_uscRegularization raw).upperSemicontinuousOn K) hFtop hFbound hz
  have hcenter : ∀ n, F c ≤ ((Real.circleAverage (g n) c R : ℝ) : EReal) := by
    intro n
    rw [show F c = uscRegularization (fun z => if z = c then (⊥ : EReal) else u z) c by
      exact uscRegularization_restrictedPuncturedFill_eq_at_center hR hclosed]
    exact PshPuncturedLineRemovable.uscRegularization_puncturedFill_le_circleAverage
      hu hR hclosed (hg n).continuousOn
      (fun z hz => by rw [← hF_eq z hz]; exact hgu n z hz) hbound
  apply circleSubmean_of_continuous_antitone_majorants c g hg
  · intro n z _
    exact hgB n z
  · intro t m n hmn
    apply EReal.coe_le_coe_iff.mpr
    exact hganti (c + circleMap 0 R t) hmn
  · intro t
    have hz : c + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere c hR.le t
    exact hginf _ hz
  · exact hcenter

/-- On a circle whose centre is distinct from the logarithmic pole, the pole
is bounded above by the logarithm of the elementary triangle-inequality
radius.  This is the outer-boundary input for the off-centre punctured-disc
barrier. -/
theorem logPoleAt_le_log_of_mem_sphere_off_center
    {a c z : ℂ} {R : ℝ} (hR : 0 < R) (hc : dist c a < R)
    (hz : z ∈ sphere a R) :
    PshPuncturedLineRemovable.logPoleAt c z ≤
      (Real.log ((R + dist c a) ^ 2) : EReal) := by
  have hzc : z ≠ c := by
    intro h
    subst z
    have hdist : dist c a = R := by simpa using mem_sphere.mp hz
    exact hc.ne hdist
  have hrad : 0 < R + dist c a := by positivity
  have hdist : dist z c ≤ R + dist c a := by
    calc
      dist z c ≤ dist z a + dist a c := dist_triangle _ _ _
      _ = R + dist c a := by rw [mem_sphere.mp hz, dist_comm]
  have hnorm : ‖z - c‖ ≤ R + dist c a := by
    simpa only [dist_eq_norm] using hdist
  have hnormpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  have hsq : ‖z - c‖ ^ 2 ≤ (R + dist c a) ^ 2 :=
    (sq_le_sq₀ hnormpos.le hrad.le).mpr hnorm
  rw [PshPuncturedLineRemovable.logPoleAt,
    logNormSq_of_ne_zero (sub_ne_zero.mpr hzc)]
  exact EReal.coe_le_coe_iff.mpr
    (Real.strictMonoOn_log.monotoneOn (sq_pos_of_pos hnormpos)
      (sq_pos_of_pos hrad) hsq)

/-- The logarithmic barrier on a punctured disc with an off-centre outer
circle.  The pole lies strictly inside the disc, while `z` is any non-pole
point of that disc.  The chosen inner radius is simultaneously small enough
to expose `z` and to preserve the annular connectivity margin. -/
theorem PlurisubharmonicOn.const_mul_logPoleAt_le_bound_of_mem_closedBall_ne_off_center
    {u : ℂ → EReal} {Omega : Set ℂ} {a c z : ℂ} {R A B e : ℝ}
    (hu : PlurisubharmonicOn u Omega) (he : 0 < e) (hR : 0 < R)
    (hc : dist c a < R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (houter : ∀ w ∈ sphere a R, u w ≤ (A : EReal))
    (hbound : ∀ w ∈ closedBall a R \ {c}, u w ≤ (B : EReal))
    (hz : z ∈ closedBall a R) (hzc : z ≠ c) :
    u z + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c z ≤
      (A + e * Real.log ((R + dist c a) ^ 2) : ℝ) := by
  let L : ℝ := Real.log ((R + dist c a) ^ 2)
  have hmargin : 0 < R - dist c a := sub_pos.mpr hc
  have hzdist : 0 < dist z c := dist_pos.mpr hzc
  let delta : ℝ := min (R - dist c a) (dist z c)
  have hdelta : 0 < delta := lt_min hmargin hzdist
  let A' : ℝ := A + e * (L - Real.log (R ^ 2))
  obtain ⟨r, hr, hrR, hrdelta, hrbound⟩ :=
    PshPuncturedLineRemovable.exists_radius_const_mul_log_inner_le_outer_lt
      (A := A') (B := B) hR he hdelta
  have hradial : r + dist c a < R := by
    have : r < R - dist c a := lt_of_lt_of_le hrdelta (min_le_left _ _)
    linarith
  have hrz : r < dist z c :=
    lt_of_lt_of_le hrdelta (min_le_right _ _)
  have hinnerbound : B + e * Real.log (r ^ 2) ≤ A + e * L := by
    calc
      B + e * Real.log (r ^ 2) ≤ A' + e * Real.log (R ^ 2) := hrbound
      _ = A + e * L := by dsimp [A']; ring
  have hK : closedBall a R \ ball c r ⊆ Omega := by
    intro w hw
    apply hclosed
    refine ⟨hw.1, ?_⟩
    intro hwc
    subst w
    exact hw.2 (mem_ball_self hr)
  have hpsh : PlurisubharmonicOn
      (fun w => u w + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w) Omega :=
    hu.add ((PshPuncturedLineRemovable.plurisubharmonicOn_const_mul_logPoleAt c he).mono
      (subset_univ _))
  have houter' : ∀ w ∈ sphere a R,
      u w + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w ≤
        (A + e * L : ℝ) := by
    intro w hw
    have hlog : PshPuncturedLineRemovable.logPoleAt c w ≤ (L : EReal) := by
      simpa [L] using logPoleAt_le_log_of_mem_sphere_off_center hR hc hw
    calc
      u w + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w ≤
          (A : EReal) + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w :=
        add_le_add (houter w hw) le_rfl
      _ ≤ (A : EReal) + (e : EReal) * (L : EReal) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog (by exact_mod_cast he.le))
      _ = (A + e * L : ℝ) := by rw [← EReal.coe_mul, ← EReal.coe_add]
  have hinner' : ∀ w ∈ sphere c r,
      u w + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w ≤
        (A + e * L : ℝ) := by
    intro w hw
    have hwclosed : w ∈ closedBall a R := by
      apply mem_closedBall.mpr
      calc
        dist w a ≤ dist w c + dist c a := dist_triangle _ _ _
        _ = r + dist c a := by rw [mem_sphere.mp hw]
        _ ≤ R := hradial.le
    have hwc : w ≠ c := by
      intro h
      subst w
      have : r = 0 := by simpa using (mem_sphere.mp hw).symm
      exact hr.ne' this
    calc
      u w + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w ≤
          (B : EReal) + (e : EReal) * PshPuncturedLineRemovable.logPoleAt c w :=
        add_le_add (hbound w ⟨hwclosed, hwc⟩) le_rfl
      _ = (B + e * Real.log (r ^ 2) : ℝ) := by
        rw [PshPuncturedLineRemovable.logPoleAt_eq_on_sphere hr hw,
          ← EReal.coe_mul, ← EReal.coe_add]
      _ ≤ (A + e * L : ℝ) := by exact_mod_cast hinnerbound
  have hmax := PlurisubharmonicOn.le_const_on_closedBall_diff_ball_of_isPreconnected
    hpsh hK (isPreconnected_closedBall_diff_ball_of_add_dist_lt hr hradial) houter' hinner'
    (exists_mem_sphere_diff_ball_of_add_dist_lt hr.le hradial)
  apply hmax z
  refine ⟨hz, ?_⟩
  rw [mem_ball]
  exact not_lt_of_ge hrz.le

/-- Sending the positive logarithmic coefficient to zero yields the off-centre
punctured-disc maximum principle. -/
theorem PlurisubharmonicOn.le_const_of_punctured_closedBall_off_center
    {u : ℂ → EReal} {Omega : Set ℂ} {a c z : ℂ} {R A B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R) (hc : dist c a < R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (houter : ∀ w ∈ sphere a R, u w ≤ (A : EReal))
    (hbound : ∀ w ∈ closedBall a R \ {c}, u w ≤ (B : EReal))
    (hz : z ∈ closedBall a R) (hzc : z ≠ c) : u z ≤ (A : EReal) := by
  apply PshPuncturedLineRemovable.EReal.le_coe_of_forall_pos_add_mul_le
  intro e he
  have hbar := PlurisubharmonicOn.const_mul_logPoleAt_le_bound_of_mem_closedBall_ne_off_center
    hu he hR hc hclosed houter hbound hz hzc
  have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
  rw [PshPuncturedLineRemovable.logPoleAt,
    logNormSq_of_ne_zero hne] at hbar
  exact hbar

/-- Fourier approximation on the off-centre outer circle, followed by the
off-centre barrier, constructs a harmonic majorant of the punctured branch
while retaining the quantitative boundary error. -/
theorem PlurisubharmonicOn.exists_global_harmonic_majorant_of_off_center_punctured_closedBall_with_error
    {u : ℂ → EReal} {Omega : Set ℂ} {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R) (hc : dist c a < R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere a R))
    (hgu : ∀ z ∈ sphere a R, u z ≤ (g z : EReal))
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h univ ∧ Continuous h ∧
      (∀ z ∈ closedBall a R \ {c}, u z ≤ (h z : EReal)) ∧
      ∀ z ∈ sphere a R, h z < g z + 2 * ε := by
  obtain ⟨h, hh, hcont, hbounds⟩ :=
    PshPuncturedLineRemovable.exists_global_harmonic_outer_majorantOn_sphere
      a hR hg hgu hε
  obtain ⟨m, hm⟩ :=
    PshPuncturedLineRemovable.exists_lower_bound_on_closedBall_of_continuous hcont a R
  have hhOmega : InnerProductSpace.HarmonicOnNhd h Omega := hh.mono (subset_univ _)
  have hsub : PlurisubharmonicOn (fun z => u z - (h z : EReal)) Omega :=
    hu.sub_harmonic hhOmega
  have houter_sub : ∀ z ∈ sphere a R, u z - (h z : EReal) ≤ (0 : EReal) := by
    intro z hz
    exact EReal.sub_nonpos.mpr (hbounds z hz).1
  have hbound_sub : ∀ z ∈ closedBall a R \ {c},
      u z - (h z : EReal) ≤ ((B - m : ℝ) : EReal) := by
    intro z hz
    calc
      u z - (h z : EReal) ≤ (B : EReal) - (h z : EReal) :=
        EReal.sub_le_sub (hbound z hz) le_rfl
      _ = ((B - h z : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ ((B - m : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (sub_le_sub le_rfl (hm z hz.1))
  refine ⟨h, hh, hcont, ?_, fun z hz => (hbounds z hz).2⟩
  intro z hz
  have hmax := PlurisubharmonicOn.le_const_of_punctured_closedBall_off_center
    hsub hR hc hclosed houter_sub hbound_sub hz.1 hz.2
  have hmax' : u z - (h z : EReal) ≤ (0 : EReal) := by simpa using hmax
  exact EReal.sub_nonpos.mp hmax'

/-- At an off-puncture centre of a disc containing the puncture, the
domain-cut-off regularization satisfies the circle-average bound for every
continuous outer majorant. -/
theorem uscRegularization_restrictedPuncturedFill_le_circleAverage_off_center
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R) (hc : dist c a < R) (hac : a ≠ c)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    {g : ℂ → ℝ} (hg : ContinuousOn g (sphere a R))
    (hgu : ∀ z ∈ sphere a R, u z ≤ (g z : EReal))
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal)) :
    uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a ≤
      ((Real.circleAverage g a R : ℝ) : EReal) := by
  apply PshPuncturedLineRemovable.EReal.le_coe_of_forall_pos_add_mul_le (L := 0) (K := 2)
  intro ε hε
  obtain ⟨h, hh, _hcont, hmajor, herr⟩ :=
    PlurisubharmonicOn.exists_global_harmonic_majorant_of_off_center_punctured_closedBall_with_error
      hu hR hc hclosed hg hgu hbound hε
  have hF : uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a =
      u a :=
    uscRegularization_restrictedPuncturedFill_eq_off_center
      (hclosed ⟨mem_closedBall_self hR.le, hac⟩) hac
      (hu.upperSemicontinuousOn _ (hclosed ⟨mem_closedBall_self hR.le, hac⟩))
  have hcenter : h a ≤ Real.circleAverage g a R + 2 * ε :=
    PshPuncturedLineRemovable.harmonic_center_le_circleAverage_add_of_le_on_sphere
      hh hR hg (fun z hz => (herr z hz).le)
  have hcenterE : (h a : EReal) ≤ (Real.circleAverage g a R + 2 * ε : ℝ) :=
    EReal.coe_le_coe_iff.mpr hcenter
  rw [hF]
  have hmajor_a : u a ≤ (h a : EReal) :=
    hmajor a ⟨mem_closedBall_self hR.le, hac⟩
  simpa [EReal.coe_mul, EReal.coe_add, mul_comm] using hmajor_a.trans hcenterE

/-- The preceding off-centre continuous-majorant estimate upgrades, through
usc sup-convolution, to the exact deficit submean inequality for a disc whose
interior contains the puncture but whose centre is distinct from it. -/
theorem circleSubmean_restrictedPuncturedFill_of_off_center_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R) (hc : dist c a < R) (hac : a ≠ c)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal)) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) a 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a).toENNReal := by
  let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
  let F : ℂ → EReal := uscRegularization raw
  let K : Set ℂ := sphere a R
  have hKne : K.Nonempty := by
    refine ⟨a + (R : ℂ), ?_⟩
    simp [K, abs_of_pos hR]
  have hF_eq : ∀ z ∈ K, F z = u z := by
    intro z hz
    apply uscRegularization_restrictedPuncturedFill_eq_off_center
    · exact hclosed ⟨sphere_subset_closedBall hz, by
        intro h
        subst z
        have hdist : dist c a = R := by simpa using mem_sphere.mp hz
        exact hc.ne hdist⟩
    · intro h
      subst z
      have hdist : dist c a = R := by simpa using mem_sphere.mp hz
      exact hc.ne hdist
    · exact hu.upperSemicontinuousOn _ (hclosed ⟨sphere_subset_closedBall hz, by
        intro h
        subst z
        have hdist : dist c a = R := by simpa using mem_sphere.mp hz
        exact hc.ne hdist⟩)
  have hFtop : ∀ z ∈ K, F z ≠ ⊤ := fun z hz => by
    rw [hF_eq z hz]
    exact (hu z (hclosed ⟨sphere_subset_closedBall hz, by
      intro h
      subst z
      have hdist : dist c a = R := by simpa using mem_sphere.mp hz
      exact hc.ne hdist⟩)).ne_top
  have hFbound : ∀ z ∈ K, F z ≤ (B : EReal) := fun z hz => by
    rw [hF_eq z hz]
    exact hbound z ⟨sphere_subset_closedBall hz, by
      intro h
      subst z
      have hdist : dist c a = R := by simpa using mem_sphere.mp hz
      exact hc.ne hdist⟩
  let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K F B n
  have hg : ∀ n, Continuous (g n) := fun n =>
    continuous_uscSupConvolution hKne hFtop hFbound n
  have hgu : ∀ n z, z ∈ K → F z ≤ (g n z : EReal) := fun n z hz =>
    le_coe_uscSupConvolution hKne hFtop hFbound n hz
  have hgB : ∀ n z, g n z ≤ B := fun n z =>
    uscSupConvolution_le hKne hFtop hFbound n z
  have hganti : ∀ z, Antitone fun n => g n z := fun z =>
    uscSupConvolution_antitone hKne hFtop hFbound z
  have hginf : ∀ z, z ∈ K → (⨅ n : ℕ, (g n z : EReal)) = F z :=
    fun z hz => iInf_coe_uscSupConvolution hKne
      ((upperSemicontinuous_uscRegularization raw).upperSemicontinuousOn K) hFtop hFbound hz
  have hcenter : ∀ n, F a ≤ ((Real.circleAverage (g n) a R : ℝ) : EReal) := by
    intro n
    exact uscRegularization_restrictedPuncturedFill_le_circleAverage_off_center
      hu hR hc hac hclosed (hg n).continuousOn
      (fun z hz => by rw [← hF_eq z hz]; exact hgu n z hz) hbound
  apply circleSubmean_of_continuous_antitone_majorants a g hg
  · intro n z _
    exact hgB n z
  · intro t m n hmn
    apply EReal.coe_le_coe_iff.mpr
    exact hganti (a + circleMap 0 R t) hmn
  · intro t
    have hz : a + circleMap 0 R t ∈ K := by
      simpa [K, circleMap] using circleMap_mem_sphere a hR.le t
    exact hginf _ hz
  · exact hcenter

/-- If the removed point lies outside a closed test disc, the cut-off fill is
identical to the original PSH branch on that disc.  The ordinary local
PSH-to-disc bridge therefore supplies the exact deficit inequality. -/
theorem circleSubmean_restrictedPuncturedFill_of_closedBall_away_from_puncture
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall a R ⊆ Omega) (hc : c ∉ closedBall a R)
    (hbound : ∀ z ∈ closedBall a R, u z ≤ (B : EReal)) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) a 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a).toENNReal := by
  let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
  let F : ℂ → EReal := uscRegularization raw
  have hF_eq : ∀ z ∈ closedBall a R, F z = u z := by
    intro z hz
    apply uscRegularization_restrictedPuncturedFill_eq_off_center (hclosed hz)
    · intro h
      subst z
      exact hc hz
    · exact hu.upperSemicontinuousOn _ (hclosed hz)
  have hsub := Hironaka.PlurisubharmonicOn.circleSubmean_of_closedBall_subset_of_harmonicApproximation
    Hironaka.hasGlobalHarmonicCircleApproximation hu hR hclosed hbound
  have hcircle : circleDeficit F a 1 R B = circleDeficit u a 1 R B := by
    unfold circleDeficit
    apply lintegral_congr
    intro t
    have hz : a + circleMap 0 R t • (1 : ℂ) ∈ closedBall a R := by
      simpa only [smul_eq_mul, mul_one] using sphere_subset_closedBall (by
        simpa [circleMap] using circleMap_mem_sphere a hR.le t)
    rw [hF_eq _ hz]
  rw [hcircle]
  change circleDeficit u a 1 R B ≤
    ENNReal.ofReal (2 * Real.pi) * ((B : EReal) - F a).toENNReal
  rw [hF_eq a (mem_closedBall_self hR.le)]
  exact hsub

/-- All punctured closed discs whose boundary avoids the puncture satisfy the
cut-off-fill deficit submean inequality.  The proof splits only on whether
the puncture is strictly inside (the centred and off-centred barrier cases)
or strictly outside (ordinary PSH locality) the disc. -/
theorem circleSubmean_restrictedPuncturedFill_of_closedBall_of_puncture_not_mem_sphere
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal))
    (hcsphere : c ∉ sphere a R) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) a 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a).toENNReal := by
  have hdistne : dist c a ≠ R := by
    intro h
    apply hcsphere
    exact mem_sphere.mpr h
  rcases lt_or_gt_of_ne hdistne with hcinside | hcoutside
  · by_cases hac : a = c
    · subst a
      simpa using circleSubmean_restrictedPuncturedFill_of_closedBall
        (c := c) hu hR hclosed hbound
    · exact circleSubmean_restrictedPuncturedFill_of_off_center_closedBall
        hu hR hcinside hac hclosed hbound
  · have hcclosed : c ∉ closedBall a R := by
      intro hcball
      exact (not_lt_of_ge (mem_closedBall.mp hcball)) hcoutside
    have hfull : closedBall a R ⊆ Omega := by
      intro z hz
      apply hclosed
      refine ⟨hz, ?_⟩
      intro hzc
      subst z
      exact hcclosed hz
    have hfullbound : ∀ z ∈ closedBall a R, u z ≤ (B : EReal) := by
      intro z hz
      exact hbound z ⟨hz, fun hzc => hcclosed (hzc ▸ hz)⟩
    exact circleSubmean_restrictedPuncturedFill_of_closedBall_away_from_puncture
      hu hR hfull hcclosed hfullbound

/-- Rescaling a complex-disc direction agrees exactly with rescaling its
radius. -/
theorem circleDeficit_rescale_direction_eq_rescale_radius
    {w : ℂ → EReal} (p : ℂ) (R s C : ℝ) :
    circleDeficit w p (s : ℂ) R C = circleDeficit w p 1 (R * s) C := by
  unfold circleDeficit
  apply lintegral_congr
  intro t
  congr 3
  simp only [circleMap, smul_eq_mul, mul_one]
  push_cast
  ring

/-- A puncture on the boundary is reached from strictly smaller concentric
discs.  Their radii tend to the original radius while the puncture remains
outside every approximating closed disc; moving-direction Fatou transfers the
already proved exterior submean bounds to the tangent disc. -/
theorem circleSubmean_restrictedPuncturedFill_of_puncture_mem_sphere
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R) (hc : c ∈ sphere a R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal)) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) a 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a).toENNReal := by
  let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
  let F : ℂ → EReal := uscRegularization raw
  let scales : ℕ → ℝ := fun n => 1 - 1 / (((n + 1 : ℕ) : ℝ) + 1)
  have hεtend : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
      (tendsto_add_atTop_iff_nat 1).mpr
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscales : Tendsto scales atTop (𝓝 1) := by
    dsimp [scales]
    simpa using tendsto_const_nhds.sub hεtend
  have hscale_pos : ∀ n, 0 < scales n := by
    intro n
    dsimp [scales]
    have hden : 0 < (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    have hinv : 1 / (((n + 1 : ℕ) : ℝ) + 1) < 1 := by
      rw [div_lt_one₀ hden]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      norm_num
      linarith
    linarith
  have hscale_le : ∀ n, scales n ≤ 1 := by
    intro n
    dsimp [scales]
    exact sub_le_self _ (by positivity)
  have hscale_lt : ∀ n, scales n < 1 := by
    intro n
    dsimp [scales]
    have hden : 0 < (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    have hinv : 0 < 1 / (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    linarith
  have hcontain : ∀ n, closedBall a (R * scales n) ⊆ closedBall a R := by
    intro n
    exact Metric.closedBall_subset_closedBall
      (by simpa using mul_le_mul_of_nonneg_left (hscale_le n) hR.le)
  have haway : ∀ n, c ∉ closedBall a (R * scales n) := by
    intro n hcball
    have hdist : dist c a = R := mem_sphere.mp hc
    have hlt : R * scales n < R :=
      (by simpa using mul_lt_mul_of_pos_left (hscale_lt n) hR)
    have hle : dist c a ≤ R * scales n := mem_closedBall.mp hcball
    rw [hdist] at hle
    exact (not_lt_of_ge hle) hlt
  have hsub : ∀ n, circleDeficit F a (scales n : ℂ) R B ≤
      ENNReal.ofReal (2 * Real.pi) * ((B : EReal) - F a).toENNReal := by
    intro n
    rw [circleDeficit_rescale_direction_eq_rescale_radius]
    apply circleSubmean_restrictedPuncturedFill_of_closedBall_away_from_puncture
      hu (mul_pos hR (hscale_pos n))
    · intro z hz
      apply hclosed
      refine ⟨hcontain n hz, ?_⟩
      intro hzc
      subst z
      exact haway n hz
    · exact haway n
    · intro z hz
      apply hbound z
      refine ⟨hcontain n hz, ?_⟩
      intro hzc
      subst z
      exact haway n hz
  have hvec : Tendsto (fun n => (scales n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hscales
  exact circleSubmean_of_moving_center_vector_circleDeficits
    (upperSemicontinuous_uscRegularization raw) a (fun _ => a)
    (fun n => (scales n : ℂ)) 1 tendsto_const_nhds hvec B tendsto_const_nhds
    ENNReal.ofReal_ne_top (by simpa [F, raw] using hsub)

/-- Exact circle-deficit submean inequality for the cut-off punctured fill on
every closed disc.  The puncture is either off the boundary (handled by the
interior/exterior split) or on it (handled by the fixed-centre shrinking
argument). -/
theorem circleSubmean_restrictedPuncturedFill_of_closedBall_all_positions
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {a c : ℂ} {R B : ℝ}
    (hu : PlurisubharmonicOn u Omega) (hR : 0 < R)
    (hclosed : closedBall a R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall a R \ {c}, u z ≤ (B : EReal)) :
    circleDeficit (uscRegularization
      (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal))) a 1 R B ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((B : EReal) - uscRegularization
          (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) a).toENNReal := by
  by_cases hc : c ∈ sphere a R
  · exact circleSubmean_restrictedPuncturedFill_of_puncture_mem_sphere
      hu hR hc hclosed hbound
  · exact circleSubmean_restrictedPuncturedFill_of_closedBall_of_puncture_not_mem_sphere
      hu hR hclosed hbound hc

/-- The affine coordinate of a nonzero complex direction is a homeomorphism
of the complex line.  Keeping the inverse explicit lets the punctured cut-off
commute exactly with upper regularization, rather than appealing to an
unproved rotation-invariance principle for circle integrals. -/
def affineComplexHomeomorph (x v : ℂ) (hv : v ≠ 0) : ℂ ≃ₜ ℂ :=
  { toFun := fun z => x + z * v
    invFun := fun y => (y - x) / v
    left_inv := by
      intro z
      field_simp
      ring
    right_inv := by
      intro y
      field_simp
      ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

open scoped Classical in
/-- A domain-cut-off punctured branch commutes with every homeomorphic
coordinate change, provided the puncture is transported by the inverse map. -/
theorem restrictedPuncturedFill_comp_homeomorph
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    (c : ℂ) (e : ℂ ≃ₜ ℂ) :
    (fun z => if z ∈ e ⁻¹' Omega ∧ z ≠ e.symm c then u (e z) else (⊥ : EReal)) =
      (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) ∘ e := by
  funext z
  by_cases hzc : z = e.symm c
  · subst z
    simp
  · have himage : e z ≠ c := by
      intro h
      apply hzc
      calc
        z = e.symm (e z) := (e.symm_apply_apply z).symm
        _ = e.symm c := congrArg _ h
    simp [hzc, himage]

open scoped Classical in
/-- Upper regularization of a punctured cut-off is covariant under a
homeomorphic coordinate change. -/
theorem uscRegularization_restrictedPuncturedFill_comp_homeomorph
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    (c z : ℂ) (e : ℂ ≃ₜ ℂ) :
    uscRegularization
        (fun w => if w ∈ e ⁻¹' Omega ∧ w ≠ e.symm c then u (e w) else (⊥ : EReal)) z =
      uscRegularization (fun y => if y ∈ Omega ∧ y ≠ c then u y else (⊥ : EReal)) (e z) := by
  rw [restrictedPuncturedFill_comp_homeomorph c e]
  exact Hironaka.uscRegularization_comp_homeomorph_apply _ e z

/-- A finite bound on one punctured closed ball controls the value inserted by
the upper regularization at its missing centre. -/
theorem uscRegularization_restrictedPuncturedFill_le_of_punctured_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) c ≤
      (B : EReal) := by
  apply Hironaka.uscRegularization_le_of_eventually_le
    (upperSemicontinuousAt_const (x := c) (z := (B : EReal)))
  filter_upwards [Metric.ball_mem_nhds c hR] with z hz
  by_cases hzc : z = c
  · simp [hzc]
  · have hzclosed : z ∈ closedBall c R := ball_subset_closedBall hz
    have hzOmega : z ∈ Omega := hclosed ⟨hzclosed, hzc⟩
    simpa [hzOmega, hzc] using hbound z ⟨hzclosed, hzc⟩

open scoped Classical in
/-- The closed-ball estimates proved above give the complete affine-disc
submean field for the intrinsic, domain-cut-off punctured fill.  A nonzero
test direction is pulled back through its affine complex homeomorphism; the
unit-direction estimate then has exactly the same angular deficit integral.
The zero direction is a constant circle. -/
theorem hasDiscSubmeanOn_restrictedPuncturedFill
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c : ℂ} (hu : PlurisubharmonicOn u Omega) :
    HasDiscSubmeanOn
      (uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)))
      (insert c Omega) := by
  intro x v r hr hD C hC
  by_cases hv : v = 0
  · subst v
    simp [circleDeficit, mul_comm]
  · let L : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight v
    let e : ℂ ≃ₜ ℂ := affineComplexHomeomorph x v hv
    let Omega' : Set ℂ := e ⁻¹' Omega
    let c' : ℂ := e.symm c
    let u' : ℂ → EReal := fun z => u (e z)
    let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
    let raw' : ℂ → EReal := fun z => if z ∈ Omega' ∧ z ≠ c' then u' z else (⊥ : EReal)
    let F : ℂ → EReal := uscRegularization raw
    have hue : PlurisubharmonicOn u' Omega' := by
      have h := hu.comp_affine L x
      simpa [u', Omega', e, affineComplexHomeomorph, L, smul_eq_mul] using h
    have he_image_disc : ∀ z ∈ closedBall 0 r, e z ∈ affineClosedDisc x v r := by
      intro z hz
      refine ⟨z, hz, ?_⟩
      simp [e, affineComplexHomeomorph, smul_eq_mul]
    have he_ne : ∀ z, z ≠ c' → e z ≠ c := by
      intro z hz h
      apply hz
      calc
        z = e.symm (e z) := (e.symm_apply_apply z).symm
        _ = e.symm c := congrArg _ h
    have hclosed : closedBall 0 r \ {c'} ⊆ Omega' := by
      intro z hz
      have hU := hD (he_image_disc z hz.1)
      change e z ∈ Omega
      exact hU.resolve_left (he_ne z hz.2)
    have hbound : ∀ z ∈ closedBall 0 r \ {c'}, u' z ≤ (C : EReal) := by
      intro z hz
      have hzOmega : e z ∈ Omega := hclosed hz
      have hzneq : e z ≠ c := he_ne z hz.2
      have hF : F (e z) = u (e z) := by
        exact uscRegularization_restrictedPuncturedFill_eq_off_center hzOmega hzneq
          (hu.upperSemicontinuousOn _ hzOmega)
      change u (e z) ≤ (C : EReal)
      rw [← hF]
      exact hC (e z) (he_image_disc z hz.1)
    have hsub := circleSubmean_restrictedPuncturedFill_of_closedBall_all_positions
      hue hr hclosed hbound
    have hreg : ∀ z : ℂ, uscRegularization raw' z = F (e z) := by
      intro z
      exact uscRegularization_restrictedPuncturedFill_comp_homeomorph c z e
    have hFpull : (fun z => F (e z)) = fun z => F (x + L z) := by
      funext z
      simp [e, affineComplexHomeomorph, L, smul_eq_mul]
    change circleDeficit (uscRegularization raw') 0 1 r C ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - uscRegularization raw' 0).toENNReal at hsub
    have hregfun : uscRegularization raw' = fun z => F (e z) := funext hreg
    rw [hregfun, hFpull] at hsub
    rw [circleDeficit_comp_affine F L x] at hsub
    change circleDeficit F x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - F x).toENNReal
    simpa [L] using hsub

/-- One finite upper bound on a punctured ball supplies the missing
non-`⊤` field at the inserted point.  Together with the preceding affine-disc
theorem, the intrinsic cut-off fill is disc-PSH on the punctured domain with
its centre inserted. -/
theorem discPshOn_restrictedPuncturedFill_of_punctured_closedBall
    {u : ℂ → EReal} {Omega : Set ℂ} [DecidablePred fun z : ℂ => z ∈ Omega]
    {c : ℂ} (hu : PlurisubharmonicOn u Omega) {R B : ℝ} (hR : 0 < R)
    (hclosed : closedBall c R \ {c} ⊆ Omega)
    (hbound : ∀ z ∈ closedBall c R \ {c}, u z ≤ (B : EReal)) :
    DiscPshOn
      (uscRegularization (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)))
      (insert c Omega) := by
  let raw : ℂ → EReal := fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)
  let F : ℂ → EReal := uscRegularization raw
  have hcenterle : F c ≤ (B : EReal) := by
    exact uscRegularization_restrictedPuncturedFill_le_of_punctured_closedBall
      hR hclosed hbound
  have hcenterne : F c ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top B) hcenterle
  refine ⟨?_, (upperSemicontinuous_uscRegularization raw).upperSemicontinuousOn _, ?_⟩
  · intro z hz
    rcases hz with hzc | hzOmega
    · subst z
      exact hcenterne
    · by_cases hzc : z = c
      · subst z
        exact hcenterne
      · rw [uscRegularization_restrictedPuncturedFill_eq_off_center hzOmega hzc
          (hu.upperSemicontinuousOn _ hzOmega)]
        exact (hu z hzOmega).ne_top
  · exact hasDiscSubmeanOn_restrictedPuncturedFill hu

open PshPuncturedLineRemovable in
/-- If a transverse line meets the ambient domain at its unique hyperplane
point, the intrinsic regularization of its cut-off branch is disc-PSH on the
whole line domain.  The local off-hyperplane bound is first intersected with
the open ambient domain and then pulled back to a parameter ball.  This is an
intrinsic statement only: it does not identify this fill with the ambient
extension. -/
theorem discPshOn_intrinsic_transverseLineFill
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i)) (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (x v : ComplexModel n) (hv : v i ≠ 0)
    (hpole : -(x i) / v i ∈ transverseLineDomain B x v) :
    DiscPshOn (uscRegularization (transverseLineRaw i B psi x v))
      (transverseLineDomain B x v) := by
  classical
  let c : ℂ := -(x i) / v i
  let D : Set ℂ := transverseLineDomain B x v
  let Omega : Set ℂ := D \ {c}
  let u : ℂ → EReal := fun z => psi (x + affineLine v z)
  have hu : PlurisubharmonicOn u Omega := by
    simpa [u, Omega, D, c, transverseLineDomain] using
      plurisubharmonicOn_comp_transverseLine_off_coordHyperplane hpsi x v hv
  obtain ⟨U, hU, C, hC⟩ := hbound (x + affineLine v c) hpole
  have hUB : U ∩ B ∈ 𝓝 (x + affineLine v c) :=
    inter_mem hU (hB.mem_nhds hpole)
  have hpre : (fun z : ℂ => x + affineLine v z) ⁻¹' (U ∩ B) ∈ 𝓝 c :=
    (continuous_const.add (affineLine v).continuous).continuousAt.preimage_mem_nhds hUB
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let R : ℝ := eps / 2
  have hR : 0 < R := half_pos heps
  have hballR : closedBall c R ⊆ ball c eps := by
    exact closedBall_subset_ball (by dsimp [R]; linarith)
  have hclosed : closedBall c R \ {c} ⊆ Omega := by
    intro z hz
    refine ⟨?_, hz.2⟩
    exact (hball (hballR hz.1)).2
  have hbound' : ∀ z ∈ closedBall c R \ {c}, u z ≤ (C : EReal) := by
    intro z hz
    apply hC (x + affineLine v z) (hball (hballR hz.1)).1
    intro hzH
    have hz' : z ∈ (fun w : ℂ => x + affineLine v w) ⁻¹' coordHyperplane i := hzH
    rw [preimage_coordHyperplane_eq_singleton hv] at hz'
    exact hz.2 (by simpa [c] using hz')
  have hdisc := discPshOn_restrictedPuncturedFill_of_punctured_closedBall
    hu hR hclosed hbound'
  have hcpole : c ∈ D := by simpa [c, D] using hpole
  have hinsert : insert c Omega = D := by
    dsimp [Omega]
    rw [insert_sdiff_singleton]
    simp [hcpole]
  rw [hinsert] at hdisc
  change DiscPshOn (uscRegularization (fun z =>
    if z ∈ D ∧ z ≠ c then u z else (⊥ : EReal))) D
  simpa [Omega] using hdisc

open PshPuncturedLineRemovable in
/-- On every transverse affine disc, the ambient extension has no larger
circle deficit than the intrinsic upper regularization of the corresponding
line raw branch.  This is the one-sided comparison needed for recovery by
parallel off-hyperplane discs; no equality of the two regularizations is
claimed. -/
theorem circleDeficit_extension_le_intrinsic_transverseFill
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (p w : ComplexModel n) (hw : w i ≠ 0) (r C : ℝ) :
    circleDeficit (extension (coordHyperplane i) psi) p w r C ≤
      circleDeficit (uscRegularization (transverseLineRaw i B psi p w)) 0 1 r C := by
  have hle := uscRegularization_transverseLineRaw_le_extension hpsi hBA p w hw
  unfold circleDeficit
  apply lintegral_mono
  intro t
  apply EReal.toENNReal_le_toENNReal
  apply EReal.sub_le_sub le_rfl
  simpa [affineLine_apply] using hle (circleMap 0 r t)

open PshPuncturedLineRemovable in
/-- The intrinsic fill on one transverse affine disc satisfies its exact
circle-deficit submean estimate as soon as that disc lies in the ambient
domain and the original branch has a finite bound there.  No assertion about
the hyperplane intersection outside this particular disc is needed. -/
theorem circleSubmean_intrinsic_transverseFill_of_closedDisc
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (p w : ComplexModel n) (hw : w i ≠ 0) {r C : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc p w r ⊆ B)
    (hbound : ∀ y ∈ affineClosedDisc p w r, y ∉ coordHyperplane i →
      psi y ≤ (C : EReal)) :
    circleDeficit (uscRegularization (transverseLineRaw i B psi p w)) 0 1 r C ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - uscRegularization (transverseLineRaw i B psi p w) 0).toENNReal := by
  classical
  let c : ℂ := -(p i) / w i
  let D : Set ℂ := transverseLineDomain B p w
  let Omega : Set ℂ := D \ {c}
  let u : ℂ → EReal := fun z => psi (p + affineLine w z)
  have hu : PlurisubharmonicOn u Omega := by
    simpa [u, Omega, D, c, transverseLineDomain] using
      plurisubharmonicOn_comp_transverseLine_off_coordHyperplane hpsi p w hw
  have hclosed : closedBall 0 r \ {c} ⊆ Omega := by
    intro z hz
    refine ⟨?_, hz.2⟩
    apply hD
    refine ⟨z, hz.1, ?_⟩
    simp
  have hbound' : ∀ z ∈ closedBall 0 r \ {c}, u z ≤ (C : EReal) := by
    intro z hz
    apply hbound (p + affineLine w z) (by
      refine ⟨z, hz.1, ?_⟩
      simp)
    intro hzH
    have hz' : z ∈ (fun t : ℂ => p + affineLine w t) ⁻¹' coordHyperplane i := hzH
    rw [preimage_coordHyperplane_eq_singleton hw] at hz'
    exact hz.2 (by simpa [c] using hz')
  have hsub := circleSubmean_restrictedPuncturedFill_of_closedBall_all_positions
    hu hr hclosed hbound'
  have hraw : (fun z => if z ∈ Omega ∧ z ≠ c then u z else (⊥ : EReal)) =
      transverseLineRaw i B psi p w := by
    funext z
    simp [Omega, transverseLineRaw, u, D, c]
  rw [hraw] at hsub
  exact hsub

open PshPuncturedLineRemovable in
/-- A convergent sequence of off-hyperplane centres transfers the intrinsic
disc estimates of their parallel transverse fills to the actual ambient
extension.  The hypotheses deliberately keep the geometric eventual-disc
containment and the finite bound explicit; the final recovery theorem obtains
them from compactness and upper semicontinuity. -/
theorem circleSubmean_extension_of_transverse_recovery
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    {q w : ComplexModel n} (hw : w i ≠ 0) {r C : ℝ} (hr : 0 < r)
    (centers : ℕ → ComplexModel n)
    (hcenters : Tendsto centers atTop (𝓝 q))
    (hoff : ∀ k, centers k ∉ coordHyperplane i)
    (hdisc : ∀ k, affineClosedDisc (centers k) w r ⊆ B)
    (hbound : ∀ k, ∀ y ∈ affineClosedDisc (centers k) w r,
      y ∉ coordHyperplane i → psi y ≤ (C : EReal))
    (hvalue : Tendsto (fun k => psi (centers k)) atTop
      (𝓝 (extension (coordHyperplane i) psi q))) :
    circleDeficit (extension (coordHyperplane i) psi) q w r C ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - extension (coordHyperplane i) psi q).toENNReal := by
  apply circleSubmean_of_moving_center_circleDeficits
    (upperSemicontinuous_extension (coordHyperplane i) psi) q centers w hcenters C hvalue
    ENNReal.ofReal_ne_top
  intro k
  have hpB : 0 ∈ transverseLineDomain B (centers k) w := by
    change centers k + affineLine w 0 ∈ B
    simpa using hdisc k (center_mem_affineClosedDisc (centers k) w hr.le)
  have hpole0 : (0 : ℂ) ≠ -(centers k i) / w i := by
    intro hzero
    apply hoff k
    have hmem : (0 : ℂ) ∈
        (fun z : ℂ => centers k + affineLine w z) ⁻¹' coordHyperplane i := by
      rw [preimage_coordHyperplane_eq_singleton hw]
      simpa using hzero
    simpa [coordHyperplane, affineLine_apply] using hmem
  have hfill : uscRegularization (transverseLineRaw i B psi (centers k) w) 0 =
      psi (centers k) := by
    rw [uscRegularization_transverseLineRaw_eq_off_pole hpsi hBA
      (centers k) w hw hpB hpole0]
    simp [affineLine_apply]
  calc
    circleDeficit (extension (coordHyperplane i) psi) (centers k) w r C ≤
        circleDeficit (uscRegularization (transverseLineRaw i B psi (centers k) w)) 0 1 r C :=
      circleDeficit_extension_le_intrinsic_transverseFill hpsi hBA (centers k) w hw r C
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - uscRegularization (transverseLineRaw i B psi (centers k) w) 0).toENNReal :=
      circleSubmean_intrinsic_transverseFill_of_closedDisc hpsi (centers k) w hw
        hr (hdisc k) (hbound k)
    _ = ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - psi (centers k)).toENNReal := by
      rw [hfill]

/-- A compact affine complex disc remains in an open set after a sufficiently
small translation of its centre.  This packages the `cthickening` argument
used to pass from the limiting ambient disc to the parallel recovery discs. -/
theorem eventually_affineClosedDisc_subset_of_tendsto_center
    {q w : ComplexModel n} {r : ℝ} {U : Set (ComplexModel n)}
    (centers : ℕ → ComplexModel n) (hcenters : Tendsto centers atTop (𝓝 q))
    (hU : IsOpen U) (hdisc : affineClosedDisc q w r ⊆ U) :
    ∀ᶠ k in atTop, affineClosedDisc (centers k) w r ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_affineClosedDisc q w r).exists_cthickening_subset_open hU hdisc
  filter_upwards [hcenters.eventually (Metric.ball_mem_nhds q hδ)] with k hk
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  apply hδU
  refine Metric.mem_cthickening_of_dist_le _ (q + z • w) δ
    (affineClosedDisc q w r) ⟨z, hz, rfl⟩ ?_
  rw [dist_eq_norm, add_sub_add_right_eq_sub]
  simpa [dist_eq_norm] using (mem_ball.mp hk).le

/-- The actual ambient upper regularization satisfies the disc submean
inequality on every transverse closed disc.  Recovery points are taken off the
hyperplane, and compactness keeps their translated discs both in the domain
and below the fixed raised upper bound. -/
theorem circleSubmean_extension_of_transverse_closedDisc
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    {q w : ComplexModel n} (hw : w i ≠ 0) {r C : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc q w r ⊆ B)
    (hC : ∀ y ∈ affineClosedDisc q w r,
      extension (coordHyperplane i) psi y ≤ (C : EReal)) :
    circleDeficit (extension (coordHyperplane i) psi) q w r C ≤
      ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - extension (coordHyperplane i) psi q).toENNReal := by
  classical
  by_cases hbot : extension (coordHyperplane i) psi q = ⊥
  · have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    rw [hbot]
    simp [hpi.ne']
  have htop : extension (coordHyperplane i) psi q ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top C)
      (hC q (center_mem_affineClosedDisc q w hr.le))
  let a : ℝ := (extension (coordHyperplane i) psi q).toReal
  have hvalueq : extension (coordHyperplane i) psi q = (a : EReal) := by
    symm
    exact EReal.coe_toReal htop hbot
  obtain ⟨centers, hcenters, hoff, hvalues⟩ :=
    exists_sequence_tendsto_branch_of_extension_eq_coe hvalueq
  let U : Set (ComplexModel n) := B ∩
    (extension (coordHyperplane i) psi) ⁻¹' Iio ((C + 1 : ℝ) : EReal)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact hB.inter ((upperSemicontinuous_extension (coordHyperplane i) psi).isOpen_preimage _)
  have hDU : affineClosedDisc q w r ⊆ U := by
    intro y hy
    refine ⟨hD hy, ?_⟩
    exact (hC y hy).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_affineClosedDisc_subset_of_tendsto_center centers hcenters hUopen hDU)
  let shifted : ℕ → ComplexModel n := fun k => centers (k + N)
  have hshifted : Tendsto shifted atTop (𝓝 q) := by
    simpa [shifted] using (tendsto_add_atTop_iff_nat N).mpr hcenters
  have hshiftedOff : ∀ k, shifted k ∉ coordHyperplane i :=
    fun k => hoff (k + N)
  have hshiftedU : ∀ k, affineClosedDisc (shifted k) w r ⊆ U :=
    fun k => hN (k + N) (Nat.le_add_left N k)
  have hshiftedD : ∀ k, affineClosedDisc (shifted k) w r ⊆ B :=
    fun k _ hy => (hshiftedU k hy).1
  have hshiftedC : ∀ k, ∀ y ∈ affineClosedDisc (shifted k) w r,
      y ∉ coordHyperplane i → psi y ≤ ((C + 1 : ℝ) : EReal) := by
    intro k y hy hyH
    rw [← extension_eq hpsi hBA ⟨(hshiftedU k hy).1, hyH⟩]
    exact (hshiftedU k hy).2.le
  have hshiftedValues : Tendsto (fun k => psi (shifted k)) atTop
      (𝓝 (extension (coordHyperplane i) psi q)) := by
    rw [hvalueq]
    simpa [shifted] using (tendsto_add_atTop_iff_nat N).mpr hvalues
  have hraised := circleSubmean_extension_of_transverse_recovery hpsi hBA hw hr
    shifted hshifted hshiftedOff hshiftedD hshiftedC hshiftedValues
  exact (discSubmean_add_bound_iff q w hr.le C 1 (by norm_num) hC).mp hraised

open PshPuncturedLineRemovable in
/-- The ambient upper regularization has the full disc-submean property on
each affine line transverse to the coordinate hyperplane.  The proof applies
the ambient closed-disc theorem after an affine change of parameter; it does
not identify ambient and intrinsic regularizations. -/
theorem hasDiscSubmeanOn_extension_comp_affineLine
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B) (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) :
    HasDiscSubmeanOn (fun z => extension (coordHyperplane i) psi
      (x + affineLine v z)) (transverseLineDomain B x v) := by
  intro a d r hr hdisc C hC
  by_cases hd : d = 0
  · subst d
    unfold circleDeficit
    simp [mul_comm]
  have hdv : (d • v) i ≠ 0 := by
    change d * v i ≠ 0
    exact mul_ne_zero hd hv
  have hambientDisc : affineClosedDisc (x + affineLine v a) (d • v) r ⊆ B := by
    rintro y ⟨z, hz, rfl⟩
    change x + affineLine v a + z • (d • v) ∈ B
    have hz' : a + z • d ∈ affineClosedDisc a d r := ⟨z, hz, rfl⟩
    have hmem := hdisc hz'
    change x + affineLine v (a + z • d) ∈ B at hmem
    simpa [affineLine_apply, add_smul, smul_smul, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hmem
  have hambientC : ∀ y ∈ affineClosedDisc (x + affineLine v a) (d • v) r,
      extension (coordHyperplane i) psi y ≤ (C : EReal) := by
    rintro y ⟨z, hz, rfl⟩
    change extension (coordHyperplane i) psi
      (x + affineLine v a + z • (d • v)) ≤ (C : EReal)
    have hz' : a + z • d ∈ affineClosedDisc a d r := ⟨z, hz, rfl⟩
    have hvalue := hC (a + z • d) hz'
    change extension (coordHyperplane i) psi
      (x + affineLine v (a + z • d)) ≤ (C : EReal) at hvalue
    simpa [affineLine_apply, add_smul, smul_smul, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hvalue
  have hambient := circleSubmean_extension_of_transverse_closedDisc hB hpsi hBA
    hdv hr hambientDisc hambientC
  calc
    circleDeficit (fun z => extension (coordHyperplane i) psi (x + affineLine v z)) a d r C =
        circleDeficit (extension (coordHyperplane i) psi)
          (x + affineLine v a) (affineLine v d) r C :=
      circleDeficit_comp_affine (extension (coordHyperplane i) psi) (affineLine v) x a d r C
    _ ≤ ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - extension (coordHyperplane i) psi (x + affineLine v a)).toENNReal := by
      simpa only [affineLine_apply] using hambient

/-- The actual ambient upper regularization has plurisubharmonic transverse
line slices.  This closes the slice interface using the direct recovery proof
above rather than an ambient--intrinsic regularization comparison. -/
theorem hasTransverseLineSlices_extension_of_punctured_plurisubharmonic
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B)
    (hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff
      (PshHypersurfaceRemovable.coordHyperplane i) B psi)
    (hpsi : PlurisubharmonicOn psi
      (B \ PshHypersurfaceRemovable.coordHyperplane i))
    (hBA : IsOpen (B \ PshHypersurfaceRemovable.coordHyperplane i)) :
    PshHypersurfaceRemovable.HasTransverseLineSlices i
      (PshCodimTwoExtension.extension (PshHypersurfaceRemovable.coordHyperplane i) psi) B := by
  apply (PshPuncturedLineRemovable.hasTransverseLineSlices_iff_forall_hasDiscSubmean
    hB hbound).mpr
  intro x v hv
  exact hasDiscSubmeanOn_extension_comp_affineLine hB hpsi hBA x v hv

/-- A locally bounded plurisubharmonic branch off a coordinate hyperplane has
a plurisubharmonic ambient upper-regularized extension. -/
theorem plurisubharmonicOn_extension_of_punctured_plurisubharmonic
    {i : Fin n} {B : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    (hB : IsOpen B)
    (hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff
      (PshHypersurfaceRemovable.coordHyperplane i) B psi)
    (hpsi : PlurisubharmonicOn psi
      (B \ PshHypersurfaceRemovable.coordHyperplane i))
    (hBA : IsOpen (B \ PshHypersurfaceRemovable.coordHyperplane i)) :
    PlurisubharmonicOn
      (PshCodimTwoExtension.extension (PshHypersurfaceRemovable.coordHyperplane i) psi) B :=
  PshHypersurfaceRemovable.plurisubharmonicOn_extensionAcross_coordHyperplane_of_transverseSlices
    hB hbound
    (hasTransverseLineSlices_extension_of_punctured_plurisubharmonic hB hbound hpsi hBA)

/-- Local upper regularization is controlled by an eventually valid continuous
real majorant.  This is the ambient-dimensional version of the limsup lemma
used on a punctured complex line. -/
theorem uscRegularization_le_coe_of_eventually_le_continuous
    {raw : ComplexModel n → EReal} {a : ComplexModel n}
    {G : ComplexModel n → ℝ} (hG : Continuous G)
    (hmajor : {y | raw y ≤ (G y : EReal)} ∈ 𝓝 a) :
    uscRegularization raw a ≤ (G a : EReal) := by
  apply le_of_forall_gt
  intro b hab
  obtain ⟨d, had, hdb⟩ := exists_between hab
  have hGd : {y | (G y : EReal) < d} ∈ 𝓝 a :=
    (EReal.continuous_coe_iff.mpr hG).upperSemicontinuous a d had
  have hU : {y | raw y ≤ (G y : EReal)} ∩ {y | (G y : EReal) < d} ∈ 𝓝 a :=
    inter_mem hmajor hGd
  exact ((uscRegularization_le_localSup raw hU).trans
    (iSup_le fun y => iSup_le fun hy => hy.1.trans (le_of_lt hy.2))).trans_lt hdb

/-- The ambient hypersurface extension is bounded at `a` by every continuous
real function that majorizes the branch on a full ambient neighborhood of `a`
off the exceptional set. -/
theorem extension_le_coe_of_eventually_off_le_continuous
    {A : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    {a : ComplexModel n} {G : ComplexModel n → ℝ} (hG : Continuous G)
    (hmajor : {y | y ∉ A → psi y ≤ (G y : EReal)} ∈ 𝓝 a) :
    extension A psi a ≤ (G a : EReal) := by
  classical
  rw [extension_eq_uscRegularization]
  apply uscRegularization_le_coe_of_eventually_le_continuous hG
  apply Filter.mem_of_superset hmajor
  intro y hy
  change (if y ∈ A then (⊥ : EReal) else psi y) ≤ (G y : EReal)
  by_cases hyA : y ∈ A
  · simp [hyA]
  · rw [if_neg hyA]
    exact hy hyA

/-- Neighborhood-set spelling of ambient continuous domination.  It is often
more convenient when a barrier has first been constructed on a ball or a
polydisc around the point. -/
theorem extension_le_coe_of_mem_nhds_off_le_continuous
    {A U : Set (ComplexModel n)} {psi : ComplexModel n → EReal}
    {a : ComplexModel n} {G : ComplexModel n → ℝ} (hG : Continuous G)
    (hU : U ∈ 𝓝 a)
    (hmajor : ∀ y ∈ U, y ∉ A → psi y ≤ (G y : EReal)) :
    extension A psi a ≤ (G a : EReal) := by
  apply extension_le_coe_of_eventually_off_le_continuous hG
  exact Filter.mem_of_superset hU fun y hy => hmajor y hy

/-- The preceding ambient majorant gives the requested bound for the actual
ambient extension restricted to any affine complex line.  No comparison with
an intrinsic line regularization is used. -/
theorem extension_comp_affineLine_le_coe_of_ambient_majorant
    {i : Fin n} {psi : ComplexModel n → EReal} {x v : ComplexModel n}
    {z : ℂ} {G : ComplexModel n → ℝ} (hG : Continuous G)
    (hmajor : {y | y ∉ coordHyperplane i → psi y ≤ (G y : EReal)} ∈
      𝓝 (x + affineLine v z)) :
    extension (coordHyperplane i) psi (x + affineLine v z) ≤
      (G (x + affineLine v z) : EReal) :=
  extension_le_coe_of_eventually_off_le_continuous hG hmajor

/-- A ball/polydisc-style local formulation of the actual ambient line bound.
A harmonic function on the selected line becomes relevant only after it is
extended to an ambient continuous function satisfying this hypothesis. -/
theorem extension_comp_affineLine_le_coe_of_ambient_nhds_majorant
    {i : Fin n} {psi : ComplexModel n → EReal} {x v : ComplexModel n}
    {z : ℂ} {U : Set (ComplexModel n)} {G : ComplexModel n → ℝ}
    (hG : Continuous G) (hU : U ∈ 𝓝 (x + affineLine v z))
    (hmajor : ∀ y ∈ U, y ∉ coordHyperplane i → psi y ≤ (G y : EReal)) :
    extension (coordHyperplane i) psi (x + affineLine v z) ≤
      (G (x + affineLine v z) : EReal) :=
  extension_le_coe_of_mem_nhds_off_le_continuous hG hU hmajor

/-- If an ambient continuous majorant restricts to a chosen line function at a
point, it controls the actual ambient extension by that line value. -/
theorem extension_comp_affineLine_le_coe_of_ambient_majorant_eq_line
    {i : Fin n} {psi : ComplexModel n → EReal} {x v : ComplexModel n}
    {z : ℂ} {G : ComplexModel n → ℝ} {h : ℂ → ℝ}
    (hG : Continuous G)
    (hmajor : {y | y ∉ coordHyperplane i → psi y ≤ (G y : EReal)} ∈
      𝓝 (x + affineLine v z))
    (hline : G (x + affineLine v z) = h z) :
    extension (coordHyperplane i) psi (x + affineLine v z) ≤ (h z : EReal) := by
  rw [← hline]
  exact extension_comp_affineLine_le_coe_of_ambient_majorant hG hmajor

end

end Hironaka.PshAmbientExtensionLineControl

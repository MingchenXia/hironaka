import Hironaka.Resolution.HironakaG8P1ArcChartFamily
import Hironaka.Resolution.HironakaG8P1ArcOffHorizontal
import Hironaka.Resolution.HironakaG8P1ArcTangentLimit
import Hironaka.Resolution.HironakaAdmissibleCalculus

set_option autoImplicit false

/-!
# First-order equations on the actual arc tower's conventional strict transform

The original closed set is pulled back from the original manifold to its
product with a line. Its conventional strict transform is dense away from
the original horizontal divisor. On the genuine original-coordinate/source
window, the actual arc-family projection equations and the rescaled
derivative limit give its first-order equation at parameter zero.

The conventional/geometric comparison is the needed public extraction of
the existing private `HironakaActualSmoothBoundaryCleanup.strictAlong_eq_library_of_avoid`
(same scope and tower-induction proof). This extraction receives no new
mathematical credit. The actual point-arc centre-avoidance theorem supplies
its hypothesis, giving the final native geometric `strictAlong` conclusion.
No tangent-space equality, general-centre birth-chart lemma, directrix
comparison, or original Hironaka goal is asserted here.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcTangentTrace

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates ProductComplexManifold
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower
  HironakaG8P1ArcChartFamily HironakaG8P1ArcOffHorizontal
  HironakaG8P1ArcTangentLimit MarkedIdeals ResolutionInvariantSpec
  HomogenizedGlueingTower RestrictEmptyTower BlowupStrictSubmanifold NormalCrossings
  HironakaActualAnchoredVerticalChart

open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The old-coordinate part of the actual product chart. -/
def oldCoordinates (w : ComplexModel (n+1)) : ComplexModel n :=
  ((prodModelEquiv n 1).symm w).1

theorem oldCoordinates_apply (w : ComplexModel (n+1)) (i : Fin n) :
    oldCoordinates w i = w (i.castAdd 1) := rfl

theorem continuous_oldCoordinates : Continuous (oldCoordinates (n := n)) :=
  (prodModelEquiv n 1).symm.continuous.fst

/-- Extract the actual atlas membership retained by an anchored chart chain.
This is the public geometric field of the existing chain construction. -/
theorem atlas_of_anchored_chart
    {Y Z : CMfd.{u} (n+1)}
    (a : OpenPartialHomeomorph Y (ComplexModel (n+1))) (R : BlowupTower Y Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hAnchor : AnchoredInheritedLastChartChain a R e) :
    e ∈ atlas (ComplexModel (n+1)) Z := by
  cases R with
  | refl =>
      obtain ⟨rfl, ha⟩ := hAnchor
      exact ha
  | step R C π hπ => exact hAnchor.1

/-- Public API extraction of the existing private comparison in
`HironakaActualSmoothBoundaryCleanup`, with its exact scope and proof route.
It does not re-prove any resolution theorem or supply a tangent comparison. -/
theorem strictAlong_eq_conventional_of_centresAvoid
    {m : ℕ} {Y : CMfd.{u} m} (W : Set Y) (hW : IsClosed W)
    (O : Opens Y) (hdense : W ⊆ closure (W ∩ (O : Set Y))) :
    {Z : CMfd.{u} m} → (T : BlowupTower Y Z) → CentresAvoid O T →
      strictAlong T W = strictTransform m T.proj W
  | _, .refl, _ => by simp [strictAlong, strictTransform, exceptionalLocus_id]
  | _, .step T C π hπ, hAvoid => by
      have hCE : C ⊆ T.proj ⁻¹' (O : Set Y)ᶜ := by
        intro y hy hyO
        exact Set.disjoint_left.mp hAvoid.2 hy hyO
      have hD : strictTransform m T.proj W ⊆
          closure (strictTransform m T.proj W \ T.proj ⁻¹' (O : Set Y)ᶜ) :=
        HironakaAdmissibleCalculus.strictTransform_subset_closure_diff T.contMDiff_proj hW
          (by simpa only [sdiff_compl] using hdense)
      have hNowhere : strictTransform m T.proj W ⊆ closure (strictTransform m T.proj W \ C) :=
        hD.trans (closure_mono (sdiff_subset_sdiff_right hCE))
      calc
        strictAlong (.step T C π hπ) W = geoStrictTransform π C (strictAlong T W) := rfl
        _ = geoStrictTransform π C (strictTransform m T.proj W) := by
          rw [strictAlong_eq_conventional_of_centresAvoid W hW O hdense T hAvoid.1]
        _ = strictTransform m π (strictTransform m T.proj W) :=
          BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hNowhere
        _ = strictTransform m (T.proj ∘ π) W :=
          (StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff W).symm

/-- The needed closure membership uses the existing public density theorem;
it needs no new generic strict-transform comparison theorem. -/
theorem mem_closure_offHorizontal_of_mem_strictTransform
    {Z : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Z)
    (W : Set X) (hW : IsClosed W) {y : Z}
    (hy : y ∈ strictTransform (n+1) T.proj ((Prod.fst : projectionAmbient X → X) ⁻¹' W)) :
    y ∈ closure (T.proj ⁻¹' (((Prod.fst : projectionAmbient X → X) ⁻¹' W) ∩
      (offHorizontal X : Set (projectionAmbient X)))) := by
  let P : Set (projectionAmbient X) := (Prod.fst : projectionAmbient X → X) ⁻¹' W
  let O : Set (projectionAmbient X) := offHorizontal X
  have hP : IsClosed P := hW.preimage continuous_fst
  have hPO : P ⊆ closure (P \ Oᶜ) := by
    simpa only [sdiff_compl] using product_subset_closure_offHorizontal W
  have hden := HironakaAdmissibleCalculus.strictTransform_subset_closure_diff
    T.contMDiff_proj hP hPO hy
  refine (closure_mono ?_) hden
  intro v hv
  refine ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage
    T.contMDiff_proj.continuous hP hv.1, ?_⟩
  simpa only [mem_preimage, mem_compl_iff, not_not] using hv.2

/-- A coordinate equation of an original closed set gives its linearized
equation at each parameter-zero point of the actual tower's conventional
strict transform, within the qualified source/original-domain window. -/
theorem derivative_eq_zero_of_arc_coordinates
    (x : X)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {Z : CMfd.{u} (n+1)} (T : BlowupTower (projectionAmbient X) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1))) (r : ℕ)
    (hcoords : ∀ v ∈ e.source,
      (∀ i : Fin n, flatCoord Φ i (T.proj v).1 =
        (e v (Fin.last n)) ^ (r + 1) * e v (i.castAdd 1)) ∧
      (T.proj v).2 0 = e v (Fin.last n))
    (W : Set X) (hW : IsClosed W)
    (g : ComplexModel n → ℂ) (A : ComplexModel n →L[ℂ] ℂ)
    (hg : HasFDerivAt g A 0)
    (hEquation : ∀ w ∈ W, w ∈ flatDomain Φ →
      g (Φ.toFun (chartAt (ComplexModel n) x w)) = g 0)
    {y : Z}
    (hy : y ∈ strictTransform (n+1) T.proj ((Prod.fst : projectionAmbient X → X) ⁻¹' W))
    (hySource : y ∈ e.source) (hyDomain : (T.proj y).1 ∈ flatDomain Φ)
    (hyParameter : (T.proj y).2 0 = 0) :
    A (oldCoordinates (e y)) = 0 := by
  let B : Set Z := T.proj ⁻¹' (((Prod.fst : projectionAmbient X → X) ⁻¹' W) ∩
    (offHorizontal X : Set (projectionAmbient X)))
  have hyClosure : y ∈ closure B :=
    mem_closure_offHorizontal_of_mem_strictTransform T W hW hy
  let l : Filter Z := 𝓝[B] y
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hyClosure
  have he : Tendsto e l (𝓝 (e y)) :=
    (e.continuousAt hySource).tendsto.mono_left nhdsWithin_le_nhds
  have hparameter : e y (Fin.last n) = 0 :=
    ((hcoords y hySource).2).symm.trans hyParameter
  have ht : Tendsto (fun v => e v (Fin.last n)) l (𝓝 (0 : ℂ)) := by
    simpa only [hparameter, Function.comp_def] using
      ((PiLp.continuous_apply 2 _ (Fin.last n)).tendsto (e y)).comp he
  have hs : Tendsto (fun v => (e v (Fin.last n)) ^ (r + 1)) l (𝓝 (0 : ℂ)) := by
    simpa only [zero_pow (Nat.succ_ne_zero r)] using ht.pow (r + 1)
  have hv : Tendsto (fun v => oldCoordinates (e v)) l (𝓝 (oldCoordinates (e y))) :=
    (continuous_oldCoordinates.tendsto (e y)).comp he
  have hsource : ∀ᶠ v in l, v ∈ e.source :=
    nhdsWithin_le_nhds (e.open_source.mem_nhds hySource)
  have hκ : Continuous (fun v : Z => (T.proj v).1) :=
    continuous_fst.comp T.contMDiff_proj.continuous
  have hdomain : ∀ᶠ v in l, (T.proj v).1 ∈ flatDomain Φ :=
    nhdsWithin_le_nhds (((isOpen_flatDomain Φ).preimage hκ).mem_nhds hyDomain)
  have hB : ∀ᶠ v in l, v ∈ B := self_mem_nhdsWithin
  have hsne : ∀ᶠ v in l, (e v (Fin.last n)) ^ (r + 1) ≠ 0 := by
    filter_upwards [hB, hsource] with v hvB hvSource
    have hne : (T.proj v).2 0 ≠ 0 := hvB.2
    rw [(hcoords v hvSource).2] at hne
    exact pow_ne_zero (r + 1) hne
  have hlevel : ∀ᶠ v in l,
      g ((e v (Fin.last n)) ^ (r + 1) • oldCoordinates (e v)) = g 0 := by
    filter_upwards [hB, hsource, hdomain] with v hvB hvSource hvDomain
    have hvec : Φ.toFun (chartAt (ComplexModel n) x (T.proj v).1) =
        (e v (Fin.last n)) ^ (r + 1) • oldCoordinates (e v) := by
      ext i
      change flatCoord Φ i (T.proj v).1 = _
      simp only [PiLp.smul_apply, smul_eq_mul, oldCoordinates_apply]
      exact (hcoords v hvSource).1 i
    rw [← hvec]
    exact hEquation _ hvB.1 hvDomain
  exact derivative_eq_zero_of_rescaled_levelSet hg hs hv hsne hlevel

/-- Ordinary marked-ideal inputs construct a family with actual Cartier
counts and genuine arc-point windows on which every original closed-set
equation has the claimed first-order exceptional trace. The returned chart
is the actually restricted `Φs`, whose qualified domain carries the original
carrier mask. The frame and projection equations are produced internally. -/
theorem exists_arcFamily_with_conventional_tangent_trace
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x ∈ M.cosupp)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    ∃ (Φs : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n))
      (S : ℕ → ArcStage n (arcY1 x)),
      Φs.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φs.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φs, w ∈ M.N ↔
        Φs.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧ IsArcFamily x hπ1 S ∧
      ∀ r, ArcCountsRaw (k := k) M x hπ1 (S r) r ∧
        (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z ∧
        (∀ v ∈ (S r).e.source,
          (∀ i : Fin n, flatCoord Φs i (((arcA1 x hπ1).append (S r).R).proj v).1 =
            ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n)) ∧
        ∃ V : Set (S r).Z, IsOpen V ∧ (S r).z ∈ V ∧ V ⊆ (S r).e.source ∧
          (∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φs) ∧
          ∀ (W : Set X), IsClosed W →
            ∀ (g : ComplexModel n → ℂ) (A : ComplexModel n →L[ℂ] ℂ),
              HasFDerivAt g A 0 →
              (∀ w ∈ W, w ∈ flatDomain Φs →
                g (Φs.toFun (chartAt (ComplexModel n) x w)) = g 0) →
              ∀ y ∈ strictTransform (n+1) ((arcA1 x hπ1).append (S r).R).proj
                  ((Prod.fst : projectionAmbient X → X) ⁻¹' W),
                y ∈ V → (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0 →
                A (oldCoordinates ((S r).e y)) = 0 := by
  obtain ⟨Φ, Φs, c, SN, U, S, _hΦsrc, _hΦ0, hΦsTo, _hΦsInv, _hΦsSrc, _hΦsTgt,
    hΦsChartSrc, hΦsZero, _hDom, hMask, _hcy, _hck, _hcj, _hOld, _hLast,
    _hSN, _h0c, _hzp, _hU, _hzU, _hUc, _hNU, hS, hAll⟩ :=
    exists_arcFamily_with_original_coordinates M hM x hx hπ1
  refine ⟨Φs, Finset.univ.filter (fun i : Fin n => i.castAdd 1 ∈ SN), S,
    hΦsChartSrc, hΦsZero, hMask, hS, ?_⟩
  intro r
  have hcoords_s : ∀ v ∈ (S r).e.source,
      (∀ i : Fin n, flatCoord Φs i (((arcA1 x hπ1).append (S r).R).proj v).1 =
        ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
      (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n) := by
    intro v hv
    have hc := (hAll r).2.2 v hv
    refine ⟨?_, hc.2⟩
    intro i
    simpa only [flatCoord, hΦsTo] using hc.1 i
  obtain ⟨V, hV, hzV, hVsource, hVdomain⟩ := exists_original_domain_window x Φs hπ1 S hS r
  refine ⟨(hAll r).1, atlas_of_anchored_chart c.homeo (S r).R (S r).e (hAll r).2.1,
    hcoords_s, V, hV, hzV, hVsource, hVdomain, ?_⟩
  intro W hW g A hg hEquation y hy hyV hyParameter
  exact derivative_eq_zero_of_arc_coordinates x Φs ((arcA1 x hπ1).append (S r).R)
    (S r).e r hcoords_s W hW g A hg hEquation hy
    (hVsource hyV) (hVdomain y hyV) hyParameter

/-- The native geometric first-order trace of the actual point-arc family.
The original dense open and centre avoidance are produced by the actual
product/point construction; the geometric/conventional comparison is proved
above rather than supplied as a hypothesis. -/
theorem exists_arcFamily_with_geometric_tangent_trace
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x ∈ M.cosupp)
    (hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))) :
    ∃ (Φs : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (J : Finset (Fin n))
      (S : ℕ → ArcStage n (arcY1 x)),
      Φs.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φs.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ w ∈ flatDomain Φs, w ∈ M.N ↔
        Φs.toFun (chartAt (ComplexModel n) x w) ∈ coordSubspace J) ∧ IsArcFamily x hπ1 S ∧
      ∀ r, ArcCountsRaw (k := k) M x hπ1 (S r) r ∧
        (S r).e ∈ atlas (ComplexModel (n+1)) (S r).Z ∧
        (∀ v ∈ (S r).e.source,
          (∀ i : Fin n, flatCoord Φs i (((arcA1 x hπ1).append (S r).R).proj v).1 =
            ((S r).e v (Fin.last n)) ^ (r + 1) * (S r).e v (i.castAdd 1)) ∧
          (((arcA1 x hπ1).append (S r).R).proj v).2 0 = (S r).e v (Fin.last n)) ∧
        ∃ V : Set (S r).Z, IsOpen V ∧ (S r).z ∈ V ∧ V ⊆ (S r).e.source ∧
          (∀ v ∈ V, (((arcA1 x hπ1).append (S r).R).proj v).1 ∈ flatDomain Φs) ∧
          ∀ (W : Set X), IsClosed W →
            ∀ (g : ComplexModel n → ℂ) (A : ComplexModel n →L[ℂ] ℂ),
              HasFDerivAt g A 0 →
              (∀ w ∈ W, w ∈ flatDomain Φs →
                g (Φs.toFun (chartAt (ComplexModel n) x w)) = g 0) →
              ∀ y ∈ strictAlong ((arcA1 x hπ1).append (S r).R)
                  ((Prod.fst : projectionAmbient X → X) ⁻¹' W),
                y ∈ V → (((arcA1 x hπ1).append (S r).R).proj y).2 0 = 0 →
                A (oldCoordinates ((S r).e y)) = 0 := by
  obtain ⟨Φs, J, S, hΦsSrc, hΦsZero, hMask, hS, hAll⟩ :=
    exists_arcFamily_with_conventional_tangent_trace M hM x hx hπ1
  refine ⟨Φs, J, S, hΦsSrc, hΦsZero, hMask, hS, ?_⟩
  intro r
  obtain ⟨hCounts, hAtlas, hcoords, V, hV, hzV, hVsource, hVdomain, hTrace⟩ := hAll r
  refine ⟨hCounts, hAtlas, hcoords, V, hV, hzV, hVsource, hVdomain, ?_⟩
  intro W hW g A hg hEquation y hy hyV hyParameter
  have hComparison := strictAlong_eq_conventional_of_centresAvoid
    ((Prod.fst : projectionAmbient X → X) ⁻¹' W) (hW.preimage continuous_fst)
    (offHorizontal X) (product_subset_closure_offHorizontal W)
    ((arcA1 x hπ1).append (S r).R) (centresAvoid_offHorizontal_arcFamily hS r)
  apply hTrace W hW g A hg hEquation y
  · rw [← hComparison]
    exact hy
  · exact hyV
  · exact hyParameter

end

end Hironaka.HironakaG8P1ArcTangentTrace

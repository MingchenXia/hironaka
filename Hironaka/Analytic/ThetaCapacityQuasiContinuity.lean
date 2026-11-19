import Hironaka.Analytic.ThetaCapacityChart
import Hironaka.Analytic.BedfordTaylorQuasiContinuity

set_option autoImplicit false

/-!
# Quasi-continuity for the global capacity

Xia's Theorem 2.3.2 says that a `theta`-PSH potential is quasi-continuous for
the capacity `Cap_theta`.  Bedford--Taylor quasi-continuity in a chart is
already available, sorry-free, in
`Hironaka.BedfordTaylorQuasiContinuity`; `Hironaka.ThetaCapacityChart` compares
`Cap_theta` with the chart capacity.  This module composes the two and
produces the **local** form: around every point of the manifold there is a
neighbourhood `N` and an open set `G` of arbitrarily small `Cap_theta` such
that the potential is continuous on `N \ G`.

The reference `V` and the potential `w` are both assumed globally bounded, and
for the reference this is a real restriction: `V_theta` itself is unbounded
below whenever `nK({theta}) != emptyset`, so what is proved is Xia's Theorem
2.3.2 *relative to a globally bounded reference*, not for `Cap_theta` proper.
See the corresponding discussion in `Hironaka.ThetaCapacityChart`; lifting the
restriction means restating the stack relative to an open set relatively
compact in `X \ nK({theta})`, which is a different architecture from the
global statements here.

The pointwise statement is then globalized.  The neighbourhood produced
around a point depends only on the chart and its smooth local potential, not
on the tolerance, so a finite subcover of the compact manifold may be
extracted first and the tolerance divided among its members afterwards;
finite subadditivity of `Cap_theta` bounds the union, and continuity off it is
glued from the members, each neighbourhood being open.  The result,
`exists_isOpen_thetaCapacity_lt_continuousOn_compl`, is Xia's Theorem 2.3.2
for a globally bounded potential and a globally bounded reference.
-/

open Set MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

namespace Hironaka.ThetaCapacityQuasiContinuity

open Hironaka.PositiveClasses Hironaka.MongeAmpere
open GlobalNonPluripolar BoundedGlobalProduct
open Hironaka.BedfordTaylor
open Hironaka.DiagonalMass
open Hironaka.ThetaCapacity
open Hironaka.ThetaCapacityChart

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- Finite subadditivity of the global capacity. -/
theorem thetaCapacity_biUnion_finset_le {iota : Type*}
    (theta : ClosedRealOneOneForm n M) (V : M → EReal) (s : Finset iota)
    (E : iota → Set M) :
    thetaCapacity theta V (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, thetaCapacity theta V (E i) :=
  thetaCapacity_le_of_forall fun _u hu h1 h2 =>
    (measure_biUnion_finset_le s E).trans (Finset.sum_le_sum fun i _ =>
      diagonalPotentialMeasure_le_thetaCapacity hu h1 h2 (E i))

/-- **Quasi-continuity near a point, with the neighbourhood chosen first.**
The neighbourhood `N` depends only on the chart and the local potential, not
on `eps`; that is what makes the compactness argument of
`exists_isOpen_thetaCapacity_lt_continuousOn_compl` possible. -/
theorem exists_nhds_forall_isOpen_thetaCapacity_lt_continuousOn
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotential w)
    {c d : ℝ} (hcd : c ≤ d) (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (x : M) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (w y).toReal) (N \ G) := by
  classical
  obtain ⟨cw, dw, hwbd⟩ := hwb
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ : ComplexModel n := e.val x with hz₀
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, rho, hz₀W, hrho⟩ :=
    Hironaka.LocalPotentials.closedRealOneOne_hasLocalPotentials
      theta e z₀ hz₀t
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hrho.1 z₀ hz₀W
  set R : ℝ := r / 8 with hR_def
  have hR : 0 < R := by positivity
  have hcb : closedBall z₀ (4 * R) ⊆ W := by
    refine subset_trans ?_ hrW
    refine closedBall_subset_ball ?_
    rw [hR_def]; linarith
  set D : Opens (ComplexModel n) := ⟨ball z₀ (4 * R), isOpen_ball⟩ with hD_def
  have hDW : (D : Set (ComplexModel n)) ⊆ W := ball_subset_closedBall.trans hcb
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := hDW.trans hrho.2.1
  have hrhoD : IsSmoothLocalPotential theta.val e (D : Set (ComplexModel n)) rho :=
    hrho.mono isOpen_ball hDW
  -- a uniform bound for the local potential on the ball
  obtain ⟨L, hLbd⟩ := (isCompact_closedBall z₀ (4 * R)).exists_bound_of_continuousOn
    ((hrho.2.2.1.continuousOn).mono hcb)
  have hL : ∀ z ∈ (D : Set (ComplexModel n)), |rho z| ≤ L := fun z hz => by
    simpa [Real.norm_eq_abs] using hLbd z (ball_subset_closedBall hz)
  have hL0 : 0 ≤ L := le_trans (abs_nonneg (rho z₀))
    (by simpa [Real.norm_eq_abs] using hLbd z₀ (mem_closedBall_self (by positivity)))
  -- the corrected chart potential and its chart quasi-continuity
  set g : ComplexModel n → ℝ := correctedChartReal w e rho with hg_def
  have hg : IsLocallyBoundedPshOn D g :=
    correctedChartReal_isLocallyBoundedPshOn hw.1 ⟨cw, dw, hwbd⟩ hrhoD hwbd hL
  set K : ℝ := (d - c + 2 * L + 2) ^ n with hK_def
  have hK0 : 0 < K := by
    have : 0 < d - c + 2 * L + 2 := by linarith
    exact pow_pos this n
  have h3R : closedBall z₀ (3 * R) ⊆ (D : Set (ComplexModel n)) := by
    refine closedBall_subset_ball ?_
    linarith
  -- the neighbourhood, which does not depend on `eps`
  set N : Set M := e.val.source ∩ e.val ⁻¹' (ball z₀ (R / 2)) with hN_def
  have hNopen : IsOpen N := e.val.isOpen_inter_preimage isOpen_ball
  have hxN : x ∈ N := ⟨hx, mem_ball_self (by positivity)⟩
  refine ⟨N, hNopen, hxN, ?_⟩
  intro eps heps
  have heps' : 0 < eps / K := by positivity
  obtain ⟨G₀, hG₀open, hG₀cap, hG₀cont⟩ :=
    IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_ball hg hR h3R heps'
  set G : Set M := e.val.source ∩ e.val ⁻¹' (G₀ ∩ (D : Set (ComplexModel n)))
    with hG_def
  have hGopen : IsOpen G := e.val.isOpen_inter_preimage (hG₀open.inter D.isOpen)
  have hGsub : G ⊆ (diagSlotChart theta e D hDt rho hrhoD).source := fun y hy =>
    ⟨hy.1, hy.2.2⟩
  have hGimg : e.val '' G ⊆ G₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2.1
  -- the capacity estimate
  have hcap : thetaCapacity theta V G < ENNReal.ofReal eps := by
    have h1 := thetaCapacity_le_relCapacity (V := V) e D hDt rho hrhoD hcd hL0
      hVbd hL G hGsub
    rw [← hK_def] at h1
    have h2 : relCapacity D (e.val '' G) < ENNReal.ofReal (eps / K) :=
      lt_of_le_of_lt (relCapacity_mono hGimg) hG₀cap
    have hKne : ENNReal.ofReal K ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hK0
    have h3 : relCapacity D (e.val '' G) * ENNReal.ofReal K <
        ENNReal.ofReal (eps / K) * ENNReal.ofReal K :=
      ENNReal.mul_lt_mul_left hKne ENNReal.ofReal_ne_top h2
    have h4 : ENNReal.ofReal (eps / K) * ENNReal.ofReal K = ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_mul heps'.le, div_mul_cancel₀ _ hK0.ne']
    calc thetaCapacity theta V G
        ≤ ENNReal.ofReal K * relCapacity D (e.val '' G) := h1
      _ = relCapacity D (e.val '' G) * ENNReal.ofReal K := mul_comm _ _
      _ < ENNReal.ofReal (eps / K) * ENNReal.ofReal K := h3
      _ = ENNReal.ofReal eps := h4
  refine ⟨G, hGopen, hcap, ?_⟩
  -- continuity off `G`
  have hmaps : MapsTo e.val (N \ G) (ball z₀ (R / 2) \ G₀) := by
    rintro y ⟨hyN, hyG⟩
    refine ⟨hyN.2, fun hmem => hyG ⟨hyN.1, hmem, ?_⟩⟩
    exact ball_subset_ball (by linarith) hyN.2
  have hcont₁ : ContinuousOn (fun z => g z - rho z) (ball z₀ (R / 2) \ G₀) := by
    refine hG₀cont.sub (((hrho.2.2.1.continuousOn).mono ?_))
    exact fun z hz => hDW (ball_subset_ball (by linarith) hz.1)
  have hcomp : ContinuousOn (fun y => g (e.val y) - rho (e.val y)) (N \ G) :=
    hcont₁.comp (e.val.continuousOn.mono fun y hy => hy.1.1) hmaps
  refine hcomp.congr ?_
  rintro y ⟨hyN, -⟩
  have hinv : e.val.symm (e.val y) = y := e.val.left_inv hyN.1
  simp only [hg_def, correctedChartReal, hinv]
  ring

/-- **Quasi-continuity near a point.**  For a globally bounded reference `V`
and a globally bounded `theta`-PSH potential `w`, every point of `M` has an
open neighbourhood `N` such that, for every `eps > 0`, there is an open `G`
with `Cap_theta(G, V) < eps` and `w` continuous on `N \ G`. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotential w)
    {c d : ℝ} (hcd : c ≤ d) (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    (x : M) {eps : ℝ} (heps : 0 < eps) :
    ∃ N G : Set M, IsOpen N ∧ x ∈ N ∧ IsOpen G ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (w y).toReal) (N \ G) := by
  obtain ⟨N, hNopen, hxN, hN⟩ :=
    exists_nhds_forall_isOpen_thetaCapacity_lt_continuousOn hw hwb hcd hVbd x
  obtain ⟨G, hGopen, hcap, hcont⟩ := hN eps heps
  exact ⟨N, G, hNopen, hxN, hGopen, hcap, hcont⟩

/-- **Xia, Hironaka, Theorem 2.3.2, global form** (`xia-sgpt:page-0063`), for a
globally bounded potential and a globally bounded reference.  For every
`eps > 0` there is one open set `G` of `Cap_theta(-, V)`-measure less than
`eps` outside which `w` is continuous on all of `M`.

The passage from the pointwise statement is a finite subcover of the compact
manifold together with the finite subadditivity of `Cap_theta`: the
neighbourhoods do not depend on `eps`, so the subcover may be extracted first
and the tolerance then divided among its members. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_compl
    {theta : ClosedRealOneOneForm n M} {V w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) (hwb : IsBoundedPotential w)
    {c d : ℝ} (hcd : c ≤ d) (hVbd : ∀ x, (c : EReal) ≤ V x ∧ V x ≤ (d : EReal))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (w y).toReal) Gᶜ := by
  classical
  choose N hNopen hxN hNeps using fun y : M =>
    exists_nhds_forall_isOpen_thetaCapacity_lt_continuousOn hw hwb hcd hVbd y
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover N hNopen
    (fun y _ => mem_iUnion.mpr ⟨y, hxN y⟩)
  -- one tolerance per member of the subcover, with room to spare
  set m : ℝ := (s.card : ℝ) with hm_def
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2 * (m + 1) := by positivity
  set delta : ℝ := eps / (2 * (m + 1)) with hdelta_def
  have hdelta : 0 < delta := by positivity
  choose G hGopen hGcap hGcont using fun y : M => hNeps y delta hdelta
  refine ⟨⋃ i ∈ s, G i, isOpen_biUnion fun i _ => hGopen i, ?_, ?_⟩
  · -- the capacity of the union
    have hsum : thetaCapacity theta V (⋃ i ∈ s, G i) ≤
        ∑ i ∈ s, thetaCapacity theta V (G i) :=
      thetaCapacity_biUnion_finset_le theta V s G
    have hbound : ∑ i ∈ s, thetaCapacity theta V (G i) ≤
        ∑ _i ∈ s, ENNReal.ofReal delta :=
      Finset.sum_le_sum fun i _ => (hGcap i).le
    have hconst : ∑ _i ∈ s, ENNReal.ofReal delta =
        (s.card : ℝ≥0∞) * ENNReal.ofReal delta := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : (s.card : ℝ≥0∞) * ENNReal.ofReal delta =
        ENNReal.ofReal (m * delta) := by
      rw [hm_def, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have harith : m * delta < eps := by
      rw [hdelta_def, ← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith
    calc thetaCapacity theta V (⋃ i ∈ s, G i)
        ≤ ∑ i ∈ s, thetaCapacity theta V (G i) := hsum
      _ ≤ ∑ _i ∈ s, ENNReal.ofReal delta := hbound
      _ = (s.card : ℝ≥0∞) * ENNReal.ofReal delta := hconst
      _ = ENNReal.ofReal (m * delta) := hcast
      _ < ENNReal.ofReal eps := (ENNReal.ofReal_lt_ofReal_iff heps).mpr harith
  · -- continuity off the union, glued along the subcover
    intro y hy
    obtain ⟨i, hiS, hyi⟩ : ∃ i ∈ s, y ∈ N i := by
      simpa using hs (mem_univ y)
    have hyG : y ∉ G i := fun hmem => hy (mem_biUnion hiS hmem)
    have h1 : ContinuousWithinAt (fun z => (w z).toReal) (N i \ G i) y :=
      hGcont i y ⟨hyi, hyG⟩
    have hsub : (⋃ j ∈ s, G j)ᶜ ∩ N i ⊆ N i \ G i := by
      rintro z ⟨hz, hzN⟩
      exact ⟨hzN, fun hmem => hz (mem_biUnion hiS hmem)⟩
    exact (continuousWithinAt_inter ((hNopen i).mem_nhds hyi)).mp (h1.mono hsub)

end

end Hironaka.ThetaCapacityQuasiContinuity

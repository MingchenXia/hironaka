import Hironaka.Analytic.PotentialTheory.GlobalPotentialsBasic
import Hironaka.Analytic.PotentialTheory.PshRegularDistribution

set_option autoImplicit false

/-!
# The identity principle for theta-PSH functions

`ThetaPlurisubharmonic` is the raw criterion: by design it is satisfied by the
germ that is identically `-∞`.  What rules that out globally is the classical
identity principle: a plurisubharmonic function on a *connected* domain which
is identically `-∞` on a nonempty open subset is identically `-∞`.  In the form
used here: a `θ`-PSH function on a connected manifold which is finite at a
single point has a pole set with empty interior, i.e. it is
`LocallyNondegenerate` and hence a genuine `θ`-PSH potential.

This is exactly what upgrades the unconditional decreasing-limit theorem of
`Hironaka.ThetaPshDecreasingLimit` — whose limit is allowed to be identically
`-∞` — to a genuine potential.

The proof is a clopen argument, not a chain of charts.  `P := interior {u = ⊥}`
is open by construction; its complement is open because of the *local*
dichotomy `PlurisubharmonicOn.ae_finite`: a PSH function on a preconnected
open set which is somewhere finite is finite almost everywhere there, so its
pole set is null and cannot contain a nonempty open set.
-/

open Set MeasureTheory Metric

namespace Hironaka.ThetaPshIdentityPrinciple



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The identity principle, in the form the workspace needs.**  On a
connected complex manifold a `θ`-PSH function which is finite at one point is
locally nondegenerate. -/
theorem locallyNondegenerate_of_exists_ne_bot [ConnectedSpace M]
    {theta : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic theta u) (hne : ∃ x : M, u x ≠ ⊥) :
    LocallyNondegenerate u := by
  have hPcompl : IsOpen (interior {x : M | u x = ⊥})ᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
    obtain ⟨W, rho, hzW, hrho, hpsh⟩ := hu (complexChartAt (n := n) x)
      ((complexChartAt (n := n) x).val x)
      ((complexChartAt (n := n) x).val.map_source hxs)
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hrho.1 _ hzW
    refine ⟨(complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹' ball ((complexChartAt (n := n) x).val x) r,
      ?_, (complexChartAt (n := n) x).val.isOpen_inter_preimage isOpen_ball,
      ⟨hxs, mem_ball_self hr⟩⟩
    -- the corrected chart representative is PSH on the ball
    have hvB : PlurisubharmonicOn
        (fun z => chartFunction u (complexChartAt (n := n) x) z + (rho z : EReal))
        (ball ((complexChartAt (n := n) x).val x) r) := fun z hz => hpsh z (hrW hz)
    -- it is somewhere finite there, because `x` is not an interior pole
    have hOsub : ¬ ((complexChartAt (n := n) x).val.source ∩
        (complexChartAt (n := n) x).val ⁻¹' ball ((complexChartAt (n := n) x).val x) r
        ⊆ {y : M | u y = ⊥}) := by
      intro hsub
      exact hx (mem_interior.mpr ⟨_, hsub,
        (complexChartAt (n := n) x).val.isOpen_inter_preimage isOpen_ball,
        ⟨hxs, mem_ball_self hr⟩⟩)
    obtain ⟨y, hyO, hy⟩ := not_subset.mp hOsub
    have hvne : ∃ z ∈ ball ((complexChartAt (n := n) x).val x) r,
        chartFunction u (complexChartAt (n := n) x) z + (rho z : EReal) ≠ ⊥ := by
      refine ⟨(complexChartAt (n := n) x).val y, hyO.2, ?_⟩
      have hval : chartFunction u (complexChartAt (n := n) x)
          ((complexChartAt (n := n) x).val y) = u y := by
        simp [chartFunction, (complexChartAt (n := n) x).val.left_inv hyO.1]
      rw [hval]
      intro hbot
      exact hy ((EReal.add_eq_bot_iff.mp hbot).resolve_right (EReal.coe_ne_bot _))
    have hae := hvB.ae_finite volume
      (convex_ball ((complexChartAt (n := n) x).val x) r).isPreconnected hvne
    have hnull : volume {z : ComplexModel n |
        ¬ (z ∈ ball ((complexChartAt (n := n) x).val x) r →
          chartFunction u (complexChartAt (n := n) x) z + (rho z : EReal) ≠ ⊤ ∧
          chartFunction u (complexChartAt (n := n) x) z + (rho z : EReal) ≠ ⊥)} = 0 :=
      ae_iff.mp ((ae_restrict_iff' measurableSet_ball).mp hae)
    -- no point of the ball can be an interior pole
    intro w hwO hwP
    obtain ⟨U, hUsub, hUopen, hwU⟩ := mem_interior.mp hwP
    have hVopen : IsOpen (((complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹' U) ∩
        ball ((complexChartAt (n := n) x).val x) r) :=
      ((complexChartAt (n := n) x).val.isOpen_inter_preimage_symm hUopen).inter isOpen_ball
    have hwV : (complexChartAt (n := n) x).val w ∈
        ((complexChartAt (n := n) x).val.target ∩
          (complexChartAt (n := n) x).val.symm ⁻¹' U) ∩
        ball ((complexChartAt (n := n) x).val x) r := by
      refine ⟨⟨(complexChartAt (n := n) x).val.map_source hwO.1, ?_⟩, hwO.2⟩
      change (complexChartAt (n := n) x).val.symm
        ((complexChartAt (n := n) x).val w) ∈ U
      rwa [(complexChartAt (n := n) x).val.left_inv hwO.1]
    have hVpos : 0 < volume (((complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹' U) ∩
        ball ((complexChartAt (n := n) x).val x) r) :=
      hVopen.measure_pos volume ⟨_, hwV⟩
    refine absurd (measure_mono_null ?_ hnull) hVpos.ne'
    rintro z ⟨⟨-, hzU⟩, hzB⟩ hcontra
    refine (hcontra hzB).2 ?_
    have hzbot : chartFunction u (complexChartAt (n := n) x) z = ⊥ := hUsub hzU
    rw [hzbot, EReal.bot_add]
  have hclopen : IsClopen (interior {x : M | u x = ⊥})ᶜ :=
    ⟨isOpen_interior.isClosed_compl, hPcompl⟩
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀mem : x₀ ∈ (interior {x : M | u x = ⊥})ᶜ := by
    simp only [mem_compl_iff]
    intro hmem
    have hbot : x₀ ∈ {x : M | u x = ⊥} :=
      interior_subset (s := {x : M | u x = ⊥}) hmem
    exact hx₀ hbot
  have huniv : (interior {x : M | u x = ⊥})ᶜ = univ :=
    hclopen.eq_univ ⟨x₀, hx₀mem⟩
  intro x U hU hxU
  by_contra hcon
  have hsub : U ⊆ {y : M | u y = ⊥} := by
    intro y hy
    by_contra hb
    exact hcon ⟨y, hy, hb⟩
  have hxP : x ∈ interior {y : M | u y = ⊥} :=
    mem_interior.mpr ⟨U, hsub, hU, hxU⟩
  have hxPc : x ∈ (interior {y : M | u y = ⊥})ᶜ := by rw [huniv]; trivial
  exact hxPc hxP

/-- The packaged form: a `θ`-PSH function on a connected manifold which is
finite somewhere is a genuine `θ`-PSH potential. -/
theorem isThetaPshPotential_of_exists_ne_bot [ConnectedSpace M]
    {theta : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic theta u) (hne : ∃ x : M, u x ≠ ⊥) :
    IsThetaPshPotential theta u :=
  ⟨hu, locallyNondegenerate_of_exists_ne_bot hu hne⟩

end

end Hironaka.ThetaPshIdentityPrinciple

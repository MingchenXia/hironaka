import Hironaka.Analytic.LocalPotentialIndependence
import Hironaka.Analytic.PshDiscLocalGlobal
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicLimits

set_option autoImplicit false

/-!
# Decreasing limits of theta-plurisubharmonic functions

A pointwise decreasing sequence of `θ`-PSH functions has a `θ`-PSH pointwise
infimum.  This is the manifold form of the local theorem
`DiscPshOn.plurisubharmonicOn_iInf_of_antitone`, and it is unconditional: the
limit is allowed to be identically `-∞`, exactly as in the local statement.

The one point needing care is that `ThetaPlurisubharmonic` supplies a
*different* local smooth potential `ρ_k` on a *different* neighbourhood `W_k`
for each member of the sequence, whereas the local decreasing-limit theorem
needs one common domain.  The fix uses only locality of plurisubharmonicity
and independence of the corrected test from the chosen potential
(`smoothLocalPotential_psh_iff`): the potential of the first member, on its own
neighbourhood `W`, already tests every member of the sequence on all of `W`.

`iInf_add_coe` is the infimum counterpart of `Hironaka.iSup_add_coe`.
-/

open Set

namespace Hironaka.ThetaPshDecreasingLimit

open Hironaka

noncomputable section

/-- Translation by a finite real value commutes with an arbitrary infimum in
`EReal`, including empty infima and values at either infinity. -/
theorem iInf_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, (f i + (c : EReal))) = (⨅ i, f i) + (c : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => add_le_add (iInf_le f i) le_rfl)
  have key : ∀ i, (⨅ j, (f j + (c : EReal))) + ((-c : ℝ) : EReal) ≤ f i := by
    intro i
    have h1 : (⨅ j, (f j + (c : EReal))) + ((-c : ℝ) : EReal)
        ≤ (f i + (c : EReal)) + ((-c : ℝ) : EReal) :=
      add_le_add (iInf_le (fun j => f j + (c : EReal)) i) le_rfl
    rwa [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] at h1
  have h3 := add_le_add (le_iInf key) (le_refl ((c : ℝ) : EReal))
  rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h3

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- One smooth local potential tests the whole sequence.  Plurisubharmonicity
is a local property, and the corrected test does not depend on which local
potential of `θ` is used, so the neighbourhood supplied for the first member
serves for every member. -/
theorem plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    {theta : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic theta u) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) :
    PlurisubharmonicOn (fun y => chartFunction u e y + (rho y : EReal)) W := by
  intro y hyW
  obtain ⟨Wk, rhok, hyWk, hrhok, hpk⟩ := hu e y (hrho.2.1 hyW)
  have hVopen : IsOpen (W ∩ Wk) := hrho.1.inter hrhok.1
  have hpV : PlurisubharmonicOn
      (fun y => chartFunction u e y + (rho y : EReal)) (W ∩ Wk) :=
    (_root_.Hironaka.smoothLocalPotential_psh_iff theta e (W ∩ Wk) rhok rho
      (hrhok.mono hVopen inter_subset_right) (hrho.mono hVopen inter_subset_left)
      (chartFunction u e)).1 (hpk.mono inter_subset_right)
  exact hpV y ⟨hyW, hyWk⟩

/-- **Decreasing limits of `θ`-PSH functions are `θ`-PSH.**  No nondegeneracy
is asserted: the infimum may be identically `-∞`, which is exactly the
dichotomy the local theorem leaves open. -/
theorem thetaPlurisubharmonic_iInf_of_antitone {theta : SmoothRealForm n M 2}
    {u : ℕ → M → EReal} (hu : ∀ k, ThetaPlurisubharmonic theta (u k))
    (hanti : ∀ x : M, Antitone fun k => u k x) :
    ThetaPlurisubharmonic theta (fun x => ⨅ k, u k x) := by
  intro e z hz
  obtain ⟨W, rho, hzW, hrho, -⟩ := hu 0 e z hz
  refine ⟨W, rho, hzW, hrho, ?_⟩
  have hdisc : ∀ k, DiscPshOn
      (fun y => chartFunction (u k) e y + (rho y : EReal)) W :=
    fun k => (plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      (hu k) e hrho).discPshOn
  have hantiW : ∀ y ∈ W,
      Antitone fun k => chartFunction (u k) e y + (rho y : EReal) := by
    intro y _ j k hjk
    exact add_le_add (hanti (e.val.symm y) hjk) le_rfl
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hrho.1 hdisc hantiW
  have heq : ∀ y : ComplexModel n, (⨅ k, (chartFunction (u k) e y + (rho y : EReal)))
      = chartFunction (fun x => ⨅ k, u k x) e y + (rho y : EReal) := by
    intro y
    rw [iInf_add_coe]
    rfl
  simpa only [heq] using hlim

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- An antitone family indexed by `Ioi (1 : ℝ)` has the same pointwise
infimum as the sequence it contains at the integer shifts `2 + k`. -/
theorem iInf_Ioi_eq_iInf_nat {eta : ℝ → M → EReal}
    (hanti : ∀ a b : ℝ, 1 < a → a ≤ b → eta b ≤ eta a) (x : M) :
    (⨅ a : Ioi (1 : ℝ), eta (a : ℝ) x) = ⨅ k : ℕ, eta (2 + (k : ℝ)) x := by
  refine le_antisymm (le_iInf fun k => ?_) (le_iInf fun a => ?_)
  · refine iInf_le (fun a : Ioi (1 : ℝ) => eta (a : ℝ) x) ⟨2 + (k : ℝ), ?_⟩
    simp only [mem_Ioi]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  · obtain ⟨k, hk⟩ := exists_nat_ge (a : ℝ)
    exact (iInf_le (fun k : ℕ => eta (2 + (k : ℝ)) x) k).trans
      (hanti (a : ℝ) (2 + (k : ℝ)) a.2 (by linarith) x)

end

end Hironaka.ThetaPshDecreasingLimit

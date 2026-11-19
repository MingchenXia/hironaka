import Hironaka.Resolution.HironakaG4ToricDivisorHistory

/-! Propagate a toric state on a carrier containing the test carrier. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG4ToricLargerCarrierHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter
  HironakaG4CoherentTowerActions HironakaG4CoherentGammaStep HironakaG4LocalToricDivisors
  HironakaG4ToricDivisorHistory

variable {n : ℕ} {X : CMfd.{u} n}

/-- A geometric test tower for a smaller carrier propagates the strong toric
state of a closed larger carrier, since every centre lies in its transform. -/
theorem localToricDivisorState_largerCarrier_geoTestTower {ι : Type v}
    (P : MarkedIdeal n X) (N : Set X) (D : ι → Set X)
    (hPN : P.N ⊆ N) (hNclosed : IsClosed N) (hDclosed : ∀ i, IsClosed (D i))
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (O : Opens (ComplexModel n)) (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    (s t : Fin n) (c : Fin n → ℕ) :
    let A := weightedScalings s t c
    let F : Filter A := 𝓝 (weightedIdentity s t c)
    let U : A → Opens X := fun a => scaleDomain Φ O a
    let V : A → Opens X := fun a => scaleDomain Φ O (invScale a)
    let φ := fun a : A => scaleDiffeo hΦsrc hOt a.2.1
    (∀ act : A → X → X, CoherentHistory U V φ (.refl : BlowupTower X X) act →
      ∀ x ∈ N, x ∈ flatDomain Φ → flatMap Φ x ∈ O →
        LocalToricDivisorState (n := n) F N D x act) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ (act : A → Y → Y), CoherentHistory U V φ T act →
      ∀ z ∈ strictAlong T N, T.proj z ∈ flatDomain Φ →
        flatMap Φ (T.proj z) ∈ O →
        LocalToricDivisorState (n := n) F (strictAlong T N) (trackedAlong D T) z act := by
  dsimp only
  intro hInit Y T
  induction T with
  | refl =>
    intro hTest act hAct z hz hwin hO
    exact hInit act hAct z hz hwin hO
  | @step Y Z T C π hπ ih =>
    intro hTest act' hAct z hz hwin hO
    have hprefix : IsGeoTestTower P T := hTest.1
    have hNpre : IsClosed (strictAlong T N) := MemberInterTowerAlong.isClosed_strictAlong T hNclosed
    have hzpre : π z ∈ strictAlong T N := by
      apply geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNpre
      exact hz
    have hC : C ⊆ strictAlong T N := by
      have hc := hTest.2.subset_N
      rw [N_geoTransformAlong] at hc
      exact hc.trans (MemberInterTowerAlong.strictAlong_mono T hPN)
    obtain ⟨act, hHist, hPres, hStep⟩ :=
      coherent_gamma_step_joint Φ hΦsrc O hOt s t c act' hAct hwin hO
    have hstate := ih hprefix act hHist (π z) hzpre hwin hO
    have hP : ∀ᶠ p in (𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 (π z),
        p.2 ∈ C → act p.1 p.2 ∈ C := hPres.mono fun _ h => h.2.mpr
    exact localToricDivisorState_step (𝓝 (weightedIdentity s t c)) hπ hNpre
      (trackedAlong_closed D hDclosed T) hC hz hstate hP
      (hStep.mono fun _ h => h.1) (hStep.mono fun _ h => h.2)

end
end Hironaka.HironakaG4ToricLargerCarrierHistory

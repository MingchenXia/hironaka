import Hironaka.Resolution.HironakaG4LocalToricDivisors
import Hironaka.Resolution.HironakaG4CoherentGammaStep
import Hironaka.Invariant.MemberInterTowerAlong

/-! Transverse toric divisor states along a coherent geometric test history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG4ToricDivisorHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34CoordinateScaling HironakaG4WeightedGammaParameter
  HironakaG4CoherentTowerActions HironakaG4CoherentGammaStep HironakaG4LocalToricDivisors

variable {n : ℕ} {X : CMfd.{u} n}

/-- An index for each initial member and each exceptional member born along a tower. -/
def TrackedIndex (ι : Type v) : {Y : CMfd.{u} n} → BlowupTower X Y → Type v
  | _, .refl => ι
  | _, .step T _ _ _ => TrackedIndex ι T ⊕ Unit

/-- Transform every old member and append the new exceptional member. -/
def trackedAlong {ι : Type v} (D : ι → Set X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → TrackedIndex ι T → Set Y
  | _, .refl => D
  | _, .step T C π _ => Sum.elim (fun i => geoStrictTransform π C (trackedAlong D T i))
      (fun _ => π ⁻¹' C)

theorem trackedAlong_closed {ι : Type v} (D : ι → Set X) (hD : ∀ i, IsClosed (D i)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) i, IsClosed (trackedAlong D T i)
  | _, .refl, i => hD i
  | _, .step T C π hπ, i => by
    change TrackedIndex ι T ⊕ Unit at i
    cases i with
    | inl i => exact isClosed_closure
    | inr i => exact hπ.1.1.preimage hπ.contMDiff.continuous

/-- The same coherent actions propagate distinct transverse divisor coordinates
at every strict-carrier point over the initial weighted chart. -/
theorem localToricDivisorState_geoTestTower {ι : Type v}
    (P : MarkedIdeal n X) (D : ι → Set X) (hNclosed : IsClosed P.N)
    (hDclosed : ∀ i, IsClosed (D i))
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
      ∀ x ∈ P.N, x ∈ flatDomain Φ → flatMap Φ x ∈ O →
        LocalToricDivisorState (n := n) F P.N D x act) →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      ∀ (act : A → Y → Y), CoherentHistory U V φ T act →
      ∀ z ∈ (geoTransformAlong P T).N, T.proj z ∈ flatDomain Φ →
        flatMap Φ (T.proj z) ∈ O →
        LocalToricDivisorState (n := n) F (geoTransformAlong P T).N (trackedAlong D T) z act := by
  dsimp only
  intro hInit Y T
  induction T with
  | refl =>
    intro hTest act hAct z hz hwin hO
    exact hInit act hAct z hz hwin hO
  | @step Y Z T C π hπ ih =>
    intro hTest act' hAct z hz hwin hO
    have hprefix : IsGeoTestTower P T := hTest.1
    have hNpre : IsClosed (geoTransformAlong P T).N := by
      rw [N_geoTransformAlong]
      exact MemberInterTowerAlong.isClosed_strictAlong T hNclosed
    have hzpre : π z ∈ (geoTransformAlong P T).N := by
      apply geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNpre
      exact hz
    have hC : C ⊆ (geoTransformAlong P T).N := hTest.2.subset_N
    obtain ⟨act, hHist, hPres, hStep⟩ :=
      coherent_gamma_step_joint Φ hΦsrc O hOt s t c act' hAct hwin hO
    have hstate := ih hprefix act hHist (π z) hzpre hwin hO
    have hP : ∀ᶠ p in (𝓝 (weightedIdentity s t c)) ×ˢ 𝓝 (π z),
        p.2 ∈ C → act p.1 p.2 ∈ C := hPres.mono fun _ h => h.2.mpr
    exact localToricDivisorState_step (𝓝 (weightedIdentity s t c)) hπ hNpre
      (trackedAlong_closed D hDclosed T) hC hz hstate hP
      (hStep.mono fun _ h => h.1) (hStep.mono fun _ h => h.2)

end
end Hironaka.HironakaG4ToricDivisorHistory

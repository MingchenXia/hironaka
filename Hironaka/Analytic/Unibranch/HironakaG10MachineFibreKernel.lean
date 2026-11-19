import Hironaka.Analytic.Unibranch.HironakaG10PNStepKernel
import Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds

/-! Coherence of the entire original fibre kernels for actual stateful
centre-machine sequences. No fixed rule on geometric stages is assumed. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel
open Hironaka
  HironakaG10PNIdealFamily HironakaG10PNPointIdeal HironakaG10PNKernelFamily
  HironakaG10ChowStrictTransformCalculus HironakaG10ChowSequenceFibreChain
  HironakaG10ChowFibreAlgebra HironakaG10ChowFlatteningDriver
  HironakaG10ChowOneStepStrictTransform HironakaG10ChowCentreMachine
  HironakaG10ChowFlatteningReduction HironakaG10ChowTowerDomination
  HironakaG10ChowFlatBimeromorphicIso HironakaG10PNStepKernel
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealFiniteType

noncomputable section

section Sequence
variable (F : FlatteningSequence)

/-- The whole one-step kernel at a point of the next base. -/
def sequenceStepKernel (n : ℕ) (x' : (F.X (n + 1)).obj.left) :
    ∀ y : (F.Y n).obj.left, Ideal ((F.Y n).obj.left.presheaf.stalk y) :=
  kerFamily (F.q n).hom.left
    (pullFamily (F.f (n + 1)).hom.left (pointFamily (F.X (n + 1)).obj.left x'))

/-- Exact equality with the original whole fibre-kernel family. -/
theorem fibreKernel_eq_kerFamily (z : ∀ n, (F.X n).obj.left) (n : ℕ) :
    fibreKernel F z n = kerFamily (F.strict n).hom.left
      (pullFamily (F.f n).hom.left (pointFamily (F.X n).obj.left (z n))) := by
  funext y
  refine iInf_congr fun yn => iInf_congr fun h => ?_
  by_cases hf : (F.f n).hom.left.base yn = z n
  · rw [iInf_pos hf]
    congr 1
    rw [← hf]
    exact (pullFamily_pointFamily_self _ yn).symm
  · rw [iInf_neg hf, pullFamily_pointFamily_of_ne _ hf, Ideal.comap_top]

theorem strict_isProperMap (hproper : ∀ n, IsProperMap (F.q n).hom.left.base) :
    ∀ n, IsProperMap (F.strict n).hom.left.base
  | 0 => isProperMap_id
  | n + 1 => (strict_isProperMap hproper n).comp (hproper n)

theorem pullFamily_le_sequenceStepKernel (n : ℕ) (x' : (F.X (n + 1)).obj.left)
    (y : (F.Y n).obj.left) :
    pullFamily (F.f n).hom.left (pointFamily (F.X n).obj.left ((F.σ n).hom.left.base x')) y ≤
      sequenceStepKernel F n x' y := by
  intro g hg
  rw [sequenceStepKernel, mem_kerFamily_iff]
  intro y' hy'
  subst hy'
  simp only [eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply]
  by_cases hf' : (F.f (n + 1)).hom.left.base y' = x'
  · have hfx : (F.f n).hom.left.base ((F.q n).hom.left.base y') =
        (F.σ n).hom.left.base x' :=
      (step_comm_apply F n y').symm.trans (congrArg (F.σ n).hom.left.base hf')
    rw [← hfx, pullFamily_pointFamily_self] at hg
    rw [← hf', pullFamily_pointFamily_self]
    exact map_fibreIdealAt_le F n y' (Ideal.mem_map_of_mem _ hg)
  · rw [pullFamily_pointFamily_of_ne _ hf']
    exact Submodule.mem_top

/-- The kernel-transfer induction uses only the actual sequence maps. -/
theorem isLocallyFinitelyGenerated_kerFamily_chain
    (hproper : ∀ n, IsProperMap (F.q n).hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective F n)
    (hstep : ∀ n (x' : (F.X (n + 1)).obj.left),
      IsLocallyFinitelyGenerated (F.Y n).obj.left (sequenceStepKernel F n x')) :
    ∀ (n : ℕ) (x : (F.X n).obj.left),
      IsLocallyFinitelyGenerated (F.Y 0).obj.left
        (kerFamily (F.strict n).hom.left
          (pullFamily (F.f n).hom.left (pointFamily (F.X n).obj.left x)))
  | 0, x => by
    have := HironakaG10PNFibreKernel.t1Space (F.X 0)
    change IsLocallyFinitelyGenerated _ (kerFamily (𝟙 (F.Y 0).obj.left) _)
    rw [kerFamily_id]
    exact isLocallyFinitelyGenerated_fibreFamily
      (HironakaG10PNSourceNoether.hasAnalyticModelCharts _) _ _
  | n + 1, x' => by
    have := HironakaG10PNFibreKernel.t1Space (F.X n)
    let x : (F.X n).obj.left := (F.σ n).hom.left.base x'
    let S : Set (F.Y n).obj.left := (F.f n).hom.left.base ⁻¹' {x}
    have hS : IsClosed S :=
      IsClosed.preimage (F.f n).hom.left.base.hom.continuous
        ((HironakaG10PNFibreKernel.t1Space (F.X n)).t1 x)
    have hinj : Set.InjOn (F.strict n).hom.left.base S := fun a ha c hc hac =>
      strict_injective n a c ((show (F.f n).hom.left.base a = x from ha).trans
        (show (F.f n).hom.left.base c = x from hc).symm) hac
    have hPS : ∀ y, y ∉ S → pullFamily (F.f n).hom.left (pointFamily _ x) y = ⊤ :=
      fun y hy => pullFamily_pointFamily_of_ne _ hy
    have hsurj' : ∀ y ∈ S, ∀ b : (F.Y n).obj.left.presheaf.stalk y,
        ∃ a : (F.Y 0).obj.left.presheaf.stalk ((F.strict n).hom.left.base y),
          b - ((F.strict n).hom.left.stalkMap y).hom a ∈
            pullFamily (F.f n).hom.left (pointFamily _ x) y := by
      intro y hy b
      obtain ⟨a, ha⟩ := exists_sub_mem_chain hsurj n y b
      refine ⟨a, ?_⟩
      rw [show x = (F.f n).hom.left.base y from
        (show (F.f n).hom.left.base y = x from hy).symm, pullFamily_pointFamily_self]
      exact ha
    have hmain := isLocallyFinitelyGenerated_kerFamily (F.strict n).hom.left
      (strict_isProperMap F hproper n).isClosedMap S hS hinj
      (pullFamily (F.f n).hom.left (pointFamily _ x)) (sequenceStepKernel F n x') hPS
      (pullFamily_le_sequenceStepKernel F n x') hsurj'
      (isLocallyFinitelyGenerated_fibreFamily
        (HironakaG10PNSourceNoether.hasAnalyticModelCharts _) _ _)
      (hstep n x') (isLocallyFinitelyGenerated_kerFamily_chain hproper hsurj hstep n x)
    change IsLocallyFinitelyGenerated _
      (kerFamily ((F.q n).hom.left ≫ (F.strict n).hom.left)
        (pullFamily (F.f (n + 1)).hom.left (pointFamily (F.X (n + 1)).obj.left x')))
    rw [kerFamily_comp]
    exact hmain

theorem isLocallyFinitelyGenerated_fibreKernel
    (hproper : ∀ n, IsProperMap (F.q n).hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective F n)
    (hstep : ∀ n (x' : (F.X (n + 1)).obj.left),
      IsLocallyFinitelyGenerated (F.Y n).obj.left (sequenceStepKernel F n x')) :
    ∀ (z : ∀ n, (F.X n).obj.left) n,
      IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n) := by
  intro z n
  rw [fibreKernel_eq_kerFamily]
  exact isLocallyFinitelyGenerated_kerFamily_chain F hproper hsurj hstep n (z n)

end Sequence

section Machine
variable (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
  (hf : IsProperMap s₀.f.hom.left.base)

/-- Properness of the actual source blowup projection, rather than the family map. -/
theorem machine_stepQ_isProperMap (n : ℕ) :
    IsProperMap ((toFlatteningSequence M s₀ d₀ hf).q n).hom.left.base := by
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  let _ : (nativePulledIdealModule (run M s₀ d₀ n).1.f.hom.left c.B c.b).IsFiniteType :=
    nativePulledIdealModule_isFiniteType (run M s₀ d₀ n).1.f.hom.left c.B c.b
  exact OriginalFiniteIdealGeometricBlowup.projection_isProperMap
    (nativePulledIdealModule (run M s₀ d₀ n).1.f.hom.left c.B c.b)
    (nativePulledIdealInclusion (run M s₀ d₀ n).1.f.hom.left c.B c.b)

/-- One-step coherence for the actual centre selected from the machine state. -/
theorem machine_stepKernelCoherent (n : ℕ)
    (x' : ((toFlatteningSequence M s₀ d₀ hf).X (n + 1)).obj.left) :
    IsLocallyFinitelyGenerated ((toFlatteningSequence M s₀ d₀ hf).Y n).obj.left
      (sequenceStepKernel (toFlatteningSequence M s₀ d₀ hf) n x') := by
  let F := toFlatteningSequence M s₀ d₀ hf
  have hT1 := HironakaG10PNFibreKernel.t1Space (F.X (n + 1))
  have hK : IsLocallyFinitelyGenerated _ (pullFamily (F.f (n + 1)).hom.left
      (pointFamily (F.X (n + 1)).obj.left x')) :=
    isLocallyFinitelyGenerated_fibreFamily (HironakaG10PNSourceNoether.hasAnalyticModelCharts _) _ _
  have hne : ∀ y', pullFamily (F.f (n + 1)).hom.left
      (pointFamily (F.X (n + 1)).obj.left x') y' ≠ ⊤ →
        (F.f (n + 1)).hom.left.base y' = x' := by
    intro y' h
    by_contra h'
    exact h (pullFamily_pointFamily_of_ne _ h')
  have hsurj : ∀ y', pullFamily (F.f (n + 1)).hom.left
      (pointFamily (F.X (n + 1)).obj.left x') y' ≠ ⊤ →
      ∀ β : (F.Y (n + 1)).obj.left.presheaf.stalk y',
        ∃ a : (F.Y n).obj.left.presheaf.stalk ((F.q n).hom.left.base y'),
          β - ((F.q n).hom.left.stalkMap y').hom a ∈ pullFamily
            (F.f (n + 1)).hom.left (pointFamily (F.X (n + 1)).obj.left x') y' := by
    intro y' hy' β
    obtain ⟨a, ha⟩ := machine_stepFibreSurjective M s₀ d₀ hf n y' β
    refine ⟨a, ?_⟩
    rw [← hne y' hy', pullFamily_pointFamily_self]
    exact ha
  have hinj : ∀ a c, pullFamily (F.f (n + 1)).hom.left
      (pointFamily (F.X (n + 1)).obj.left x') a ≠ ⊤ →
      pullFamily (F.f (n + 1)).hom.left
        (pointFamily (F.X (n + 1)).obj.left x') c ≠ ⊤ →
      (F.q n).hom.left.base a = (F.q n).hom.left.base c → a = c :=
    fun a c ha hc hq => (F.data n).strict.pair_injective a c
      ((hne a ha).trans (hne c hc).symm) hq
  have hclosed : IsClosedMap (F.q n).hom.left.base :=
    (machine_stepQ_isProperMap M s₀ d₀ hf n).isClosedMap
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  by_cases hE : (F.σ n).hom.left.base x' ∈ EmbeddedIdealBlowupNonunitLocus.nonunitLocus c.B c.b
  · refine isLocallyFinitelyGenerated_kerFamily_strictQ c.B c.b (run M s₀ d₀ n).1.f
      _ hK hinj ?_ hsurj
    intro y' hy'
    by_contra h
    apply (mem_pulledUnitLocus_iff c.B c.b (run M s₀ d₀ n).1.f _).mp h
    have hp : (strictP c.B c.b c.dense (run M s₀ d₀ n).1.f).hom.left.base y' = x' := hne y' hy'
    rw [← strictP_comp_apply c.B c.b c.dense (run M s₀ d₀ n).1.f y', hp]
    exact hE
  · obtain ⟨V, jV, hjV, hrange, hjVQ⟩ := strict_openImmersionOn c.B c.b c.dense (run M s₀ d₀ n).1.f
    refine isLocallyFinitelyGenerated_kerFamily_of_openImmersionOn _ hclosed _ hK jV hjV hjVQ ?_
    intro y' hy'
    have hp : (strictP c.B c.b c.dense (run M s₀ d₀ n).1.f).hom.left.base y' = x' := hne y' hy'
    have h5 : y' ∈ (strictP c.B c.b c.dense (run M s₀ d₀ n).1.f).hom.left.base ⁻¹'
        (stepExcep c.B c.b c.dense)ᶜ := by
      show (stepProj c.B c.b c.dense).hom.left.base
        ((strictP c.B c.b c.dense (run M s₀ d₀ n).1.f).hom.left.base y') ∉
          EmbeddedIdealBlowupNonunitLocus.nonunitLocus c.B c.b
      rw [hp]
      exact hE
    exact (Set.ext_iff.mp hrange y').mpr h5

/-- Every whole original fibre kernel of every centre-machine run is coherent. -/
theorem machine_fibreKernel_isLocallyFinitelyGenerated :
    ∀ (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence M s₀ d₀ hf).Y 0).obj.left
        (fibreKernel (toFlatteningSequence M s₀ d₀ hf) z n) :=
  isLocallyFinitelyGenerated_fibreKernel (toFlatteningSequence M s₀ d₀ hf)
    (machine_stepQ_isProperMap M s₀ d₀ hf)
    (machine_stepFibreSurjective M s₀ d₀ hf)
    (machine_stepKernelCoherent M s₀ d₀ hf)

end Machine

/-- Round-data termination with the actual coherent-kernel input discharged. -/
theorem exists_flattening_of_roundData (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base) (R : HironakaG10ChowLeavingRounds.RoundData s₀ hf)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence R.M s₀ R.d₀ hf).nonflatImage n)) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  HironakaG10ChowLeavingRounds.exists_flattening_of_roundData s₀ hX hf R hclosed
    (machine_fibreKernel_isLocallyFinitelyGenerated R.M s₀ R.d₀ hf)

end
end Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel

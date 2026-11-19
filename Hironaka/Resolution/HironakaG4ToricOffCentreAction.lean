import Hironaka.Resolution.HironakaG4ToricOffCentreChart
import Hironaka.Resolution.HironakaG34ToricCharts

/-!
# Transport of the actual diagonal action off a blowup centre

Off the centre the blowup has a holomorphic inverse. Commutation with the
actual lifted maps forces their images into the retained local chart near the
point; no continuity in the parameter or of the lifted maps is assumed.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricOffCentreAction
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupStrictSubmanifold
  NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricOffCentreChart BlowupIsomorphismOff HironakaNormalCrossingsDiagonalLiftOrbits

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {z : Y}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- The lifted maps converge jointly to the point off the centre, because
the base maps do and the blowup has a continuous inverse there. -/
theorem tendsto_lifted_action_off_centre (hπ : IsBlowupAlong n C π) (hz : π z ∉ C)
    {A : Type*} {F : Filter A} {act : A → X → X} {act' : A → Y → Y}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2)) :
    Tendsto (fun p : A × Y => act' p.1 p.2) (F ×ˢ 𝓝 z) (𝓝 z) := by
  classical
  have hπcont := hπ.contMDiff.continuous.continuousAt (x := z)
  have hΦcont := (continuousOn_flatMap Φ).continuousAt
    ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ))
  have hinput : Tendsto (fun p : A × Y => (p.1, π p.2))
      (F ×ˢ 𝓝 z) (F ×ˢ 𝓝 (π z)) := tendsto_fst.prodMk (hπcont.tendsto.comp tendsto_snd)
  have hdiag' := hinput.eventually hdiag
  have hcoord : Tendsto (fun p : A × Y => diagonal (μ p.1) (flatMap Φ (π p.2)))
      (F ×ˢ 𝓝 z) (𝓝 (flatMap Φ (π z))) := by
    have h := (continuous_diagonal_prod.tendsto (1, flatMap Φ (π z))).comp
      ((hμ.comp tendsto_fst).prodMk_nhds ((hΦcont.tendsto.comp hπcont.tendsto).comp tendsto_snd))
    rwa [diagonal_one] at h
  have hbase : Tendsto (fun p : A × Y => act p.1 (π p.2)) (F ×ˢ 𝓝 z) (𝓝 (π z)) := by
    have hinv := (tendsto_flatInverse Φ (mem_flatDomain_self Φ)).comp hcoord
    apply hinv.congr'
    filter_upwards [hdiag'] with p hp
    change (chartAt (ComplexModel n) (π z)).symm
      (Φ.invFun (diagonal (μ p.1) (flatMap Φ (π p.2)))) = act p.1 (π p.2)
    rw [← hp.2.2]
    exact flatInverse_flat Φ hp.2.1
  have hproj : Tendsto (fun p : A × Y => π (act' p.1 p.2)) (F ×ˢ 𝓝 z) (𝓝 (π z)) :=
    hbase.congr' (hcomm.mono fun _ hp => hp.symm)
  obtain ⟨s, hs, hsπ, hsec⟩ := exists_section_compl hπ
  let inv : X → Y := fun x => if hx : x ∈ Cᶜ then s ⟨x, hx⟩ else z
  have hinv : ∀ p : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X), inv p = s p := by
    rintro ⟨x, hx⟩
    change (if h : x ∈ Cᶜ then s ⟨x, h⟩ else z) = s ⟨x, hx⟩
    have hx' : x ∈ Cᶜ := hx
    rw [dif_pos hx']
  have hinvcont : ContinuousAt inv (π z) := by
    have hcomp : ContinuousAt (inv ∘ (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) → X)) ⟨π z,hz⟩ := by
      have heq : inv ∘ (Subtype.val : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) → X) = s := funext hinv
      rw [heq]
      exact hs.continuous.continuousAt
    exact hπ.1.1.isOpen_compl.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hcomp
  have hinvz : inv (π z) = z := by
    rw [hinv ⟨π z,hz⟩]
    exact hsec z hz
  have hoff : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) ∈ Cᶜ :=
    hproj.eventually (hπ.1.1.isOpen_compl.mem_nhds hz)
  have hι : Tendsto (fun p : A × Y => inv (π (act' p.1 p.2))) (F ×ˢ 𝓝 z) (𝓝 z) := by
    simpa only [hinvz, Function.comp_def] using hinvcont.tendsto.comp hproj
  apply hι.congr'
  filter_upwards [hoff] with p hp
  rw [hinv ⟨π (act' p.1 p.2), hp⟩, hsec]

/-- The actual lifted action is diagonal in the retained uncentred chart
off the blowup centre. -/
theorem exists_diagonal_off_centre_chart (hπ : IsBlowupAlong n C π) (hz : π z ∉ C)
    {A : Type*} {F : Filter A} {act : A → X → X} {act' : A → Y → Y}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2)) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      (∀ u ∈ flatDomain Ψ, π u ∉ C ∧ π u ∈ flatDomain Φ ∧ flatMap Ψ u = flatMap Φ (π u)) ∧
      ActsDiagonallyNear F act' μ Ψ z := by
  obtain ⟨Ψ, hΨsrc, hcoords⟩ := exists_uncentred_off_centre_chart hπ hz Φ
  have hact := tendsto_lifted_action_off_centre hπ hz hμ hdiag hcomm
  have hinput : Tendsto (fun p : A × Y => (p.1, π p.2))
      (F ×ˢ 𝓝 z) (F ×ˢ 𝓝 (π z)) :=
    tendsto_fst.prodMk (hπ.contMDiff.continuous.continuousAt.tendsto.comp tendsto_snd)
  have hdiag' := hinput.eventually hdiag
  have hsource : ∀ᶠ p in F ×ˢ 𝓝 z, p.2 ∈ flatDomain Ψ :=
    tendsto_snd.eventually ((isOpen_flatDomain Ψ).mem_nhds (mem_flatDomain_self Ψ))
  have htarget : ∀ᶠ p in F ×ˢ 𝓝 z, act' p.1 p.2 ∈ flatDomain Ψ :=
    hact.eventually ((isOpen_flatDomain Ψ).mem_nhds (mem_flatDomain_self Ψ))
  refine ⟨Ψ, hΨsrc, hcoords, ?_⟩
  filter_upwards [hsource, htarget, hdiag', hcomm] with p hp hp' hd hc
  refine ⟨hp, hp', ?_⟩
  rw [(hcoords _ hp').2.2, hc, hd.2.2, ← (hcoords _ hp).2.2]

end
end Hironaka.HironakaG4ToricOffCentreAction

import Hironaka.Resolution.HironakaG1FixedReaderBoundaryUnits

/-! Paired actual extensions of all complementary coordinates of a fixed reader. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1FixedReaderComplementExtensions
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaG1RelativeBoundaryUnitsOnGraph HironakaG1FixedReaderBoundaryUnits
  HironakaG1SNCReaderNormalization

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}

/-- A local scalar function in the actual target ambient manifold has a
holomorphic ambient representative of its intrinsic pullback near the source
anchor. The actual source quotient stalk determines the germ. -/
theorem exists_holomorphic_ambient_graph_extension
    {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) {g : N → ℂ} (hg : HolomorphicAt m g (e.base p).val) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f p.val),
      (actualSubspaceInclusion (n := n) C).stalkMap p (actualOriginalFunctionGerm p.val f hf) =
        e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
          (actualOriginalFunctionGerm (e.base p).val g hg)) ∧
      ∀ᶠ x : C in 𝓝 p, f x.val = g (e.base x).val := by
  obtain ⟨r, hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C p
    (e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
          (actualOriginalFunctionGerm (e.base p).val g hg)))
  obtain ⟨U, hpU, s, hs⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  let f := sectionExtension U s
  have hf : HolomorphicAt n f p.val := sectionExtension_holomorphicAt U s p.val hpU
  have hR := (actualOriginalFunctionGerm_eq_section U p.val hpU s f hf EventuallyEq.rfl).trans hs
  have heq := (congrArg ((actualSubspaceInclusion (n := n) C).stalkMap p) hR).trans hr
  exact ⟨f, hf, heq, original_germ_relation_on_graph e he p hf hg heq⟩

/-- Finite coordinate families extend simultaneously to one source ambient
open, inside any prescribed source window. -/
theorem simultaneous_holomorphic_graph_extensions
    {ι : Type} [Finite ι] {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) (g : ι → N → ℂ) (hg : ∀ i, HolomorphicAt m (g i) (e.base p).val)
    (U₀ : Opens M) (hp : p.val ∈ U₀) :
    ∃ (U : Opens M) (f : ι → M → ℂ),
      p.val ∈ U ∧ U ≤ U₀ ∧
      (∀ x ∈ U, ∀ i, HolomorphicAt n (f i) x) ∧
      ∀ x : C, x.val ∈ U → ∀ i, f i x.val = g i (e.base x).val := by
  classical
  choose f hf _ hGraph using fun i => exists_holomorphic_ambient_graph_extension e he p (hg i)
  have hNear := Filter.eventually_all.mpr hGraph
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at hNear
  have hHol := Filter.eventually_all.mpr (fun i => (hf i).eventually)
  obtain ⟨S, hS, hOpen, hpS⟩ := mem_nhds_iff.mp (hHol.and (hNear.and (U₀.isOpen.mem_nhds hp)))
  exact ⟨⟨S, hOpen⟩, f, hpS, fun _ hx => (hS hx).2.2,
    fun _ hx => (hS hx).1, fun x hx => (hS hx).2.1 x rfl⟩

/-- Shrink arbitrary ambient windows on both sides so their carrier
traces correspond exactly under the intrinsic isomorphism. -/
theorem paired_ambient_subwindows
    {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (p : C) (U₀ : Opens M) (V₀ : Opens N)
    (hpU : p.val ∈ U₀) (hpV : (e.hom.base p).val ∈ V₀) :
    ∃ (U : Opens M) (V : Opens N),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧ U ≤ U₀ ∧ V ≤ V₀ ∧
      (∀ x : C, x.val ∈ U ↔ (e.hom.base x).val ∈ V) ∧
      (∀ y : D, y.val ∈ V ↔ (e.inv.base y).val ∈ U) := by
  have hleft (x : C) : e.inv.base (e.hom.base x) = x :=
    congrArg (fun h => h.base x) e.hom_inv_id
  have hright (y : D) : e.hom.base (e.inv.base y) = y :=
    congrArg (fun h => h.base y) e.inv_hom_id
  let A : Set C := (fun x : C => (e.hom.base x).val) ⁻¹' (V₀ : Set N)
  let B : Set D := (fun y : D => (e.inv.base y).val) ⁻¹' (U₀ : Set M)
  have hA : IsOpen A := V₀.isOpen.preimage (continuous_subtype_val.comp e.hom.base.hom.continuous)
  have hB : IsOpen B := U₀.isOpen.preimage (continuous_subtype_val.comp e.inv.base.hom.continuous)
  obtain ⟨A₀, hA₀, hEqA⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hA
  obtain ⟨B₀, hB₀, hEqB⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hB
  let U : Opens M := U₀ ⊓ ⟨A₀, hA₀⟩
  let V : Opens N := V₀ ⊓ ⟨B₀, hB₀⟩
  have hAu (x : C) : x.val ∈ A₀ ↔ (e.hom.base x).val ∈ V₀ :=
    Set.ext_iff.mp hEqA x
  have hBu (y : D) : y.val ∈ B₀ ↔ (e.inv.base y).val ∈ U₀ :=
    Set.ext_iff.mp hEqB y
  refine ⟨U, V, ⟨hpU, (hAu p).mpr hpV⟩, ⟨hpV, (hBu _).mpr (by rwa [hleft])⟩,
    inf_le_left, inf_le_left, ?_, ?_⟩
  · intro x
    change x.val ∈ U₀ ∧ x.val ∈ A₀ ↔ (e.hom.base x).val ∈ V₀ ∧ (e.hom.base x).val ∈ B₀
    rw [hAu, hBu, hleft, and_comm]
  · intro y
    change y.val ∈ V₀ ∧ y.val ∈ B₀ ↔ (e.inv.base y).val ∈ U₀ ∧ (e.inv.base y).val ∈ A₀
    rw [hBu, hAu, hright, and_comm]

variable {C : Set M} {D : Set N}
  (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
  (p : C) {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p.val (e.hom.base p).val E F τ)

/-- The exact source complement coordinates of the fixed relative reader. -/
def sourceComplement (i : Fin R.a) : M → ℂ :=
  flatCoord R.Φ₁ (R.σ₁ (i.natAdd R.r))

/-- The exact target complement coordinates of the fixed relative reader. -/
def targetComplement (i : Fin R.b) : N → ℂ :=
  flatCoord R.Φ₂ (R.σ₂ (i.natAdd R.r))

theorem sourceComplement_eq_normalized (x : readerSource R.Φ₁) (i : Fin R.a) :
    sourceComplement e p R i x.val = (R.sourceDiffeomorph x).val (i.natAdd R.r) := rfl

theorem targetComplement_eq_normalized (y : readerSource R.Φ₂) (i : Fin R.b) :
    targetComplement e p R i y.val = (R.targetDiffeomorph y).val (i.natAdd R.r) := rfl

private theorem complement_smooth {d : ℕ} {U : Opens M} {a : Fin d → M → ℂ}
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞
      (fun z => (EuclideanSpace.equiv (Fin d) ℂ).symm (fun i => a i z)) U := by
  intro z hz
  have hp : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, Fin d → ℂ) ∞
      (fun z => fun i => a i z) z :=
    contMDiffAt_pi_space.mpr fun i => contMDiffAt_of_eventually_mdifferentiableAt (ha z hz i)
  exact ((EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap.contMDiffAt.comp z hp).contMDiffWithinAt

set_option maxHeartbeats 550000 in
/-- All normalized complement coordinates extend holomorphically in both
directions on paired subwindows of any given reader windows. Thus all ratio
identities already valid on the input windows restrict to the output windows. -/
theorem paired_reader_complement_extensions
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (U₀ : Opens M) (V₀ : Opens N) (hpU : p.val ∈ U₀) (hpV : (e.hom.base p).val ∈ V₀)
    (hU₀ : (U₀ : Set M) ⊆ flatDomain R.Φ₁) (hV₀ : (V₀ : Set N) ⊆ flatDomain R.Φ₂) :
    ∃ (U : Opens M) (V : Opens N) (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧ U ≤ U₀ ∧ V ≤ V₀ ∧
      (U : Set M) ⊆ flatDomain R.Φ₁ ∧ (V : Set N) ⊆ flatDomain R.Φ₂ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel R.b) ∞ forward U ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel R.a) ∞ backward V ∧
      forward p.val = 0 ∧ backward (e.hom.base p).val = 0 ∧
      (∀ x : C, x.val ∈ U ↔ (e.hom.base x).val ∈ V) ∧
      (∀ y : D, y.val ∈ V ↔ (e.inv.base y).val ∈ U) ∧
      (∀ x : C, x.val ∈ U → ∀ i, forward x.val i = targetComplement e p R i (e.hom.base x).val) ∧
      ∀ y : D, y.val ∈ V → ∀ i, backward y.val i = sourceComplement e p R i (e.inv.base y).val := by
  let p' := e.hom.base p
  have hpoint : e.inv ≫ subspacePointMap (n := n) C = subspacePointMap (n := m) D := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hleft : e.inv.base p' = p := congrArg (fun h => h.base p) e.hom_inv_id
  have ht (i : Fin R.b) : HolomorphicAt m (targetComplement e p R i) p'.val :=
    holomorphicAt_flatCoord R.Φ₂ _ (mem_flatDomain_self R.Φ₂)
  have hs (i : Fin R.a) : HolomorphicAt n (sourceComplement e p R i) (e.inv.base p').val := by
    rw [hleft]
    exact holomorphicAt_flatCoord R.Φ₁ _ (mem_flatDomain_self R.Φ₁)
  obtain ⟨U₁, af, hUp, hU, ha, hGraph⟩ :=
    simultaneous_holomorphic_graph_extensions e.hom he p (targetComplement e p R) ht U₀ hpU
  obtain ⟨V₁, bf, hVp, hV, hb, hGraph'⟩ :=
    simultaneous_holomorphic_graph_extensions e.inv hpoint p' (sourceComplement e p R) hs V₀ hpV
  obtain ⟨U, V, hp, hp', hu, hv, hPair, hPair'⟩ := paired_ambient_subwindows e p U₁ V₁ hUp hVp
  let forward (x : M) : ComplexModel R.b :=
    (EuclideanSpace.equiv (Fin R.b) ℂ).symm (fun i => af i x)
  let backward (y : N) : ComplexModel R.a :=
    (EuclideanSpace.equiv (Fin R.a) ℂ).symm (fun i => bf i y)
  have hforward (x : C) (hx : x.val ∈ U) (i : Fin R.b) :
      forward x.val i = targetComplement e p R i (e.hom.base x).val :=
    hGraph x (hu hx) i
  have hbackward (y : D) (hy : y.val ∈ V) (i : Fin R.a) :
      backward y.val i = sourceComplement e p R i (e.inv.base y).val :=
    hGraph' y (hv hy) i
  have hf₀ : forward p.val = 0 := by
    ext i
    rw [hforward p hp i]
    change R.Φ₂.toFun (chartAt (ComplexModel m) p'.val p'.val) (R.σ₂ (i.natAdd R.r)) = 0
    rw [R.zero₂]
    rfl
  have hb₀ : backward p'.val = 0 := by
    ext i
    rw [hbackward p' hp' i, hleft]
    change R.Φ₁.toFun (chartAt (ComplexModel n) p.val p.val) (R.σ₁ (i.natAdd R.r)) = 0
    rw [R.zero₁]
    rfl
  exact ⟨U, V, forward, backward, hp, hp', hu.trans hU, hv.trans hV,
    fun _ hx => hU₀ (hU (hu hx)), fun _ hy => hV₀ (hV (hv hy)),
    complement_smooth (fun x hx => ha x (hu hx)), complement_smooth (fun y hy => hb y (hv hy)),
    hf₀, hb₀, hPair, hPair', hforward, hbackward⟩

end
end Hironaka.HironakaG1FixedReaderComplementExtensions

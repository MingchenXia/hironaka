import Hironaka.Resolution.StrictTransformSubvariety
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Analytic.NonKahlerLocusPoleSet
import Hironaka.Analytic.ModificationInputs
import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

/-!
# Strict transforms leave analytic sets and non-nef loci

Source: CT22, Lemma 4.3 (the reduction to `W ⊄ E_nn(α)`); blueprint
`ana:rv-birational-blowup`.

Let `g : Z → Y` be the blowup of a compact complex manifold along a smooth centre and
`W ⊆ Y` a closed irreducible analytic subvariety with `W ⊄ g(Exc g)`.

* An irreducible subvariety that meets an open set `U` inside an analytic set `A` lies in
  `A`: the regular points of `W` off `A` are dense in `W`
  (`StrictTransformSubvariety.eq_closure_component` and `ComponentComplementConnected`).
* By Baire, the same holds when `W ∩ U` lies in a countable union of analytic sets: some
  member contains a nonempty relatively open part of `W ∩ U`.
* Since `g` is onto, `W \ g(Exc g) ⊆ g(W̃)`.  Hence `W̃ ⊆ g⁻¹ A` forces `W ⊆ A` for an
  analytic `A`, and `W̃ ⊆ E_nn(g^*α) = g⁻¹ E_nn(α)` (CT22, Lemma 4.2) forces
  `W ⊆ E_nn(α) = ⋃_m E_nK(α + ω/(m+1))`, a countable union of analytic sets for big `α`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformLocus

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

section Density

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- An irreducible subvariety meeting an open set inside an analytic set lies in that set. -/
theorem subset_of_inter_isOpen_subset (V : ClosedIrreducibleAnalyticSubvariety n M)
    {A U : Set M} (hA : IsComplexAnalyticSubset (n := n) A) (hU : IsOpen U)
    (hVU : (V.carrier ∩ U).Nonempty) (hsub : V.carrier ∩ U ⊆ A) : V.carrier ⊆ A := by
  by_contra hVA
  obtain ⟨c, hc, hcA⟩ :=
    AnalyticIrreducibleComponents.exists_mem_regularLocus_not_mem_of_not_subset V hA hVA
  have hc' : RegularAtDim (n := n) V.carrier c V.dim := hc
  have hVeq := StrictTransformSubvariety.eq_closure_component V.irreducible_carrier hc'
  have hK : ¬ RegularLocusComponent.component (n := n) V.carrier c ⊆ A := fun h =>
    hcA (h (RegularLocusComponent.mem_component_self hc'))
  have hcl := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    V.irreducible_carrier.analytic hA hc' hK).2
  obtain ⟨x, hxV, hxU⟩ := hVU
  have hx : x ∈ closure (RegularLocusComponent.component (n := n) V.carrier c \ A) :=
    closure_minimal hcl isClosed_closure (hVeq ▸ hxV)
  obtain ⟨y, hyU, hyK, hyA⟩ := mem_closure_iff.mp hx U hU hxU
  exact hyA (hsub ⟨RegularLocusComponent.component_subset (n := n) V.carrier c hyK, hyU⟩)

/-- **Baire.**  An irreducible subvariety meeting an open set inside a countable union of
analytic sets lies in one of them. -/
theorem exists_subset_of_inter_isOpen_subset_iUnion (V : ClosedIrreducibleAnalyticSubvariety n M)
    {A : ℕ → Set M} (hA : ∀ m, IsComplexAnalyticSubset (n := n) (A m)) {U : Set M}
    (hU : IsOpen U) (hVU : (V.carrier ∩ U).Nonempty) (hsub : V.carrier ∩ U ⊆ ⋃ m, A m) :
    ∃ m, V.carrier ⊆ A m := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  set O : Set M := V.carrier ∩ U with hO
  have hOlc : IsLocallyClosed O := V.isClosed_carrier.isLocallyClosed.inter hU.isLocallyClosed
  have : LocallyCompactSpace O := hOlc.locallyCompactSpace
  have : BaireSpace O := BaireSpace.of_t2Space_locallyCompactSpace
  let B : ℕ → Set O := fun m => (Subtype.val : O → M) ⁻¹' A m
  have hBc : ∀ m, IsClosed (B m) := fun m =>
    (hA m).isClosed.preimage continuous_subtype_val
  have hBu : ⋃ m, B m = univ := by
    refine eq_univ_of_forall fun p => ?_
    simpa [B] using hsub p.2
  have : Nonempty O := hVU.to_subtype
  obtain ⟨m, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hBc hBu
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp (isOpen_interior (s := B m))
  refine ⟨m, subset_of_inter_isOpen_subset V (hA m) (hW.inter hU) ?_ ?_⟩
  · refine ⟨p.1, p.2.1, ?_, p.2.2⟩
    have : p ∈ (Subtype.val : O → M) ⁻¹' W := hWeq ▸ hp
    exact this
  · rintro y ⟨hyV, hyW, hyU⟩
    have hy : (⟨y, hyV, hyU⟩ : O) ∈ interior (B m) := by
      rw [← hWeq]
      exact hyW
    exact (interior_subset hy : (⟨y, hyV, hyU⟩ : O) ∈ B m)

/-- **The polar set of a potential with analytic singularities in the `I-0489` convention is
analytic.**  This is the one lemma in the pipeline that reasons AT a pole, and it uses nothing
of the remainder there beyond its being a real number: `c log \sum_j |f_j|^2 + b y = -\infty`
happens exactly where all `f_j` vanish. -/
theorem isComplexAnalyticSubset_poleSet_of_smoothOffPole {u : M → EReal}
    (hu : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) :
    IsComplexAnalyticSubset (n := n) (poleSet u) := by
  intro x
  set e := complexChartAt (n := n) x with he
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨c, N, f, hc, ⟨U, hUo, hzU, hf⟩, b, -, -, heq⟩ := hu e (e.val x) hz
  obtain ⟨t, htp, hto, hzt⟩ := eventually_nhds_iff.mp heq
  refine ⟨{
    generatorCount := N
    generator := f
    coordinateNeighborhood := e.val.target ∩ (U ∩ t)
    isOpen_coordinateNeighborhood := e.val.open_target.inter (hUo.inter hto)
    center_mem_coordinateNeighborhood := ⟨hz, hzU, hzt⟩
    coordinateNeighborhood_subset_target := inter_subset_left
    generator_holomorphic := fun i => (hf i).mono (inter_subset_right.trans inter_subset_left)
    zeroLocus := ?_ }⟩
  intro y hysrc hymem
  have hyy : e.val.symm (e.val y) = y := e.val.left_inv hysrc
  have h1 := htp (e.val y) hymem.2.2
  simp only [chartFunction, hyy] at h1
  simp only [mem_poleSet, h1]
  exact scaled_generatorLog_add_eq_bot_iff f (e.val y) hc (b (e.val y))

/-- The polar set of a potential with smooth analytic singularities is analytic. -/
theorem isComplexAnalyticSubset_poleSet {u : M → EReal}
    (hu : HasManifoldSmoothAnalyticSingularities (n := n) u) :
    IsComplexAnalyticSubset (n := n) (poleSet u) :=
  isComplexAnalyticSubset_poleSet_of_smoothOffPole hu.smoothOffPole

end Density

section Blowup

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Off the image of the exceptional locus, a subvariety lies in the image of its strict
transform. -/
theorem mem_image_strictTransform_of_not_mem [CompactSpace Y] {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) {W : Set Y} {w : Y} (hwW : w ∈ W)
    (hwE : w ∉ g '' exceptionalLocus n g) :
    ∃ z ∈ strictTransform n g W, g z = w := by
  obtain ⟨z, rfl⟩ := StrictTransformComposition.surjective_of_isBlowupAlong hg w
  refine ⟨z, subset_closure ⟨hwW, fun hz => hwE ⟨z, hz, rfl⟩⟩, rfl⟩

/-- A strict transform contained in the preimage of an analytic set forces the subvariety
into that set. -/
theorem not_strictTransform_subset_preimage [CompactSpace Y] {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) {A : Set Y}
    (hA : IsComplexAnalyticSubset (n := n) A) (h : ¬ W.carrier ⊆ A) :
    ¬ strictTransform n g W.carrier ⊆ g ⁻¹' A := by
  intro hsub
  refine h (subset_of_inter_isOpen_subset W hA
    (ExceptionalFibres.isClosed_image_exceptionalLocus hg).isOpen_compl ?_ ?_)
  · obtain ⟨w, hwW, hwE⟩ := not_subset.mp hW
    exact ⟨w, hwW, hwE⟩
  · rintro w ⟨hwW, hwE⟩
    obtain ⟨z, hz, rfl⟩ := mem_image_strictTransform_of_not_mem hg hwW hwE
    exact hsub hz

/-- The strict transform of a subvariety not in `E_nn(α)` is not in `E_nn(g^*α)`. -/
theorem not_strictTransform_subset_nonNefLocus [CompactSpace Y] (hn : 0 < n)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (h : ¬ W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    ¬ strictTransform n g W.carrier ⊆ nonNefLocus omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) := by
  intro hsub
  rw [ModificationInputs.nonNefLocus_pullback_of_isBlowupAlong omega omegaZ θ hbig hg] at hsub
  set alpha := RealBottChern.ofRepresentative θ with halpha
  let A : ℕ → Set Y := fun m =>
    nonKahlerLocus (alpha + ((1 : ℝ) / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form)
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => Nat.one_div_pos_of_nat
  have hA : ∀ m, IsComplexAnalyticSubset (n := n) (A m) := by
    intro m
    obtain ⟨T⟩ := hbig
    exact NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus hn _
      ⟨T.addSmulKahler omega (hpos m)⟩
  have hAsub : ∀ m, A m ⊆ nonNefLocus omega alpha := fun m x hx =>
    mem_nonNefLocus.mpr ⟨⟨_, hpos m⟩, hx⟩
  have hunion : W.carrier ∩ (g '' exceptionalLocus n g)ᶜ ⊆ ⋃ m, A m := by
    rintro w ⟨hwW, hwE⟩
    obtain ⟨z, hz, rfl⟩ := mem_image_strictTransform_of_not_mem hg hwW hwE
    obtain ⟨epsilon, hx⟩ := mem_nonNefLocus.mp (hsub hz)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt epsilon.2
    refine mem_iUnion.mpr ⟨m, fun T => ?_⟩
    have hd : (0 : ℝ) < (epsilon : ℝ) - 1 / ((m : ℝ) + 1) := sub_pos.mpr hm
    have hclass : alpha + ((1 : ℝ) / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form +
        ((epsilon : ℝ) - 1 / ((m : ℝ) + 1)) • RealBottChern.ofRepresentative omega.form =
        alpha + (epsilon : ℝ) • RealBottChern.ofRepresentative omega.form := by
      module
    exact hx (NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hclass (T.addSmulKahler omega hd))
  obtain ⟨m, hm⟩ := exists_subset_of_inter_isOpen_subset_iUnion W hA
    (ExceptionalFibres.isClosed_image_exceptionalLocus hg).isOpen_compl
    (by obtain ⟨w, hwW, hwE⟩ := not_subset.mp hW; exact ⟨w, hwW, hwE⟩) hunion
  exact h (hm.trans (hAsub m))

end Blowup

end

end Hironaka.StrictTransformLocus

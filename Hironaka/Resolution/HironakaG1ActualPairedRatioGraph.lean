import Hironaka.Resolution.HironakaG1RelativeReaderWindow
import Hironaka.Resolution.HironakaG1FixedReaderComplementExtensions

/-! The actual paired native graph lifted to the common ordered ratio window. -/

set_option autoImplicit false

open CategoryTheory Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1ActualPairedRatioGraph

open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupFlatCoordinates
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1SNCReaderNormalization
  HironakaG1RelativeReaderWindow HironakaG1FixedReaderBoundaryUnits
  HironakaG1FixedReaderComplementExtensions

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m} {C : Set M} {D : Set N}
  (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
  (p : C) {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p.val (e.hom.base p).val E F τ)

private theorem base_inv_hom (x : C) : e.inv.base (e.hom.base x) = x :=
  congrArg (fun f => f.base x) e.hom_inv_id

private theorem base_hom_inv (y : D) : e.hom.base (e.inv.base y) = y :=
  congrArg (fun f => f.base y) e.inv_hom_id

set_option maxHeartbeats 1000000 in
/-- The actual native overlap lifts into the ratio window. Both restrictions
of the reader projections are bijections onto the paired traces, and each
point lifts the intrinsic isomorphism with the same nonzero ratio block.
The selected complements come from genuine holomorphic ambient extensions. -/
theorem exists_actual_paired_ratio_graph
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hI : ∀ i : Fin E.length, Ideal.map (e.hom.stalkMap p).hom
      (actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p)) =
        actualLabelledBoundaryTraceIdeal C E i p) :
    ∃ (U : Opens M) (V : Opens N) (G : Set (readerUnitWindow R))
      (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
      (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧
      (U : Set M) ⊆ flatDomain R.Φ₁ ∧ (V : Set N) ⊆ flatDomain R.Φ₂ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel R.b) ∞ forward U ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel R.a) ∞ backward V ∧
      (∀ x ∈ U, ∀ j, HolomorphicAt n (a j) x ∧ a j x ≠ 0) ∧
      (∀ y ∈ V, ∀ j, HolomorphicAt m (b j) y ∧ b j y ≠ 0) ∧
      BijOn (firstReaderMap R) G (C ∩ (U : Set M)) ∧
      BijOn (secondReaderMap R) G (D ∩ (V : Set N)) ∧
      ∀ z ∈ G, ∃ (hx : firstReaderMap R z ∈ C) (hy : secondReaderMap R z ∈ D),
        e.hom.base ⟨firstReaderMap R z,hx⟩ = ⟨secondReaderMap R z,hy⟩ ∧
        z.val.1.2 = (fun j => a j (firstReaderMap R z)) ∧
        z.val.1.2 = (fun j => b j (secondReaderMap R z)) ∧
        (∀ i, forward (firstReaderMap R z) i =
          targetComplement e p R i (secondReaderMap R z)) ∧
        ∀ i, backward (secondReaderMap R z) i =
          sourceComplement e p R i (firstReaderMap R z) := by
  classical
  obtain ⟨U₀,V₀,a,b,hpU₀,hpV₀,hU₀,hV₀,ha,hb,hRatio⟩ := active_reader_units_on_graph e p R he hI
  obtain ⟨U,V,forward,backward,hpU,hpV,hU,hV,hUF,hVF,hForward,hBackward,_,_,hPair,hPair',hF,hB⟩ :=
    paired_reader_complement_extensions e p R he U₀ V₀ hpU₀ hpV₀ hU₀ hV₀
  let X := {x : C // x.val ∈ U}
  have hLift (x : X) : ∃ z : readerUnitWindow R, firstReaderMap R z = x.val.val ∧
      secondReaderMap R z = (e.hom.base x.val).val ∧ z.val.1.2 = (fun j => a j x.val.val) := by
    obtain ⟨hx,hy,_,hCoord⟩ := hRatio x.val (hU x.property)
    exact exists_reader_lift_of_coordinate_ratio R ⟨x.val.val,hx⟩ ⟨(e.hom.base x.val).val,hy⟩
      (fun j => a j x.val.val) (fun j => (ha _ (hU x.property) j).2) (fun j => (hCoord j).2)
  choose lift hLeft hRight hRat using hLift
  refine ⟨U,V,range lift,a,b,forward,backward,hpU,hpV,hUF,hVF,hForward,hBackward,
    (fun x hx => ha x (hU hx)),(fun y hy => hb y (hV hy)),?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · rintro _ ⟨x,rfl⟩
      rw [hLeft]
      exact ⟨x.val.property,x.property⟩
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ heq
      apply congrArg lift
      exact Subtype.ext (Subtype.ext ((hLeft x).symm.trans (heq.trans (hLeft y))))
    · intro x hx
      let x' : X := ⟨⟨x,hx.1⟩,hx.2⟩
      exact ⟨lift x',mem_range_self x',hLeft x'⟩
  · refine ⟨?_,?_,?_⟩
    · rintro _ ⟨x,rfl⟩
      rw [hRight]
      exact ⟨(e.hom.base x.val).property,(hPair x.val).mp x.property⟩
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ heq
      have hBase : e.hom.base x.val = e.hom.base y.val :=
        Subtype.ext ((hRight x).symm.trans (heq.trans (hRight y)))
      apply congrArg lift
      apply Subtype.ext
      simpa only [base_inv_hom] using congrArg e.inv.base hBase
    · intro y hy
      let y' : D := ⟨y,hy.1⟩
      let x : X := ⟨e.inv.base y',(hPair' y').mp hy.2⟩
      refine ⟨lift x,mem_range_self x,?_⟩
      rw [hRight]
      exact congrArg Subtype.val (base_hom_inv e y')
  · rintro _ ⟨x,rfl⟩
    have hx : firstReaderMap R (lift x) ∈ C := (hLeft x).symm ▸ x.val.property
    have hy : secondReaderMap R (lift x) ∈ D := (hRight x).symm ▸ (e.hom.base x.val).property
    refine ⟨hx,hy,?_,?_,?_,?_,?_⟩
    · exact (congrArg e.hom.base (Subtype.ext (hLeft x))).trans (Subtype.ext (hRight x).symm)
    · rw [hLeft]
      exact hRat x
    · rw [hRat x,hRight]
      funext j
      obtain ⟨_,_,_,h⟩ := hRatio x.val (hU x.property)
      exact (h j).1
    · intro i
      rw [hLeft,hRight]
      exact hF x.val x.property i
    · intro i
      rw [hLeft,hRight]
      have heq := hB (e.hom.base x.val) ((hPair x.val).mp x.property) i
      rwa [base_inv_hom] at heq

#print axioms exists_actual_paired_ratio_graph

end Hironaka.HironakaG1ActualPairedRatioGraph

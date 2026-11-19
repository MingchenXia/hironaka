import Hironaka.Resolution.HironakaG1RatioGraphProductEquations
import Hironaka.Resolution.HironakaG1IteratedNormalBlockIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals

/-! Block cylinder coordinates for both exact paired ratio graph equations. -/
set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioBlockGraphAdapters
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupFlatCoordinates MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG1RelativeBoundaryProjections HironakaG1SNCReaderNormalization
  HironakaG1RelativeReaderWindow HironakaG1ReaderProductSubmersions HironakaG1RatioGraphProductEquations
  HironakaActualIntrinsicStableAmbientIso HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal HironakaSmoothSubmersionCoefficientIdeals

section ReaderBase
variable {n k : ℕ} {M : CMfd.{0} n} {S : Opens M} {T : Opens (ComplexModel k)}
  (η : S ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel k)⟯ T)

 /-- The actual normalized base open inside the fixed reader's target. -/
def normalizedBaseOpen (U : Opens M) : Opens (ComplexModel k) :=
  ⟨(Subtype.val : T → ComplexModel k) '' {w : T | (η.symm w).val ∈ U},
    T.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
      (U.isOpen.preimage (continuous_subtype_val.comp η.symm.continuous))⟩

private theorem normalizedBase_le (U : Opens M) : normalizedBaseOpen η U ≤ T := by
  rintro _ ⟨y,_,rfl⟩
  exact y.property

/-- Original ambient map of the actual smaller normalized window. -/
def normalizedBaseMap (U : Opens M) (y : normalizedBaseOpen η U) : M :=
  (η.symm (Opens.inclusion (normalizedBase_le η U) y)).val

theorem normalizedBaseMap_hol (U : Opens M) :
    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ (normalizedBaseMap η U) :=
  contMDiff_subtype_val.comp (η.symm.contMDiff.comp (contMDiff_inclusion (normalizedBase_le η U)))

theorem normalizedBaseMap_mem (U : Opens M) (y : normalizedBaseOpen η U) :
    normalizedBaseMap η U y ∈ U := by
  obtain ⟨w,hw,he⟩ := y.property
  have hEq : Opens.inclusion (normalizedBase_le η U) y = w := Subtype.ext he.symm
  change (η.symm (Opens.inclusion (normalizedBase_le η U) y)).val ∈ U
  rw [hEq]
  exact hw

theorem normalizedBaseMap_on_reader (U : Opens M) (w : T) (hw : (η.symm w).val ∈ U) :
    normalizedBaseMap η U (⟨w.val, ⟨w,hw,rfl⟩⟩ : normalizedBaseOpen η U) = (η.symm w).val := rfl

end ReaderBase

section Adapters
variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
  {p : M} {q : N} {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p q E F τ) (U : Opens M) (V : Opens N)

abbrev LBase := normalizedBaseOpen R.sourceDiffeomorph U
abbrev RBase := normalizedBaseOpen R.targetDiffeomorph V
abbrev Common := graphEquationWindow R U V

private def rp (z : Common R U V) : readerUnitWindow R := graphEquationWindowToRatio R U V z

private def lPair (z : Common R U V) : ComplexModel (R.r+R.a) × ComplexModel (R.r+R.b) :=
  sourceProduct R.r R.a R.b (rp R U V z).val

private def rPair (z : Common R U V) : ComplexModel (R.r+R.b) × ComplexModel (R.r+R.a) :=
  targetProduct R.r R.a R.b (unitScaling R.r R.a R.b (rp R U V z).val)

private theorem lPair_fst (z : Common R U V) :
    (lPair R U V z).1 = (R.sourceDiffeomorph (lPoint R (rp R U V z))).val := by
  let w := rp R U V z
  let y : R.sourceCoordinateOpen :=
    ⟨joinBlock R.r R.a (leftProjection R.r R.a R.b w.val), w.property.1.2⟩
  exact (congrArg Subtype.val (R.sourceDiffeomorph.apply_symm_apply y)).symm

private theorem rPair_fst (z : Common R U V) :
    (rPair R U V z).1 = (R.targetDiffeomorph (rPoint R (rp R U V z))).val := by
  let w := rp R U V z
  let y : R.targetCoordinateOpen :=
    ⟨joinBlock R.r R.b (rightProjection R.r R.a R.b w.val), w.property.2⟩
  exact (congrArg Subtype.val (R.targetDiffeomorph.apply_symm_apply y)).symm

/-- Source chart in the exact normalized reader block cylinder. -/
def leftBlockMap (z : Common R U V) : blockOpen (LBase R U) (R.r+R.b) :=
  ⟨join (lPair R U V z).1 (lPair R U V z).2, by
    change tangentProjection _ _ (join _ _) ∈ LBase R U
    rw [first_join,lPair_fst]
    exact ⟨R.sourceDiffeomorph (lPoint R (rp R U V z)),
      by
        change (R.sourceDiffeomorph.symm (R.sourceDiffeomorph (lPoint R (rp R U V z)))).val ∈ U
        rw [R.sourceDiffeomorph.symm_apply_apply]
        exact z.property.1,rfl⟩⟩

/-- Target chart in the normalized reader block cylinder after ratio scaling. -/
def rightBlockMap (z : Common R U V) : blockOpen (RBase R V) (R.r+R.a) :=
  ⟨join (rPair R U V z).1 (rPair R U V z).2, by
    change tangentProjection _ _ (join _ _) ∈ RBase R V
    rw [first_join,rPair_fst]
    exact ⟨R.targetDiffeomorph (rPoint R (rp R U V z)),
      by
        change (R.targetDiffeomorph.symm (R.targetDiffeomorph (rPoint R (rp R U V z)))).val ∈ V
        rw [R.targetDiffeomorph.symm_apply_apply]
        exact z.property.2,rfl⟩⟩

/-- The exact source base after transport is the original first reader map. -/
theorem leftBlockMap_base (z : Common R U V) :
    normalizedBaseMap R.sourceDiffeomorph U (blockProjection (leftBlockMap R U V z)) =
      firstReaderMap R (rp R U V z) := by
  let b := R.sourceDiffeomorph (lPoint R (rp R U V z))
  have hEq : Opens.inclusion (normalizedBase_le R.sourceDiffeomorph U)
      (blockProjection (leftBlockMap R U V z)) = b := by
    apply Subtype.ext
    change tangentProjection _ _ (join _ _) = _
    rw [first_join,lPair_fst]
  change (R.sourceDiffeomorph.symm
    (Opens.inclusion (normalizedBase_le R.sourceDiffeomorph U)
      (blockProjection (leftBlockMap R U V z)))).val = _
  rw [hEq, R.sourceDiffeomorph.symm_apply_apply]
  rfl

/-- The exact target base after transport is the original second reader map. -/
theorem rightBlockMap_base (z : Common R U V) :
    normalizedBaseMap R.targetDiffeomorph V (blockProjection (rightBlockMap R U V z)) =
      secondReaderMap R (rp R U V z) := by
  let b := R.targetDiffeomorph (rPoint R (rp R U V z))
  have hEq : Opens.inclusion (normalizedBase_le R.targetDiffeomorph V)
      (blockProjection (rightBlockMap R U V z)) = b := by
    apply Subtype.ext
    change tangentProjection _ _ (join _ _) = _
    rw [first_join,rPair_fst]
  change (R.targetDiffeomorph.symm
    (Opens.inclusion (normalizedBase_le R.targetDiffeomorph V)
      (blockProjection (rightBlockMap R U V z)))).val = _
  rw [hEq, R.targetDiffeomorph.symm_apply_apply]
  rfl

/-- The left padded graph function on its exact normalized base. -/
def leftBlockGraphValue (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b) :
    LBase R U → ComplexModel (R.r+R.b) :=
  leftGraphValue R a forward ∘ normalizedBaseMap R.sourceDiffeomorph U

/-- The right padded graph function on its exact normalized base. -/
def rightBlockGraphValue (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a) :
    RBase R V → ComplexModel (R.r+R.a) :=
  rightGraphValue R b backward ∘ normalizedBaseMap R.targetDiffeomorph V

/-- Both exact cylinder maps pull back the literal graph to the same
actual graph in the common Euclidean open. -/
theorem blockGraph_preimages
    {C : Set M} {D : Set N} {G : Set (readerUnitWindow R)}
    (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)
    (hL : ∀ z : readerUnitWindow R, z ∈ G ↔ firstReaderMap R z ∈ C ∩ (U : Set M) ∧
      (sourceProduct R.r R.a R.b z.val).2 = leftGraphValue R a forward (firstReaderMap R z))
    (hR : ∀ z : readerUnitWindow R, z ∈ G ↔ secondReaderMap R z ∈ D ∩ (V : Set N) ∧
      (targetProduct R.r R.a R.b (unitScaling R.r R.a R.b z.val)).2 =
        rightGraphValue R b backward (secondReaderMap R z)) :
    (leftBlockMap R U V ⁻¹' blockGraph (leftBlockGraphValue R U a forward)
      (normalizedBaseMap R.sourceDiffeomorph U ⁻¹' C) = graphEquationWindowToRatio R U V ⁻¹' G) ∧
    (rightBlockMap R U V ⁻¹' blockGraph (rightBlockGraphValue R V b backward)
      (normalizedBaseMap R.targetDiffeomorph V ⁻¹' D) = graphEquationWindowToRatio R U V ⁻¹' G) := by
  constructor
  · ext z
    rw [mem_preimage, mem_preimage, hL]
    change normalizedBaseMap R.sourceDiffeomorph U (blockProjection (leftBlockMap R U V z)) ∈ C ∧
        actualJointNormalProjection _ _ (join (lPair R U V z).1 (lPair R U V z).2) =
          leftGraphValue R a forward
            (normalizedBaseMap R.sourceDiffeomorph U (blockProjection (leftBlockMap R U V z))) ↔ _
    rw [leftBlockMap_base, second_join]
    exact ⟨fun h => ⟨⟨h.1,z.property.1⟩,h.2⟩, fun h => ⟨h.1.1,h.2⟩⟩
  · ext z
    rw [mem_preimage, mem_preimage, hR]
    change normalizedBaseMap R.targetDiffeomorph V (blockProjection (rightBlockMap R U V z)) ∈ D ∧
        actualJointNormalProjection _ _ (join (rPair R U V z).1 (rPair R U V z).2) =
          rightGraphValue R b backward
            (normalizedBaseMap R.targetDiffeomorph V (blockProjection (rightBlockMap R U V z))) ↔ _
    rw [rightBlockMap_base, second_join]
    exact ⟨fun h => ⟨⟨h.1,z.property.2⟩,h.2⟩, fun h => ⟨h.1.1,h.2⟩⟩

private abbrev cdim := (R.r+R.a)+(R.r+R.b)

/-- Pull the actual left padded block record back to the common window. -/
def leftRatioMarked (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b)
    (P : MarkedIdeal n M) : MarkedIdeal (cdim R) (Common R U V) :=
  markedPullback (m := cdim R) (leftBlockMap R U V)
    (blockAmbientMarked (leftBlockGraphValue R U a forward)
      (markedPullback (m := R.r+R.a) (normalizedBaseMap R.sourceDiffeomorph U) P))

/-- Pull the actual scaled right padded block record back to the same
common window, using the literal cross-dimensional pullback. -/
def rightRatioMarked (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a)
    (Q : MarkedIdeal m N) : MarkedIdeal (cdim R) (Common R U V) :=
  markedPullback (m := cdim R) (rightBlockMap R U V)
    (blockAmbientMarked (rightBlockGraphValue R V b backward)
      (markedPullback (m := R.r+R.b) (normalizedBaseMap R.targetDiffeomorph V) Q))

@[simp] theorem leftRatioMarked_mark (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b)
    (P : MarkedIdeal n M) : (leftRatioMarked R U V a forward P).d = P.d := rfl

@[simp] theorem rightRatioMarked_mark (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a)
    (Q : MarkedIdeal m N) : (rightRatioMarked R U V b backward Q).d = Q.d := rfl

/-- Every original left boundary position is pulled back by the exact
unscaled first reader map, including positions with empty trace. -/
theorem leftRatioMarked_boundary (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b)
    (P : MarkedIdeal n M) :
    (leftRatioMarked R U V a forward P).E =
      P.E.map ((firstReaderMap R ∘ graphEquationWindowToRatio R U V) ⁻¹' ·) := by
  change ((P.E.map ((normalizedBaseMap R.sourceDiffeomorph U) ⁻¹' ·)).map
    (blockProjection ⁻¹' ·)).map ((leftBlockMap R U V) ⁻¹' ·) = _
  simp only [List.map_map]
  apply congrArg (fun f : Set M → Set (Common R U V) => P.E.map f)
  funext H
  ext z
  change normalizedBaseMap R.sourceDiffeomorph U (blockProjection (leftBlockMap R U V z)) ∈ H ↔
    firstReaderMap R (graphEquationWindowToRatio R U V z) ∈ H
  rw [leftBlockMap_base]
  rfl

/-- Every original right boundary position is pulled back by the exact
scaled second reader map. -/
theorem rightRatioMarked_boundary (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a)
    (Q : MarkedIdeal m N) :
    (rightRatioMarked R U V b backward Q).E =
      Q.E.map ((secondReaderMap R ∘ graphEquationWindowToRatio R U V) ⁻¹' ·) := by
  change ((Q.E.map ((normalizedBaseMap R.targetDiffeomorph V) ⁻¹' ·)).map
    (blockProjection ⁻¹' ·)).map ((rightBlockMap R U V) ⁻¹' ·) = _
  simp only [List.map_map]
  apply congrArg (fun f : Set N → Set (Common R U V) => Q.E.map f)
  funext H
  ext z
  change normalizedBaseMap R.targetDiffeomorph V (blockProjection (rightBlockMap R U V z)) ∈ H ↔
    secondReaderMap R (graphEquationWindowToRatio R U V z) ∈ H
  rw [rightBlockMap_base]
  rfl

/-- For position-preserving labels the two literal padded records carry
the identical full ordered boundary on the common ambient open. -/
theorem ratioMarked_ordered_boundary_eq (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ)
    (forward : M → ComplexModel R.b) (backward : N → ComplexModel R.a)
    (P : MarkedIdeal n M) (Q : MarkedIdeal m N)
    (hP : P.E = E) (hQ : Q.E = F) (hτ : ∀ i, (τ i).val = i.val) :
    (leftRatioMarked R U V a forward P).E = (rightRatioMarked R U V b backward Q).E := by
  rw [leftRatioMarked_boundary, rightRatioMarked_boundary, hP, hQ]
  let f : Set (readerUnitWindow R) → Set (Common R U V) :=
    fun H => graphEquationWindowToRatio R U V ⁻¹' H
  change E.map (f ∘ (firstReaderMap R ⁻¹' ·)) = F.map (f ∘ (secondReaderMap R ⁻¹' ·))
  rw [← List.map_map, ← List.map_map, reader_maps_ordered_boundary_eq R hτ]

private def literalJoin (a b : ℕ) : (ComplexModel a × ComplexModel b) ≃L[ℂ] ComplexModel (a+b) :=
  { toFun := fun z => join z.1 z.2
    invFun := fun z => (tangentProjection a b z,actualJointNormalProjection a b z)
    left_inv z := Prod.ext (first_join _ _) (second_join _ _)
    right_inv := join_projections
    map_add' := by
      intro x y
      simp only [HironakaActualIntrinsicStableAmbientIso.join, Prod.fst_add, Prod.snd_add, map_add]
      abel
    map_smul' := by
      intro c x
      simp [HironakaActualIntrinsicStableAmbientIso.join, map_smul, smul_add]
    continuous_toFun := by
      change Continuous (fun z : ComplexModel a × ComplexModel b => tangentInclusion a b z.1 +
        actualJointNormalInclusion a b z.2)
      fun_prop
    continuous_invFun := by
      fun_prop }

private abbrev raw (z : Common R U V) : Ambient R.r R.a R.b := (rp R U V z).val

private theorem raw_hol :
    ContMDiff 𝓘(ℂ,ComplexModel (cdim R)) 𝓘(ℂ,Ambient R.r R.a R.b) ∞ (raw R U V) :=
  (ambientEuclidean R.r R.a R.b).symm.contDiff.contMDiff.comp
    (contMDiff_subtype_val.comp contMDiff_subtype_val)

private theorem raw_openEmbedding : Topology.IsOpenEmbedding (raw R U V) :=
  (ambientEuclidean R.r R.a R.b).symm.toHomeomorph.isOpenEmbedding.comp
    ((euclideanReaderWindow R).isOpen.isOpenEmbedding_subtypeVal.comp
      (Common R U V).isOpen.isOpenEmbedding_subtypeVal)

/-- The left block adapter is holomorphic on the genuine common Euclidean open. -/
theorem leftBlockMap_hol :
    ContMDiff 𝓘(ℂ,ComplexModel (cdim R)) 𝓘(ℂ,ComplexModel (cdim R)) ∞ (leftBlockMap R U V) := by
  apply (ContMDiff.subtypeVal_comp_iff (blockOpen (LBase R U) (R.r+R.b)) _).mp
  exact (literalJoin (R.r+R.a) (R.r+R.b)).contDiff.contMDiff.comp
    ((sourceProduct R.r R.a R.b).contDiff.contMDiff.comp (raw_hol R U V))

/-- The right block adapter is holomorphic in the actual scaled model. -/
theorem rightBlockMap_hol :
    ContMDiff 𝓘(ℂ,ComplexModel (cdim R)) 𝓘(ℂ,ComplexModel ((R.r+R.b)+(R.r+R.a))) ∞
      (rightBlockMap R U V) := by
  apply (ContMDiff.subtypeVal_comp_iff (blockOpen (RBase R V) (R.r+R.a)) _).mp
  exact (literalJoin (R.r+R.b) (R.r+R.a)).contDiff.contMDiff.comp
    ((targetProduct R.r R.a R.b).contDiff.contMDiff.comp
      ((contDiff_unitScaling R.r R.a R.b).contMDiff.comp (raw_hol R U V)))

/-- The exact unscaled adapter embeds the common open as an open set of
the normalized left cylinder. -/
theorem leftBlockMap_openEmbedding : Topology.IsOpenEmbedding (leftBlockMap R U V) :=
  Topology.IsOpenEmbedding.of_comp _
    (blockOpen (LBase R U) (R.r+R.b)).isOpen.isOpenEmbedding_subtypeVal
    ((literalJoin (R.r+R.a) (R.r+R.b)).toHomeomorph.isOpenEmbedding.comp
      ((sourceProduct R.r R.a R.b).toHomeomorph.isOpenEmbedding.comp (raw_openEmbedding R U V)))

private theorem scaling_on_common_openEmbedding :
    Topology.IsOpenEmbedding (unitScaling R.r R.a R.b ∘ raw R U V) := by
  let d := scalingChart R.r R.a R.b
  let h (z : Common R U V) : d.source := ⟨raw R U V z,(rp R U V z).property.1.1⟩
  have hh : Topology.IsOpenEmbedding h :=
    Topology.IsOpenEmbedding.of_comp _ d.open_source.isOpenEmbedding_subtypeVal (raw_openEmbedding R U V)
  exact d.open_target.isOpenEmbedding_subtypeVal.comp (d.toHomeomorphSourceTarget.isOpenEmbedding.comp hh)

/-- The exact scaled adapter embeds the common open as an open set of
the normalized right cylinder. -/
theorem rightBlockMap_openEmbedding : Topology.IsOpenEmbedding (rightBlockMap R U V) :=
  Topology.IsOpenEmbedding.of_comp _
    (blockOpen (RBase R V) (R.r+R.a)).isOpen.isOpenEmbedding_subtypeVal
    ((literalJoin (R.r+R.b) (R.r+R.a)).toHomeomorph.isOpenEmbedding.comp
      ((targetProduct R.r R.a R.b).toHomeomorph.isOpenEmbedding.comp (scaling_on_common_openEmbedding R U V)))

/-- The actual left complement function is holomorphic on its own
normalized reader base. -/
theorem leftBlockGraphValue_hol (a : Fin R.r → M → ℂ) (forward : M → ComplexModel R.b)
    (ha : ∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel R.b) ∞ forward U) :
    ContMDiff 𝓘(ℂ,ComplexModel (R.r+R.a)) 𝓘(ℂ,ComplexModel (R.r+R.b)) ∞
      (leftBlockGraphValue R U a forward) :=
  contMDiffOn_univ.mp ((leftGraphValue_hol R U a forward ha hf).comp
    (normalizedBaseMap_hol R.sourceDiffeomorph U).contMDiffOn
    (fun y _ => normalizedBaseMap_mem R.sourceDiffeomorph U y))

/-- The actual right complement function is holomorphic on its own
normalized reader base. -/
theorem rightBlockGraphValue_hol (b : Fin R.r → N → ℂ) (backward : N → ComplexModel R.a)
    (hb : ∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel R.a) ∞ backward V) :
    ContMDiff 𝓘(ℂ,ComplexModel (R.r+R.b)) 𝓘(ℂ,ComplexModel (R.r+R.a)) ∞
      (rightBlockGraphValue R V b backward) := by
  have hPi : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,Block R.r) ∞ (fun y i => b i y) V := by
    intro y hy
    exact (contMDiffAt_pi_space.mpr (fun i =>
      contMDiffAt_of_eventually_mdifferentiableAt (hb y hy i))).contMDiffWithinAt
  have hG : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel (R.r+R.a)) ∞
      (rightGraphValue R b backward) V :=
    (joinBlock R.r R.a).contDiff.contMDiff.comp_contMDiffOn
      (hPi.prodMk_space ((euclideanBlock R.a).symm.contDiff.contMDiff.comp_contMDiffOn hf))
  exact contMDiffOn_univ.mp (hG.comp (normalizedBaseMap_hol R.targetDiffeomorph V).contMDiffOn
    (fun y _ => normalizedBaseMap_mem R.targetDiffeomorph V y))

end Adapters
end
end Hironaka.HironakaG1RatioBlockGraphAdapters

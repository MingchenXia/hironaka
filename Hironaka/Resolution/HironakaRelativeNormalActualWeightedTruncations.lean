/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualCompatibleTruncations

/-! Actual mixed tangent weights on the original whole normal filtration. -/
set_option autoImplicit false
open scoped DirectSum
namespace Hironaka.HironakaRelativeNormalActualWeightedTruncations
noncomputable section
open HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalActualCompatibleTruncations
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]
variable (I J : Ideal R) (m : Ideal B)

/-- Actual original coordinate weights, including the full unit-weight high-degree tail. -/
def actualWeightedCoordinates (s : ℕ) : Submodule B (⨁ q : ℕ, idealPowerLayer B I J q) where
  carrier := {v | ∀ q, v q ∈ m ^ (s-q) • (⊤ : Submodule B (idealPowerLayer B I J q))}
  zero_mem' := by intro q; exact Submodule.zero_mem _
  add_mem' := by intro v w hv hw q; exact Submodule.add_mem _ (hv q) (hw q)
  smul_mem' := by intro b v hv q; exact Submodule.smul_mem _ b (hv q)

/-- The literal finite weighted sum of the genuine original normal tails. -/
def actualWeightedTailSum (s : ℕ) : Submodule B (⨁ q : ℕ, idealPowerLayer B I J q) :=
  ⨆ q : Fin (s+1), m ^ (s-q.val) • actualNormalTail (B := B) I J q.val

/-- A true degree inclusion lies in its original high-degree tail. -/
theorem actualDegreeRange_le_tail (q : ℕ) :
    (⊤ : Submodule B (idealPowerLayer B I J q)).map
      (DirectSum.lof B ℕ (layerFamily B I J) q) ≤ actualNormalTail (B := B) I J q := by
  rintro v ⟨x,hx,rfl⟩ j hj
  exact DirectSum.of_eq_of_ne (β := layerFamily B I J) q j x (Nat.ne_of_lt hj)

/-- The entire finite weighted tail sum has exactly the original coordinate weights. -/
theorem actualWeightedTailSum_eq_coordinates (s : ℕ) :
    actualWeightedTailSum (B := B) I J m s = actualWeightedCoordinates (B := B) I J m s := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro q
    apply Submodule.smul_le.mpr
    intro b hb v hv j
    change b • v j ∈ m ^ (s-j) • (⊤ : Submodule B (idealPowerLayer B I J j))
    by_cases hjq : j < q.val
    · rw [hv j hjq,smul_zero]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem_smul
        ((Ideal.pow_le_pow_right (by omega : s-j ≤ s-q.val)) hb) Submodule.mem_top
  · intro v hv
    rw [← DirectSum.sum_support_of v]
    apply Submodule.sum_mem
    intro j hj
    change DirectSum.lof B ℕ (layerFamily B I J) j (v j) ∈ actualWeightedTailSum I J m s
    by_cases hjs : j < s
    · have hm : DirectSum.lof B ℕ (layerFamily B I J) j (v j) ∈
          m ^ (s-j) • actualNormalTail (B := B) I J j := by
        apply (smul_mono_right (m ^ (s-j)) (actualDegreeRange_le_tail (B := B) I J j))
        rw [← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem (hv j)
      exact (le_iSup (fun q : Fin (s+1) =>
        m ^ (s-q.val) • actualNormalTail (B := B) I J q.val) ⟨j,by omega⟩) hm
    · have hm : DirectSum.lof B ℕ (layerFamily B I J) j (v j) ∈
          m ^ (s-s) • actualNormalTail (B := B) I J s := by
        rw [Nat.sub_self,pow_zero,Ideal.one_eq_top,Submodule.top_smul]
        intro q hq
        exact DirectSum.of_eq_of_ne (β := layerFamily B I J) j q (v j) (by omega)
      exact (le_iSup (fun q : Fin (s+1) =>
        m ^ (s-q.val) • actualNormalTail (B := B) I J q.val) ⟨s,Nat.lt_succ_self s⟩) hm

/-- Literal whole mixed ideal, before choosing any layer coordinates. -/
def actualMixedPower (s : ℕ) : Ideal R := ((m.map (algebraMap B R)) ⊔ J) ^ s

/-- All true finite mixed terms, with no tangent term discarded. -/
theorem actualMixedPower_eq_iSup (s : ℕ) :
    actualMixedPower (B := B) J m s =
      ⨆ q : Fin (s+1), (m.map (algebraMap B R)) ^ (s-q.val) * J ^ q.val := by
  rw [actualMixedPower,HironakaRelativeNormalMixedTangentPowers.ideal_sup_pow_eq_mixed,
    Ideal.sum_eq_sup]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    exact le_iSup (fun q : Fin (s+1) => (m.map (algebraMap B R)) ^ (s-q.val) * J ^ q.val)
      ⟨q,Finset.mem_range.mp hq⟩
  · apply iSup_le
    intro q
    exact Finset.le_sup (f := fun q => (m.map (algebraMap B R)) ^ (s-q) * J ^ q)
      (Finset.mem_range.mpr q.isLt)

/-- The literal base extension and actual whole ideal product have the SAME original base action. -/
theorem actualMixedPower_restrictScalars (s : ℕ) :
    (actualMixedPower (B := B) J m s).restrictScalars B =
      ⨆ q : Fin (s+1), m ^ (s-q.val) • powerModule B J q.val := by
  rw [actualMixedPower_eq_iSup,Submodule.restrictScalars_iSup]
  apply congrArg iSup
  funext q
  rw [← Ideal.map_pow]
  exact Submodule.restrictScalars_map_smul_eq (m ^ (s-q.val)) (J ^ q.val)

/-- The genuine image of the whole original mixed ideal in the actual normal truncation. -/
def actualMixedPowerImage (s : ℕ) : Submodule B (R ⧸ (I ⊔ J ^ s)) :=
  (actualMixedPower (B := B) J m s).restrictScalars B |>.map
    (Ideal.Quotient.mkₐ B (I ⊔ J ^ s)).toLinearMap

/-- The actual original mixed ideal image is exactly the weighted whole normal filtration. -/
theorem actualMixedPowerImage_eq_weighted (s : ℕ) :
    actualMixedPowerImage (B := B) I J m s =
      ⨆ q : Fin (s+1), m ^ (s-q.val) • actualNormalPowerImage (B := B) I J s q.val := by
  rw [actualMixedPowerImage,actualMixedPower_restrictScalars,Submodule.map_iSup]
  apply congrArg iSup
  funext q
  exact Submodule.map_smul'' _ _ _

/-- The image submodule is the literal actual quotient image IDEAL with its original base action. -/
theorem actualMixedPowerImage_eq_ideal_image (s : ℕ) :
    actualMixedPowerImage (B := B) I J m s =
      (Ideal.map (Ideal.Quotient.mk (I ⊔ J ^ s)) (actualMixedPower (B := B) J m s)).restrictScalars B := by
  ext z
  change (∃ g, g ∈ actualMixedPower (B := B) J m s ∧
    Ideal.Quotient.mk (I ⊔ J ^ s) g = z) ↔
      z ∈ Ideal.map (Ideal.Quotient.mk (I ⊔ J ^ s)) (actualMixedPower (B := B) J m s)
  exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).symm

-- Both quotients use the actual standard module quotient instances.
local instance actualWeightedDirectSumHasQuotient :
    HasQuotient (⨁ q : ℕ, idealPowerLayer B I J q)
      (Submodule B (⨁ q : ℕ, idealPowerLayer B I J q)) :=
  @Submodule.hasQuotient B (⨁ q : ℕ, idealPowerLayer B I J q) _ _ _
local instance actualNormalTruncationHasQuotient (s : ℕ) :
    HasQuotient (R ⧸ (I ⊔ J ^ s)) (Submodule B (R ⧸ (I ⊔ J ^ s))) :=
  @Submodule.hasQuotient B (R ⧸ (I ⊔ J ^ s)) _ _ _

section FreeLayers

variable [∀ q, Module.Free B (idealPowerLayer B I J q)]

/-- The true whole map sends all weighted original coordinates onto the actual mixed ideal image. -/
theorem actualWeightedCoordinates_map (s : ℕ) :
    (actualWeightedCoordinates (B := B) I J m s).map
      (actualNormalTruncationMap (B := B) I J s) = actualMixedPowerImage (B := B) I J m s := by
  rw [← actualWeightedTailSum_eq_coordinates,actualWeightedTailSum,Submodule.map_iSup,
    actualMixedPowerImage_eq_weighted]
  apply congrArg iSup
  funext q
  rw [Submodule.map_smul'',actualNormalTruncationMap_tail_image]

omit [∀ q, Module.Free B (idealPowerLayer B I J q)] in
/-- The entire actual kernel is contained in the original unit-weight final summand. -/
theorem actualNormalTail_le_weighted (s : ℕ) :
    actualNormalTail (B := B) I J s ≤ actualWeightedCoordinates (B := B) I J m s := by
  intro v hv q
  by_cases hqs : q < s
  · rw [hv q hqs]
    exact Submodule.zero_mem _
  · rw [Nat.sub_eq_zero_of_le (by omega : s ≤ q),pow_zero,Ideal.one_eq_top,Submodule.top_smul]
    exact Submodule.mem_top

/-- The genuine weighted mixed ideal preimage is EXACTLY the entire original coordinate-weight submodule. -/
theorem actualMixedPowerImage_comap (s : ℕ) :
    (actualMixedPowerImage (B := B) I J m s).comap
      (actualNormalTruncationMap (B := B) I J s) = actualWeightedCoordinates (B := B) I J m s := by
  ext v
  change actualNormalTruncationMap (B := B) I J s v ∈ actualMixedPowerImage (B := B) I J m s ↔
    v ∈ actualWeightedCoordinates (B := B) I J m s
  rw [← actualWeightedCoordinates_map]
  constructor
  · rintro ⟨w,hw,he⟩
    have hdiff : v-w ∈ actualNormalTail (B := B) I J s := by
      apply (actualNormalTruncationMap_eq_zero_iff (B := B) I J s (v-w)).mp
      rw [map_sub,he,sub_self]
    have hmem := (actualWeightedCoordinates (B := B) I J m s).add_mem hw
      (actualNormalTail_le_weighted (B := B) I J m s hdiff)
    have hvw : w+(v-w)=v := by abel
    rw [hvw] at hmem
    exact hmem
  · intro hv
    exact Submodule.mem_map_of_mem hv

/-- The actual normal truncation quotient by its TRUE original mixed ideal image. -/
abbrev actualWeightedTruncation (s : ℕ) :=
  (R ⧸ (I ⊔ J ^ s)) ⧸ actualMixedPowerImage (B := B) I J m s

/-- The original WHOLE representative map followed by the two actual quotient maps. -/
def actualWeightedTruncationMap (s : ℕ) :
    (⨁ q : ℕ, idealPowerLayer B I J q) →ₗ[B] actualWeightedTruncation (B := B) I J m s :=
  (actualMixedPowerImage (B := B) I J m s).mkQ.comp (actualNormalTruncationMap (B := B) I J s)

/-- Every actual double-quotient class has a preimage in the WHOLE original direct sum. -/
theorem actualWeightedTruncationMap_surjective (s : ℕ) :
    Function.Surjective (actualWeightedTruncationMap (B := B) I J m s) :=
  (Submodule.Quotient.mk_surjective (actualMixedPowerImage (B := B) I J m s)).comp
    (actualNormalTruncationMap_surjective (B := B) I J s)

/-- The FULL kernel of the true mixed weighted quotient is the literal coordinate-weight submodule. -/
theorem actualWeightedTruncationMap_ker (s : ℕ) :
    LinearMap.ker (actualWeightedTruncationMap (B := B) I J m s) =
      actualWeightedCoordinates (B := B) I J m s := by
  rw [actualWeightedTruncationMap,LinearMap.ker_comp,Submodule.ker_mkQ,
    actualMixedPowerImage_comap]

/-- The WHOLE original coordinate-weight quotient is the actual weighted normal truncation. -/
def actualWeightedWholeQuotientEquiv (s : ℕ) :
    ((⨁ q : ℕ, idealPowerLayer B I J q) ⧸ actualWeightedCoordinates (B := B) I J m s) ≃ₗ[B]
      actualWeightedTruncation (B := B) I J m s :=
  (Submodule.quotEquivOfEq _ _ (actualWeightedTruncationMap_ker (B := B) I J m s).symm).trans
    ((actualWeightedTruncationMap (B := B) I J m s).quotKerEquivOfSurjective
      (actualWeightedTruncationMap_surjective (B := B) I J m s))

/-- EVERY whole representative keeps the SAME actual original double-quotient class. -/
theorem actualWeightedWholeQuotientEquiv_mk (s : ℕ)
    (v : ⨁ q : ℕ, idealPowerLayer B I J q) :
    actualWeightedWholeQuotientEquiv (B := B) I J m s (Submodule.Quotient.mk v) =
      actualWeightedTruncationMap (B := B) I J m s v := by
  simp only [actualWeightedWholeQuotientEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]

end FreeLayers

local instance actualLayerHasQuotient (q : ℕ) :
    HasQuotient (idealPowerLayer B I J q) (Submodule B (idealPowerLayer B I J q)) :=
  @Submodule.hasQuotient B (idealPowerLayer B I J q) _ _ _

/-- The genuine quotient of the actual original layer by its whole original tangent weight. -/
abbrev actualWeightedLayerQuotient (s q : ℕ) :=
  (idealPowerLayer B I J q) ⧸ (m ^ (s-q) • (⊤ : Submodule B (idealPowerLayer B I J q)))

section GenericLayerQuotient
variable {L : ℕ → Type*} [∀ q, AddCommGroup (L q)] [∀ q, Module B (L q)]

/-- True coordinate weights for an arbitrary family with its given ORIGINAL module actions. -/
def weightedLayerCoordinates (s : ℕ) : Submodule B (⨁ q, L q) where
  carrier := {v | ∀ q, v q ∈ m ^ (s-q) • (⊤ : Submodule B (L q))}
  zero_mem' := by intro q; exact Submodule.zero_mem _
  add_mem' := by intro v w hv hw q; exact Submodule.add_mem _ (hv q) (hw q)
  smul_mem' := by intro b v hv q; exact Submodule.smul_mem _ b (hv q)

abbrev weightedLayerQuotient (s q : ℕ) := (L q) ⧸ (m ^ (s-q) • (⊤ : Submodule B (L q)))

/-- The given original module-family coordinates map to their actual finite family of quotients. -/
def weightedLayerFunctionMap (s : ℕ) :
    (⨁ q, L q) →ₗ[B] ∀ j : Fin s, weightedLayerQuotient (L := L) m s j.val :=
  LinearMap.pi (fun j => (m ^ (s-j.val) • (⊤ : Submodule B (L j.val))).mkQ.comp
    (DirectSum.component B ℕ L j.val))

theorem weightedLayerFunctionMap_surjective (s : ℕ) :
    Function.Surjective (weightedLayerFunctionMap (L := L) m s) := by
  classical
  intro z
  let rep (j : Fin s) : L j.val := Classical.choose
    (Submodule.Quotient.mk_surjective (R := B) (M := L j.val)
      (m ^ (s-j.val) • (⊤ : Submodule B (L j.val))) (z j))
  let v : ⨁ q, L q := DFinsupp.mk (Finset.range s)
    (fun q => rep ⟨q.val,Finset.mem_range.mp q.property⟩)
  refine ⟨v,?_⟩
  funext j
  change (Submodule.Quotient.mk (DFinsupp.mk (β := L) (Finset.range s)
    (fun q => rep ⟨q.val,Finset.mem_range.mp q.property⟩) j.val) :
      weightedLayerQuotient (L := L) m s j.val) = z j
  rw [DFinsupp.mk_of_mem (Finset.mem_range.mpr j.isLt)]
  exact Classical.choose_spec (Submodule.Quotient.mk_surjective (R := B) (M := L j.val)
    (m ^ (s-j.val) • (⊤ : Submodule B (L j.val))) (z j))

theorem weightedLayerFunctionMap_ker (s : ℕ) :
    LinearMap.ker (weightedLayerFunctionMap (L := L) m s) = weightedLayerCoordinates (L := L) m s := by
  ext v
  change weightedLayerFunctionMap (L := L) m s v = 0 ↔
    ∀ q, v q ∈ m ^ (s-q) • (⊤ : Submodule B (L q))
  constructor
  · intro hv q
    by_cases hqs : q < s
    · have hz := congrFun hv ⟨q,hqs⟩
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    · rw [Nat.sub_eq_zero_of_le (by omega : s ≤ q),pow_zero,Ideal.one_eq_top,Submodule.top_smul]
      exact Submodule.mem_top
  · intro hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hv j.val)

/-- The true whole quotient of a GIVEN module family is its finite sum of genuine quotient layers. -/
def weightedLayerQuotientEquiv (s : ℕ) :
    ((⨁ q, L q) ⧸ weightedLayerCoordinates (L := L) m s) ≃ₗ[B]
      ⨁ j : Fin s, weightedLayerQuotient (L := L) m s j.val := by
  let e : ((⨁ q, L q) ⧸ weightedLayerCoordinates (L := L) m s) ≃ₗ[B]
      ∀ j : Fin s, weightedLayerQuotient (L := L) m s j.val :=
    (Submodule.quotEquivOfEq _ _ (weightedLayerFunctionMap_ker (L := L) m s).symm).trans
      ((weightedLayerFunctionMap (L := L) m s).quotKerEquivOfSurjective
        (weightedLayerFunctionMap_surjective (L := L) m s))
  exact e.trans (DirectSum.linearEquivFunOnFintype B (Fin s)
    (fun j => weightedLayerQuotient (L := L) m s j.val)).symm
end GenericLayerQuotient

/-- The original coordinate-weight quotient is genuinely the finite sum of its SAME weighted layers. -/
def actualWeightedLayerQuotientEquiv (s : ℕ) :
    ((⨁ q : ℕ, idealPowerLayer B I J q) ⧸ actualWeightedCoordinates (B := B) I J m s) ≃ₗ[B]
      ⨁ j : Fin s, actualWeightedLayerQuotient (B := B) I J m s j.val :=
  weightedLayerQuotientEquiv (L := layerFamily B I J) m s

/-- The original normal power is retained as the unit-weight final mixed term. -/
theorem actualNormalPower_le_mixed (s : ℕ) : J ^ s ≤ actualMixedPower (B := B) J m s := by
  rw [actualMixedPower_eq_iSup]
  have h := le_iSup (fun q : Fin (s+1) =>
    (m.map (algebraMap B R)) ^ (s-q.val) * J ^ q.val) ⟨s,Nat.lt_succ_self s⟩
  simpa only [Nat.sub_self,pow_zero,one_mul] using h

/-- The literal true double-quotient kernel is the original mixed ambient kernel. -/
theorem actualMixedDoubleKernel (s : ℕ) :
    (I ⊔ J ^ s) ⊔ actualMixedPower (B := B) J m s = I ⊔ actualMixedPower (B := B) J m s := by
  rw [sup_assoc,sup_eq_right.mpr (actualNormalPower_le_mixed (B := B) J m s)]

/-- The genuine module quotient and the actual ring quotient use the SAME original base scalar action. -/
def actualWeightedImageRingQuotientEquiv (s : ℕ) :
    actualWeightedTruncation (B := B) I J m s ≃ₗ[B]
      ((R ⧸ (I ⊔ J ^ s)) ⧸ Ideal.map (Ideal.Quotient.mk (I ⊔ J ^ s))
        (actualMixedPower (B := B) J m s)) := by
  let K := Ideal.map (Ideal.Quotient.mk (I ⊔ J ^ s)) (actualMixedPower (B := B) J m s)
  let e : actualWeightedTruncation (B := B) I J m s ≃+
      ((R ⧸ (I ⊔ J ^ s)) ⧸ K) :=
    (Submodule.quotEquivOfEq _ _ (actualMixedPowerImage_eq_ideal_image (B := B) I J m s)).toAddEquiv
  refine { e with map_smul' := ?_ }
  intro b z
  obtain ⟨g,rfl⟩ := Submodule.Quotient.mk_surjective (actualMixedPowerImage (B := B) I J m s) z
  change Ideal.Quotient.mk K (b • g) = b • Ideal.Quotient.mk K g
  exact (Ideal.Quotient.mkₐ B K).toLinearMap.map_smul b g

/-- The true base-module weighted truncation is the genuine whole ambient mixed-power quotient. -/
def actualWeightedAmbientEquiv (s : ℕ) :
    actualWeightedTruncation (B := B) I J m s ≃ₗ[B] R ⧸ (I ⊔ actualMixedPower (B := B) J m s) :=
  (actualWeightedImageRingQuotientEquiv (B := B) I J m s).trans
    (((DoubleQuot.quotQuotEquivQuotSupₐ B (I ⊔ J ^ s) (actualMixedPower (B := B) J m s)).trans
      (Ideal.quotientEquivAlgOfEq B (actualMixedDoubleKernel (B := B) I J m s))).toLinearEquiv)

/-- Every original WHOLE numerator retains its same true ambient class. -/
theorem actualWeightedAmbientEquiv_mk (s : ℕ) (g : R) :
    actualWeightedAmbientEquiv (B := B) I J m s
      (Submodule.Quotient.mk (Ideal.Quotient.mk (I ⊔ J ^ s) g)) =
        Ideal.Quotient.mk (I ⊔ actualMixedPower (B := B) J m s) g := by
  exact Ideal.quotientEquivAlgOfEq_mk B (actualMixedDoubleKernel (B := B) I J m s) g

section FreeAmbient
variable [∀ q, Module.Free B (idealPowerLayer B I J q)]

/-- The ACTUAL whole ambient quotient decomposes into the SAME genuinely weighted original layers. -/
def actualAmbientWeightedLayersEquiv (s : ℕ) :
    (R ⧸ (I ⊔ actualMixedPower (B := B) J m s)) ≃ₗ[B]
      ⨁ j : Fin s, actualWeightedLayerQuotient (B := B) I J m s j.val :=
  (actualWeightedAmbientEquiv (B := B) I J m s).symm.trans
    ((actualWeightedWholeQuotientEquiv (B := B) I J m s).symm.trans
      (actualWeightedLayerQuotientEquiv (B := B) I J m s))
end FreeAmbient

end

open Hironaka.HolomorphicIdealSheaves HolGerm Set Filter
  HironakaRelativeNormalGradedAlgebra
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalNearbyUniformRanks HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalFibreHilbertSamuel
open scoped Topology Manifold ContDiff

/-- The SAME actual tangent-base extension makes the literal mixed power the genuine ambient maximal power. -/
theorem originalActualMixedPower_eq_maximalIdeal_power (d t s : ℕ) :
    let := tangentAlgebra d t
    actualMixedPower (B := HolGerm (ComplexModel d)) (normalIdeal d t)
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) s =
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s := by
  let := tangentAlgebra d t
  change (originalBaseMaximalIdeal d t ⊔ normalIdeal d t) ^ s = _
  rw [baseMaximalIdeal_sup_normalIdeal]

/-- ONLY original coherence gives the actual AMBIENT weighted-layer decomposition on the SAME open, with true complex scalars. -/
theorem exists_original_nearby_ambient_weighted_layer_decomposition (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
      IsScalarTower.of_algHom (tangentPullback d t)
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
        ∃ hfree : ∀ q, Module.Free (HolGerm (ComplexModel d))
          (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q),
          (∀ q, Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) ∧
            Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t Ia q) = r q) ∧
          letI := hfree
          ∀ s : ℕ, Nonempty
            ((HolGerm (ComplexModel (d+t)) ⧸
              (Ia ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s)) ≃ₗ[ℂ]
                ⨁ j : Fin s, actualWeightedLayerQuotient (B := HolGerm (ComplexModel d))
                  Ia (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) s j.val) := by
  let := tangentAlgebra d t
  let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    IsScalarTower.of_algHom (tangentPullback d t)
  obtain ⟨U,r,hU,hmeet,hdegree⟩ := exists_original_nearby_all_degree_uniform_rank_open d t I hI
  refine ⟨U,r,hU,hmeet,?_⟩
  intro a ha
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  let hfree : ∀ q, Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hdegree a ha q).1
  refine ⟨hfree,fun q => (hdegree a ha q).2,?_⟩
  let := hfree
  intro s
  let e := actualAmbientWeightedLayersEquiv (B := HolGerm (ComplexModel d))
    Ia (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) s
  let em := Ideal.quotientEquivAlgOfEq ℂ
    (congrArg (fun J => Ia ⊔ J) (originalActualMixedPower_eq_maximalIdeal_power d t s).symm)
  exact ⟨em.toLinearEquiv.trans (e.restrictScalars ℂ)⟩

end Hironaka.HironakaRelativeNormalActualWeightedTruncations

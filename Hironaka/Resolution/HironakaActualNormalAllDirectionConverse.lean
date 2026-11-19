import Hironaka.Resolution.HironakaActualNormalMarkedDirection
import Hironaka.Resolution.HironakaActualInheritedNormalInsertion
import Hironaka.Resolution.HironakaActualCanonicalNormalDirectionOrder
import Hironaka.Resolution.HironakaActualNormalRename

/-! All-direction formal converse for the SAME full source family. Auxiliary
source shears and normal insertion use actual formal monic/head interfaces;
no analytic realization of a sheared formal family is presumed. Original-chart
HS and exceptional regularity are outputs. Raw original-chart diagrams need
not equal the original source diagram. Source-only draft, not kernel checked. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalAllDirectionConverse
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalBlowupAllDirections
  HironakaActualFormalStrictGenerators HironakaActualReducedBasisDivision
  HironakaActualRelativeStandardnessInheritedDivision HironakaActualNormalZeroOwnerConverse
  HironakaActualNormalZeroFormalSaturation HironakaActualNormalMarkedDirection
  HironakaActualCanonicalTriangularShear HironakaActualCanonicalNormalDirectionOrder
  HironakaActualNormalCentreChartTransition HironakaActualPointChartTransition
  HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualRelativeStandardnessPivotPriority
  HironakaActualNormalRename HironakaActualInheritedNormalInsertion
  HironakaActualInheritedSourceOwnerPermutation HironakaActualRelativeStandardnessNormalPointBridge

private def MonicAt {m : ℕ} (F : MvPowerSeries (Fin m) ℂ) (a : Fin m →₀ ℕ) : Prop :=
  MvPowerSeries.coeff a F = 1 ∧ ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a →
    MvPowerSeries.coeff β F = 0

private theorem monicAt_mul {m : ℕ} (F G : MvPowerSeries (Fin m) ℂ) (a c : Fin m →₀ ℕ)
    (hF : MonicAt F a) (hG : MonicAt G c) : MonicAt (F*G) (a+c) := by
  have hFn : F ≠ 0 := by intro h; exact one_ne_zero (hF.1.symm.trans (by rw [h, map_zero]))
  have hGn : G ≠ 0 := by intro h; exact one_ne_zero (hG.1.symm.trans (by rw [h, map_zero]))
  have ha := actualInitialExponent_eq_of_coefficients MonomialOrder.degLex F hFn a
    (by rw [hF.1]; exact one_ne_zero) hF.2
  have hc := actualInitialExponent_eq_of_coefficients MonomialOrder.degLex G hGn c
    (by rw [hG.1]; exact one_ne_zero) hG.2
  constructor
  · simpa only [ha, hc, hF.1, hG.1, one_mul] using
      coeff_mul_actualInitialExponent MonomialOrder.degLex F G hFn hGn
  · intro β hβ
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (F*G) (mul_ne_zero hFn hGn) β
    rwa [actualInitialExponent_mul MonomialOrder.degLex F G hFn hGn, ha, hc]

private theorem shear_product_monic {m : ℕ} (f : Fin m) (w : Fin m → ℂ)
    (htri : ∀ i, i ≠ f → w i ≠ 0 → MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single f 1)) (α : Fin m →₀ ℕ) :
    MonicAt (α.prod fun i k => actualFormalCenterShearCoordinates Set.univ f w i ^ k) α := by
  have h1 : MonicAt (1 : MvPowerSeries (Fin m) ℂ) 0 := by
    constructor
    · simp
    · intro β hβ
      rw [map_zero] at hβ
      exact False.elim ((not_lt_of_ge (MonomialOrder.degLex.zero_le _)) hβ)
  have hp (i : Fin m) (k : ℕ) : MonicAt (actualFormalCenterShearCoordinates Set.univ f w i ^ k) (Finsupp.single i k) := by
    induction k with
    | zero => simpa only [pow_zero, Finsupp.single_zero] using h1
    | succ k ih =>
      simpa only [pow_succ, Finsupp.single_add] using monicAt_mul _ _ _ _ ih
        (actualFormalCenterShear_coordinate_initial_data MonomialOrder.degLex f w htri i)
  have hs (s : Finset (Fin m)) : MonicAt (∏ i ∈ s, actualFormalCenterShearCoordinates Set.univ f w i ^ α i)
      (∑ i ∈ s, Finsupp.single i (α i)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using h1
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using monicAt_mul _ _ _ _ (hp i (α i)) ih
  have he : (∑ i ∈ α.support, Finsupp.single i (α i)) = α := by simpa only [Finsupp.sum] using α.sum_single
  simpa only [Finsupp.prod, he] using hs α.support

/-- The generic accepted shear-head calculation also retains the SAME monic
coefficient, needed when the auxiliary family is not canonical. -/
theorem actualFormalCenterShear_same_monic {m : ℕ} (f : Fin m) (w : Fin m → ℂ)
    (htri : ∀ i, i ≠ f → w i ≠ 0 → MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single f 1))
    (a : Fin m →₀ ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (hc : MvPowerSeries.coeff a F = 1)
    (hl : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a → MvPowerSeries.coeff β F = 0) :
    MvPowerSeries.coeff a (actualFormalCenterShear Set.univ f w F) = 1 ∧
      ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a →
        MvPowerSeries.coeff β (actualFormalCenterShear Set.univ f w F) = 0 := by
  have hF : F ≠ 0 := by intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  have hhead := actualInitialExponent_eq_of_coefficients MonomialOrder.degLex F hF a
    (by rw [hc]; exact one_ne_zero) hl
  obtain ⟨hSF, hShead⟩ := actualFormalCenterShear_initialExponent MonomialOrder.degLex f w htri F hF
  constructor
  · rw [actualFormalCenterShear, MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (actualFormalCenterShearCoordinates_constant_zero Set.univ f w)) F a]
    rw [finsum_eq_single _ a]
    · rw [(shear_product_monic f w htri a).1, hc]
      simp
    · intro β hβ
      by_cases hz : MvPowerSeries.coeff β F = 0
      · rw [hz, zero_smul]
      · have hlt : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β := by
          apply lt_of_le_of_ne
          · simpa only [hhead] using (actualInitialExponent_spec MonomialOrder.degLex F hF).2 β hz
          · intro he
            exact hβ (MonomialOrder.degLex.toSyn.injective he).symm
        rw [(shear_product_monic f w htri β).2 a hlt, smul_zero]
  · intro β hβ
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hSF β
    rwa [hShead, hhead]

private theorem minimal_image_iff {m : ℕ} (p : Fin m ≃ Fin m) (D : Set (Fin m →₀ ℕ)) (α : Fin m →₀ ℕ) :
    Minimal (· ∈ Finsupp.domCongr p '' D) (Finsupp.domCongr p α) ↔ Minimal (· ∈ D) α := by
  constructor
  · intro h
    have hα : α ∈ D := by
      obtain ⟨β, hβ, he⟩ := h.prop
      exact (Finsupp.domCongr p).injective he ▸ hβ
    refine ⟨hα, ?_⟩
    intro β hβ hβα
    exact (sourceExponentPermutation_le_iff p α β).mp
      (h.2 ⟨β, hβ, rfl⟩ ((sourceExponentPermutation_le_iff p β α).mpr hβα))
  · intro h
    refine ⟨⟨α, h.prop, rfl⟩, ?_⟩
    rintro γ ⟨β, hβ, rfl⟩ hβα
    exact (sourceExponentPermutation_le_iff p α β).mpr
      (h.2 hβ ((sourceExponentPermutation_le_iff p β α).mp hβα))

private def vertexEquivOfDiagram {m : ℕ}
    (K J : Ideal (MvPowerSeries (Fin m) ℂ)) (p : Fin m ≃ Fin m)
    (hD : actualInitialDiagram MonomialOrder.degLex J = Finsupp.domCongr p '' actualInitialDiagram MonomialOrder.degLex K) :
    actualInitialVertices MonomialOrder.degLex K ≃ actualInitialVertices MonomialOrder.degLex J where
  toFun a := ⟨Finsupp.domCongr p a.val, by
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    have h := (minimal_image_iff p _ _).mpr ha
    rw [← hD] at h
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using h⟩
  invFun a := ⟨(Finsupp.domCongr p).symm a.val, by
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex J) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    rw [hD] at ha
    have h := (minimal_image_iff p _ ((Finsupp.domCongr p).symm a.val)).mp
      (by simpa only [AddEquiv.apply_symm_apply] using ha)
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using h⟩
  left_inv a := Subtype.ext ((Finsupp.domCongr p).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((Finsupp.domCongr p).apply_symm_apply a.val)

private theorem degree_permutation {m : ℕ} (p : Fin m ≃ Fin m) (α : Fin m →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  unfold normalExponentDegree
  exact Fintype.sum_equiv p.symm _ _ (fun i => sourceExponentPermutation_apply p α i)

private theorem normal_pivot_mem {n : ℕ} (q f : Fin (n+1)) (hqf : q ≤ f) (i : Fin (n+1)) :
    normalPivotEquiv q f i ∈ Set.Ici q ↔ i ∈ Set.Ici q := by
  constructor
  · intro hi
    by_contra h
    have ht := normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    by_contra h
    have hpi : normalPivotEquiv q f i < q := lt_of_not_ge h
    have hfix := normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hpi
    have heq : normalPivotEquiv q f i = i := (normalPivotEquiv q f).injective hfix
    rw [heq] at hpi
    exact (not_lt_of_ge hi) hpi

/-- The actual auxiliary source ideal, using only origin-preserving FORMAL maps. -/
def actualNormalAdaptedSourceIdeal {n : ℕ} (K : Ideal (MvPowerSeries (Fin (n+1)) ℂ))
    (q e f : Fin (n+1)) (b : Fin (n+1) → ℂ) : Ideal (MvPowerSeries (Fin (n+1)) ℂ) :=
  Ideal.map (normalPivotRename q f).toRingHom
    (Ideal.map (actualFormalCenterShear (Set.Ici q) f
      (fun i => actualNormalMarkedDirection (Set.Ici q) e b i / actualNormalMarkedDirection (Set.Ici q) e b f)).toRingHom K)

/-- All current labels, SAME members, source marks and normalized orders of the
adapted zero family are PRODUCED. No target monicness or diagram input is used. -/
theorem exists_same_formal_normal_adapted_family_of_marked_orders {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin (n+1)) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (q e : Fin (n+1)) (hqe : q ≤ e) (b : Fin (n+1) → ℂ)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal (n+1) (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, actualNormalizedFormalMember (Set.Ici q) e hqe b
      (normalExponentDegree a.val) (B.series a) (hpower a) ∈ genuineFormalVariables (n+1) ^ normalExponentDegree a.val) :
    ∃ f : Fin (n+1), ∃ hqf : q ≤ f, actualNormalMarkedDirection (Set.Ici q) e b f ≠ 0 ∧
      ∃ E : actualInitialVertices MonomialOrder.degLex K ≃
        actualInitialVertices MonomialOrder.degLex (actualNormalAdaptedSourceIdeal K q e f b),
      ∃ BP : ActualMonicVertexFamily MonomialOrder.degLex (actualNormalAdaptedSourceIdeal K q e f b),
      ∃ hp : ∀ a, BP.series a ∈ actualFormalCoordinateIdeal (n+1) (Set.Ici q) ^ normalExponentDegree a.val,
      (∀ a, (E a).val = Finsupp.domCongr (normalPivotEquiv q f) a.val) ∧
      (∀ a, BP.series (E a) = normalPivotRename q f
        (actualFormalCenterShear (Set.Ici q) f
          (fun i => actualNormalMarkedDirection (Set.Ici q) e b i / actualNormalMarkedDirection (Set.Ici q) e b f) (B.series a))) ∧
      (∀ a, sameMonicZeroNormalizedVertex (actualNormalAdaptedSourceIdeal K q e f b) BP q hp a ∈
        genuineFormalVariables (n+1) ^ normalExponentDegree a.val) ∧
      (∀ ℓ, genuineFormalHilbertSamuelValue (n+1) (actualNormalAdaptedSourceIdeal K q e f b) ℓ =
        genuineFormalHilbertSamuelValue (n+1) K ℓ) ∧
      Ideal.map (normalPivotRename q f).toRingHom
        (actualFormalStrictTransform K (Set.Ici q) f hqf
          (fun i => actualNormalMarkedDirection (Set.Ici q) e b i / actualNormalMarkedDirection (Set.Ici q) e b f)) =
        actualFormalStrictTransform (actualNormalAdaptedSourceIdeal K q e f b) (Set.Ici q) q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0) := by
  let A := Set.Ici q
  let v := actualNormalMarkedDirection A e b
  obtain ⟨f, hfA, hvf, hmax, hf⟩ := exists_actual_normal_unused_pivot_of_marked_orders K B A e hqe b hpower horder
  let w (i : Fin (n+1)) := v i / v f
  have hwA (i : Fin (n+1)) (hi : i ∉ A) : w i = 0 := by
    have hie : i ≠ e := by intro h; subst i; exact hi hqe
    simp [w, v, actualNormalMarkedDirection, hie, actualNormalPointDirection, hi]
  have htri : ∀ i, i ≠ f → w i ≠ 0 → MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single f 1) := by
    intro i hif hwi
    have hvi : v i ≠ 0 := by intro h; exact hwi (by simp only [w, h, zero_div])
    apply lt_of_le_of_ne (hmax i hvi)
    intro heq
    exact hif (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
      (MonomialOrder.degLex.toSyn.injective heq))
  let S := actualFormalCenterShear A f w
  let KS := Ideal.map S.toRingHom K
  have hS := actualFormalCenterShear_normal_eq_point A f w hwA
  have hDS : actualInitialDiagram MonomialOrder.degLex KS = actualInitialDiagram MonomialOrder.degLex K := by
    dsimp only [KS, S]
    rw [hS]
    exact actualInitialDiagram_map_centerShear MonomialOrder.degLex K f w htri
  have hVS : actualInitialVertices MonomialOrder.degLex KS = actualInitialVertices MonomialOrder.degLex K := by
    ext α
    simp only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hDS]
  let ES : actualInitialVertices MonomialOrder.degLex K ≃ actualInitialVertices MonomialOrder.degLex KS :=
    { toFun := fun a => ⟨a.val, by simpa only [hVS] using a.property⟩
      invFun := fun a => ⟨a.val, by simpa only [hVS] using a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hSmonic (a : actualInitialVertices MonomialOrder.degLex K) :
      MvPowerSeries.coeff a.val (S (B.series a)) = 1 ∧
        ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a.val →
          MvPowerSeries.coeff β (S (B.series a)) = 0 := by
    simpa only [S, hS] using actualFormalCenterShear_same_monic f w htri a.val
      (B.series a) (B.monic a) (B.lower a)
  let BS : ActualMonicVertexFamily MonomialOrder.degLex KS :=
    { series := fun a => S (B.series (ES.symm a))
      mem := fun a => Ideal.mem_map_of_mem _ (B.mem (ES.symm a))
      monic := fun a => (hSmonic (ES.symm a)).1
      lower := fun a β hβ => (hSmonic (ES.symm a)).2 β hβ }
  have hBSf (a : actualInitialVertices MonomialOrder.degLex KS) : a.val f = 0 := by
    obtain ⟨a, rfl⟩ := ES.surjective a
    exact hf a
  let p := normalPivotEquiv q f
  have hpf : p f = q := normalPivotEquiv_pivot q f hfA
  let KP := actualNormalAdaptedSourceIdeal K q e f b
  have hDP : actualInitialDiagram MonomialOrder.degLex KP = Finsupp.domCongr p '' actualInitialDiagram MonomialOrder.degLex KS := by
    apply actual_initial_diagram_rename_of_same_family_heads KS BS p
    intro a
    exact (normalInsertion_same_member_monic q f hfA a.val (BS.series a) (hBSf a) (BS.monic a) (BS.lower a)).2
  let EP := vertexEquivOfDiagram KS KP p hDP
  let E := ES.trans EP
  have hE (a : actualInitialVertices MonomialOrder.degLex K) : (E a).val = Finsupp.domCongr p a.val := by rfl
  have hEPval (a : actualInitialVertices MonomialOrder.degLex KP) :
      Finsupp.domCongr p (EP.symm a).val = a.val := congrArg Subtype.val (EP.apply_symm_apply a)
  let BP : ActualMonicVertexFamily MonomialOrder.degLex KP :=
    { series := fun a => normalPivotRename q f (BS.series (EP.symm a))
      mem := fun a => Ideal.mem_map_of_mem _ (BS.mem (EP.symm a))
      monic := fun a => by
        have h : MvPowerSeries.coeff (Finsupp.domCongr p (EP.symm a).val)
            (normalPivotRename q f (BS.series (EP.symm a))) = 1 :=
          (normalInsertion_same_member_monic q f hfA (EP.symm a).val
            (BS.series (EP.symm a)) (hBSf _) (BS.monic _) (BS.lower _)).1
        rw [hEPval a] at h
        exact h
      lower := fun a β hβ => by
        have hlt : MonomialOrder.degLex.toSyn β <
            MonomialOrder.degLex.toSyn (Finsupp.domCongr p (EP.symm a).val) := by
          rw [hEPval a]
          exact hβ
        exact (normalInsertion_same_member_monic q f hfA (EP.symm a).val
          (BS.series (EP.symm a)) (hBSf _) (BS.monic _) (BS.lower _)).2 β hlt }
  have hBlit (a : actualInitialVertices MonomialOrder.degLex K) : BP.series (E a) = normalPivotRename q f (S (B.series a)) := by
    simp only [BP, E, Equiv.trans_apply, Equiv.symm_apply_apply, BS]
  have hpS (a : actualInitialVertices MonomialOrder.degLex K) : S (B.series a) ∈
      actualFormalCoordinateIdeal (n+1) A ^ normalExponentDegree a.val :=
    (mem_coordinate_power_iff_centerShear A f hfA w _ _).mp (hpower a)
  have hp (a : actualInitialVertices MonomialOrder.degLex KP) : BP.series a ∈
      actualFormalCoordinateIdeal (n+1) A ^ normalExponentDegree a.val := by
    obtain ⟨a, rfl⟩ := E.surjective a
    rw [hBlit, hE, degree_permutation]
    exact (mem_normal_power_iff_normalPivot q f hfA _ _).mp (hpS a)
  have hve : v e = 1 := by simp only [v, actualNormalMarkedDirection, if_true]
  have hnormdir (a : actualInitialVertices MonomialOrder.degLex K) :
      actualNormalizedFormalMember A e hqe v (normalExponentDegree a.val) (B.series a) (hpower a) =
        actualNormalizedFormalMember A e hqe b (normalExponentDegree a.val) (B.series a) (hpower a) := by
    apply actualNormalizedFormalMember_unique A e hqe b _ (B.series a) (hpower a)
    have hc : actualFormalBlowup A e v = actualFormalBlowup A e b := by
      apply AlgHom.ext
      intro F
      have hcoords : actualFormalBlowupCoordinates A e v = actualFormalBlowupCoordinates A e b := by
        funext i
        by_cases hi : i ∈ A <;> by_cases hie : i=e <;>
          simp [actualFormalBlowupCoordinates, v, actualNormalMarkedDirection, actualNormalPointDirection, hi, hie]
      simp only [actualFormalBlowup, MvPowerSeries.substAlgHom_apply, hcoords]
    exact (actualNormalizedFormalMember_spec A e hqe v _ (B.series a) (hpower a)).trans
      (DFunLike.congr_fun hc (B.series a))
  have hOp (a : actualInitialVertices MonomialOrder.degLex KP) :
      sameMonicZeroNormalizedVertex KP BP q hp a ∈ genuineFormalVariables (n+1) ^ normalExponentDegree a.val := by
    obtain ⟨a, rfl⟩ := E.surjective a
    have hoV : actualNormalizedFormalMember A e hqe v _ (B.series a) (hpower a) ∈
        genuineFormalVariables (n+1) ^ normalExponentDegree a.val := by rw [hnormdir a]; exact horder a
    have hoW := (normalized_member_mem_power_iff_normal_chart_transition A e f hqe hfA v hve hvf
      _ (B.series a) (hpower a) _).mp hoV
    have hoS : actualNormalizedFormalMember A f hfA (fun _ => 0) _ (S (B.series a)) (hpS a) ∈
        genuineFormalVariables (n+1) ^ normalExponentDegree a.val := by
      rwa [actualNormalizedFormalMember_normal_zero_centerShear A f hfA w _ _ _]
    have hoP := (mem_variables_power_iff_normalPivot q f _ _).mp hoS
    have heq : sameMonicZeroNormalizedVertex KP BP q hp (E a) = normalPivotRename q f
        (actualNormalizedFormalMember A f hfA (fun _ => 0) _ (S (B.series a)) (hpS a)) := by
      symm
      apply actualNormalizedFormalMember_unique A q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0) _ (BP.series (E a)) (hp (E a))
      rw [hE, degree_permutation]
      have hren := congrArg (normalPivotRename q f)
        (actualNormalizedFormalMember_spec A f hfA (fun _ => 0) _ (S (B.series a)) (hpS a))
      have hxrename : normalPivotRename q f (MvPowerSeries.X f) = MvPowerSeries.X q := by
        change MvPowerSeries.rename p (MvPowerSeries.X f) = MvPowerSeries.X q
        rw [MvPowerSeries.rename_X, hpf]
      rw [map_mul, map_pow, hxrename] at hren
      have htarget := rename_actual_normal_blowup p A (normal_pivot_mem q f hfA) f (fun _ => 0) (S (B.series a))
      rw [hpf] at htarget
      change normalPivotRename q f (actualFormalBlowup A f (fun _ => 0) (S (B.series a))) =
        actualFormalBlowup A q (fun _ => 0) (normalPivotRename q f (S (B.series a))) at htarget
      exact hren.trans (htarget.trans (congrArg (actualFormalBlowup A q (fun _ => 0)) (hBlit a).symm))
    rw [heq, hE, degree_permutation]
    exact hoP
  have hSmax : Ideal.map (actualFormalCenterShearAlgEquiv A f w).toRingEquiv.toRingHom (genuineFormalVariables (n+1)) =
      genuineFormalVariables (n+1) := by
    change Ideal.map S.toRingHom (genuineFormalVariables (n+1)) = _
    rw [show S = actualFormalCenterShear Set.univ f w from hS]
    have hpoint : actualFormalCoordinateIdeal (n+1) Set.univ = genuineFormalVariables (n+1) := by
      simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]
    rw [← hpoint]
    exact map_coordinateIdeal_centerShear Set.univ f (mem_univ f) w
  have hsourceHS (ℓ : ℕ) : genuineFormalHilbertSamuelValue (n+1) KP ℓ = genuineFormalHilbertSamuelValue (n+1) K ℓ := by
    exact ((genuineFormalHilbertSamuelValue_map_formalAlgEquiv (MvPowerSeries.renameEquiv ℂ p)
      (map_genuineFormalVariables_rename p) KS ℓ).symm).trans
        ((genuineFormalHilbertSamuelValue_map_formalAlgEquiv (actualFormalCenterShearAlgEquiv A f w) hSmax K ℓ).symm)
  have hstrict : Ideal.map (normalPivotRename q f).toRingHom (actualFormalStrictTransform K A f hfA w) =
      actualFormalStrictTransform KP A q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0) := by
    have hKSstrict : actualFormalStrictTransform KS A f hfA (fun _ => 0) =
        actualFormalStrictTransform K A f hfA w :=
      actual_normal_strict_zero_map_centerShear K A f hfA w
    have hKP : Ideal.map (MvPowerSeries.rename p).toRingHom KS = KP := rfl
    have h := map_actual_normal_strict_rename KS p A (normal_pivot_mem q f hfA) f hfA (fun _ => 0)
    rw [hKP] at h
    have hidx : (⟨p f, (normal_pivot_mem q f hfA f).mpr hfA⟩ : {i : Fin (n+1) // i ∈ A}) =
        ⟨q, Set.mem_Ici.mpr (le_refl q)⟩ := Subtype.ext hpf
    have hchart := congrArg (fun i : {i : Fin (n+1) // i ∈ A} =>
      actualFormalStrictTransform KP A i.val i.property (fun _ => 0)) hidx
    have hmapped : Ideal.map (normalPivotRename q f).toRingHom
        (actualFormalStrictTransform KS A f hfA (fun _ => 0)) =
          actualFormalStrictTransform KP A q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0) := h.trans hchart
    exact (congrArg (Ideal.map (normalPivotRename q f).toRingHom) hKSstrict.symm).trans hmapped
  exact ⟨f, hfA, hvf, E, BP, hp, hE, hBlit, hOp, hsourceHS, hstrict⟩

private theorem equiv_mem_map_iff {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) (I : Ideal R) (J : Ideal S) (hJ : Ideal.map E.toRingHom I = J) (F : R) :
    E F ∈ J ↔ F ∈ I := by
  rw [← hJ]
  constructor
  · intro h
    obtain ⟨G, hG, he⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp h
    rwa [E.injective he] at hG
  · exact Ideal.mem_map_of_mem _

/-- Regularity of a mapped product implies regularity of each factor; the
actual chart-overlap factor is in fact a unit, but no unit premise is needed. -/
theorem regular_factor_of_ringEquiv_map
    {R S : Type*} [CommRing R] [CommRing S] (E : R ≃+* S)
    (I : Ideal R) (J : Ideal S) (hJ : Ideal.map E.toRingHom I = J)
    (x : R) (y u : S) (hxy : E x = y*u)
    (hreg : ∀ F : R, x*F ∈ I → F ∈ I) : ∀ F : S, y*F ∈ J → F ∈ J := by
  intro F hF
  have hprod : E (x * E.symm F) ∈ J := by
    rw [map_mul, hxy, E.apply_symm_apply]
    simpa only [mul_assoc, mul_left_comm] using J.mul_mem_left u hF
  have h := hreg (E.symm F) ((equiv_mem_map_iff E I J hJ _).mp hprod)
  simpa only [E.apply_symm_apply] using (equiv_mem_map_iff E I J hJ (E.symm F)).mpr h

private theorem strict_eq_of_normal_parameters {m : ℕ}
    (K : Ideal (MvPowerSeries (Fin m) ℂ)) (A : Set (Fin m)) (e : Fin m) (he : e ∈ A)
    (b c : Fin m → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i) :
    actualFormalStrictTransform K A e he b = actualFormalStrictTransform K A e he c := by
  have hσ : actualFormalBlowup A e b = actualFormalBlowup A e c := by
    apply AlgHom.ext
    intro F
    have hc : actualFormalBlowupCoordinates A e b = actualFormalBlowupCoordinates A e c := by
      funext i
      by_cases hi : i ∈ A <;> by_cases hie : i=e <;> simp [actualFormalBlowupCoordinates, hi, hie, hbc]
    simp only [actualFormalBlowup, MvPowerSeries.substAlgHom_apply, hc]
  have hn (μ : ℕ) (F : MvPowerSeries (Fin m) ℂ) (hF : F ∈ actualFormalCoordinateIdeal m A ^ μ) :
      actualNormalizedFormalMember A e he b μ F hF = actualNormalizedFormalMember A e he c μ F hF := by
    apply actualNormalizedFormalMember_unique A e he c μ F hF
    exact (actualNormalizedFormalMember_spec A e he b μ F hF).trans (DFunLike.congr_fun hσ F)
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal K A e he b,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal K A e he c]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro H ⟨μ, F, hFK, hF, rfl⟩
    exact Ideal.subset_span ⟨μ, F, hFK, hF, hn μ F hF⟩
  · apply Ideal.span_le.mpr
    rintro H ⟨μ, F, hFK, hF, rfl⟩
    exact Ideal.subset_span ⟨μ, F, hFK, hF, (hn μ F hF).symm⟩

/-- The natural all-direction formal converse: actual marked orders of the SAME
source family internally give ALL HS values and exceptional regularity of the
WHOLE original chart ideal. No raw original target-diagram equality is asserted. -/
theorem actual_normal_all_direction_hs_and_regular_of_marked_orders {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, actualNormalizedFormalMember (Set.Ici q) e hqe b
      (normalExponentDegree a.val) (B.series a) (hpower a) ∈ genuineFormalVariables n ^ normalExponentDegree a.val) :
    (∀ ℓ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K (Set.Ici q) e hqe b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ) ∧
    (∀ r (F : MvPowerSeries (Fin n) ℂ),
      (MvPowerSeries.X e)^r * F ∈ actualFormalStrictTransform K (Set.Ici q) e hqe b ↔
        F ∈ actualFormalStrictTransform K (Set.Ici q) e hqe b) := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ n =>
    obtain ⟨f, hqf, hvf, E, BP, hp, _hlabels, _hliteral, horderP, hsourceHS, hstrict⟩ :=
      exists_same_formal_normal_adapted_family_of_marked_orders K B q e hqe b hpower horder
    let A := Set.Ici q
    let v := actualNormalMarkedDirection A e b
    let w (i : Fin (n+1)) := v i/v f
    let KP := actualNormalAdaptedSourceIdeal K q e f b
    let Jf := actualFormalStrictTransform K A f hqf w
    let Jv := actualFormalStrictTransform K A e hqe v
    let J0 := actualFormalStrictTransform KP A q (Set.mem_Ici.mpr (le_refl q)) (fun _ => 0)
    have hve : v e = 1 := by simp only [v, actualNormalMarkedDirection, if_true]
    have hJvb : Jv = actualFormalStrictTransform K A e hqe b :=
      strict_eq_of_normal_parameters K A e hqe v b (by
        intro i hi hie
        simp only [v, actualNormalMarkedDirection, if_neg hie, actualNormalPointDirection, if_pos hi])
    have hHS0 := (actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders KP KP
      (⟨BP.series, BP.monic, BP.lower⟩ : InheritedMonicFamily MonomialOrder.degLex KP)
      rfl BP.mem q hp horderP).2.2
    have hreg0 (F : MvPowerSeries (Fin (n+1)) ℂ) (hF : MvPowerSeries.X q * F ∈ J0) : F ∈ J0 := by
      apply (actual_normal_zero_Xpow_mul_mem_strict_iff_of_marked_orders KP BP q hp horderP 1 F).mp
      simpa only [pow_one] using hF
    let P := MvPowerSeries.renameEquiv ℂ (normalPivotEquiv q f)
    have hPmap : Ideal.map P.toRingEquiv.toRingHom Jf = J0 := hstrict
    have hPX : P (MvPowerSeries.X f) = MvPowerSeries.X q := by
      change MvPowerSeries.rename (normalPivotEquiv q f) (MvPowerSeries.X f) = MvPowerSeries.X q
      rw [MvPowerSeries.rename_X, normalPivotEquiv_pivot q f hqf]
    have hregf (F : MvPowerSeries (Fin (n+1)) ℂ) (hF : MvPowerSeries.X f * F ∈ Jf) : F ∈ Jf := by
      have ht := Ideal.mem_map_of_mem P.toRingEquiv.toRingHom hF
      change P (MvPowerSeries.X f * F) ∈ Ideal.map P.toRingEquiv.toRingHom Jf at ht
      rw [map_mul, hPX, hPmap] at ht
      exact (equiv_mem_map_iff P.toRingEquiv Jf J0 hPmap F).mp (hreg0 (P F) ht)
    let C := actualNormalChartTransitionAlgEquiv A e f hqe hqf v hve hvf
    have hC : Ideal.map C.toRingEquiv.toRingHom Jf = Jv :=
      map_actual_normal_strict_chart_transition K A e f hqe hqf v hve hvf
    have hCX : C (MvPowerSeries.X f) = MvPowerSeries.X e * actualNormalChartPivotUnit e f v := by
      change actualNormalChartTransitionHom A e f v (MvPowerSeries.X f) = _
      rw [actualNormalChartTransition_X, actualNormalChartTransitionCoordinates,
        if_pos (show f ∈ A from Set.mem_Ici.mpr hqf), if_pos rfl]
    have hregv := regular_factor_of_ringEquiv_map C.toRingEquiv Jf Jv hC
      (MvPowerSeries.X f) (MvPowerSeries.X e) (actualNormalChartPivotUnit e f v) hCX hregf
    constructor
    · intro ℓ
      calc
        _ = genuineFormalHilbertSamuelValue (n+1) Jv ℓ := by rw [hJvb]
        _ = genuineFormalHilbertSamuelValue (n+1) Jf ℓ :=
          (genuineFormalHilbertSamuelValue_normal_chart_transition K A e f hqe hqf v hve hvf ℓ).symm
        _ = genuineFormalHilbertSamuelValue (n+1) J0 ℓ := by
          have hm := genuineFormalHilbertSamuelValue_map_formalAlgEquiv P
            (map_genuineFormalVariables_rename (normalPivotEquiv q f)) Jf ℓ
          rwa [hPmap] at hm
        _ = genuineFormalHilbertSamuelValue (n+1) KP ℓ := hHS0 ℓ
        _ = genuineFormalHilbertSamuelValue (n+1) K ℓ := hsourceHS ℓ
    · intro r F
      rw [← hJvb]
      exact pow_mul_mem_iff_of_mul_mem Jv (MvPowerSeries.X e) hregv r F

end
end Hironaka.HironakaActualNormalAllDirectionConverse

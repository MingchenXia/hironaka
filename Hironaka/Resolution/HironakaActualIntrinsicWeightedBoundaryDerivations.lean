import Hironaka.Resolution.HironakaActualIntrinsicLabelledBoundaryIdeals
import Hironaka.Analytic.SNCHolomorphicTestNecessity

/-! Whole original weighted divisor ideal images and ALL same-ring native complex derivations. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualIntrinsicWeightedBoundaryDerivations
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.RegularLocusDense
  BlowupTowers NormalCrossings BlowupFlatCoordinates GiraudAlong HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceIntrinsicHS HironakaActualIntrinsicCarrierDerivationTransport
  HironakaReducedComplexAnalyticSpaces
  HironakaActualIntrinsicLogQuotientDictionary HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaHolomorphicJetMonomialSpan HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem preserves_principal_iff (D : Derivation ℂ R R) (a : R) :
    Set.MapsTo D (Ideal.span {a} : Set R) (Ideal.span {a}) ↔ a ∣ D a := by
  constructor
  · intro h
    exact Ideal.mem_span_singleton.mp (h (Ideal.mem_span_singleton_self a))
  · intro ha f hf
    obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp hf
    obtain ⟨c,hc⟩ := ha
    apply Ideal.mem_span_singleton.mpr
    refine ⟨D b + b*c,?_⟩
    rw [D.leibniz,hc]
    simp only [smul_eq_mul]
    ring

private theorem positive_nat_isUnit {m : ℕ} (hm : 0 < m) : IsUnit (m : R) := by
  have hC : IsUnit (m : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  simpa using hC.map (algebraMap ℂ R)

private theorem prime_power_derivation [IsDomain R] (D : Derivation ℂ R R)
    {p Q : R} (hp : Prime p) (hQ : ¬p ∣ Q) {m : ℕ} (hm : 0 < m)
    (h : p^m*Q ∣ D (p^m*Q)) : p ∣ D p := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨b,hb⟩ := h
  have hder : D (p^(t+1)*Q) = p^t * (p*D Q+(t+1 : R)*Q*D p) := by
    rw [D.leibniz,D.leibniz_pow]
    simp only [smul_eq_mul,nsmul_eq_mul,Nat.add_sub_cancel,pow_succ]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rw [hder] at hb
  have hc : p*D Q+(t+1 : R)*Q*D p = p*Q*b := by
    apply mul_left_cancel₀ (pow_ne_zero t hp.ne_zero)
    simpa only [pow_succ,mul_assoc] using hb
  have hterm : (t+1 : R)*Q*D p = p*(Q*b-D Q) := by
    calc
      _ = (p*D Q+(t+1 : R)*Q*D p)-p*D Q := by ring
      _ = p*Q*b-p*D Q := by rw [hc]
      _ = _ := by ring
  have hu : IsUnit (t+1 : R) := by
    simpa only [Nat.cast_succ] using positive_nat_isUnit (R := R) (Nat.succ_pos t)
  have hnot : ¬p ∣ (t+1 : R) := fun hd => hp.not_dvd_one
    (hd.trans (isUnit_iff_dvd_one.mp hu))
  exact (hp.dvd_or_dvd (show p ∣ ((t+1 : R)*Q)*D p from ⟨Q*b-D Q,hterm⟩)).resolve_left
    (hp.not_dvd_mul hnot hQ)

omit [Algebra ℂ R] in
private theorem prime_not_dvd_prod {ι : Type*} (p : R) (hp : Prime p)
    (s : Finset ι) (f : ι → R) (hn : ∀ i ∈ s, ¬p ∣ f i) : ¬p ∣ ∏i ∈ s,f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact hp.not_dvd_mul (hn i (Finset.mem_insert_self i s))
      (ih (fun j hj => hn j (Finset.mem_insert_of_mem hj)))

private theorem pow_dvd_derivation_pow (D : Derivation ℂ R R) (a : R) (m : ℕ)
    (h : m≠0 → a ∣ D a) : a^m ∣ D (a^m) := by
  cases m with
  | zero => simp
  | succ t =>
    obtain ⟨b,hb⟩ := h (Nat.succ_ne_zero t)
    refine ⟨(t+1 : R)*b,?_⟩
    rw [D.leibniz_pow,hb]
    simp only [smul_eq_mul,nsmul_eq_mul,Nat.add_sub_cancel,pow_succ]
    simp only [Nat.cast_add,Nat.cast_one]
    ring

private theorem prod_dvd_derivation_prod {ι : Type*} (D : Derivation ℂ R R)
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i ∣ D (f i)) :
    (∏i ∈ s,f i) ∣ D (∏i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨b,hb⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨c,hc⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,D.leibniz,hb,hc]
    refine ⟨b+c,?_⟩
    simp only [smul_eq_mul]
    ring

/-- Pure SAME-ring complex derivations preserve the entire weighted principal product
iff every positive-weight component ideal is preserved. -/
theorem derivation_preserves_weighted_product_iff [IsDomain R]
    {ι : Type*} [Fintype ι] (a : ι → R) (m : ι → ℕ)
    (ha : ∀ i, IsUnit (a i) ∨ Prime (a i))
    (hsep : ∀ i j, i≠j → Prime (a i) → ¬a i ∣ a j) (D : Derivation ℂ R R) :
    Set.MapsTo D (Ideal.span {∏i,a i^(m i)} : Set R) (Ideal.span {∏i,a i^(m i)}) ↔
      ∀ i, m i≠0 → Set.MapsTo D (Ideal.span {a i} : Set R) (Ideal.span {a i}) := by
  classical
  simp only [preserves_principal_iff]
  constructor
  · intro h i hmi
    rcases ha i with hu | hp
    · exact (isUnit_iff_dvd_one.mp hu).trans (one_dvd _)
    · let Q : R := ∏j ∈ Finset.univ.erase i,a j^(m j)
      have hQ : ¬a i ∣ Q := prime_not_dvd_prod (a i) hp (Finset.univ.erase i) _
        (fun j hj hd => hsep i j (Finset.mem_erase.mp hj).1.symm hp (hp.dvd_of_dvd_pow hd))
      have he : a i^(m i)*Q = ∏j,a j^(m j) :=
        Finset.mul_prod_erase Finset.univ (fun j => a j^(m j)) (Finset.mem_univ i)
      exact prime_power_derivation D hp hQ (Nat.pos_of_ne_zero hmi) (by rwa [he])
  · intro h
    exact prod_dvd_derivation_prod D Finset.univ (fun i => a i^(m i))
      (fun i _ => pow_dvd_derivation_pow D (a i) (m i) (h i))

end Algebra

section Transport
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

private theorem preservation_conjugation_iff (e : R ≃ₐ[ℂ] S) (D : Derivation ℂ R R) (I : Ideal R) :
    Set.MapsTo D (I : Set R) I ↔
      Set.MapsTo (derivationConjugationEquiv e D) (Ideal.map e.toRingHom I : Set S)
        (Ideal.map e.toRingHom I) := by
  constructor
  · intro h f hf
    obtain ⟨r,hr,rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hf
    rw [derivationConjugationEquiv_apply]
    change e (D (e.symm (e r))) ∈ Ideal.map e.toRingHom I
    rw [AlgEquiv.symm_apply_apply]
    exact Ideal.mem_map_of_mem e.toRingHom (h hr)
  · intro h r hr
    have ht := h (Ideal.mem_map_of_mem e.toRingHom hr)
    rw [derivationConjugationEquiv_apply] at ht
    change e (D (e.symm (e r))) ∈ Ideal.map e.toRingHom I at ht
    rw [AlgEquiv.symm_apply_apply] at ht
    obtain ⟨f,hf,he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp ht
    have he' : e f=e (D r) := he
    exact (e.injective he') ▸ hf

end Transport

variable {n : ℕ} {X : CMfd.{0} n}

/-- The ENTIRE original weighted ambient Cartier ideal, before any chart or carrier image. -/
def ambientWeightedBoundaryIdeal (E : List (Set X)) (m : Fin E.length → ℕ) (p : X) :
    Ideal (actualComplexStructureStalk (n := n) p) :=
  ∏i : Fin E.length,(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p)^(m i)

/-- The TRUE native inclusion IMAGE of the original whole ambient weighted product. -/
def actualWeightedBoundaryTraceIdeal (N : Set X) (E : List (Set X))
    (m : Fin E.length → ℕ) (p : N) : Ideal (((actualSubspaceSheaf (n := n) N).presheaf.stalk p).carrier) :=
  Ideal.map ((actualSubspaceInclusion (n := n) N).stalkMap p).hom
    (ambientWeightedBoundaryIdeal E m p.val)

/-- Ideal images preserve the literal FULL original finite product and all original multiplicities. -/
theorem weightedBoundaryTraceIdeal_eq_prod (N : Set X) (E : List (Set X))
    (m : Fin E.length → ℕ) (p : N) :
    actualWeightedBoundaryTraceIdeal N E m p = ∏i : Fin E.length,
      (actualLabelledBoundaryTraceIdeal N E i p)^(m i) := by
  change (Ideal.mapHom ((actualSubspaceInclusion (n := n) N).stalkMap p).hom)
    (∏i : Fin E.length,(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val)^(m i)) = _
  rw [map_prod]
  simp only [Ideal.mapHom_apply,Ideal.map_pow,actualLabelledBoundaryTraceIdeal]

private theorem slot_of_nonunit {l k : ℕ} (τ : Fin l → Option (Fin k)) (v : ComplexModel k)
    (i : Fin l) (hn : ¬IsUnit (labelledParameterBoundaryGerm τ v i)) :
    ∃ j : Fin k, τ i=some j ∧ v j=0 ∧ labelledParameterBoundaryGerm τ v i=coordinateGerm j := by
  cases hi : τ i with
  | none => exact (hn (by simp [labelledParameterBoundaryGerm,hi])).elim
  | some j =>
    have hv : v j=0 := by
      by_contra hv
      apply hn
      rw [labelledParameterBoundaryGerm,hi,HolGerm.isUnit_iff_eval_ne_zero]
      simpa [coordinateGerm] using hv
    exact ⟨j,rfl,hv,by simp [labelledParameterBoundaryGerm,hi,hv]⟩

private theorem slot_unit_or_prime {l k : ℕ} (τ : Fin l → Option (Fin k)) (v : ComplexModel k)
    (i : Fin l) : IsUnit (labelledParameterBoundaryGerm τ v i) ∨
      Prime (labelledParameterBoundaryGerm τ v i) := by
  by_cases hu : IsUnit (labelledParameterBoundaryGerm τ v i)
  · exact Or.inl hu
  · obtain ⟨j,_,_,he⟩ := slot_of_nonunit τ v i hu
    right
    rw [he]
    simpa [coordinateGerm] using HolomorphicCoordinatePrime.prime_coordinate_germ j

private theorem slot_prime_separation {l k : ℕ} (τ : Fin l → Option (Fin k)) (v : ComplexModel k)
    (hinj : ∀ i j a, τ i=some a → τ j=some a → i=j)
    (i j : Fin l) (hij : i≠j) (hp : Prime (labelledParameterBoundaryGerm τ v i)) :
    ¬labelledParameterBoundaryGerm τ v i ∣ labelledParameterBoundaryGerm τ v j := by
  by_cases hu : IsUnit (labelledParameterBoundaryGerm τ v j)
  · intro hd
    exact hp.not_dvd_one (hd.trans (isUnit_iff_dvd_one.mp hu))
  · obtain ⟨a,hia,_,hea⟩ := slot_of_nonunit τ v i hp.not_isUnit
    obtain ⟨b,hjb,_,heb⟩ := slot_of_nonunit τ v j hu
    have hab : a≠b := by
      intro he
      exact hij (hinj i j a hia (by simpa only [he] using hjb))
    rw [hea,heb]
    simpa [coordinateGerm] using SNCHolomorphicTestNecessity.coordinate_germ_not_dvd_of_ne hab.symm

private theorem ambient_slot_of_intrinsic_some {k : ℕ} (hk : k≤n)
    (s : Option (Fin n)) (t : Option (Fin k))
    (hval : Option.map Fin.val t=Option.map Fin.val s) {j : Fin k} (ht : t=some j) :
    s=some (j.castLE hk) := by
  cases s with
  | none => simp [ht] at hval
  | some a =>
    have hv : j.val=a.val := by simpa [ht] using hval
    exact congrArg some (Fin.ext hv.symm)

/-- ONLY the original geometry chooses ONE native chart before ALL points, full original
weight families and ANY same-ring complex derivation; entire ideals and every label are retained. -/
theorem exists_actual_intrinsic_weighted_boundary_derivation_dictionary
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x∈N) :
    ∃ k≤n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)) (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
      (τ : Fin E.length → Option (Fin k)),
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ i j, κ i=some j → j.val<k) ∧ Set.InjOn κ {i | x∈E.get i} ∧
      (∀ i, Option.map Fin.val (τ i)=Option.map Fin.val (κ i)) ∧
      (k=0 → ∀ i, τ i=none) ∧
      (∀ p∈flatDomain Φ,
        (p∈N ↔ flatMap Φ p∈complexCoordinatePlane n k) ∧
        ∀ i, p∈E.get i ↔ ∃ j, κ i=some j ∧ flatCoord Φ j p=0) ∧
      (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
        ambientPointMap n X=ambientPointMap k (parameterOpen Φ k)) ∧
      ∀ v : parameterOpen Φ k,
        ∃ hp : parameterMapOn Φ k v∈N,
          ∃ e : ((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier ≃ₐ[ℂ]
              HolGerm (ComplexModel k),
            (∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e ((actualSubspaceInclusion (n := n) N).stalkMap ⟨parameterMapOn Φ k v,hp⟩ r)=
                parameterGermPullback Φ k hsrc v r) ∧
            (∀ i : Fin E.length,
              Ideal.map e.toRingHom (actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩)=
                Ideal.span {labelledParameterBoundaryGerm τ v.val i} ∧
              (IsUnit (labelledParameterBoundaryGerm τ v.val i) ↔ parameterMapOn Φ k v∉E.get i)) ∧
            ∀ m : Fin E.length → ℕ,
              actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩=
                ∏i : Fin E.length,(actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩)^(m i) ∧
              Ideal.map e.toRingHom (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩)=
                Ideal.span {∏i : Fin E.length,(labelledParameterBoundaryGerm τ v.val i)^(m i)} ∧
              ∀ D : Derivation ℂ
                  (((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier)
                  (((actualSubspaceSheaf (n := n) N).presheaf.stalk ⟨parameterMapOn Φ k v,hp⟩).carrier),
                Set.MapsTo D (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩ : Set _)
                  (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩) ↔
                ∀ i, m i≠0 →
                  Set.MapsTo D (actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩ : Set _)
                    (actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩) := by
  obtain ⟨k,hk,Φ,κ,hsrc,τ,h0,hκ,hinj,hval,hk0,hcharts,hpoint,hall⟩ :=
    exists_actual_intrinsic_labelled_boundary_ideal_dictionary hE hT x hx
  have hcenter (i : Fin E.length) (a : Fin n) (ha : κ i=some a) : x∈E.get i := by
    apply ((hcharts x (mem_flatDomain_self Φ)).2 i).mpr
    refine ⟨a,ha,?_⟩
    change Φ.toFun (chartAt (ComplexModel n) x x) a=0
    rw [h0]
    rfl
  have hτinj : ∀ i j a, τ i=some a → τ j=some a → i=j := by
    intro i j a hi hj
    have hki := ambient_slot_of_intrinsic_some hk (κ i) (τ i) (hval i) hi
    have hkj := ambient_slot_of_intrinsic_some hk (κ j) (τ j) (hval j) hj
    exact hinj (hcenter i _ hki) (hcenter j _ hkj) (hki.trans hkj.symm)
  refine ⟨k,hk,Φ,κ,hsrc,τ,h0,hκ,hinj,hval,hk0,hcharts,hpoint,?_⟩
  intro v
  obtain ⟨hp,e,he,hcomp⟩ := hall v
  refine ⟨hp,e,he,hcomp,?_⟩
  intro m
  have hImage : Ideal.map e.toRingHom
      (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩)=
        Ideal.span {∏i : Fin E.length,(labelledParameterBoundaryGerm τ v.val i)^(m i)} := by
    rw [weightedBoundaryTraceIdeal_eq_prod]
    change (Ideal.mapHom e.toRingHom)
      (∏i : Fin E.length,(actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩)^(m i)) = _
    rw [map_prod]
    simp only [Ideal.mapHom_apply,Ideal.map_pow]
    calc
      _ = ∏i : Fin E.length,Ideal.span {(labelledParameterBoundaryGerm τ v.val i)^(m i)} := by
        apply Finset.prod_congr rfl
        intro i _
        rw [(hcomp i).1,Ideal.span_singleton_pow]
      _ = _ := Ideal.prod_span_singleton Finset.univ _
  refine ⟨weightedBoundaryTraceIdeal_eq_prod N E m _,hImage,?_⟩
  intro D
  let D' := derivationConjugationEquiv e D
  have hGeneric := derivation_preserves_weighted_product_iff
    (labelledParameterBoundaryGerm τ v.val) m (slot_unit_or_prime τ v.val)
    (slot_prime_separation τ v.val hτinj) D'
  calc
    _ ↔ Set.MapsTo D' (Ideal.map e.toRingHom
        (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩) : Set _)
        (Ideal.map e.toRingHom (actualWeightedBoundaryTraceIdeal N E m ⟨parameterMapOn Φ k v,hp⟩)) :=
      preservation_conjugation_iff e D _
    _ ↔ Set.MapsTo D' (Ideal.span {∏i : Fin E.length,(labelledParameterBoundaryGerm τ v.val i)^(m i)} : Set _)
        (Ideal.span {∏i : Fin E.length,(labelledParameterBoundaryGerm τ v.val i)^(m i)}) := by rw [hImage]
    _ ↔ ∀ i, m i≠0 → Set.MapsTo D' (Ideal.span {labelledParameterBoundaryGerm τ v.val i} : Set _)
        (Ideal.span {labelledParameterBoundaryGerm τ v.val i}) := hGeneric
    _ ↔ _ := by
      apply forall_congr'
      intro i
      apply imp_congr_right
      intro _
      have ht := preservation_conjugation_iff e D
        (actualLabelledBoundaryTraceIdeal N E i ⟨parameterMapOn Φ k v,hp⟩)
      rw [(hcomp i).1] at ht
      exact ht.symm

end
end Hironaka.HironakaActualIntrinsicWeightedBoundaryDerivations

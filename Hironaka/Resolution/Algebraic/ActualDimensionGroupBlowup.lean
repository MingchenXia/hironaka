import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The actual affine blowup separating the intrinsic minimal-prime dimension
groups of a reduced Noetherian ring. This constructs its literal Proj-Rees
clopen chart partition and quotient chart maps, without an equidimensionality,
regular-locus, naturality or resolution-history assertion.
Source-first proof: `actual-dimension-group-blowup-20261101.tex`. -/
set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
universe u v

namespace Hironaka.Resolution.Algebraic.ActualDimensionGroupBlowup
noncomputable section

variable (R : Type u) [CommRing R]

/-- The dimension of the SAME actual irreducible-component quotient ring. -/
def componentDimension (p : minimalPrimes R) : WithBot ℕ∞ :=
  ringKrullDim (R ⧸ p.val)

/-- Exactly the occurring dimensions, including no label for an empty group. -/
def dimensionIndex : Type := ↥(Set.range (componentDimension R))

/-- The intrinsic reduced ideal of the union of all components of dimension d. -/
def dimensionGroupIdeal (d : dimensionIndex R) : Ideal R :=
  ⨅ p : minimalPrimes R, ⨅ (_ : componentDimension R p = d.val), p.val

/-- Intersection of every other group's actual ideal, with empty intersection top. -/
def complementIdeal {ι : Type v} (I : ι → Ideal R) (d : ι) : Ideal R :=
  ⨅ e : ι, ⨅ (_ : e ≠ d), I e

/-- The actual separation centre is the sum of the complementary group ideals. -/
def separationIdeal {ι : Type v} (I : ι → Ideal R) : Ideal R :=
  ⨆ d : ι, complementIdeal R I d

def dimensionSeparationIdeal : Ideal R := separationIdeal R (dimensionGroupIdeal R)

private theorem complementIdeal_le_separation {ι : Type v} (I : ι → Ideal R) (d : ι) :
    complementIdeal R I d ≤ separationIdeal R I := le_iSup _ d

/-- A literal union of native degree-one chart opens inside the SAME actual blowup. -/
def groupOpen {ι : Type v} (I : ι → Ideal R) (d : ι) :
    (affineBlowUp (separationIdeal R I)).Opens :=
  ⨆ a : complementIdeal R I d,
    Proj.basicOpen (reesAlgebra.grading (separationIdeal R I))
      (reesAlgebra.degreeOne (separationIdeal R I)
        ⟨a.val,complementIdeal_le_separation R I d a.property⟩)

def dimensionPartOpen (d : dimensionIndex R) : (affineBlowUp (dimensionSeparationIdeal R)).Opens :=
  groupOpen R (dimensionGroupIdeal R) d

/-- Noetherianity derives finiteness of the intrinsic dimension image. -/
theorem dimensionIndex_finite [IsNoetherianRing R] : Finite (dimensionIndex R) := by
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  exact Set.finite_range (componentDimension R) |>.to_subtype

/-- The group intersection is the nilradical, hence zero in the actual reduced ring. -/
theorem dimensionGroupIdeal_iInf_eq_bot [IsReduced R] :
    (⨅ d : dimensionIndex R, dimensionGroupIdeal R d) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hp : x ∈ sInf (minimalPrimes R) := by
    apply Ideal.mem_sInf.mpr
    intro p hpm
    let q : minimalPrimes R := ⟨p,hpm⟩
    let d : dimensionIndex R := ⟨componentDimension R q,⟨q,rfl⟩⟩
    have hd := (Ideal.mem_iInf.mp hx) d
    exact (Ideal.mem_iInf.mp ((Ideal.mem_iInf.mp hd) q)) rfl
  simpa only [Ideal.sInf_minimalPrimes,Ideal.radical_bot_of_isReduced,Ideal.mem_bot] using hp

private theorem complementIdeal_le {ι : Type v} (I : ι → Ideal R) {d e : ι} (h : e ≠ d) :
    complementIdeal R I d ≤ I e :=
  (iInf_le _ e).trans (iInf_le _ h)

private theorem group_complement_mul_eq_bot {ι : Type v} (I : ι → Ideal R)
    (hI : (⨅ d, I d) = ⊥) (d : ι) : I d * complementIdeal R I d = ⊥ := by
  apply eq_bot_iff.mpr
  rw [← hI]
  apply le_iInf
  intro e
  by_cases he : e = d
  · subst e
    exact Ideal.mul_le_left
  · exact Ideal.mul_le_right.trans (complementIdeal_le R I he)

private theorem complements_mul_eq_bot {ι : Type v} (I : ι → Ideal R)
    (hI : (⨅ d, I d) = ⊥) {d e : ι} (hde : d ≠ e) :
    complementIdeal R I d * complementIdeal R I e = ⊥ := by
  apply eq_bot_iff.mpr
  rw [← hI]
  apply le_iInf
  intro f
  by_cases hf : f = d
  · subst f
    exact Ideal.mul_le_right.trans (complementIdeal_le R I hde)
  · exact Ideal.mul_le_left.trans (complementIdeal_le R I hf)

/-- Every needed annihilation is DERIVED from the actual reduced minimal-prime groups. -/
theorem dimension_group_annihilation [IsReduced R] :
    (∀ d : dimensionIndex R,
      dimensionGroupIdeal R d * complementIdeal R (dimensionGroupIdeal R) d = ⊥) ∧
    Pairwise (fun d e : dimensionIndex R =>
      complementIdeal R (dimensionGroupIdeal R) d *
        complementIdeal R (dimensionGroupIdeal R) e = ⊥) := by
  exact ⟨group_complement_mul_eq_bot R _ (dimensionGroupIdeal_iInf_eq_bot R),
    fun _ _ h => complements_mul_eq_bot R _ (dimensionGroupIdeal_iInf_eq_bot R) h⟩

private theorem span_complements {ι : Type v} (I : ι → Ideal R) :
    Ideal.span (⋃ d : ι, (complementIdeal R I d : Set R)) = separationIdeal R I := by
  simp only [Ideal.span_iUnion,Ideal.span_eq,separationIdeal]

private theorem iSup_groupOpen_eq_top {ι : Type v} (I : ι → Ideal R) :
    (⨆ d : ι, groupOpen R I d) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨a,ha⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (separationIdeal R I) (⋃ d : ι, (complementIdeal R I d : Set R))
    (span_complements R I) x
  obtain ⟨d,hd⟩ := Set.mem_iUnion.mp a.property
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨d,TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a.val,hd⟩,?_⟩⟩
  simpa only [affineBlowUp.opensRange_chart] using ha

private theorem disjoint_groupOpen {ι : Type v} (I : ι → Ideal R)
    (hI : (⨅ d, I d) = ⊥) {d e : ι} (hde : d ≠ e) :
    Disjoint (groupOpen R I d : Set (affineBlowUp (separationIdeal R I)))
      (groupOpen R I e : Set (affineBlowUp (separationIdeal R I))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨b,hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have hab : a.val * b.val = 0 := by
    apply Ideal.mem_bot.mp
    rw [← complements_mul_eq_bot R I hI hde]
    exact Ideal.mul_mem_mul a.property b.property
  let a' : separationIdeal R I :=
    ⟨a.val,complementIdeal_le_separation R I d a.property⟩
  let b' : separationIdeal R I :=
    ⟨b.val,complementIdeal_le_separation R I e b.property⟩
  have ht : reesAlgebra.degreeOne (separationIdeal R I) a' *
      reesAlgebra.degreeOne (separationIdeal R I) b' = 0 := by
    apply Subtype.ext
    change Polynomial.monomial 1 a.val * Polynomial.monomial 1 b.val = 0
    rw [Polynomial.monomial_mul_monomial,hab,Polynomial.monomial_zero_right]
  have hm : x ∈ Proj.basicOpen (reesAlgebra.grading (separationIdeal R I))
      (reesAlgebra.degreeOne (separationIdeal R I) a' *
        reesAlgebra.degreeOne (separationIdeal R I) b') := by
    rw [Proj.basicOpen_mul]
    exact ⟨ha,hb⟩
  rw [ht,Proj.basicOpen_zero] at hm
  exact hm

private theorem isClosed_groupOpen {ι : Type v} (I : ι → Ideal R)
    (hI : (⨅ d, I d) = ⊥) (d : ι) :
    IsClosed (groupOpen R I d : Set (affineBlowUp (separationIdeal R I))) := by
  have hComp : (groupOpen R I d : Set (affineBlowUp (separationIdeal R I)))ᶜ =
      ⋃ e : ι, ⋃ (_ : e ≠ d),
        (groupOpen R I e : Set (affineBlowUp (separationIdeal R I))) := by
    ext x
    constructor
    · intro hx
      have htop : x ∈ (⨆ e : ι, groupOpen R I e) := by
        rw [iSup_groupOpen_eq_top]
        trivial
      obtain ⟨e,he⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
      refine Set.mem_iUnion₂.mpr ⟨e,?_,he⟩
      intro hed
      subst e
      exact hx he
    · intro hx hd
      obtain ⟨e,hed,he⟩ := Set.mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp (disjoint_groupOpen R I hI hed.symm) hd he
  apply isOpen_compl_iff.mp
  rw [hComp]
  exact isOpen_iUnion fun e => isOpen_iUnion fun _ => (groupOpen R I e).isOpen

/-- The intrinsic group charts cover the literal blowup and form disjoint clopen pieces. -/
theorem dimension_group_clopen_partition [IsReduced R] :
    (⨆ d : dimensionIndex R, dimensionPartOpen R d) = ⊤ ∧
    Pairwise (fun d e : dimensionIndex R =>
      Disjoint (dimensionPartOpen R d : Set (affineBlowUp (dimensionSeparationIdeal R)))
        (dimensionPartOpen R e : Set (affineBlowUp (dimensionSeparationIdeal R)))) ∧
    ∀ d : dimensionIndex R,
      IsClosed (dimensionPartOpen R d : Set (affineBlowUp (dimensionSeparationIdeal R))) := by
  exact ⟨iSup_groupOpen_eq_top R _,
    (fun _ _ h => disjoint_groupOpen R _ (dimensionGroupIdeal_iInf_eq_bot R) h),
    isClosed_groupOpen R _ (dimensionGroupIdeal_iInf_eq_bot R)⟩

private theorem chart_base_kills_group {ι : Type v} (I : ι → Ideal R)
    (hI : (⨅ d, I d) = ⊥) (d : ι) (a : complementIdeal R I d)
    (x : R) (hx : x ∈ I d) :
    algebraMap R (affineBlowUpAlgebra (separationIdeal R I) a.val) x = 0 := by
  have hxa : x * a.val = 0 := by
    apply Ideal.mem_bot.mp
    rw [← group_complement_mul_eq_bot R I hI d]
    exact Ideal.mul_mem_mul hx a.property
  apply Subtype.ext
  change algebraMap R (Localization.Away a.val) x = 0
  have hu : IsUnit (algebraMap R (Localization.Away a.val) a.val) :=
    IsLocalization.Away.algebraMap_isUnit a.val
  apply hu.mul_left_inj.mp
  rw [zero_mul,← map_mul,hxa,map_zero]

/-- The actual chart-ring map out of the original dimension-group quotient. -/
def dimensionChartQuotientMap [IsReduced R] (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    (R ⧸ dimensionGroupIdeal R d) →+*
      affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val :=
  Ideal.Quotient.lift (dimensionGroupIdeal R d)
    (algebraMap R (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val))
    (chart_base_kills_group R (dimensionGroupIdeal R) (dimensionGroupIdeal_iInf_eq_bot R) d a)

/-- The quotient factorization is the SAME native chart-to-original-base morphism. -/
theorem dimension_chart_factorization [IsReduced R] (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    let aJ : dimensionSeparationIdeal R :=
      ⟨a.val,complementIdeal_le_separation R (dimensionGroupIdeal R) d a.property⟩
    affineBlowUp.chart (dimensionSeparationIdeal R) aJ ≫
        affineBlowUp.π (dimensionSeparationIdeal R) =
      Spec.map (CommRingCat.ofHom (dimensionChartQuotientMap R d a)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (dimensionGroupIdeal R d))) := by
  dsimp only
  rw [affineBlowUp.chart_π,← Spec.map_comp]
  congr 1

end
end Hironaka.Resolution.Algebraic.ActualDimensionGroupBlowup

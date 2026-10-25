import DeJongAlterations.StableModification.Resolution.StrictifyBlowup

/-!
# The blowup step of the strictification

Let `X` be a smooth variety over an algebraically closed field `k` and `F` a normal crossings
family (`IsNCFamily`) with a distinguished member `F₀ = F none` of multiplicity at most `m ≥ 1`
and further members `F (some i)` of multiplicity at most `1`. Let `C` be the `m`-fold locus of
`F₀` (`mFoldLocus`) and `π : X' → X` the blowup along `C`. Then `X'` is regular and the family

* `F'₀` = the strict transform of `F₀` (the support of `(I(F₀)𝒪_{X'} : I(C)𝒪_{X'}^m)`),
* `F' (some (castSucc i)) = π⁻¹ F (some i)`,
* `F' (some last) = π⁻¹ C` (the exceptional divisor)

is a normal crossings family with multiplicities `m - 1` for `F'₀` and `1` for the others. This
is the step of the strictification of normal crossings divisors by blowups along regular strata
(de Jong 1996, 2.4, `references/dejong96-alterations/tex/page-0006.tex`), computed in completed
local rings by `exists_chart_coordinates`.

## Main results

* `linearIndependent_toCotangent_iff`: independence in `𝔪/𝔪²` in terms of coefficients.
* `formalIdeal_preimage_eq`: the completed ideal of a preimage `π⁻¹ F`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Algebra.NodeFittingIdealSheaf Algebra.CompletionLocalMap Geometry.BlowupGluing

universe u

section Cotangent

variable {R S ι : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Fintype ι]

/-- Linear independence in `𝔪/𝔪²`, in terms of coefficients in `R`. -/
theorem linearIndependent_toCotangent_iff (t : ι → maximalIdeal R) :
    LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i)) ↔
      ∀ c : ι → R, ∑ i, c i * (t i : R) ∈ maximalIdeal R ^ 2 → ∀ i, c i ∈ maximalIdeal R := by
  have key : ∀ c : ι → R, ∑ i, residue R (c i) • (maximalIdeal R).toCotangent (t i) =
      (maximalIdeal R).toCotangent (∑ i, c i • t i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
    exact algebraMap_smul (ResidueField R) (c i) _
  have hcoe : ∀ c : ι → R, ((∑ i, c i • t i : maximalIdeal R) : R) = ∑ i, c i * (t i : R) := by
    intro c
    simp [smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i
    have := h (fun i ↦ residue R (c i)) (by
      rw [key, Ideal.toCotangent_eq_zero, hcoe]
      exact hc) i
    exact (residue_eq_zero_iff _).mp this
  · intro h g hg i
    choose c hc using fun i ↦ residue_surjective (R := R) (g i)
    have hgc : g = fun i ↦ residue R (c i) := funext fun i ↦ (hc i).symm
    subst hgc
    rw [key, Ideal.toCotangent_eq_zero, hcoe] at hg
    exact (residue_eq_zero_iff _).mpr (h c hg i)

/-- A ring isomorphism of local rings carries regular systems of parameters to regular systems
of parameters: linear independence in `𝔪/𝔪²`. -/
theorem linearIndependent_toCotangent_of_ringEquiv (e : R ≃+* S) (t : ι → maximalIdeal R)
    (ht : LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i)))
    (t' : ι → maximalIdeal S) (ht' : ∀ i, (t' i : S) = e (t i)) :
    LinearIndependent (ResidueField S) (fun i ↦ (maximalIdeal S).toCotangent (t' i)) := by
  rw [linearIndependent_toCotangent_iff] at ht ⊢
  have hm : ∀ s : S, s ∈ maximalIdeal S ↔ e.symm s ∈ maximalIdeal R := by
    intro s
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact (isUnit_map_iff e.symm s).not.symm
  have hm2 : ∀ s ∈ maximalIdeal S ^ 2, e.symm s ∈ maximalIdeal R ^ 2 := by
    intro s hs
    have hle : maximalIdeal S ^ 2 ≤ (maximalIdeal R ^ 2).comap (e.symm : S →+* R) := by
      rw [pow_two, Ideal.mul_le]
      intro a ha b hb
      rw [Ideal.mem_comap, map_mul, pow_two]
      exact Ideal.mul_mem_mul ((hm a).mp ha) ((hm b).mp hb)
    exact hle hs
  intro c hc i
  rw [hm]
  apply ht (fun i ↦ e.symm (c i)) _ i
  have := hm2 _ hc
  simpa [map_sum, map_mul, ht'] using this

end Cotangent

section Radical

variable {P Q ι : Type*} [CommRing P] [CommRing Q] [IsRegularLocalRing Q]

/-- If `J Q = (∏_{i ∈ A} z_i)` for part `z` of a regular system of parameters of `Q`, then also
`√J Q = (∏_{i ∈ A} z_i)`. -/
theorem map_radical_eq_span_prod (τ : P →+* Q) (z : ι → maximalIdeal Q)
    (hz : LinearIndependent (ResidueField Q) (fun i ↦ (maximalIdeal Q).toCotangent (z i)))
    (A : Finset ι) (J : Ideal P) (hJ : J.map τ = Ideal.span {∏ i ∈ A, (z i : Q)}) :
    J.radical.map τ = Ideal.span {∏ i ∈ A, (z i : Q)} := by
  rw [map_radical_eq_of_isRadical τ J (hJ ▸ span_prod_param_isRadical z hz A), hJ]

end Radical

section Preimage

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- **Completed ideals of preimages.** Let `π : Y → X`, `y ∈ Y`, and suppose
`I(F)_{π y} Ô_{X,π y} = (∏_{i ∈ A} t_i)` while the images of the `t_i`, `i ∈ A`, in `Ô_{Y,y}` are
part `z` of a regular system of parameters. Then `I(π⁻¹F)_y Ô_{Y,y} = (∏_{i ∈ A} z_i)`. -/
theorem formalIdeal_preimage_eq (π : Y ⟶ X) (F : Closeds X) (y : Y) {ι : Type*}
    [IsRegularLocalRing (Y.completedLocalRing y)] (A : Finset ι)
    (t : ι → X.completedLocalRing (π y))
    (hF : formalIdeal F (π y) = Ideal.span {∏ i ∈ A, t i})
    (z : ι → maximalIdeal (Y.completedLocalRing y))
    (hz : LinearIndependent (ResidueField (Y.completedLocalRing y))
      (fun i ↦ (maximalIdeal (Y.completedLocalRing y)).toCotangent (z i)))
    (htz : ∀ i ∈ A, completionMap (π.stalkMap y).hom (t i) = z i) :
    formalIdeal (F.preimage π.continuous) y =
      Ideal.span {∏ i ∈ A, (z i : Y.completedLocalRing y)} := by
  rw [formalIdeal, localIdeal_preimage]
  apply map_radical_eq_span_prod _ z hz A
  rw [Ideal.map_map]
  have hcomp : (Y.toCompletedLocalRing y).comp (π.stalkMap y).hom =
      (completionMap (π.stalkMap y).hom).comp (X.toCompletedLocalRing (π y)) :=
    RingHom.ext fun a ↦ (completionMap_algebraMap (π.stalkMap y).hom a).symm
  rw [hcomp, ← Ideal.map_map]
  change (formalIdeal F (π y)).map _ = _
  rw [hF, Ideal.map_span, Set.image_singleton, map_prod]
  congr 2
  exact Finset.prod_congr rfl htz

end Preimage

section Family

/-- The index sets of a transformed chart: `A₀` for the strict transform, `A_old i` for the
transforms of the old members and `A_new` for the new exceptional divisor. -/
def extendSets {α : Type*} {r : ℕ} (A₀ : Finset α) (Aold : Fin r → Finset α) (Anew : Finset α) :
    Option (Fin (r + 1)) → Finset α :=
  fun l ↦ l.elim A₀ (Fin.lastCases Anew Aold)

@[simp] theorem extendSets_none {α : Type*} {r : ℕ} (A₀ : Finset α) (Aold : Fin r → Finset α)
    (Anew : Finset α) : extendSets A₀ Aold Anew none = A₀ := rfl

@[simp] theorem extendSets_last {α : Type*} {r : ℕ} (A₀ : Finset α) (Aold : Fin r → Finset α)
    (Anew : Finset α) : extendSets A₀ Aold Anew (some (Fin.last r)) = Anew := by
  simp [extendSets]

@[simp] theorem extendSets_castSucc {α : Type*} {r : ℕ} (A₀ : Finset α) (Aold : Fin r → Finset α)
    (Anew : Finset α) (i : Fin r) : extendSets A₀ Aold Anew (some i.castSucc) = Aold i := by
  simp [extendSets]

theorem pairwise_disjoint_extendSets {α : Type*} {r : ℕ} (A₀ : Finset α)
    (Aold : Fin r → Finset α) (Anew : Finset α) (h0 : ∀ i, Disjoint A₀ (Aold i))
    (hold : Pairwise fun i i' ↦ Disjoint (Aold i) (Aold i')) (h0new : Disjoint A₀ Anew)
    (hnew : ∀ i, Disjoint (Aold i) Anew) :
    Pairwise fun l l' ↦ Disjoint (extendSets A₀ Aold Anew l) (extendSets A₀ Aold Anew l') := by
  have key : ∀ l : Fin (r + 1), Disjoint A₀ (extendSets A₀ Aold Anew (some l)) := by
    intro l
    induction l using Fin.lastCases with
    | last => simpa using h0new
    | cast i => simpa using h0 i
  have key' : ∀ l l' : Fin (r + 1), l ≠ l' →
      Disjoint (extendSets A₀ Aold Anew (some l)) (extendSets A₀ Aold Anew (some l')) := by
    intro l l' hll'
    induction l using Fin.lastCases with
    | last =>
      induction l' using Fin.lastCases with
      | last => exact absurd rfl hll'
      | cast i' => simpa using (hnew i').symm
    | cast i =>
      induction l' using Fin.lastCases with
      | last => simpa using hnew i
      | cast i' =>
        simp only [extendSets_castSucc]
        exact hold fun h ↦ hll' (by rw [h])
  rintro (_ | l) (_ | l') h
  · exact absurd rfl h
  · simpa using key l'
  · simpa using (key l).symm
  · exact key' l l' fun h' ↦ h (by rw [h'])

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- The strict transform of `F` under `π` with respect to a centre `C` of multiplicity `m`: the
support of `(I(F) 𝒪_Y : (I(C) 𝒪_Y)^m)`. -/
def strictTransform (π : Y ⟶ X) (F C : Closeds X) (m : ℕ) : Closeds Y :=
  (colonIter ((Scheme.IdealSheafData.vanishingIdeal F).comap π)
    ((Scheme.IdealSheafData.vanishingIdeal C).comap π) m).support

/-- The transformed family after blowing up `C`: the strict transform of `F none`, the preimages
of the other members and the exceptional divisor `π⁻¹ C` (last). -/
def transformFamily (π : Y ⟶ X) {r : ℕ} (F : Option (Fin r) → Closeds X) (C : Closeds X)
    (m : ℕ) : Option (Fin (r + 1)) → Closeds Y :=
  fun l ↦ l.elim (strictTransform π (F none) C m)
    (Fin.lastCases (C.preimage π.continuous) fun i ↦ (F (some i)).preimage π.continuous)

@[simp] theorem transformFamily_none (π : Y ⟶ X) {r : ℕ} (F : Option (Fin r) → Closeds X)
    (C : Closeds X) (m : ℕ) : transformFamily π F C m none = strictTransform π (F none) C m :=
  rfl

@[simp] theorem transformFamily_last (π : Y ⟶ X) {r : ℕ} (F : Option (Fin r) → Closeds X)
    (C : Closeds X) (m : ℕ) :
    transformFamily π F C m (some (Fin.last r)) = C.preimage π.continuous := by
  simp [transformFamily]

@[simp] theorem transformFamily_castSucc (π : Y ⟶ X) {r : ℕ} (F : Option (Fin r) → Closeds X)
    (C : Closeds X) (m : ℕ) (i : Fin r) :
    transformFamily π F C m (some i.castSucc) = (F (some i)).preimage π.continuous := by
  simp [transformFamily]

/-- The ideal of the strict transform at `y`: `√((I(F)_x 𝒪_y : (I(C)_x 𝒪_y)^m))`, `x = π y`. -/
theorem localIdeal_strictTransform (π : Y ⟶ X) (F C : Closeds X) (m : ℕ) (y : Y) :
    localIdeal (strictTransform π F C m) y =
      ((fun I : Ideal (Y.presheaf.stalk y) ↦
        I.colon (((localIdeal C (π y)).map (π.stalkMap y).hom : Ideal _) : Set _))^[m]
        ((localIdeal F (π y)).map (π.stalkMap y).hom)).radical := by
  rw [localIdeal, strictTransform, Scheme.IdealSheafData.vanishingIdeal_support,
    stalkIdeal_radical, stalkIdeal_colonIter, stalkIdeal_comap, stalkIdeal_comap]
  rfl

/-- Away from the centre the strict transform is the preimage. -/
theorem localIdeal_strictTransform_of_not_mem (π : Y ⟶ X) (F C : Closeds X) (m : ℕ) (y : Y)
    (hy : π y ∉ C) :
    localIdeal (strictTransform π F C m) y = localIdeal (F.preimage π.continuous) y := by
  have hC : localIdeal C (π y) = ⊤ := by
    by_contra h
    exact hy ((localIdeal_ne_top_iff C (π y)).mp h)
  rw [localIdeal_strictTransform, localIdeal_preimage, hC, Ideal.map_top, iterate_colon_top]

omit [IsLocallyNoetherian Y] in
/-- Away from the centre the exceptional divisor is not met. -/
theorem formalIdeal_preimage_of_not_mem (π : Y ⟶ X) (C : Closeds X) (y : Y) (hy : π y ∉ C) :
    formalIdeal (C.preimage π.continuous) y = ⊤ := by
  have hC : localIdeal C (π y) = ⊤ := by
    by_contra h
    exact hy ((localIdeal_ne_top_iff C (π y)).mp h)
  rw [formalIdeal, localIdeal_preimage, hC, Ideal.map_top, Ideal.radical_top, Ideal.map_top]

theorem ringEquiv_mem_maximalIdeal {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (e : R ≃+* S) {a : R} (ha : a ∈ maximalIdeal R) : e a ∈ maximalIdeal S := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ha)

variable [IsLocallyNoetherian X]

/-- **Charts where `π` is a local isomorphism.** If the stalk map of `π` at `y` is an isomorphism
and `π y ∉ C`, a chart at `π y` transports to a chart of the transformed family at `y`, with the
same index sets and no exceptional branch. -/
theorem exists_ncChart_of_isIso (π : Y ⟶ X) (y : Y) [IsIso (π.stalkMap y)] {r : ℕ}
    (F : Option (Fin r) → Closeds X) (C : Closeds X) (m : ℕ) (hy : π y ∉ C)
    (c : NCChart F (π y)) [IsRegularLocalRing (X.completedLocalRing (π y))] :
    ∃ c' : NCChart (transformFamily π F C m) y, ∀ l,
      (c'.A l).card = (extendSets (c.A none) (fun i ↦ c.A (some i)) ∅ l).card := by
  classical
  let φ := (π.stalkMap y).hom
  let e : X.presheaf.stalk (π y) ≃+* Y.presheaf.stalk y :=
    (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv
  have he : (e : X.presheaf.stalk (π y) →+* Y.presheaf.stalk y) = φ := RingHom.ext fun _ ↦ rfl
  let E := completionEquiv e
  have hE : ∀ a, E a = completionMap φ a := fun a ↦ by
    rw [completionEquiv_apply, completionMap_congr he]
  have : IsRegularLocalRing (Y.completedLocalRing y) := IsRegularLocalRing.of_ringEquiv E
  let z : Fin c.n → maximalIdeal (Y.completedLocalRing y) :=
    fun i ↦ ⟨E (c.t i), ringEquiv_mem_maximalIdeal E (c.t i).2⟩
  have hz : LinearIndependent (ResidueField (Y.completedLocalRing y))
      (fun i ↦ (maximalIdeal (Y.completedLocalRing y)).toCotangent (z i)) :=
    linearIndependent_toCotangent_of_ringEquiv E c.t c.indep z fun _ ↦ rfl
  have hzspan : Ideal.span (Set.range fun i ↦ (z i : Y.completedLocalRing y)) =
      maximalIdeal (Y.completedLocalRing y) := by
    have : (Set.range fun i ↦ (z i : Y.completedLocalRing y)) =
        E '' Set.range fun i ↦ (c.t i : X.completedLocalRing (π y)) := by
      rw [← Set.range_comp]
      rfl
    rw [this, ← Ideal.map_span, c.span_eq, map_ringEquiv_maximalIdeal]
  have htz : ∀ i, completionMap φ (c.t i) = z i := fun i ↦ (hE _).symm
  refine ⟨
    { n := c.n
      t := z
      indep := hz
      span_eq := hzspan
      A := extendSets (c.A none) (fun i ↦ c.A (some i)) ∅
      disjoint := pairwise_disjoint_extendSets _ _ _ (fun i ↦ c.disjoint (by simp))
        (fun i i' h ↦ c.disjoint fun h' ↦ h (Option.some_injective _ h'))
        (Finset.disjoint_empty_right _) (fun _ ↦ Finset.disjoint_empty_right _)
      formalIdeal_eq := ?_ }, fun _ ↦ rfl⟩
  rintro (_ | l)
  · rw [transformFamily_none, extendSets_none, formalIdeal,
      localIdeal_strictTransform_of_not_mem π _ C m y hy, ← formalIdeal]
    exact formalIdeal_preimage_eq π (F none) y (c.A none) (fun i ↦ c.t i) (c.formalIdeal_eq none)
      z hz fun i _ ↦ htz i
  · induction l using Fin.lastCases with
    | last =>
      rw [transformFamily_last, extendSets_last, Finset.prod_empty, Ideal.span_singleton_one]
      exact formalIdeal_preimage_of_not_mem π C y hy
    | cast i =>
      rw [transformFamily_castSucc, extendSets_castSucc]
      exact formalIdeal_preimage_eq π (F (some i)) y (c.A (some i)) (fun i ↦ c.t i)
        (c.formalIdeal_eq (some i)) z hz fun i _ ↦ htz i

/-- **Charts over the centre.** At a point `y` over `x = π y ∈ C`, where `C` is cut out formally by
the `m` branches `t_i`, `i ∈ A none`, of the chart `c`, and the stalk map of `π` has chart data for
`I(C)_x` (a localization of a blowup chart), the transformed family has a chart at `y` with at most
`m - 1` branches of the strict transform, the old branches of the other members and one branch
of the exceptional divisor; moreover `Ô_{Y,y}` is regular. -/
theorem exists_ncChart_of_chartData (π : Y ⟶ X) (y : Y) {k : Type*} [Field k]
    [Algebra k (X.presheaf.stalk (π y))] [Algebra k (Y.presheaf.stalk y)]
    [IsDomain (Y.presheaf.stalk y)]
    (hφk : ∀ c : k, (π.stalkMap y).hom (algebraMap k _ c) = algebraMap k _ c)
    (hresO : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk (π y)))))
    (hresP : Function.Bijective (algebraMap k (ResidueField (Y.presheaf.stalk y))))
    {r : ℕ} (F : Option (Fin r) → Closeds X) (C : Closeds X) (m : ℕ)
    (c : NCChart F (π y)) [IsRegularLocalRing (X.completedLocalRing (π y))]
    (hcard : (c.A none).card = m)
    (hC : formalIdeal C (π y) = Ideal.span
      ((fun i ↦ (c.t i : X.completedLocalRing (π y))) '' (c.A none : Set (Fin c.n))))
    (H : HasChartData (π.stalkMap y).hom (localIdeal C (π y)))
    (hdim : (c.n : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)) :
    IsRegularLocalRing (Y.completedLocalRing y) ∧
      ∃ c' : NCChart (transformFamily π F C m) y, (c'.A none).card ≤ m - 1 ∧
        (∀ i : Fin r, (c'.A (some i.castSucc)).card = (c.A (some i)).card) ∧
        (c'.A (some (Fin.last r))).card = 1 := by
  classical
  let φ := (π.stalkMap y).hom
  obtain ⟨g, hg, hgen, hIg, hg0⟩ := H
  have : IsDomain (X.completedLocalRing (π y)) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  obtain ⟨j, z, S', hjS, hreg, hz, hzspan, hzout, -, hS', hgz, hstrict⟩ :=
    exists_chart_coordinates φ hresP hφk hresO c.t c.span_eq (localIdeal C (π y)) (c.A none) hC
      g hg hIg hg0 hgen (by simpa using hdim)
  refine ⟨hreg, ?_⟩
  -- a principal equation of the old member
  obtain ⟨h0, -, hJ, hspan0⟩ := exists_span_singleton_eq_of_map_eq_span_singleton
    (X.toCompletedLocalRing (π y))
    (fun J ↦ Algebra.CompletionRegularityBasics.comap_map (X.presheaf.stalk (π y)) J)
    (localIdeal (F none) (π y)) _ (c.formalIdeal_eq none)
  obtain ⟨h', hh', hh'span⟩ := hstrict h0 hspan0
  rw [hcard] at hh'
  have hregg : IsSMulRegular (Y.presheaf.stalk y) (φ g) := fun a b hab ↦
    mul_left_cancel₀ hg0 hab
  have hdisj : ∀ i : Fin r, Disjoint (c.A (some i)) (c.A none) :=
    fun i ↦ c.disjoint (Option.some_ne_none i)
  refine ⟨
    { n := c.n
      t := z
      indep := hz
      span_eq := hzspan
      A := extendSets S' (fun i ↦ c.A (some i)) {j}
      disjoint := pairwise_disjoint_extendSets _ _ _
        (fun i ↦ Finset.disjoint_of_subset_left (hS'.trans (Finset.erase_subset _ _))
          (hdisj i).symm)
        (fun i i' h ↦ c.disjoint fun h' ↦ h (Option.some_injective _ h'))
        (Finset.disjoint_singleton_right.mpr fun h ↦ Finset.notMem_erase j _ (hS' h))
        (fun i ↦ Finset.disjoint_singleton_right.mpr fun h ↦
          Finset.disjoint_left.mp (hdisj i) h hjS)
      formalIdeal_eq := ?_ }, ?_, fun i ↦ by simp, by simp⟩
  · rintro (_ | l)
    · rw [transformFamily_none, extendSets_none, formalIdeal, localIdeal_strictTransform, hIg, hJ,
        Ideal.map_span, Set.image_singleton, hh', iterate_colon_span_pow_mul hregg]
      apply map_radical_eq_span_prod _ z hz S'
      rw [Ideal.map_span, Set.image_singleton]
      exact hh'span
    · induction l using Fin.lastCases with
      | last =>
        rw [transformFamily_last, extendSets_last, formalIdeal, localIdeal_preimage, hIg]
        apply map_radical_eq_span_prod _ z hz {j}
        rw [Finset.prod_singleton, Ideal.map_span, Set.image_singleton]
        exact hgz
      | cast i =>
        rw [transformFamily_castSucc, extendSets_castSucc]
        exact formalIdeal_preimage_eq π (F (some i)) y (c.A (some i)) (fun i ↦ c.t i)
          (c.formalIdeal_eq (some i)) z hz fun l hl ↦
            (hzout l fun hlS ↦ Finset.disjoint_left.mp (hdisj i) hl hlS).symm
  · change S'.card ≤ m - 1
    calc S'.card ≤ ((c.A none).erase j).card := Finset.card_le_card hS'
      _ = m - 1 := by rw [Finset.card_erase_of_mem hjS, hcard]

end Family

section Step

/-- A part of a regular system of parameters of `Ô` has at most `dim O` members. -/
theorem card_le_ringKrullDim_of_linearIndependent {O : Type*} [CommRing O] [IsRegularLocalRing O]
    {n : ℕ} (t : Fin n → maximalIdeal (AdicCompletion (maximalIdeal O) O))
    (ht : LinearIndependent (ResidueField (AdicCompletion (maximalIdeal O) O))
      fun i ↦ (maximalIdeal (AdicCompletion (maximalIdeal O) O)).toCotangent (t i)) :
    (n : WithBot ℕ∞) ≤ ringKrullDim O := by
  have h1 := ht.fintype_card_le_finrank
  rw [Fintype.card_fin, ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    AdicCompletion.spanFinrank_maximalIdeal_eq] at h1
  rw [← (isRegularLocalRing_iff O).mp inferInstance]
  exact_mod_cast h1

/-- Blowups of locally Noetherian schemes are locally Noetherian. -/
instance isLocallyNoetherian_blowup {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) : IsLocallyNoetherian (blowup D) := by
  have := Geometry.BlowupAlteration.blowupStructure_isProper D
  exact LocallyOfFiniteType.isLocallyNoetherian (blowupStructure D)

/-- Away from the support of `D`, the blowup is a local isomorphism. -/
theorem isIso_stalkMap_blowupStructure {X : Scheme.{u}} [IsIntegral X] (D : X.IdealSheafData)
    (y : blowup D) (hy : blowupStructure D y ∉ D.support) :
    IsIso ((blowupStructure D).stalkMap y) := by
  have := Geometry.BlowupComplement.blowupStructure_supportComplement_isIso D
  have h1 : IsOpenImmersion ((blowupStructure D ⁻¹ᵁ D.support.compl).ι ≫ blowupStructure D) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have h2 := (IsOpenImmersion.iff_isIso_stalkMap.mp h1).2 ⟨y, hy⟩
  rw [Scheme.Hom.stalkMap_comp] at h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ ((blowupStructure D).stalkMap y)
    ((blowupStructure D ⁻¹ᵁ D.support.compl).ι.stalkMap ⟨y, hy⟩) inferInstance h2

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType p]

/-- **The blowup step at a closed point.** Let `F` be a normal crossings family with
multiplicity at most `m ≥ 1` for `F none` and at most `1` for the other members, `C` the `m`-fold
locus of `F none` (`C ≠ X`) and `π` the blowup along `C`. At every closed point `y` of the blowup,
`𝒪_y` is regular and the transformed family has a chart with multiplicity at most `m - 1` for
the strict transform and at most `1` for the others. -/
theorem blowup_step_point [Smooth p] {r m : ℕ} (hm : 1 ≤ m) (F : Option (Fin r) → Closeds X)
    (hF : IsNCFamily F (fun l ↦ l.elim m fun _ ↦ 1)) (hC : mFoldLocus F none m ≠ ⊤)
    (y : blowup (Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none m)))
    (hy : IsClosed ({y} : Set (blowup (Scheme.IdealSheafData.vanishingIdeal
      (mFoldLocus F none m))))) :
    IsRegularLocalRing
        ((blowup (Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none m))).presheaf.stalk y) ∧
      ∃ c' : NCChart (transformFamily (blowupStructure (Scheme.IdealSheafData.vanishingIdeal
          (mFoldLocus F none m))) F (mFoldLocus F none m) m) y,
        ∀ l, (c'.A l).card ≤ l.elim (m - 1) fun _ ↦ 1 := by
  classical
  let C := mFoldLocus F none m
  let D := Scheme.IdealSheafData.vanishingIdeal C
  let π := blowupStructure D
  have hD : D.support ≠ ⊤ := by
    rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
  have hmod : IsModification π := Geometry.BlowupModification.blowupStructure_isModification D hD
  have : IsIntegral (blowup D) := hmod.sourceIntegral
  have hreg : IsRegularScheme X := Geometry.RegularSmooth.isRegularScheme_of_smooth p
  have hx : IsClosed ({π y} : Set X) := by
    have := π.isClosedMap _ hy
    rwa [Set.image_singleton] at this
  obtain ⟨c, hcb⟩ := hF (π y) hx
  have : IsRegularLocalRing (X.presheaf.stalk (π y)) := hreg (π y)
  have : IsRegularLocalRing (X.completedLocalRing (π y)) :=
    Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
  have hspec := mFoldLocus_spec p F _ hF none hm (π y) hx c
  have hcbn : (c.A none).card ≤ m := hcb none
  by_cases hxC : π y ∈ C
  · have hcard : (c.A none).card = m := by
      by_contra hne
      exact hspec.2 (lt_of_le_of_ne hcbn hne) hxC
    obtain ⟨-, hCf⟩ := hspec.1 hcard
    let : Algebra k (X.presheaf.stalk (π y)) := (Scheme.baseToStalk p (π y)).hom.toAlgebra
    let : Algebra k ((blowup D).presheaf.stalk y) :=
      (Scheme.baseToStalk (π ≫ p) y).hom.toAlgebra
    have hφk : ∀ a : k, (π.stalkMap y).hom (algebraMap k _ a) = algebraMap k _ a := by
      intro a
      have h := Scheme.baseToStalk_comp_stalkMap π p y
      exact congrArg (fun f ↦ f.hom a) h
    have hresO : Function.Surjective (algebraMap k (ResidueField (X.presheaf.stalk (π y)))) :=
      residue_comp_baseToStalk_surjective' p (π y) hx
    have hresP : Function.Bijective (algebraMap k (ResidueField ((blowup D).presheaf.stalk y))) :=
      ⟨(algebraMap k _).injective, residue_comp_baseToStalk_surjective' (π ≫ p) y hy⟩
    have hdim : (c.n : WithBot ℕ∞) ≤ ringKrullDim ((blowup D).presheaf.stalk y) := by
      rw [ringKrullDim_stalk_eq_of_isClosed (π ≫ p) y hy,
        DeJong.topologicalKrullDim_eq_of_isModification p π,
        ← ringKrullDim_stalk_eq_of_isClosed p (π y) hx]
      exact card_le_ringKrullDim_of_linearIndependent c.t c.indep
    obtain ⟨hQ, c', h1, h2, h3⟩ := exists_ncChart_of_chartData π y hφk hresO hresP F C m c hcard
      hCf (hasChartData_blowupStructure C y) hdim
    refine ⟨Algebra.CompletionRegularity.isRegularLocalRing_of_completion _, c', ?_⟩
    rintro (_ | l)
    · exact h1
    · induction l using Fin.lastCases with
      | last => exact h3.le
      | cast i =>
        rw [h2]
        exact hcb (some i)
  · have hyD : π y ∉ D.support := by
      rwa [Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
    have := isIso_stalkMap_blowupStructure D y hyD
    obtain ⟨c', hc'⟩ := exists_ncChart_of_isIso π y F C m hxC c
    have hlt : (c.A none).card < m := lt_of_le_of_ne hcbn fun h ↦ hxC (hspec.1 h).1
    refine ⟨IsRegularLocalRing.of_ringEquiv
      (asIso (π.stalkMap y)).commRingCatIsoToRingEquiv, c', ?_⟩
    rintro (_ | l)
    · rw [hc', extendSets_none]
      change (c.A none).card ≤ m - 1
      omega
    · induction l using Fin.lastCases with
      | last => rw [hc', extendSets_last]; simp
      | cast i =>
        rw [hc', extendSets_castSucc]
        exact hcb (some i)

/-- **The blowup step** (de Jong 2.4): blowing up the `m`-fold locus `C ≠ X` of `F none` gives a
regular scheme on which the transformed family is a normal crossings family with multiplicity at
most `m - 1` for the strict transform and at most `1` for the other members. -/
theorem blowup_step [Smooth p] {r m : ℕ} (hm : 1 ≤ m) (F : Option (Fin r) → Closeds X)
    (hF : IsNCFamily F (fun l ↦ l.elim m fun _ ↦ 1)) (hC : mFoldLocus F none m ≠ ⊤) :
    IsRegularScheme (blowup (Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none m))) ∧
      IsNCFamily (transformFamily (blowupStructure (Scheme.IdealSheafData.vanishingIdeal
          (mFoldLocus F none m))) F (mFoldLocus F none m) m)
        (fun l ↦ l.elim (m - 1) fun _ ↦ 1) := by
  have := Geometry.BlowupAlteration.blowupStructure_isProper
    (Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none m))
  refine ⟨isRegularScheme_of_closedPoints
    (blowupStructure (Scheme.IdealSheafData.vanishingIdeal (mFoldLocus F none m)) ≫ p)
    fun y hy ↦ (blowup_step_point p hm F hF hC y hy).1,
    fun y hy ↦ (blowup_step_point p hm F hF hC y hy).2⟩

end Step

section Bookkeeping

theorem mem_iSup_closeds {α ι : Type*} [TopologicalSpace α] [Finite ι] (f : ι → Closeds α)
    (x : α) : x ∈ ⨆ i, f i ↔ ∃ i, x ∈ f i := by
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup, ← SetLike.mem_coe, Closeds.coe_finset_sup]
  simp

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- The transformed family covers the preimage of the family, if the centre lies in `F none`. -/
theorem exists_mem_transformFamily_iff (π : Y ⟶ X) {r : ℕ} (F : Option (Fin r) → Closeds X)
    (C : Closeds X) (m : ℕ) (hCF : C ≤ F none) (y : Y) :
    (∃ l, y ∈ transformFamily π F C m l) ↔ ∃ l, π y ∈ F l := by
  constructor
  · rintro ⟨_ | l, hl⟩
    · refine ⟨none, ?_⟩
      have hle : strictTransform π (F none) C m ≤ (F none).preimage π.continuous := by
        have h := Scheme.IdealSheafData.support_antitone
          (le_colonIter ((Scheme.IdealSheafData.vanishingIdeal (F none)).comap π)
            ((Scheme.IdealSheafData.vanishingIdeal C).comap π) m)
        rwa [Scheme.IdealSheafData.support_comap,
          Geometry.ReducedClosedSubscheme.support_vanishingIdeal] at h
      exact hle hl
    · induction l using Fin.lastCases with
      | last =>
        rw [transformFamily_last] at hl
        exact ⟨none, hCF hl⟩
      | cast i =>
        rw [transformFamily_castSucc] at hl
        exact ⟨some i, hl⟩
  · rintro ⟨_ | i, hi⟩
    · by_cases hyC : π y ∈ C
      · exact ⟨some (Fin.last r), by rw [transformFamily_last]; exact hyC⟩
      · refine ⟨none, ?_⟩
        rw [transformFamily_none, ← localIdeal_ne_top_iff,
          localIdeal_strictTransform_of_not_mem π _ C m y hyC, localIdeal_ne_top_iff]
        exact hi
    · exact ⟨some i.castSucc, by rw [transformFamily_castSucc]; exact hi⟩

omit [IsLocallyNoetherian Y] in
/-- The members of a family with a chart at some point are proper closed subsets. -/
theorem ne_top_of_ncChart [IsIntegral X] [IsLocallyNoetherian X] {ι : Type*}
    (F : ι → Closeds X) (x : X) (c : NCChart F x) [IsDomain (X.completedLocalRing x)] (l : ι) :
    F l ≠ ⊤ := by
  intro htop
  have hloc : localIdeal (F l) x = ⊥ := by
    rw [localIdeal, htop, ← Scheme.IdealSheafData.support_bot,
      Scheme.IdealSheafData.vanishingIdeal_support, stalkIdeal_radical]
    obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
    rw [stalkIdeal_eq_map_germ _ U hxU, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      Ideal.map_bot, Ideal.radical_bot_of_isReduced]
  have h := c.formalIdeal_eq l
  rw [formalIdeal, hloc, Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot,
    Finset.prod_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  apply c.indep.ne_zero i
  rw [Ideal.toCotangent_eq_zero, hi]
  exact zero_mem _

end Bookkeeping

end DeJongAlterations.StableModification.Resolution.Strictify

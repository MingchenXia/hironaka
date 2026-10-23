import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination

/-!
# Flat base change of intersections and colon ideals

For a flat `R`-algebra `S` (for us: the completion of a Noetherian local ring), extension of
ideals commutes with finite intersections (`map_inf_of_flat`, `map_finsetInf_of_flat`) and with
colon ideals by finitely generated ideals (`map_colon_of_flat`): `(I : J) S = (I S : J S)`.
Both are proved with the equational criterion of flatness
(`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`).

These are used to compute the formal traces of the global centres of the resolution of a nodal
curve, which are built from the singular-locus ideal sheaf and the boundary ideal sheaves by
colon operations (blueprint `def:sm-dj-global-centres`, `lem:sm-dj-centre-traces`, chapter
`sm-dj-resolution-global.tex`; de Jong 1996, 3.4 and 4.27).
-/

noncomputable section

namespace DeJongAlterations.StableModification.Resolution.Global

section Flat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An element of an extended ideal is a finite combination of images of elements of the ideal. -/
theorem exists_sum_of_mem_map (I : Ideal R) {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ (n : ℕ) (c : Fin n → S) (a : Fin n → R), (∀ i, a i ∈ I) ∧
      x = ∑ i, a i • c i := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, hx⟩ := hx
  choose a ha hag using fun i ↦ (g i).2
  refine ⟨n, c, a, ha, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, Algebra.smul_def, hag, mul_comm]

theorem sum_smul_mem_map (I : Ideal R) {n : ℕ} (c : Fin n → S) (a : Fin n → R)
    (ha : ∀ i, a i ∈ I) : ∑ i, a i • c i ∈ I.map (algebraMap R S) := by
  refine sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i))

variable [Module.Flat R S]

/-- **Flat base change preserves intersections of two ideals**: `(I ∩ J) S = I S ∩ J S`. The proof
is the equational criterion of flatness. -/
theorem map_inf_of_flat (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) ?_
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨n, c, a, ha, hx⟩ := exists_sum_of_mem_map I hxI
  obtain ⟨n', c', a', ha', hx'⟩ := exists_sum_of_mem_map J hxJ
  let r : Fin n ⊕ Fin n' → R := Sum.elim a (fun j ↦ -a' j)
  let v : Fin n ⊕ Fin n' → S := Sum.elim c c'
  have hrel : ∑ l, r l • v l = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [r, v, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
    rw [← hx, ← hx', ← sub_eq_add_neg, sub_self]
  obtain ⟨k, A, y, hv, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  let d : Fin k → R := fun m ↦ ∑ i, a i * A (Sum.inl i) m
  have hdI : ∀ m, d m ∈ I := fun m ↦
    sum_mem fun i _ ↦ Ideal.mul_mem_right _ _ (ha i)
  have hdJ : ∀ m, d m ∈ J := by
    intro m
    have h := hA m
    rw [Fintype.sum_sum_type] at h
    simp only [r, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h
    have : d m = ∑ j, a' j * A (Sum.inr j) m := by
      change ∑ i, a i * A (Sum.inl i) m = _
      linear_combination h
    rw [this]
    exact sum_mem fun j _ ↦ Ideal.mul_mem_right _ _ (ha' j)
  have hxd : x = ∑ m, d m • y m := by
    rw [hx]
    simp only [d, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := hv (Sum.inl i)
    simp only [v, Sum.elim_inl] at this
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [smul_smul]
  rw [hxd]
  exact sum_smul_mem_map _ y d fun m ↦ ⟨hdI m, hdJ m⟩

/-- Flat base change preserves finite intersections of ideals. -/
theorem map_finsetInf_of_flat {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (s.inf I).map (algebraMap R S) = s.inf fun i ↦ (I i).map (algebraMap R S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert i s hi ih => rw [Finset.inf_insert, Finset.inf_insert, map_inf_of_flat, ih]

/-- **Flat base change of a principal colon ideal**: `(I : b) S = (I S : b)`. -/
theorem map_colon_singleton_of_flat (I : Ideal R) (b : R) :
    (I.colon {b}).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon {algebraMap R S b} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ (by simpa [smul_eq_mul] using
      Submodule.mem_colon_singleton.mp hr)
  · intro x hx
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨n, c, a, ha, hxc⟩ := exists_sum_of_mem_map I hx
    let r : Unit ⊕ Fin n → R := Sum.elim (fun _ ↦ b) (fun j ↦ -a j)
    let v : Unit ⊕ Fin n → S := Sum.elim (fun _ ↦ x) c
    have hrel : ∑ l, r l • v l = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [r, v, Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib,
        Finset.univ_unique, Finset.sum_singleton]
      rw [← hxc, Algebra.smul_def, mul_comm, ← sub_eq_add_neg, sub_self]
    obtain ⟨k, A, y, hv, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
    have hcol : ∀ m, A (Sum.inl ()) m ∈ I.colon {b} := by
      intro m
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      have h := hA m
      rw [Fintype.sum_sum_type] at h
      simp only [r, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib,
        Finset.univ_unique, Finset.sum_singleton] at h
      have : A (Sum.inl ()) m * b = ∑ j, a j * A (Sum.inr j) m := by
        linear_combination h
      rw [this]
      exact sum_mem fun j _ ↦ Ideal.mul_mem_right _ _ (ha j)
    have hxv := hv (Sum.inl ())
    simp only [v, Sum.elim_inl] at hxv
    rw [hxv]
    exact sum_smul_mem_map _ y _ hcol

/-- **Flat base change of colon ideals** by a finitely generated ideal:
`(I : J) S = (I S : J S)`. -/
theorem map_colon_of_flat (I J : Ideal R) (hJ : J.FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon ((J.map (algebraMap R S) : Ideal S) : Set S) := by
  classical
  obtain ⟨T, rfl⟩ := hJ
  have h1 : I.colon ((Ideal.span (T : Set R) : Ideal R) : Set R) =
      T.inf fun t ↦ I.colon {t} := by
    rw [Ideal.colon_span]
    ext r
    simp only [Submodule.mem_colon, Submodule.mem_finsetInf, Set.mem_singleton_iff, forall_eq,
      Finset.mem_coe]
  have h2 : (I.map (algebraMap R S)).colon
      (((Ideal.span (T : Set R)).map (algebraMap R S) : Ideal S) : Set S) =
      T.inf fun t ↦ (I.map (algebraMap R S)).colon {algebraMap R S t} := by
    rw [Ideal.map_span, Ideal.colon_span]
    ext r
    simp only [Submodule.mem_colon, Submodule.mem_finsetInf, Set.mem_singleton_iff, forall_eq,
      Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [h1, h2, map_finsetInf_of_flat]
  exact Finset.inf_congr rfl fun t _ ↦ map_colon_singleton_of_flat I t

end Flat

end DeJongAlterations.StableModification.Resolution.Global

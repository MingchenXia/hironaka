import Hironaka.Resolution.HironakaG4MonomialFiniteTopPhase
import Hironaka.Resolution.HironakaG4MonomialCoefficientDeletion
import Hironaka.Invariant.MonomialInvariant

/-!
# Internally selected finite all-chart monomial strategies

BM97 Lemma12.8, arithmetic blowup-only scope. Every selected set must be
feasible for every tracked positive marked row; all pivot/incidence children
are constructed. Actual geometric centre realization is separate.
Blueprint: `hironaka-g4-monomial-internal-selector.tex`.
-/
set_option autoImplicit false
open Finset

namespace Hironaka.HironakaG4MonomialInternalSelector

open HironakaG4MonomialMaximalContact HironakaG4MonomialCoefficientDeletion

noncomputable section

/-- An internally selected well-founded tree covering all over-centre charts. -/
inductive FiniteStrategy {ι : Type} (d : ι → ℕ) :
    {b : ℕ} → (ι → Fin b → ℕ) → Finset (Fin b) → Prop
  | done {b : ℕ} {F : ι → Fin b → ℕ} {J : Finset (Fin b)}
      (i : ι) (failure : rowWeight (F i) J < d i) : FiniteStrategy d F J
  | step {b : ℕ} {F : ι → Fin b → ℕ} {J : Finset (Fin b)}
      (S : Finset (Fin b)) (hSJ : S ⊆ J) (hne : S.Nonempty)
      (feasible : ∀ i, d i ≤ rowWeight (F i) S)
      (children : ∀ (p : Fin b), p ∈ S → ∀ (R : Finset (Fin b)), R ⊆ J.erase p →
        FiniteStrategy d (transformMarkedRows d S R F)
          (insert (Fin.last b) (R.image Fin.castSucc))) : FiniteStrategy d F J

private def natLabels {b : ℕ} (J : Finset (Fin b)) : Finset ℕ := J.map Fin.valEmbedding

private def natRow {b : ℕ} (a : Fin b → ℕ) (j : ℕ) : ℕ :=
  if h : j < b then a ⟨j,h⟩ else 0

private theorem natRow_val {b : ℕ} (a : Fin b → ℕ) (j : Fin b) :
    natRow a j.val = a j := by simp [natRow]

private theorem weight_nat {b : ℕ} (a : Fin b → ℕ) (J : Finset (Fin b)) :
    ∑ j ∈ natLabels J, natRow a j = rowWeight a J := by
  simp [natLabels, rowWeight, natRow, Finset.sum_map]

private theorem inv_congr_on {n d : ℕ} {J : Finset ℕ} {a a' : ℕ → ℕ}
    (h : ∀ j ∈ J, a j = a' j) :
    MonomialInvariant.inv n J a d = MonomialInvariant.inv n J a' d := by
  have hs (K : Finset ℕ) (hK : K ⊆ J) : ∑ j ∈ K, a j = ∑ j ∈ K, a' j :=
    Finset.sum_congr rfl fun j hj => h j (hK hj)
  have hf : MonomialInvariant.feasible J a d = MonomialInvariant.feasible J a' d := by
    ext K
    rw [MonomialInvariant.mem_feasible, MonomialInvariant.mem_feasible]
    by_cases hK : K ⊆ J
    · simp only [hK, true_and, hs K hK]
    · simp [hK]
  unfold MonomialInvariant.inv
  congr 1
  rw [hf]
  apply Finset.image_congr
  intro K hK
  have hKJ := (MonomialInvariant.mem_feasible.mp hK).1
  simp only [MonomialInvariant.key, hs K hKJ]

private def principalValue {b : ℕ} (n d : ℕ) (a : Fin b → ℕ) (J : Finset (Fin b)) :=
  MonomialInvariant.inv n (natLabels J) (natRow a) d

private theorem principal_drop {b n d : ℕ} (a : Fin b → ℕ)
    (J S : Finset (Fin b)) (hn : J.card ≤ n)
    (hS : natLabels S ∈ MonomialInvariant.feasible (natLabels J) (natRow a) d)
    (htop : ∀ K ∈ MonomialInvariant.feasible (natLabels J) (natRow a) d,
      MonomialInvariant.key n (natRow a) K ≤ MonomialInvariant.key n (natRow a) (natLabels S))
    (p : Fin b) (hp : p ∈ S) (R : Finset (Fin b)) (hR : R ⊆ J.erase p) :
    principalValue n d (transformRow d S R a)
      (insert (Fin.last b) (R.image Fin.castSucc)) < principalValue n d a J := by
  let a' : ℕ → ℕ := Function.update (natRow a) b (rowWeight a S-d)
  have hb : b ∉ natLabels J := by
    simp only [natLabels, mem_map, Fin.valEmbedding_apply]
    rintro ⟨j,_,hj⟩
    exact (Nat.ne_of_lt j.isLt) hj
  have ha' : ∀ j ∈ natLabels J, a' j = natRow a j := by
    intro j hj
    exact Function.update_of_ne (by intro he; exact hb (he ▸ hj)) _ _
  have hSel : d ≤ rowWeight a S := by
    simpa only [weight_nat] using (MonomialInvariant.mem_feasible.mp hS).2
  have hD : a' b+d = ∑ j ∈ natLabels S, natRow a j := by
    simp only [a', Function.update_self, weight_nat]
    omega
  have hnew : natLabels (insert (Fin.last b) (R.image Fin.castSucc)) = insert b (natLabels R) := by
    ext j
    simp [natLabels, Finset.mem_map, Finset.mem_image]
  have hsub : natLabels R ⊆ (natLabels J).erase p.val := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
    have hkJ := hR hk
    exact mem_erase.mpr ⟨by intro he; exact (ne_of_mem_erase hkJ) (Fin.ext he),
      Finset.mem_map.mpr ⟨k,mem_of_mem_erase hkJ,rfl⟩⟩
  have hcompare := MonomialInvariant.inv_lt_of_blowup
    (by simpa [natLabels] using hn) hS htop
    (Finset.mem_map.mpr ⟨p,hp,rfl⟩) (Finset.insert_subset_insert b hsub) ha' hD
  change MonomialInvariant.inv n _ _ d < _
  rw [hnew]
  have hcongr : MonomialInvariant.inv n (insert b (natLabels R))
      (natRow (transformRow d S R a)) d =
      MonomialInvariant.inv n (insert b (natLabels R)) a' d := by
    apply inv_congr_on
    intro j hj
    rcases mem_insert.mp hj with hjb | hj
    · subst j
      have heval : natRow (transformRow d S R a) b =
          transformRow d S R a (Fin.last b) := by
        dsimp only [natRow]
        rw [dif_pos (Nat.lt_succ_self b)]
        rfl
      rw [heval]
      simp [transformRow,a']
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
      change natRow (transformRow d S R a) k.castSucc.val=a' k.val
      rw [natRow_val]
      have hkne : k.val ≠ b := Nat.ne_of_lt k.isLt
      simp only [transformRow,Fin.lastCases_castSucc,if_pos hk]
      simp [a',hkne,natRow_val]
  rw [hcongr]
  exact hcompare

private theorem least_row_strategy {ι : Type} {d n : ℕ} (hd : 0<d) (w : ι) :
    ∀ {b : ℕ} (F : ι → Fin b → ℕ) (J : Finset (Fin b)), J.card ≤ n →
      (∀ i j, j ∈ J → F w j ≤ F i j) → FiniteStrategy (fun _ => d) F J := by
  have hwf := MonomialInvariant.wellFoundedLT_val
  suffices ∀ v : WithBot MonomialInvariant.Val, ∀ {b : ℕ}
      (F : ι → Fin b → ℕ) (J : Finset (Fin b)), principalValue n d (F w) J = v →
      J.card ≤ n → (∀ i j, j ∈ J → F w j ≤ F i j) →
      FiniteStrategy (fun _ => d) F J by
    intro b F J hn hleast
    exact this _ F J rfl hn hleast
  intro v
  induction v using hwf.wf.induction with
  | h v ih =>
    intro b F J hv hn hleast
    by_cases halive : d ≤ rowWeight (F w) J
    · obtain ⟨I,hI,hval,htop⟩ := MonomialInvariant.exists_top
        (n:=n) (S:=natLabels J) (a:=natRow (F w)) (d:=d)
        (by simpa only [weight_nat] using halive)
      have hIJ := (MonomialInvariant.mem_feasible.mp hI).1
      let S := J.filter (fun j => j.val ∈ I)
      have hS : natLabels S = I := by
        ext j
        constructor
        · rintro hj
          obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
          exact (mem_filter.mp hk).2
        · intro hj
          obtain ⟨k,hk,hkj⟩ := Finset.mem_map.mp (hIJ hj)
          change k.val=j at hkj
          have hkI : k.val ∈ I := hkj.symm ▸ hj
          exact Finset.mem_map.mpr ⟨k,mem_filter.mpr ⟨hk,hkI⟩,hkj⟩
      have hSJ : S ⊆ J := Finset.filter_subset _ _
      have hSel : d ≤ rowWeight (F w) S := by
        rw [← weight_nat, hS]
        exact (MonomialInvariant.mem_feasible.mp hI).2
      have hne : S.Nonempty := by
        by_contra he
        have he' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        simp [he',rowWeight] at hSel
        omega
      apply FiniteStrategy.step S hSJ hne
      · intro i
        exact hSel.trans (Finset.sum_le_sum fun j hj => hleast i j (hSJ hj))
      · intro p hp R hR
        have hlt := principal_drop (F w) J S hn (hS.symm ▸ hI)
          (by simpa only [hS] using htop) p hp R hR
        rw [hv] at hlt
        apply ih _ hlt (transformMarkedRows (fun _ => d) S R F)
          (insert (Fin.last b) (R.image Fin.castSucc)) rfl
        · have hpJ := hSJ hp
          have hcardR := Finset.card_le_card hR
          have hcard : R.card+1 ≤ J.card := by
            rw [Finset.card_erase_of_mem hpJ] at hcardR
            have hpos := Finset.card_pos.mpr ⟨p,hpJ⟩
            omega
          calc
            (insert (Fin.last b) (R.image Fin.castSucc)).card ≤
              (R.image Fin.castSucc).card+1 := Finset.card_insert_le _ _
            _ ≤ R.card+1 := Nat.add_le_add_right (Finset.card_image_le) 1
            _ ≤ n := hcard.trans hn
        · intro i j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simp only [transformMarkedRows, transformRow, Fin.lastCases_last]
            exact Nat.sub_le_sub_right
              (Finset.sum_le_sum fun k hk => hleast i k (hSJ hk)) d
          · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
            simp only [transformMarkedRows, transformRow, Fin.lastCases_castSucc,
              if_pos hk]
            exact hleast i k (mem_of_mem_erase (hR hk))
    · exact FiniteStrategy.done w (Nat.lt_of_not_ge halive)

private theorem weight_scale {b : ℕ} (t : ℕ) (a : Fin b → ℕ) (J : Finset (Fin b)) :
    rowWeight (fun j => t*a j) J = t*rowWeight a J := by
  simp only [rowWeight, Finset.mul_sum]

private theorem transform_scale {b : ℕ} (t d : ℕ) (a : Fin b → ℕ)
    (S R : Finset (Fin b)) :
    transformRow (t*d) S R (fun j => t*a j) = fun j => t*transformRow d S R a j := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [transformRow, Fin.lastCases_last, weight_scale, Nat.mul_sub_left_distrib]
  · by_cases hk : k ∈ R <;> simp [transformRow, hk]

private theorem strategy_scale_reflection {ι : Type} (d t : ι → ℕ) (ht : ∀ i, 0<t i) :
    ∀ {b : ℕ} (G : ι → Fin b → ℕ) (J : Finset (Fin b)),
      FiniteStrategy (fun i => t i*d i) G J →
      ∀ F : ι → Fin b → ℕ, (∀ i j, G i j = t i*F i j) → FiniteStrategy d F J := by
  intro b G J T
  induction T with
  | @done b G J i failure =>
    intro F hscale
    apply FiniteStrategy.done i
    have hrow : G i = fun j => t i*F i j := funext (hscale i)
    rw [hrow, weight_scale] at failure
    exact Nat.lt_of_mul_lt_mul_left failure
  | @step b G J S hSJ hne hf children ih =>
    intro F hscale
    apply FiniteStrategy.step S hSJ hne
    · intro i
      have hrow : G i = fun j => t i*F i j := funext (hscale i)
      have hi := hf i
      rw [hrow, weight_scale] at hi
      exact Nat.le_of_mul_le_mul_left hi (ht i)
    · intro p hp R hR
      apply ih p hp R hR (transformMarkedRows d S R F)
      intro i j
      have hrow : G i = fun j => t i*F i j := funext (hscale i)
      simp only [transformMarkedRows, hrow, transform_scale]

private def allCommon {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) (j : Fin b) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => F i j)

private def allResidual {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) : ι → Fin b → ℕ := fun i j => F i j-allCommon F j

private def residualMinimum {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => rowWeight (allResidual F i) Finset.univ)

private theorem allCommon_le {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) (i : ι) (j : Fin b) : allCommon F j ≤ F i j :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem common_split {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) (i : ι) (j : Fin b) :
    F i j = allCommon F j+allResidual F i j := by
  have h := allCommon_le F i j
  dsimp only [allResidual]
  omega

private theorem exists_residual_minimum {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) :
    ∃ w : ι, rowWeight (allResidual F w) Finset.univ = residualMinimum F := by
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => rowWeight (allResidual F i) Finset.univ)
  exact ⟨w,hw.symm⟩

private theorem residual_minimum_le {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F : ι → Fin b → ℕ) (i : ι) :
    residualMinimum F ≤ rowWeight (allResidual F i) Finset.univ :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem residual_minimum_le_split {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    (F B : ι → Fin b → ℕ) (c : Fin b → ℕ)
    (hsplit : ∀ i j, F i j = c j+B i j) (i : ι) :
    residualMinimum F ≤ rowWeight (B i) Finset.univ := by
  apply (residual_minimum_le F i).trans
  apply Finset.sum_le_sum
  intro j _
  have hc : c j ≤ allCommon F j := by
    apply Finset.le_inf'
    intro k _
    rw [hsplit k j]
    omega
  have hf := hsplit i j
  dsimp only [allResidual]
  omega

def Supported {ι : Type} {b : ℕ} (F : ι → Fin b → ℕ)
    (J : Finset (Fin b)) : Prop := ∀ i j, j ∉ J → F i j=0

private theorem weight_of_supported {ι : Type} {b : ℕ} {F : ι → Fin b → ℕ}
    {J : Finset (Fin b)} (hs : Supported F J) (i : ι) :
    rowWeight (F i) J = rowWeight (F i) Finset.univ := by
  apply Finset.sum_subset (Finset.subset_univ J)
  intro j _ hj
  exact hs i j hj

theorem transform_supported {ι : Type} {b : ℕ} (d : ι → ℕ)
    (F : ι → Fin b → ℕ) (S R : Finset (Fin b)) :
    Supported (transformMarkedRows d S R F)
      (insert (Fin.last b) (R.image Fin.castSucc)) := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · intro hj
    exact False.elim (hj (Finset.mem_insert_self _ _))
  · intro hj
    have hk : k ∉ R := by
      intro hk
      exact hj (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,hk,rfl⟩))
    simp [transformMarkedRows, transformRow, hk]

private theorem residual_supported {ι : Type} [Fintype ι] [Nonempty ι] {b : ℕ}
    {F : ι → Fin b → ℕ} {J : Finset (Fin b)} (hs : Supported F J) :
    Supported (allResidual F) J := by
  intro i j hj
  simp [allResidual,hs i j hj]

private theorem weight_transform_live {b d : ℕ} (a : Fin b → ℕ)
    (S R : Finset (Fin b)) :
    rowWeight (transformRow d S R a) (insert (Fin.last b) (R.image Fin.castSucc)) =
      rowWeight a R+(rowWeight a S-d) := by
  have hnot : Fin.last b ∉ R.image Fin.castSucc := by simp
  rw [rowWeight, Finset.sum_insert hnot]
  simp only [transformRow, Fin.lastCases_last]
  have himg : ∑ j ∈ R.image Fin.castSucc, Fin.lastCases (rowWeight a S-d)
      (fun j => if j ∈ R then a j else 0) j = rowWeight a R := by
    rw [Finset.sum_image (by intro i _ j _ h; exact Fin.castSucc_inj.mp h)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  rw [himg]
  omega

private theorem selected_degree_eq {b L : ℕ} (a : Fin b → ℕ) (S : Finset (Fin b))
    (hf : L ≤ rowWeight a S) (hdeg : rowWeight a Finset.univ ≤ L) :
    rowWeight a S=L := by
  have hs := Finset.sum_le_sum_of_subset (Finset.subset_univ S) (f:=a)
  change rowWeight a S ≤ rowWeight a Finset.univ at hs
  omega

private theorem degree_transform_le {b L : ℕ} (a : Fin b → ℕ)
    (S R : Finset (Fin b)) (hf : L ≤ rowWeight a S)
    (hdeg : rowWeight a Finset.univ ≤ L) :
    rowWeight (transformRow L S R a) Finset.univ ≤ L := by
  have hs := selected_degree_eq a S hf hdeg
  have hsum : rowWeight (transformRow L S R a) Finset.univ = rowWeight a R := by
    have hs0 : (∑ j ∈ S, a j)-L=0 := by
      change rowWeight a S-L=0
      omega
    simp only [rowWeight, Fin.sum_univ_castSucc, transformRow,
      Fin.lastCases_castSucc, Fin.lastCases_last,hs0,add_zero]
    simp
  rw [hsum]
  exact (Finset.sum_le_sum_of_subset (Finset.subset_univ R)).trans hdeg

private theorem degree_transform_lt_of_lost {b L : ℕ} (a : Fin b → ℕ)
    (S R : Finset (Fin b)) (hf : L ≤ rowWeight a S)
    (hdeg : rowWeight a Finset.univ ≤ L) (h : Fin b) (hpos : 0<a h)
    (hnot : h ∉ R) :
    rowWeight (transformRow L S R a) Finset.univ < L := by
  have hs := selected_degree_eq a S hf hdeg
  have hsum : rowWeight (transformRow L S R a) Finset.univ = rowWeight a R := by
    have hs0 : (∑ j ∈ S, a j)-L=0 := by
      change rowWeight a S-L=0
      omega
    simp only [rowWeight, Fin.sum_univ_castSucc, transformRow,
      Fin.lastCases_castSucc, Fin.lastCases_last,hs0,add_zero]
    simp
  rw [hsum]
  have hsub : R ⊆ Finset.univ.erase h := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨by intro he; exact hnot (he ▸ hj),Finset.mem_univ j⟩
  have hle := Finset.sum_le_sum_of_subset hsub (f:=a)
  change rowWeight a R ≤ rowWeight a (Finset.univ.erase h) at hle
  have heq := Finset.add_sum_erase Finset.univ a (Finset.mem_univ h)
  change a h+rowWeight a (Finset.univ.erase h)=rowWeight a Finset.univ at heq
  omega

private abbrev NormalIndex (ι : Type) (D L : ℕ) := ι ⊕ {_u : Unit // L<D}

private def normalMarks {ι : Type} (D L : ℕ) : NormalIndex ι D L → ℕ :=
  Sum.elim (fun _ => L) (fun _ => D-L)

private def normalRows {ι : Type} {b D L : ℕ} (B : ι → Fin b → ℕ)
    (c : Fin b → ℕ) : NormalIndex ι D L → Fin b → ℕ := Sum.elim B (fun _ => c)

private def commonStep {b : ℕ} (D L : ℕ) (S R : Finset (Fin b))
    (c : Fin b → ℕ) : Fin (b+1) → ℕ :=
  Fin.lastCases (rowWeight c S+L-D) (fun j => if j ∈ R then c j else 0)

private theorem normal_transform {ι : Type} {b D L : ℕ}
    (B : ι → Fin b → ℕ) (c : Fin b → ℕ) (S R : Finset (Fin b)) :
    normalRows (D:=D) (L:=L) (transformFamily L S R B) (commonStep D L S R c) =
      transformMarkedRows (normalMarks D L) S R (normalRows (D:=D) (L:=L) B c) := by
  funext i j
  cases i with
  | inl i => rfl
  | inr u =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [normalRows, Sum.elim_inr, commonStep, transformMarkedRows,
        transformRow, normalMarks, Fin.lastCases_last]
      have h := u.property
      omega
    · simp only [normalRows,Sum.elim_inr,commonStep,transformMarkedRows,
        transformRow,normalMarks,Fin.lastCases_castSucc]

private theorem normal_feasible_original {ι : Type} {b D L : ℕ}
    (F B : ι → Fin b → ℕ) (c : Fin b → ℕ)
    (hsplit : ∀ i j, F i j=c j+B i j) (S : Finset (Fin b))
    (hf : markedCosupport (normalRows (D:=D) (L:=L) B c) (normalMarks D L) S) :
    ∀ i, D ≤ rowWeight (F i) S := by
  intro i
  have hB := hf (Sum.inl i)
  change L ≤ rowWeight (B i) S at hB
  have hs : rowWeight (F i) S=rowWeight c S+rowWeight (B i) S := by
    simp only [rowWeight,hsplit,Finset.sum_add_distrib]
  by_cases hLD : L<D
  · have hc := hf (Sum.inr ⟨(),hLD⟩)
    change D-L ≤ rowWeight c S at hc
    omega
  · omega

private theorem split_transform {ι : Type} {b D L : ℕ}
    (F B : ι → Fin b → ℕ) (c : Fin b → ℕ)
    (hsplit : ∀ i j, F i j=c j+B i j) (S R : Finset (Fin b))
    (hf : markedCosupport (normalRows (D:=D) (L:=L) B c) (normalMarks D L) S) :
    ∀ i j, transformMarkedRows (fun _ => D) S R F i j =
      commonStep D L S R c j+transformFamily L S R B i j := by
  intro i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hB := hf (Sum.inl i)
    change L ≤ rowWeight (B i) S at hB
    have hNat : D ≤ rowWeight c S+L := by
      by_cases hLD : L<D
      · have hc := hf (Sum.inr ⟨(),hLD⟩)
        change D-L ≤ rowWeight c S at hc
        omega
      · omega
    have hs : rowWeight (F i) S=rowWeight c S+rowWeight (B i) S := by
      simp only [rowWeight,hsplit,Finset.sum_add_distrib]
    simp only [transformMarkedRows, transformFamily, transformRow, commonStep,
      Fin.lastCases_last]
    omega
  · by_cases hk : k ∈ R <;>
      simp [transformMarkedRows, transformFamily, transformRow, commonStep, hk,hsplit]

private theorem coeff_selected {κ : Type} {b : ℕ} (e : κ → ℕ) (α : κ → ℕ)
    (N : κ → Fin b → ℕ) (h : Fin b) (hα : ∀ i, N i h=α i)
    (G : {i : κ // α i<e i} → Fin b → ℕ)
    (hG : ∀ i, G i=eraseRow h (N i.val)) (T : Finset (Fin b)) (hT : h ∉ T)
    (hf : ∀ i : {i : κ // α i<e i}, e i.val-α i.val ≤ rowWeight (G i) T) :
    markedCosupport N e (insert h T) := by
  intro i
  have hs : rowWeight (N i) (insert h T)=α i+rowWeight (N i) T := by
    simp only [rowWeight,Finset.sum_insert hT,hα]
  by_cases hi : α i<e i
  · have hc := hf ⟨i,hi⟩
    change e i-α i ≤ rowWeight (G ⟨i,hi⟩) T at hc
    have heq : rowWeight (G ⟨i,hi⟩) T=rowWeight (N i) T := by
      rw [hG]
      apply Finset.sum_congr rfl
      intro j hj
      have hjh : j ≠ h := by intro he; exact hT (he ▸ hj)
      simp [eraseRow,hjh]
    rw [heq] at hc
    omega
  · omega

private theorem coeff_transform {κ : Type} {b : ℕ} (e α : κ → ℕ)
    (N : κ → Fin b → ℕ) (h : Fin b) (hα : ∀ i, N i h=α i)
    (G : {i : κ // α i<e i} → Fin b → ℕ)
    (hG : ∀ i, G i=eraseRow h (N i.val))
    (T R : Finset (Fin b)) (hT : h ∉ T) :
    ∀ i : {i : κ // α i<e i},
      transformMarkedRows (fun i : {i : κ // α i<e i} => e i.val-α i.val) T (R.erase h) G i =
      eraseRow h.castSucc (transformMarkedRows e (insert h T) R N i.val) := by
  intro i
  have hs : rowWeight (N i.val) (insert h T)=α i.val+rowWeight (G i) T := by
    rw [rowWeight,Finset.sum_insert hT,hα]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hG]
    have hjh : j ≠ h := by intro he; exact hT (he ▸ hj)
    simp [eraseRow,hjh]
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [transformMarkedRows, transformRow, Fin.lastCases_last, eraseRow,
      if_neg (Ne.symm (Fin.castSucc_ne_last h))]
    have hi := i.property
    omega
  · by_cases hk : k=h
    · subst k
      simp [transformMarkedRows,transformRow,eraseRow,hG]
    · simp [transformMarkedRows,transformRow,eraseRow,hG,hk]

private theorem live_card_le {b : ℕ} (J : Finset (Fin b)) (p : Fin b)
    (hp : p ∈ J) (R : Finset (Fin b)) (hR : R ⊆ J.erase p) :
    (insert (Fin.last b) (R.image Fin.castSucc)).card ≤ J.card := by
  have hc := Finset.card_le_card hR
  rw [Finset.card_erase_of_mem hp] at hc
  have hp' := Finset.card_pos.mpr ⟨p,hp⟩
  calc
    (insert (Fin.last b) (R.image Fin.castSucc)).card ≤
      (R.image Fin.castSucc).card+1 := Finset.card_insert_le _ _
    _ ≤ R.card+1 := Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ J.card := by omega

private theorem phase_finish {ι : Type} [Fintype ι] [Nonempty ι] {D L n b : ℕ}
    (F B : ι → Fin b → ℕ) (c : Fin b → ℕ) (J : Finset (Fin b)) (w : ι)
    (hn : J.card ≤ n) (hs : Supported F J)
    (hsplit : ∀ i j, F i j=c j+B i j)
    (hdeg : rowWeight (B w) Finset.univ ≤ L)
    (hfail : ¬markedCosupport (normalRows (D:=D) (L:=L) B c) (normalMarks D L) J)
    (next : ∀ {b' : ℕ} (F' : ι → Fin b' → ℕ) (J' : Finset (Fin b')),
      J'.card ≤ n → Supported F' J' → residualMinimum F'<L →
      FiniteStrategy (fun _ => D) F' J') : FiniteStrategy (fun _ => D) F J := by
  classical
  by_cases hex : ∃ i, rowWeight (F i) J<D
  · obtain ⟨i,hi⟩ := hex
    exact FiniteStrategy.done i hi
  · have halive : ∀ i, D ≤ rowWeight (F i) J := by
      intro i
      exact Nat.le_of_not_gt (fun hi => hex ⟨i,hi⟩)
    have hBs : Supported B J := by
      intro i j hj
      have hf := hs i j hj
      have hsp := hsplit i j
      omega
    obtain ⟨i,hi⟩ := Classical.not_forall.mp hfail
    cases i with
    | inl i =>
      have hi' : rowWeight (B i) J<L := Nat.lt_of_not_ge hi
      apply next F J hn hs
      apply lt_of_le_of_lt (residual_minimum_le_split F B c hsplit i)
      rw [← weight_of_supported hBs i]
      exact hi'
    | inr u =>
      have hi' : rowWeight c J<D-L := Nat.lt_of_not_ge hi
      have hw := halive w
      have hsub : rowWeight (B w) J ≤ L :=
        (Finset.sum_le_sum_of_subset (Finset.subset_univ J)).trans hdeg
      have heq : rowWeight (F w) J=rowWeight c J+rowWeight (B w) J := by
        simp only [rowWeight,hsplit,Finset.sum_add_distrib]
      have hLD := u.property
      omega

private theorem lift_coefficient_strategy {ι : Type} {D L n : ℕ}
    (w : ι) (α : NormalIndex ι D L → ℕ) (hαw : 0<α (Sum.inl w))
    (finish : ∀ {b : ℕ} (F B : ι → Fin b → ℕ) (c : Fin b → ℕ)
      (J : Finset (Fin b)), J.card ≤ n → Supported F J →
      (∀ i j, F i j=c j+B i j) → rowWeight (B w) Finset.univ ≤ L →
      ¬markedCosupport (normalRows (D:=D) (L:=L) B c) (normalMarks D L) J →
      FiniteStrategy (fun _ => D) F J) :
    ∀ {b : ℕ} (G : {i : NormalIndex ι D L // α i<normalMarks D L i} → Fin b → ℕ)
      (Jc : Finset (Fin b)),
      FiniteStrategy (fun i : {i : NormalIndex ι D L // α i<normalMarks D L i} =>
        normalMarks D L i.val-α i.val) G Jc →
      ∀ (h : Fin b) (F B : ι → Fin b → ℕ) (c : Fin b → ℕ) (J : Finset (Fin b)),
        Jc=J.erase h → h ∈ J → J.card ≤ n → Supported F J →
        (∀ i j, F i j=c j+B i j) → rowWeight (B w) Finset.univ ≤ L →
        (∀ i, normalRows (D:=D) (L:=L) B c i h=α i) →
        (∀ i, G i=eraseRow h (normalRows (D:=D) (L:=L) B c i.val)) →
        FiniteStrategy (fun _ => D) F J := by
  classical
  intro b G Jc T
  induction T with
  | @done b G Jc i failure =>
    intro h F B c J hJc hh hn hs hsplit hdeg hα hG
    apply finish F B c J hn hs hsplit hdeg
    intro halive
    have hi := halive i.val
    have hsum := Finset.add_sum_erase J
      (normalRows (D:=D) (L:=L) B c i.val) hh
    change normalRows B c i.val h+
      rowWeight (normalRows B c i.val) (J.erase h)=
      rowWeight (normalRows B c i.val) J at hsum
    have hcoeff : rowWeight (G i) Jc=
        rowWeight (normalRows (D:=D) (L:=L) B c i.val) (J.erase h) := by
      rw [hJc,hG]
      apply Finset.sum_congr rfl
      intro j hj
      simp [eraseRow,ne_of_mem_erase hj]
    rw [hcoeff] at failure
    have ha := hα i.val
    have hsmall := i.property
    omega
  | @step b G Jc Tc hTc hne hf children ih =>
    intro h F B c J hJc hh hn hs hsplit hdeg hα hG
    have hTcJ : Tc ⊆ J.erase h := hJc ▸ hTc
    have hnot : h ∉ Tc := fun hhT => (ne_of_mem_erase (hTcJ hhT)) rfl
    let S := insert h Tc
    have hSJ : S ⊆ J := Finset.insert_subset hh
      (fun j hj => mem_of_mem_erase (hTcJ hj))
    have hnorm : markedCosupport (normalRows (D:=D) (L:=L) B c) (normalMarks D L) S :=
      coeff_selected (normalMarks D L) α (normalRows B c) h hα G hG Tc hnot hf
    apply FiniteStrategy.step S hSJ (Finset.insert_nonempty _ _)
      (normal_feasible_original F B c hsplit S hnorm)
    intro p hp R hR
    let J' := insert (Fin.last b) (R.image Fin.castSucc)
    let F' := transformMarkedRows (fun _ : ι => D) S R F
    let B' := transformFamily L S R B
    let c' := commonStep D L S R c
    have hn' : J'.card ≤ n := (live_card_le J p (hSJ hp) R hR).trans hn
    have hs' : Supported F' J' := transform_supported (fun _ => D) F S R
    have hsplit' : ∀ i j, F' i j=c' j+B' i j := split_transform F B c hsplit S R hnorm
    have hfB : L ≤ rowWeight (B w) S := hnorm (Sum.inl w)
    have hdeg' : rowWeight (B' w) Finset.univ ≤ L := degree_transform_le (B w) S R hfB hdeg
    have hN : normalRows (D:=D) (L:=L) B' c' =
        transformMarkedRows (normalMarks D L) S R (normalRows B c) := normal_transform B c S R
    by_cases hRlive : h ∈ R
    · have hpn : p ≠ h := by
        intro he
        exact (ne_of_mem_erase (hR hRlive)) he.symm
      have hpTc : p ∈ Tc := (Finset.mem_insert.mp hp).resolve_left hpn
      have hRc : R.erase h ⊆ Jc.erase p := by
        intro j hj
        have hjJ := hR (mem_of_mem_erase hj)
        rw [hJc]
        exact Finset.mem_erase.mpr ⟨ne_of_mem_erase hjJ,
          Finset.mem_erase.mpr ⟨ne_of_mem_erase hj,mem_of_mem_erase hjJ⟩⟩
      have hJnew : insert (Fin.last b) ((R.erase h).image Fin.castSucc)=J'.erase h.castSucc := by
        ext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [J',Ne.symm (Fin.castSucc_ne_last h)]
        · simp [J',Finset.mem_image,Fin.castSucc_inj]
      have hh' : h.castSucc ∈ J' := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h,hRlive,rfl⟩)
      apply ih p hpTc (R.erase h) hRc h.castSucc F' B' c' J'
        hJnew hh' hn' hs' hsplit' hdeg'
      · intro i
        rw [hN]
        simpa only [transformMarkedRows,transformRow,Fin.lastCases_castSucc,if_pos hRlive] using hα i
      · intro i
        rw [hN]
        exact coeff_transform (normalMarks D L) α (normalRows B c) h hα G hG Tc R hnot i
    · have hpos : 0<B w h := by
        have heq : B w h=α (Sum.inl w) := hα (Sum.inl w)
        rw [heq]
        exact hαw
      have hdef := degree_transform_lt_of_lost (B w) S R hfB hdeg h hpos hRlive
      change rowWeight (B' w) Finset.univ<L at hdef
      apply finish F' B' c' J' hn' hs' hsplit' hdeg'
      intro halive
      have hrow := halive (Sum.inl w)
      change L ≤ rowWeight (B' w) J' at hrow
      have hle := Finset.sum_le_sum_of_subset (Finset.subset_univ J') (f:=B' w)
      change rowWeight (B' w) J' ≤ rowWeight (B' w) Finset.univ at hle
      omega

private theorem strategy_by_live_bound (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (d : ι → ℕ), (∀ i, 0<d i) →
      ∀ {b : ℕ} (F : ι → Fin b → ℕ) (J : Finset (Fin b)), J.card ≤ n →
        Supported F J → FiniteStrategy d F J := by
  classical
  induction n with
  | zero =>
    intro ι _ _ d hd b F J hn _
    have hJ : J=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    let w : ι := Classical.choice inferInstance
    apply FiniteStrategy.done w
    simpa [hJ,rowWeight] using hd w
  | succ n outer =>
    intro ι _ _ d hd
    have common : ∀ D : ℕ, 0<D → ∀ {b : ℕ} (F : ι → Fin b → ℕ)
        (J : Finset (Fin b)), J.card ≤ n+1 → Supported F J →
        FiniteStrategy (fun _ => D) F J := by
      intro D hD
      suffices ∀ L : ℕ, ∀ {b : ℕ} (F : ι → Fin b → ℕ) (J : Finset (Fin b)),
          J.card ≤ n+1 → Supported F J → residualMinimum F=L →
          FiniteStrategy (fun _ => D) F J by
        intro b F J hn hs
        exact this _ F J hn hs rfl
      intro L
      induction L using Nat.strong_induction_on with
      | h L inner =>
        intro b F J hn hs hL
        by_cases hex : ∃ i, rowWeight (F i) J<D
        · obtain ⟨i,hi⟩ := hex
          exact FiniteStrategy.done i hi
        · have halive : ∀ i, D ≤ rowWeight (F i) J := by
            intro i
            exact Nat.le_of_not_gt (fun hi => hex ⟨i,hi⟩)
          obtain ⟨w,hw⟩ := exists_residual_minimum F
          rw [hL] at hw
          by_cases hzero : L=0
          · have hzeroRow : ∀ j, allResidual F w j=0 := by
              intro j
              have hle := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin b))) =>
                Nat.zero_le (allResidual F w k)) (Finset.mem_univ j)
              change allResidual F w j ≤ rowWeight (allResidual F w) Finset.univ at hle
              omega
            apply least_row_strategy hD w F J hn
            intro i j _
            have hsplit := common_split F w j
            have hc := allCommon_le F i j
            rw [hzeroRow j] at hsplit
            omega
          · have hLpos : 0<L := Nat.pos_of_ne_zero hzero
            let B := allResidual F
            let c := allCommon F
            have hsplit : ∀ i j, F i j=c j+B i j := common_split F
            have hBs : Supported B J := residual_supported hs
            have hcs : ∀ j, j ∉ J → c j=0 := by
              intro j hj
              have hz := hs w j hj
              have hc := allCommon_le F w j
              change c j ≤ F w j at hc
              omega
            let H := J.filter (fun j => 0<B w j)
            have hH : H.Nonempty := by
              by_contra he
              have hz : ∀ j ∈ J, B w j=0 := by
                intro j hj
                by_contra hz
                exact he ⟨j,Finset.mem_filter.mpr ⟨hj,Nat.pos_of_ne_zero hz⟩⟩
              have hsum : rowWeight (B w) J=0 := Finset.sum_eq_zero hz
              rw [weight_of_supported hBs w] at hsum
              change rowWeight (allResidual F w) Finset.univ=0 at hsum
              omega
            let h := H.min' hH
            have hhH : h ∈ H := Finset.min'_mem H hH
            have hh : h ∈ J := (Finset.mem_filter.mp hhH).1
            have hpos : 0<B w h := (Finset.mem_filter.mp hhH).2
            let N := normalRows (D:=D) (L:=L) B c
            let e := normalMarks (ι:=ι) D L
            let α : NormalIndex ι D L → ℕ := fun i => N i h
            let κ := {i : NormalIndex ι D L // α i<e i}
            have hκ : Nonempty κ := by
              obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => F i h)
              have hi0 : B i h=0 := by
                change F i h-allCommon F h=0
                exact Nat.sub_eq_zero_of_le hi.symm.le
              exact ⟨⟨Sum.inl i,by change B i h<L; omega⟩⟩
            let q : κ → ℕ := fun i => e i.val-α i.val
            let G : κ → Fin b → ℕ := fun i => eraseRow h (N i.val)
            have hq : ∀ i : κ, 0<q i := by
              intro i
              have hi := i.property
              change 0<e i.val-α i.val
              omega
            have hGs : Supported G (J.erase h) := by
              intro i j hj
              by_cases hjh : j=h
              · subst j
                simp [G,eraseRow]
              · have hjJ : j ∉ J := by
                  intro hmem
                  exact hj (Finset.mem_erase.mpr ⟨hjh,hmem⟩)
                have hNj : N i.val j=0 := by
                  cases hi : i.val with
                  | inl k => exact hBs k j hjJ
                  | inr u => exact hcs j hjJ
                simp [G,eraseRow,hjh,hNj]
            have hcard : (J.erase h).card ≤ n := by
              rw [Finset.card_erase_of_mem hh]
              omega
            have T : FiniteStrategy q G (J.erase h) := @outer κ inferInstance hκ q hq b G (J.erase h) hcard hGs
            have finish : ∀ {b' : ℕ} (F' B' : ι → Fin b' → ℕ) (c' : Fin b' → ℕ)
                (J' : Finset (Fin b')), J'.card ≤ n+1 → Supported F' J' →
                (∀ i j, F' i j=c' j+B' i j) → rowWeight (B' w) Finset.univ ≤ L →
                ¬markedCosupport (normalRows (D:=D) (L:=L) B' c') (normalMarks D L) J' →
                FiniteStrategy (fun _ => D) F' J' := by
              intro b' F' B' c' J' hn' hs' hsp' hdeg' hfail'
              apply phase_finish F' B' c' J' w hn' hs' hsp' hdeg' hfail'
              intro b'' F'' J'' hn'' hs'' hless
              exact inner (residualMinimum F'') hless F'' J'' hn'' hs'' rfl
            apply lift_coefficient_strategy w α hpos finish G (J.erase h) T h F B c J
              rfl hh hn hs hsplit hw.le
            · intro i
              rfl
            · intro i
              rfl
    intro b F J hn hs
    let D := ∏ i : ι, d i
    let t : ι → ℕ := fun i => ∏ j ∈ (Finset.univ : Finset ι).erase i, d j
    have prod_pos : ∀ K : Finset ι, 0<∏ i ∈ K, d i := by
      intro K
      induction K using Finset.induction_on with
      | empty => simp
      | @insert i K hi ih => rw [Finset.prod_insert hi]; exact Nat.mul_pos (hd i) ih
    have hD : 0<D := prod_pos Finset.univ
    have ht : ∀ i, 0<t i := fun i => prod_pos (Finset.univ.erase i)
    have htd : ∀ i, t i*d i=D := by
      intro i
      calc
        t i*d i=d i*t i := Nat.mul_comm _ _
        _ = ∏ j ∈ insert i ((Finset.univ : Finset ι).erase i), d j :=
          (Finset.prod_insert (by simp) (f:=d)).symm
        _ = D := by simp [D]
    let G : ι → Fin b → ℕ := fun i j => t i*F i j
    have hGs : Supported G J := by
      intro i j hj
      simp [G,hs i j hj]
    have hcommon := common D hD G J hn hGs
    have hmarks : (fun i => t i*d i)=(fun _ : ι => D) := funext htd
    apply strategy_scale_reflection d t ht G J
    · rw [hmarks]
      exact hcommon
    · intro i j
      rfl

/-- Genuine internally selected finite resolution of a simultaneous nonempty
positive-marked monomial family, covering every pivot and retained branch. -/
theorem exists_finite_marked_monomial_strategy {ι : Type} [Fintype ι] [Nonempty ι]
    {b : ℕ} (F : ι → Fin b → ℕ) (d : ι → ℕ) (hd : ∀ i, 0<d i)
    (J : Finset (Fin b)) (hs : ∀ i j, j ∉ J → F i j=0) : FiniteStrategy d F J :=
  strategy_by_live_bound J.card ι d hd F J le_rfl hs

/-- The original current proper-row family and actual positive native nuOne
internally produce a finite all-chart residual phase; no history is supplied. -/
theorem exists_original_positive_residual_strategy {r b : ℕ}
    (A : Fin r → Fin b → ℕ) (hL : 0<HironakaG4MonomialFamilyInvariant.nuOne A) :
    FiniteStrategy (fun _ => HironakaG4MonomialFamilyInvariant.nuOne A)
      (residualFamily A) Finset.univ := by
  classical
  have hP : (HironakaG4MonomialFamilyInvariant.properRows A).Nonempty := by
    by_contra he
    simp [HironakaG4MonomialFamilyInvariant.nuOne,he] at hL
  obtain ⟨i,hi⟩ := hP
  apply @exists_finite_marked_monomial_strategy
    (HironakaG4MonomialFamilyInvariant.properRows A) inferInstance ⟨⟨i,hi⟩⟩ b
    (residualFamily A) (fun _ => HironakaG4MonomialFamilyInvariant.nuOne A)
    (fun _ => hL) Finset.univ
  intro i j hj
  exact False.elim (hj (Finset.mem_univ j))

end
end Hironaka.HironakaG4MonomialInternalSelector

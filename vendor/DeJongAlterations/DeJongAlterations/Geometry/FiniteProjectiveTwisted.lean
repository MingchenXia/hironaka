import DeJongAlterations.Geometry.FiniteProjectiveCharts

/-!
# Actual compatible twisted sections on inverse projective charts

A twisted section is recorded as its actual sections and their true stalk
transition identities. Localization clears annihilators on the whole affine
overlaps, so the extension theorem does not discard nilpotents.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}

/-- Actual sections of the pullback of O(d), expressed in the native coordinate trivializations. -/
structure TwistedSection (g : Y ⟶ projectiveSpace R n) (d : ℕ) where
  val : ∀ i : Fin (n + 1), Γ(Y, chartOpen g i)
  compatible : ∀ (i j : Fin (n + 1)) (x : Y)
    (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j),
    Y.presheaf.germ (chartOpen g i) x hi (val i) =
      Y.presheaf.germ (chartOpen g j) x hj (val j) *
        Y.presheaf.germ (chartOpen g i) x hi (chartRatio g i j) ^ d

/-- The actual coordinate Xk, as a compatible degree-one tuple. -/
def coordinateTwisted (g : Y ⟶ projectiveSpace R n) (k : Fin (n + 1)) :
    TwistedSection g 1 where
  val i := chartRatio g i k
  compatible i j x hi hj := by
    simpa only [chartRatio, pow_one] using
      chartForm_germ_ratio g j i x hj hi (MvPolynomial.isHomogeneous_X R k)

/-- Product of the actual native local sections adds their twisting degrees. -/
def TwistedSection.mul {g : Y ⟶ projectiveSpace R n} {d e : ℕ}
    (s : TwistedSection g d) (t : TwistedSection g e) : TwistedSection g (d + e) where
  val i := s.val i * t.val i
  compatible i j x hi hj := by
    rw [map_mul, map_mul, s.compatible i j x hi hj, t.compatible i j x hi hj, pow_add]
    ring

/-- Raising an actual compatible tuple to a power multiplies its twisting degree. -/
def TwistedSection.pow {g : Y ⟶ projectiveSpace R n} {d : ℕ}
    (s : TwistedSection g d) (e : ℕ) : TwistedSection g (d * e) where
  val i := s.val i ^ e
  compatible i j x hi hj := by
    rw [map_pow, map_pow, s.compatible i j x hi hj, mul_pow, ← pow_mul]

/-- The original overlap of two actual inverse coordinate charts. -/
def overlap (g : Y ⟶ projectiveSpace R n) (j k : Fin (n + 1)) : Y.Opens :=
  chartOpen g j ⊓ chartOpen g k

/-- Actual restriction from the first chart to the overlap. -/
def overlapLeft (g : Y ⟶ projectiveSpace R n) (j k : Fin (n + 1)) :
    Γ(Y, chartOpen g j) →+* Γ(Y, overlap g j k) :=
  (Y.presheaf.map (homOfLE inf_le_left).op).hom

/-- Actual restriction from the second chart to the overlap. -/
def overlapRight (g : Y ⟶ projectiveSpace R n) (j k : Fin (n + 1)) :
    Γ(Y, chartOpen g k) →+* Γ(Y, overlap g j k) :=
  (Y.presheaf.map (homOfLE inf_le_right).op).hom

/-- The original coordinate Xi/Xj restricted to the entire overlap. -/
def overlapRatio (g : Y ⟶ projectiveSpace R n) (j k i : Fin (n + 1)) :
    Γ(Y, overlap g j k) := overlapLeft g j k (chartRatio g j i)

/-- The actual ratio basic open on an overlap is the genuine triple intersection. -/
theorem overlapRatio_basicOpen (g : Y ⟶ projectiveSpace R n) (j k i : Fin (n + 1)) :
    Y.basicOpen (overlapRatio g j k i) = overlap g j k ⊓ chartOpen g i := by
  dsimp only [overlapRatio, overlapLeft]
  rw [Scheme.basicOpen_res, chartRatio_basicOpen]
  simp only [overlap, inf_assoc, inf_left_comm, inf_left_idem]

/-- The true first-chart restriction has the original first-chart germ. -/
theorem overlapLeft_germ (g : Y ⟶ projectiveSpace R n) (j k : Fin (n + 1))
    (t : Γ(Y, chartOpen g j)) (x : Y) (hx : x ∈ overlap g j k) :
    Y.presheaf.germ (overlap g j k) x hx (overlapLeft g j k t) =
      Y.presheaf.germ (chartOpen g j) x hx.1 t :=
  Y.presheaf.germ_res_apply (homOfLE inf_le_left) x hx t

/-- The true second-chart restriction has the original second-chart germ. -/
theorem overlapRight_germ (g : Y ⟶ projectiveSpace R n) (j k : Fin (n + 1))
    (t : Γ(Y, chartOpen g k)) (x : Y) (hx : x ∈ overlap g j k) :
    Y.presheaf.germ (overlap g j k) x hx (overlapRight g j k t) =
      Y.presheaf.germ (chartOpen g k) x hx.2 t :=
  Y.presheaf.germ_res_apply (homOfLE inf_le_right) x hx t

/-- The actual discrepancy between preliminary degree-d local extensions. -/
def overlapDifference (g : Y ⟶ projectiveSpace R n) (d : ℕ)
    (s : ∀ j : Fin (n + 1), Γ(Y, chartOpen g j)) (j k : Fin (n + 1)) :
    Γ(Y, overlap g j k) :=
  overlapLeft g j k (s j) - overlapRight g j k (s k) *
    overlapLeft g j k (chartRatio g j k) ^ d

/-- The whole actual overlap discrepancy has its literal stalk formula. -/
theorem overlapDifference_germ (g : Y ⟶ projectiveSpace R n) (d : ℕ)
    (s : ∀ j : Fin (n + 1), Γ(Y, chartOpen g j)) (j k : Fin (n + 1))
    (x : Y) (hx : x ∈ overlap g j k) :
    Y.presheaf.germ (overlap g j k) x hx (overlapDifference g d s j k) =
      Y.presheaf.germ (chartOpen g j) x hx.1 (s j) -
        Y.presheaf.germ (chartOpen g k) x hx.2 (s k) *
          Y.presheaf.germ (chartOpen g j) x hx.1 (chartRatio g j k) ^ d := by
  simp only [overlapDifference, map_sub, map_mul, map_pow, overlapLeft_germ, overlapRight_germ]

/-- Actual affine localization supplies a real coordinate-power annihilator
for every preliminary overlap discrepancy. -/
theorem exists_overlap_annihilator (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i : Fin (n + 1)) (b : Γ(Y, chartOpen g i)) (d : ℕ)
    (s : ∀ j : Fin (n + 1), Γ(Y, chartOpen g j))
    (hs : ∀ (j : Fin (n + 1)) (x : Y) (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j),
      Y.presheaf.germ (chartOpen g j) x hj (s j) =
        Y.presheaf.germ (chartOpen g i) x hi b *
          Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ d)
    (j k : Fin (n + 1)) :
    ∃ e : ℕ, overlapRatio g j k i ^ e * overlapDifference g d s j k = 0 := by
  let W := overlap g j k
  let ξ := overlapRatio g j k i
  let B := Y.basicOpen ξ
  let : Algebra Γ(Y, W) Γ(Y, B) := Scheme.algebra_section_section_basicOpen ξ
  let : IsLocalization.Away ξ Γ(Y, B) := (chartOpen_inf_isAffine g j k).isLocalization_basicOpen ξ
  have hz : algebraMap Γ(Y, W) Γ(Y, B) (overlapDifference g d s j k) = 0 := by
    apply TopCat.Presheaf.section_ext Y.sheaf B
    intro x hx
    have hxW : x ∈ W := Y.basicOpen_le ξ hx
    have hxi : x ∈ chartOpen g i := by
      have H := (overlapRatio_basicOpen g j k i).le hx
      exact H.2
    change Y.presheaf.germ B x hx
      (Y.presheaf.map (homOfLE (Y.basicOpen_le ξ)).op (overlapDifference g d s j k)) =
        Y.presheaf.germ B x hx 0
    rw [TopCat.Presheaf.germ_res_apply, map_zero, overlapDifference_germ,
      hs j x hxi hxW.1, hs k x hxi hxW.2]
    have hr := chartForm_germ_ratio g k j x hxW.2 hxW.1 (MvPolynomial.isHomogeneous_X R i)
    change Y.presheaf.germ (chartOpen g j) x hxW.1 (chartRatio g j i) =
      Y.presheaf.germ (chartOpen g k) x hxW.2 (chartRatio g k i) *
        Y.presheaf.germ (chartOpen g j) x hxW.1 (chartRatio g j k) ^ 1 at hr
    rw [pow_one] at hr
    rw [hr, mul_pow]
    ring
  have hz' : algebraMap Γ(Y, W) Γ(Y, B) (overlapDifference g d s j k) =
      algebraMap Γ(Y, W) Γ(Y, B) 0 := hz.trans (map_zero _).symm
  obtain ⟨e, he⟩ := IsLocalization.Away.exists_of_eq ξ (S := Γ(Y, B)) hz'
  exact ⟨e, by simpa only [mul_zero] using he⟩

/-- Every section on one genuine inverse affine coordinate chart extends to
an actual compatible twisted section, without a reducedness assumption. -/
theorem exists_twisted_extension (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i : Fin (n + 1)) (b : Γ(Y, chartOpen g i)) :
    ∃ (d : ℕ) (t : TwistedSection g d), t.val i = b := by
  classical
  obtain ⟨d, s, hsi, hs⟩ := exists_common_chart_extension g i b
  choose e he using fun j k : Fin (n + 1) => exists_overlap_annihilator g i b d s hs j k
  let E := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => e p.1 p.2)
  have hE (j k : Fin (n + 1)) : e j k ≤ E :=
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => e p.1 p.2)
      (Finset.mem_univ (j, k))
  let t (j : Fin (n + 1)) : Γ(Y, chartOpen g j) := s j * chartRatio g j i ^ E
  have ht (j k : Fin (n + 1)) (x : Y) (hj : x ∈ chartOpen g j) (hk : x ∈ chartOpen g k) :
      Y.presheaf.germ (chartOpen g j) x hj (t j) =
        Y.presheaf.germ (chartOpen g k) x hk (t k) *
          Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ (d + E) := by
    have ha := congrArg (Y.presheaf.germ (overlap g j k) x ⟨hj, hk⟩) (he j k)
    simp only [map_mul, map_pow, map_zero, overlapRatio, overlapLeft_germ,
      overlapDifference_germ] at ha
    have hzero : Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ E *
        (Y.presheaf.germ (chartOpen g j) x hj (s j) -
          Y.presheaf.germ (chartOpen g k) x hk (s k) *
            Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ d) = 0 := by
      calc
        _ = Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ (E - e j k) *
            (Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ (e j k) *
              (Y.presheaf.germ (chartOpen g j) x hj (s j) -
                Y.presheaf.germ (chartOpen g k) x hk (s k) *
                  Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ d)) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hE j k)]
        _ = 0 := by rw [ha, mul_zero]
    have hr := chartForm_germ_ratio g k j x hk hj (MvPolynomial.isHomogeneous_X R i)
    change Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) =
      Y.presheaf.germ (chartOpen g k) x hk (chartRatio g k i) *
        Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ 1 at hr
    rw [pow_one] at hr
    dsimp only [t]
    rw [map_mul, map_pow, map_mul, map_pow, pow_add]
    apply sub_eq_zero.mp
    calc
      _ = Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ E *
          (Y.presheaf.germ (chartOpen g j) x hj (s j) -
            Y.presheaf.germ (chartOpen g k) x hk (s k) *
              Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ d) := by
        rw [hr, mul_pow]
        ring
      _ = 0 := hzero
  refine ⟨d + E, ⟨t, ht⟩, ?_⟩
  change s i * chartRatio g i i ^ E = b
  rw [hsi, chartRatio_self, one_pow, mul_one]

/-- Raising a genuine twisted section to a later degree by an original
coordinate preserves its value on that coordinate chart. -/
def TwistedSection.raise {g : Y ⟶ projectiveSpace R n} {d : ℕ}
    (s : TwistedSection g d) (i : Fin (n + 1)) (D : ℕ) (h : d ≤ D) :
    TwistedSection g D where
  val j := s.val j * chartRatio g j i ^ (D - d)
  compatible j k x hj hk := by
    have hr := chartForm_germ_ratio g k j x hk hj (MvPolynomial.isHomogeneous_X R i)
    change Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) =
      Y.presheaf.germ (chartOpen g k) x hk (chartRatio g k i) *
        Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ 1 at hr
    rw [pow_one] at hr
    rw [map_mul, map_pow, map_mul, map_pow, s.compatible j k x hj hk, hr]
    calc
      _ = (Y.presheaf.germ (chartOpen g k) x hk (s.val k) *
          Y.presheaf.germ (chartOpen g k) x hk (chartRatio g k i) ^ (D - d)) *
            Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j k) ^ (d + (D - d)) := by
        rw [mul_pow, pow_add]
        ring
      _ = _ := by rw [Nat.add_sub_of_le h]

/-- Degree raising is the stated multiplication on the entire actual chart. -/
theorem TwistedSection.raise_val {g : Y ⟶ projectiveSpace R n} {d : ℕ}
    (s : TwistedSection g d) (i : Fin (n + 1)) (D : ℕ) (h : d ≤ D) (j : Fin (n + 1)) :
    (s.raise i D h).val j = s.val j * chartRatio g j i ^ (D - d) := rfl

/-- The actual original-chart section is retained when the twisting degree is raised. -/
theorem TwistedSection.raise_val_self {g : Y ⟶ projectiveSpace R n} {d : ℕ}
    (s : TwistedSection g d) (i : Fin (n + 1)) (D : ℕ) (h : d ≤ D) :
    (s.raise i D h).val i = s.val i := by
  rw [TwistedSection.raise_val, chartRatio_self, one_pow, mul_one]

end DeJongAlterations.Geometry.FiniteProjective

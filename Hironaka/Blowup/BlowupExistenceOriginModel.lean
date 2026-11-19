import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The model blowup: `ℂᵈ` blown up at the origin, as a complex manifold

Source: Griffiths--Harris, Chapter 4 §6; Voisin I, §3.3; Copy-4, `sec:prelim`.

Everything in the workspace that blows up a manifold assumes a blowup is *given*
(`Hironaka.BlowupSequences.IsBlowupAlong`), and
`Hironaka.BlowupExistence.exists_isBlowupAlong` -- the statement that one always exists -- is an
open target.  `Hironaka.BlowupExistenceCodimOne` settles the range in which the blowup is the
identity.  The remaining content is codimension `≥ 2`, and there the blowup is a genuinely new
manifold.  This file constructs the local model of that manifold, from scratch:

`OriginBlowup d` is the incidence variety `{(v, L) : v ∈ L, L a line through 0 in ℂᵈ}`.  It is
a *subtype*, not a quotient: the projective direction is recorded by the `Submodule` it spans,
so no quotient topology is involved anywhere.  Its `d` monomial charts are the maps
`z ↦ (z_j · gen j z, ℂ · gen j z)` with `gen j z` the vector whose `j`-th coordinate is `1` and
whose other coordinates are those of `z`.  The file supplies

* `originChart j`, a `PartialEquiv` with source the `j`-th chart domain and target `univ`;
* `originChartedSpaceCore`, hence the topology and the `ChartedSpace (ComplexModel d)` structure;
* `T2Space` -- proved directly from the charts: two points in a common chart are separated by
  the chart, and a point of `U_j \ U_l` and a point of `U_l \ U_j` are separated by
  `|z_l| < 1` and `|z'_j| < 1`, because on the overlap `z_l · z'_j = 1`;
* `SecondCountableTopology` -- the `d` chart domains are a finite open cover by copies of `ℂᵈ`;
* `IsComplexManifold d (OriginBlowup d)` -- the transitions are
  `z ↦ (z_j z_l, (gen j z)_i / z_l)`, holomorphic where `z_l ≠ 0`.

`originProj : OriginBlowup d → ComplexModel d` is the projection `(v, L) ↦ v`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.BlowupExistenceOriginModel



noncomputable section

variable {d : ℕ}

/-! ### The normalized generator of the `j`-th chart -/

/-- The vector whose `j`-th coordinate is `1` and whose `i`-th coordinate is `zᵢ` otherwise.
As `j` ranges over `Fin d` and `z` over `ℂᵈ`, `ℂ · gen j z` runs through every line. -/
def gen (j : Fin d) (z : ComplexModel d) : ComplexModel d :=
  WithLp.toLp 2 fun i => if i = j then 1 else z i

@[simp] theorem gen_apply (j i : Fin d) (z : ComplexModel d) :
    gen j z i = if i = j then 1 else z i := rfl

@[simp] theorem gen_self (j : Fin d) (z : ComplexModel d) : gen j z j = 1 := by simp

theorem gen_ne_zero (j : Fin d) (z : ComplexModel d) : gen j z ≠ 0 := by
  intro h
  have : gen j z j = 0 := by rw [h]; rfl
  rw [gen_self] at this
  exact one_ne_zero this

theorem exists_coord_ne_zero {w : ComplexModel d} (hw : w ≠ 0) : ∃ i, w i ≠ 0 := by
  by_contra h
  refine hw ?_
  ext i
  simpa using not_not.mp (fun hi => h ⟨i, hi⟩)

/-! ### The incidence variety -/

/-- A point of the blowup of `ℂᵈ` at the origin: a point `v` together with a line `L` through
the origin containing it. -/
structure OriginBlowup (d : ℕ) where
  /-- The image point in `ℂᵈ`. -/
  point : ComplexModel d
  /-- The line through the origin recording the direction. -/
  line : Submodule ℂ (ComplexModel d)
  /-- `line` really is a line. -/
  isLine : ∃ w : ComplexModel d, w ≠ 0 ∧ line = Submodule.span ℂ {w}
  /-- The point lies on the line. -/
  point_mem : point ∈ line

namespace OriginBlowup

@[ext] theorem ext {p q : OriginBlowup d} (hp : p.point = q.point) (hl : p.line = q.line) :
    p = q := by
  cases p; cases q; simp_all

end OriginBlowup

/-- The projection of the blowup to `ℂᵈ`. -/
def originProj (p : OriginBlowup d) : ComplexModel d := p.point

/-- Two nonzero vectors spanning the same line are proportional. -/
theorem exists_smul_eq_of_span_eq {v w : ComplexModel d} (hv : v ≠ 0)
    (h : Submodule.span ℂ ({v} : Set (ComplexModel d)) = Submodule.span ℂ {w}) :
    ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  have hv' : v ∈ Submodule.span ℂ ({w} : Set (ComplexModel d)) := by
    rw [← h]; exact Submodule.mem_span_singleton_self v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨c, by rintro rfl; simp at hc; exact hv hc.symm, hc.symm⟩

/-! ### The chart maps -/

/-- The `j`-th chart of the model blowup, as a map into it. -/
def originMk (j : Fin d) (z : ComplexModel d) : OriginBlowup d where
  point := z j • gen j z
  line := Submodule.span ℂ {gen j z}
  isLine := ⟨gen j z, gen_ne_zero j z, rfl⟩
  point_mem := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

@[simp] theorem originMk_line (j : Fin d) (z : ComplexModel d) :
    (originMk j z).line = Submodule.span ℂ {gen j z} := rfl

@[simp] theorem originMk_point (j : Fin d) (z : ComplexModel d) :
    (originMk j z).point = z j • gen j z := rfl

/-- The `j`-th chart domain: the points whose line is not contained in `{wⱼ = 0}`. -/
def originSource (j : Fin d) : Set (OriginBlowup d) :=
  {p | ∃ w : ComplexModel d, w ≠ 0 ∧ p.line = Submodule.span ℂ {w} ∧ w j ≠ 0}

/-- Every generator of the line of a point of the `j`-th chart domain has nonzero `j`-th
coordinate. -/
theorem coord_ne_zero_of_mem_originSource {j : Fin d} {p : OriginBlowup d}
    (hp : p ∈ originSource j) {w : ComplexModel d}
    (hline : p.line = Submodule.span ℂ {w}) : w j ≠ 0 := by
  obtain ⟨v, hv, hvline, hvj⟩ := hp
  obtain ⟨c, hc, hcv⟩ := exists_smul_eq_of_span_eq hv (hvline.symm.trans hline)
  intro h
  apply hvj
  rw [hcv]
  change c * w j = 0
  rw [h, mul_zero]

/-! ### The chart coordinate map -/

/-- A chosen generator of the line of a point. -/
def originRep (p : OriginBlowup d) : ComplexModel d := Classical.choose p.isLine

theorem originRep_ne_zero (p : OriginBlowup d) : originRep p ≠ 0 :=
  (Classical.choose_spec p.isLine).1

theorem line_eq_span_originRep (p : OriginBlowup d) :
    p.line = Submodule.span ℂ {originRep p} := (Classical.choose_spec p.isLine).2

/-- The `j`-th chart coordinates: the `j`-th one is the value of the point there, the others
are the ratios `wᵢ / wⱼ` of any generator `w` of the line. -/
def originCoord (j : Fin d) (p : OriginBlowup d) : ComplexModel d :=
  WithLp.toLp 2 fun i => if i = j then p.point j else originRep p i / originRep p j

/-- The chart coordinates do not depend on the chosen generator. -/
theorem originCoord_apply {j : Fin d} {p : OriginBlowup d} {w : ComplexModel d}
    (hline : p.line = Submodule.span ℂ {w}) (i : Fin d) :
    originCoord j p i = if i = j then p.point j else w i / w j := by
  obtain ⟨c, hc, hcw⟩ :=
    exists_smul_eq_of_span_eq (originRep_ne_zero p)
      ((line_eq_span_originRep p).symm.trans hline)
  have hi : originRep p i = c * w i := by rw [hcw]; rfl
  have hj : originRep p j = c * w j := by rw [hcw]; rfl
  show (if i = j then p.point j else originRep p i / originRep p j) = _
  rw [hi, hj]
  split_ifs with h
  · rfl
  · exact mul_div_mul_left _ _ hc

theorem originMk_mem_originSource (j : Fin d) (z : ComplexModel d) :
    originMk j z ∈ originSource j :=
  ⟨gen j z, gen_ne_zero j z, rfl, by rw [gen_self]; exact one_ne_zero⟩

theorem originCoord_originMk (j : Fin d) (z : ComplexModel d) :
    originCoord j (originMk j z) = z := by
  ext i
  rw [originCoord_apply (w := gen j z) rfl i]
  split_ifs with h
  · subst h
    change (z i • gen i z) i = z i
    simp
  · simp [h]

/-- On its chart domain, `originMk j` inverts `originCoord j`. -/
theorem originMk_originCoord {j : Fin d} {p : OriginBlowup d} (hp : p ∈ originSource j) :
    originMk j (originCoord j p) = p := by
  obtain ⟨w, hw, hline, hwj⟩ := hp
  have hgen : gen j (originCoord j p) = (w j)⁻¹ • w := by
    ext i
    rw [gen_apply]
    change _ = (w j)⁻¹ * w i
    split_ifs with h
    · subst h; field_simp
    · rw [originCoord_apply hline i, if_neg h]
      field_simp
  have hspan : Submodule.span ℂ ({gen j (originCoord j p)} : Set (ComplexModel d)) = p.line := by
    rw [hgen, hline]
    exact Submodule.span_singleton_smul_eq (by simpa using inv_ne_zero hwj) _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline ▸ p.point_mem)
  refine OriginBlowup.ext ?_ hspan
  have hpj : p.point j = c * w j := by rw [← hc]; rfl
  change originCoord j p j • gen j (originCoord j p) = p.point
  rw [originCoord_apply hline j, if_pos rfl, hgen, hpj, smul_smul, ← hc]
  congr 1
  field_simp

/-- The `j`-th chart of the model blowup. -/
def originChart (j : Fin d) : PartialEquiv (OriginBlowup d) (ComplexModel d) where
  toFun := originCoord j
  invFun := originMk j
  source := originSource j
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := originMk_mem_originSource j z
  left_inv' _ hp := originMk_originCoord hp
  right_inv' z _ := originCoord_originMk j z

@[simp] theorem originChart_source (j : Fin d) :
    (originChart j).source = originSource j := rfl

@[simp] theorem originChart_target (j : Fin d) : (originChart j).target = univ := rfl

@[simp] theorem originChart_apply (j : Fin d) (p : OriginBlowup d) :
    originChart j p = originCoord j p := rfl

@[simp] theorem originChart_symm_apply (j : Fin d) (z : ComplexModel d) :
    (originChart j).symm z = originMk j z := rfl

/-- Every point lies in one of the `d` chart domains. -/
theorem exists_mem_originSource (p : OriginBlowup d) : ∃ j, p ∈ originSource j := by
  obtain ⟨w, hw, hline⟩ := p.isLine
  obtain ⟨j, hj⟩ := exists_coord_ne_zero hw
  exact ⟨j, w, hw, hline, hj⟩

/-- The `j`-th chart domain, seen in the `j`-th coordinates, meets the `l`-th one exactly where
`(gen j z) l ≠ 0`. -/
theorem originMk_mem_originSource_iff (j l : Fin d) (z : ComplexModel d) :
    originMk j z ∈ originSource l ↔ gen j z l ≠ 0 := by
  constructor
  · rintro ⟨w, hw, hline, hwl⟩
    intro h
    exact hwl (by
      obtain ⟨c, -, hcw⟩ := exists_smul_eq_of_span_eq hw (hline.symm.trans rfl)
      have : w l = c * gen j z l := by rw [hcw]; rfl
      rw [this, h, mul_zero])
  · intro h
    exact ⟨gen j z, gen_ne_zero j z, rfl, h⟩

/-! ### The charted space structure -/

/-- The overlap of the `j`-th and `l`-th charts, in `j`-coordinates. -/
def overlapSet (j l : Fin d) : Set (ComplexModel d) := {z | gen j z l ≠ 0}

theorem contDiff_coord (j : Fin d) : ContDiff ℂ ∞ fun z : ComplexModel d => z j :=
  (EuclideanSpace.proj j : ComplexModel d →L[ℂ] ℂ).contDiff

theorem contDiff_gen_coord (j i : Fin d) : ContDiff ℂ ∞ fun z : ComplexModel d => gen j z i := by
  simp only [gen_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_coord i

theorem isOpen_overlapSet (j l : Fin d) : IsOpen (overlapSet (d := d) j l) :=
  isOpen_ne.preimage (contDiff_gen_coord j l).continuous

theorem trans_source_eq (j l : Fin d) :
    ((originChart j).symm.trans (originChart l)).source = overlapSet (d := d) j l := by
  ext z
  simp [PartialEquiv.trans_source, overlapSet, originMk_mem_originSource_iff]

/-- The transition between the `j`-th and `l`-th charts. -/
theorem originCoord_originMk_apply (j l : Fin d) (z : ComplexModel d) (i : Fin d) :
    originCoord l (originMk j z) i =
      if i = l then z j * gen j z l else gen j z i / gen j z l := by
  rw [originCoord_apply (w := gen j z) rfl i]
  split_ifs with h
  · subst h
    change (z j • gen j z) i = z j * gen j z i
    rfl
  · rfl

theorem contDiffOn_originTrans (j l : Fin d) :
    ContDiffOn ℂ ∞ (fun z : ComplexModel d => originCoord l (originMk j z))
      (overlapSet (d := d) j l) := by
  refine (contDiffOn_piLp 2).2 fun i => ?_
  have h : ∀ z : ComplexModel d,
      originCoord l (originMk j z) i =
        if i = l then z j * gen j z l else gen j z i / gen j z l :=
    fun z => originCoord_originMk_apply j l z i
  simp only [h]
  split_ifs
  · exact ((contDiff_coord j).mul (contDiff_gen_coord j l)).contDiffOn
  · exact (contDiff_gen_coord j i).contDiffOn.div (contDiff_gen_coord j l).contDiffOn
      fun z hz => hz

/-- A chosen chart index for each point. -/
def originIndex (p : OriginBlowup d) : Fin d := Classical.choose (exists_mem_originSource p)

theorem mem_originSource_originIndex (p : OriginBlowup d) : p ∈ originSource (originIndex p) :=
  Classical.choose_spec (exists_mem_originSource p)

/-- The model blowup as a charted space without topology. -/
def originCore (d : ℕ) : ChartedSpaceCore (ComplexModel d) (OriginBlowup d) where
  atlas := Set.range originChart
  chartAt p := originChart (originIndex p)
  mem_chart_source p := mem_originSource_originIndex p
  chart_mem_atlas p := ⟨originIndex p, rfl⟩
  open_source := by
    rintro e e' ⟨j, rfl⟩ ⟨l, rfl⟩
    rw [trans_source_eq]
    exact isOpen_overlapSet j l
  continuousOn_toFun := by
    rintro e e' ⟨j, rfl⟩ ⟨l, rfl⟩
    rw [trans_source_eq]
    exact (contDiffOn_originTrans j l).continuousOn

instance : TopologicalSpace (OriginBlowup d) := (originCore d).toTopologicalSpace

instance : ChartedSpace (ComplexModel d) (OriginBlowup d) := (originCore d).toChartedSpace

/-- The `j`-th chart as an open partial homeomorphism. -/
def originHomeomorph (j : Fin d) : OpenPartialHomeomorph (OriginBlowup d) (ComplexModel d) :=
  (originCore d).openPartialHomeomorph (originChart j) ⟨j, rfl⟩

@[simp] theorem originHomeomorph_source (j : Fin d) :
    (originHomeomorph (d := d) j).source = originSource j := rfl

@[simp] theorem originHomeomorph_apply (j : Fin d) (p : OriginBlowup d) :
    originHomeomorph j p = originCoord j p := rfl

theorem isOpen_originSource (j : Fin d) : IsOpen (originSource (d := d) j) :=
  (originHomeomorph (d := d) j).open_source

theorem continuousOn_originCoord (j : Fin d) :
    ContinuousOn (originCoord (d := d) j) (originSource j) :=
  (originHomeomorph (d := d) j).continuousOn

/-! ### Hausdorff -/

theorem isOpen_chartPreimage {j : Fin d} {A : Set (ComplexModel d)} (hA : IsOpen A) :
    IsOpen (originSource (d := d) j ∩ originCoord j ⁻¹' A) :=
  (originHomeomorph (d := d) j).isOpen_inter_preimage hA

/-- Two distinct points lying in a common chart are separated by that chart. -/
theorem exists_separating_of_common {p q : OriginBlowup d} (hpq : p ≠ q) {j : Fin d}
    (hp : p ∈ originSource j) (hq : q ∈ originSource j) :
    ∃ u v : Set (OriginBlowup d), IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  have hne : originCoord j p ≠ originCoord j q := by
    intro h
    exact hpq (((originMk_originCoord hp).symm.trans (by rw [h])).trans
      (originMk_originCoord hq))
  obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ := t2_separation hne
  refine ⟨originSource j ∩ originCoord j ⁻¹' A, originSource j ∩ originCoord j ⁻¹' B,
    isOpen_chartPreimage hA, isOpen_chartPreimage hB, ⟨hp, hpA⟩, ⟨hq, hqB⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro r ⟨-, hrA⟩ ⟨-, hrB⟩
  exact (Set.disjoint_left.mp hAB) hrA hrB

/-- A point of `U_j \ U_l` and a point of `U_l \ U_j` are separated, because on the overlap
the two coordinates `z_l` and `z'_j` are reciprocal. -/
theorem exists_separating_of_split {p q : OriginBlowup d} {j l : Fin d}
    (hp : p ∈ originSource j) (hpl : p ∉ originSource l)
    (hq : q ∈ originSource l) (hqj : q ∉ originSource j) :
    ∃ u v : Set (OriginBlowup d), IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  have hjl : j ≠ l := by rintro rfl; exact hpl hp
  have hball : ∀ i : Fin d, IsOpen {z : ComplexModel d | ‖z i‖ < 1} :=
    fun i => isOpen_lt ((contDiff_coord i).continuous.norm) continuous_const
  -- the `l`-th coordinate of `p` in the `j`-th chart vanishes, and symmetrically
  have hzero : ∀ {r : OriginBlowup d} {a b : Fin d}, a ≠ b → r ∈ originSource a →
      r ∉ originSource b → originCoord a r b = 0 := by
    intro r a b hab hra hrb
    obtain ⟨w, hw, hline, hwa⟩ := hra
    have hwb : w b = 0 := by
      by_contra h
      exact hrb ⟨w, hw, hline, h⟩
    rw [originCoord_apply hline b, if_neg (Ne.symm hab), hwb, zero_div]
  refine ⟨originSource j ∩ originCoord j ⁻¹' {z | ‖z l‖ < 1},
    originSource l ∩ originCoord l ⁻¹' {z | ‖z j‖ < 1},
    isOpen_chartPreimage (hball l), isOpen_chartPreimage (hball j),
    ⟨hp, by simp [hzero hjl hp hpl]⟩, ⟨hq, by simp [hzero (Ne.symm hjl) hq hqj]⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro r ⟨hrj, hrA⟩ ⟨hrl, hrB⟩
  obtain ⟨w, hw, hline, hwj⟩ := hrj
  have hwl : w l ≠ 0 := coord_ne_zero_of_mem_originSource hrl hline
  have h1 : originCoord j r l = w l / w j := by
    rw [originCoord_apply hline l, if_neg (Ne.symm hjl)]
  have h2 : originCoord l r j = w j / w l := by
    rw [originCoord_apply hline j, if_neg hjl]
  have hprod : ‖originCoord j r l‖ * ‖originCoord l r j‖ = 1 := by
    rw [h1, h2, ← norm_mul]
    rw [div_mul_div_comm, mul_comm (w l) (w j), div_self (mul_ne_zero hwj hwl)]
    simp
  have hlt : ‖originCoord j r l‖ * ‖originCoord l r j‖ < 1 := by
    calc ‖originCoord j r l‖ * ‖originCoord l r j‖
        ≤ 1 * ‖originCoord l r j‖ := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hrA) (norm_nonneg _)
      _ < 1 := by simpa using hrB
  exact absurd hprod (ne_of_lt hlt)

instance : T2Space (OriginBlowup d) := by
  refine ⟨fun {p q} hpq => ?_⟩
  obtain ⟨j, hj⟩ := exists_mem_originSource p
  obtain ⟨l, hl⟩ := exists_mem_originSource q
  by_cases hq : q ∈ originSource j
  · exact exists_separating_of_common hpq hj hq
  · by_cases hp : p ∈ originSource l
    · exact exists_separating_of_common hpq hp hl
    · exact exists_separating_of_split hj hp hl hq

/-! ### Second countability -/

theorem iUnion_originSource : (⋃ j : Fin d, originSource (d := d) j) = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_originSource p

instance : SecondCountableTopology (OriginBlowup d) := by
  have : ∀ j : Fin d, SecondCountableTopology (originSource (d := d) j) := fun j =>
    (originHomeomorph (d := d) j).secondCountableTopology_source
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun j : Fin d => originSource j)
    isOpen_originSource iUnion_originSource

/-! ### The complex structure -/

theorem exists_eq_originHomeomorph {e : OpenPartialHomeomorph (OriginBlowup d) (ComplexModel d)}
    (he : e ∈ atlas (ComplexModel d) (OriginBlowup d)) : ∃ j, e = originHomeomorph j := by
  have he' : e ∈ ⋃ (e₀ : PartialEquiv (OriginBlowup d) (ComplexModel d))
      (he₀ : e₀ ∈ (originCore d).atlas), {(originCore d).openPartialHomeomorph e₀ he₀} := he
  rw [mem_iUnion] at he'
  obtain ⟨e₀, he'⟩ := he'
  rw [mem_iUnion] at he'
  obtain ⟨he₀, he'⟩ := he'
  rw [mem_singleton_iff] at he'
  obtain ⟨j, rfl⟩ := he₀
  exact ⟨j, he'⟩

instance : IsManifold 𝓘(ℂ, ComplexModel d) ∞ (OriginBlowup d) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨j, rfl⟩ := exists_eq_originHomeomorph he
  obtain ⟨l, rfl⟩ := exists_eq_originHomeomorph he'
  have hsrc : (originHomeomorph (d := d) j).target ∩
      ((originHomeomorph (d := d) j).symm ⁻¹' (originHomeomorph (d := d) l).source)
      = overlapSet (d := d) j l := trans_source_eq j l
  simp only [mfld_simps]
  rw [hsrc]
  exact (contDiffOn_originTrans j l).congr fun z _ => rfl

instance : IsComplexManifold d (OriginBlowup d) where

/-! ### The projection to `ℂᵈ` -/

theorem originHomeomorph_mem_atlas (j : Fin d) :
    originHomeomorph (d := d) j ∈ atlas (ComplexModel d) (OriginBlowup d) := by
  show originHomeomorph j ∈ ⋃ (e₀ : PartialEquiv (OriginBlowup d) (ComplexModel d))
    (he₀ : e₀ ∈ (originCore d).atlas), {(originCore d).openPartialHomeomorph e₀ he₀}
  rw [mem_iUnion]
  exact ⟨originChart j, by rw [mem_iUnion]; exact ⟨⟨j, rfl⟩, rfl⟩⟩

theorem contDiff_gen (j : Fin d) : ContDiff ℂ ∞ (gen (d := d) j) :=
  (contDiff_piLp 2).2 fun i => contDiff_gen_coord j i

theorem contMDiffOn_originProj (j : Fin d) :
    ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ originProj (originSource j) := by
  have hchart : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (originHomeomorph (d := d) j) (originSource j) :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (n := ∞) (originHomeomorph_mem_atlas j))
  have hout : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (fun z : ComplexModel d => z j • gen j z) :=
    (((contDiff_coord (d := d) j).smul (contDiff_gen j))).contMDiff
  refine (hout.comp_contMDiffOn hchart).congr fun p hp => ?_
  change originProj p = (originMk j (originCoord j p)).point
  rw [originMk_originCoord hp]
  rfl

theorem contMDiff_originProj :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (originProj (d := d)) := fun p =>
  (contMDiffOn_originProj (originIndex p)).contMDiffAt
    ((isOpen_originSource _).mem_nhds (mem_originSource_originIndex p))

@[simp] theorem originProj_originMk (j : Fin d) (z : ComplexModel d) :
    originProj (originMk j z) = z j • gen j z := rfl

end

end Hironaka.BlowupExistenceOriginModel

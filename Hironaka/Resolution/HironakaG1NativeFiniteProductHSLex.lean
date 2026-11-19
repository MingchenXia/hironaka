import Hironaka.Resolution.HironakaG1NativeFiniteProductState
import Mathlib.Order.PiLex

/-! The TRUE toLex order embedding of actual finite free-product HS profiles.
Blueprint FIRST: hironaka-g1-native-finite-product-hs-lex.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaG1NativeFiniteProductHSLex
noncomputable section
open HironakaG11PresLineState HironakaG1NativeFiniteProductState

/-- The SAME first differing coefficient witnesses the actual line-HS comparison. -/
theorem lineHS_lex_strictMono :
    StrictMono (fun H : Lex (ℕ→ℕ)=>toLex (lineHS (ofLex H))) := by
  rintro A B ⟨i,hbefore,hi⟩
  refine ⟨i,?_,?_⟩
  · intro j hj
    change (∑ k∈Finset.range (j+1),ofLex A k)=
      ∑ k∈Finset.range (j+1),ofLex B k
    apply Finset.sum_congr rfl
    intro k hk
    exact hbefore k (by have := Finset.mem_range.mp hk; omega)
  · change (∑ k∈Finset.range (i+1),ofLex A k)<
      ∑ k∈Finset.range (i+1),ofLex B k
    have hsum : (∑ k∈Finset.range i,ofLex A k)=∑ k∈Finset.range i,ofLex B k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hbefore k (Finset.mem_range.mp hk)
    rw [Finset.sum_range_succ,Finset.sum_range_succ,hsum]
    exact Nat.add_lt_add_left hi _

/-- Exact LEX order, not pointwise order reflection. -/
theorem finiteProductHS_lex_strictMono (r : ℕ) :
    StrictMono (fun H : Lex (ℕ→ℕ)=>toLex (finiteProductHS r (ofLex H))) := by
  induction r with
  | zero=>exact strictMono_id
  | succ r ih=>exact lineHS_lex_strictMono.comp ih

/-- The actual profile order embedding consumed by native HS maximum schedules. -/
def finiteProductHSLexEmbedding (r : ℕ) : Lex (ℕ→ℕ) ↪o Lex (ℕ→ℕ) :=
  OrderEmbedding.ofStrictMono _ (finiteProductHS_lex_strictMono r)

theorem finiteProductHS_lex_lt_iff (r : ℕ) (A B : ℕ→ℕ) :
    toLex (finiteProductHS r A)<toLex (finiteProductHS r B) ↔ toLex A<toLex B :=
  (finiteProductHS_lex_strictMono r).lt_iff_lt

theorem finiteProductHS_lex_le_iff (r : ℕ) (A B : ℕ→ℕ) :
    toLex (finiteProductHS r A)≤toLex (finiteProductHS r B) ↔ toLex A≤toLex B :=
  (finiteProductHS_lex_strictMono r).le_iff_le

theorem finiteProductHS_eq_iff (r : ℕ) (A B : ℕ→ℕ) :
    finiteProductHS r A=finiteProductHS r B ↔ A=B :=
  (finiteProductHS_injective r).eq_iff

end
end Hironaka.HironakaG1NativeFiniteProductHSLex

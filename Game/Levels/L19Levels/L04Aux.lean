import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.List.Range
import Mathlib.Data.List.Intervals
import Mathlib.Tactic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Fold
import Mathlib.Data.Multiset.Count
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic
import Mathlib.Data.List.Range
import Mathlib.Data.List.Range
import Mathlib.Data.List.Intervals

set_option tactic.hygienic true

section Meta

syntax:min term atomic(" #" ws) term:min : term
syntax:min term atomic(" ##" ws) term:min : term

macro_rules
  | `($f $args* # $a) =>
    if a.raw.isMissing then
      `($f $args*)
    else
      `($f $args* $a)
  | `($f # $a) =>
    if a.raw.isMissing then
      `($f)
    else
      `($f $a)

macro_rules
  | `($f $args* ## $a) =>
    if a.raw.isMissing then
      `($f $args*)
    else
      `($f $args* $a)
  | `($f ## $a) =>
    if a.raw.isMissing then
      `($f)
    else
      `($f $a)

macro "nm " args:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| rename_i $args*)

end Meta

section Logic

theorem epsilon_eq_of_exiu {α : Type*} [ha : Nonempty α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∃! x, p x) : Classical.epsilon p = x := by
  have hp : p = λ y => x = y
  · ext y; obtain ⟨z, h₂, h₃⟩ := h₂
    constructor <;> intro h₄
    · rw [h₃ _ h₁, h₃ _ h₄]
    · rwa [←h₄]
  have h₃ := Classical.epsilon_spec h₂
  dsimp at h₃; subst hp; simp at h₃; exact h₃.symm

theorem epsilon_eq_of {α : Type*} [ha : Nonempty α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∀ y, p y → y = x) : Classical.epsilon p = x := by
  apply epsilon_eq_of_exiu h₁; use x

@[simp]
theorem epsilon_eq_left {α : Type*} {x : α} [ha : Nonempty α] :
Classical.epsilon (λ y => y = x) = x := by
  apply epsilon_eq_of <;> simp

@[simp]
theorem epsilon_eq_right {α : Type*} {x : α} [ha : Nonempty α] :
Classical.epsilon (λ y => x = y) = x := by
  apply epsilon_eq_of <;> simp

theorem ne_symm' {α : Type*} {a b : α} (h : ¬(a = b)) : ¬(b = a) := by tauto
theorem iff_iff_not' {P Q : Prop} : (P ↔ Q) ↔ (¬P ↔ ¬Q) := by tauto
theorem not_and_iff_or {P Q} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by tauto
theorem and_of {P Q : Prop} (h₁ : P) (h₂ : P → Q) : P ∧ Q := by tauto

@[simp]
theorem forall_ne_iff_not {α : Type*} {p : α → Prop} {x : α} : (∀ y, p y → y ≠ x) ↔ ¬p x := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    apply a
    on_goal 2 => rfl
    · simp_all only
  · intro a y a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    subst a_2
    simp_all only

@[simp]
theorem forall_ne_iff_not' {α : Type*} {p : α → Prop} {x : α} : (∀ y, p y → x ≠ y) ↔ ¬p x := by
  convert forall_ne_iff_not using 2; tauto

end Logic

namespace Function

attribute [simp] comp_def

end Function

namespace Nat

noncomputable
def find! (p : ℕ → Prop) : ℕ :=
  haveI := Classical.propDecidable
  if h : ∃ n, p n ∧ ∀ k < n, ¬p k then h.choose else 0

theorem find!_eq {p} :
haveI := Classical.propDecidable
find! p = if h : ∃ n, p n then Nat.find h else 0 := by
  classical
  unfold find!
  symm
  by_cases h₁ : ∃ n, p n
  · have h₂ : ∃ n, p n ∧ ∀ k < n, ¬p k :=
      by
        use Nat.find h₁
        rw [←Nat.find_eq_iff h₁]
    simp [h₁, h₂]
    generalize_proofs
    rw [Nat.find_eq_iff h₁]
    exact h₂.choose_spec
  split_ifs with h₂
  · simp at h₁
    obtain ⟨n, h₂⟩ := h₂
    cases h₁ n h₂.1
  rfl

theorem find!_eq_zero_of {p : ℕ → Prop} (h : ∀ n, ¬p n) : find! p = 0 := by
  rw [find!_eq]
  split_ifs with h₁
  · contrapose! h
    exact h₁
  rfl

theorem find!_eq_iff {p : ℕ → Prop} {n} : by classical exact (
find! p = n ↔ ite (∃ n, p n) (p n ∧ ∀ k < n, ¬p k) (n = 0)) := by
  split_ifs with h₁
  · rw [find!_eq]; simp [h₁, Nat.find_eq_iff]
  simp at h₁
  rw [find!_eq_zero_of h₁, eq_comm]

theorem find!_spec' {p : ℕ → Prop} (h : ∃ n, p n) : p (find! p) ∧
∀ k, p k → find! p ≤ k := by
  classical
  simp [find!_eq, h]
  use Nat.find_spec h
  intro k hk
  use k

theorem find!_spec {p : ℕ → Prop} (h : ∃ n, p n) : p (find! p) := by
  exact (find!_spec' h).1

theorem find!_min {p : ℕ → Prop} {n} (h : n < find! p) : ¬p n := by
  classical
  rw [find!_eq] at h
  split_ifs at h with h₁
  · exact Nat.find_min h₁ h
  simp at h

end Nat

namespace Real

theorem abs_sub_lt_of_lt_lt_half {a b c d : ℝ}
(h₁ : |a - c| < d / 2) (h₂ : |b - c| < d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

end Real

namespace Prod

variable {α β : Type*}
variable {a b c : α × β}
variable {x x₁ x₂ x₃ : α}
variable {y y₁ y₂ y₃ : β}

theorem fst_eq_of_eq_mk (h : a = (x, y)) : x = a.1 :=
  congrArg (·.1) h |>.symm

theorem snd_eq_of_eq_mk (h : a = (x, y)) : y = a.2 :=
  congrArg (·.2) h |>.symm

end Prod

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

theorem getElem!_eq_getElem [ha : Inhabited α] {i} (h : i < xs.length) : xs[i]! = xs[i] :=
  getElem!_pos xs i h

theorem min?_eq_some_iff₁ {ha : LinearOrder α} {x} :
xs.min? = some x ↔ x ∈ xs ∧ ∀ y ∈ xs, x ≤ y := by
  induction xs generalizing x; simp; clear! xs; nm z xs ih
  simp; cases h : xs.min?; aesop; nm m; dsimp; simp [ih] at h
  rcases h with ⟨h₁, h₂⟩; constructor
  · rintro rfl; simp; constructor
    · rw [or_iff_not_imp_left]; intro h₃
      simp at h₃; rwa [min_eq_right_of_lt h₃]
    · intro b hb; specialize h₂ b hb; simp [h₂]
  rintro ⟨rfl | h₃, h₄, h₅⟩
  · simp; exact h₅ _ h₁
  · have h₆ := h₂ _ h₃; have h₇ := h₆.trans h₄
    rw [min_eq_right h₇]; have h₈ := h₅ _ h₁
    exact le_antisymm h₆ h₈

theorem eq_of_getElem_and_nodup {i j : ℕ} {hi hj}
(h₁ : xs[i]'hi = xs[j]'hj) (h₂ : xs.Nodup) : i = j := by
  rwa [←h₂.getElem_inj_iff]

theorem sum_map_eq_sum_getElem_finset_range [hb : Ring β] {f : α → β} :
(xs.map f).sum = ∑ i ∈ Finset.range xs.length, if h : i < xs.length then f xs[i] else 0 := by
  induction xs using List.reverseRecOn <;> simp
  clear! xs; nm xs x ih
  rw [ih]; clear ih
  simp [Finset.range_add_one]
  rw [add_comm (a := f x)]
  congr 1
  apply Finset.sum_congr rfl
  intro i h₁
  simp at h₁
  simp [h₁]
  omega

@[simp]
theorem take_length_add {n} : xs.take (xs.length + n) = xs := by
  simp [take_add]

theorem take_take_append {k} (h : k ≤ xs.length) :
(xs.take k ++ ys).take k = xs.take k := by
  induction k generalizing xs ys
  · simp
  nm k ih
  cases xs
  · simp at h
  nm x xs
  simp
  simp at h
  exact ih h

attribute [simp] take_prefix

theorem sum_take_le_of_nonneg [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
{k} (h₁ : ∀ x ∈ xs, 0 ≤ x) : (xs.take k).sum ≤ xs.sum := by
  wlog h₂ : k ≤ xs.length with ih
  · push_neg at h₂
    specialize @ih α xs _ _ _ xs.length h₁ (by rfl)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le # le_of_lt h₂
    simp
  nm x y; clear! x y
  choose ys h₃ using show take k xs <+: xs by simp
  rw [←h₃, take_take_append h₂]
  simp
  apply List.sum_nonneg
  intro y hy
  rw [←h₃] at h₁
  apply h₁
  simp [hy]

theorem sum_nonpos [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
(h : ∀ x ∈ xs, x ≤ 0) : xs.sum ≤ 0 := by
  induction xs
  · simp
  clear! xs; nm x xs ih
  simp
  specialize ih # by grind
  specialize h x (by simp)
  exact add_nonpos h ih

@[simp]
theorem sum_map_neg [ha : Ring α] : (xs.map (-·)).sum = -xs.sum := by
  induction xs; simp; grind

theorem le_sum_take_of_nonpos [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
{k} (h₁ : ∀ x ∈ xs, x ≤ 0) : xs.sum ≤ (xs.take k).sum := by
  generalize hy : xs.map (-·) = ys
  replace h₁ : ∀ y ∈ ys, 0 ≤ y; grind
  replace h₁ := sum_take_le_of_nonneg h₁ (k := k)
  simp [←hy] at h₁
  rw [le_neg] at h₁
  apply h₁.trans
  rw [←map_take, sum_map_neg]
  simp

theorem sum_map_eq_sum_toFinset [ha : DecidableEq α] [hb : Ring β] {f : α → β}
(h : xs.Nodup) : (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  rw [List.sum_toFinset _ h]

theorem nodup_take {n} (h : xs.Nodup) : (xs.take n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp
  nm n
  simp
  split_ands
  · contrapose! h₁
    exact mem_of_mem_take h₁
  exact ih h₂

theorem nodup_drop {n} (h : xs.Nodup) : (xs.drop n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp [h₁, h₂]
  nm n
  simp
  exact ih h₂

end List

section Order

theorem pos_of_abs_lt {α : Type*} {a b : α}
[ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
(h : |a| < b) : 0 < b := lt_of_le_of_lt (abs_nonneg _) h

theorem mul_lt_mul_iff_right₀.{u_1} : ∀ {α : Type u_1} [inst : Mul α]
[inst_1 : Zero α] [inst_2 : Preorder α]
  {a b c : α} [PosMulStrictMono α] [PosMulReflectLT α], 0 < a → (a * b < a * c ↔ b < c) :=
fun {α} [Mul α] [Zero α] [Preorder α] {a b c} [PosMulStrictMono α] [PosMulReflectLT α] a0 ↦
  rel_iff_cov { x // 0 < x } α (fun x y ↦ ↑x * y) (fun x1 x2 ↦ x1 < x2) ⟨a, a0⟩

section

variable {α : Type*} [LinearOrder α] [NormedField α] [IsStrictOrderedRing α]

theorem abs_sub_lt_trans {a c e : α} (b : α)
(h : |a - b| + |b - c| < e) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans {a c e : α} (b : α)
(h : |a - b| + |b - c| ≤ e) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_lt_trans_half {a c e : α} (b : α)
(h₁ : |a - b| < e / 2) (h₂ : |b - c| < e / 2) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans_half {a c e : α} (b : α)
(h₁ : |a - b| ≤ e / 2) (h₂ : |b - c| ≤ e / 2) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

end

theorem abs_sub_lt_iff' {x y z : ℝ} : |x - y| < z ↔ y - z < x ∧ x < y + z := by
  rw [abs_sub_lt_iff]; constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem bddBelow_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, x ≤ f i) : BddBelow (Set.range f) := by
  use x; simpa [lowerBounds]

theorem bddAbove_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, f i ≤ x) : BddAbove (Set.range f) := by
  use x; simpa [upperBounds]

theorem bddBelow_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddBelow (Set.range f) ↔ ∃ x, ∀ i, x ≤ f i := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [lowerBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddBelow_range_of_forall_le x h

theorem bddAbove_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddAbove (Set.range f) ↔ ∃ x, ∀ i, f i ≤ x := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [upperBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddAbove_range_of_forall_le x h

theorem bddBelow_range_neg {ι α : Type*} [ha₁ : LinearOrder α] [ha₂ : Ring α]
[ha₃ : AddLeftMono α] [ha₄ : AddRightMono α] {f : ι → α} :
BddBelow (Set.range (-f)) ↔ BddAbove (Set.range f) := by
  simp [bddBelow_range, bddAbove_range]
  constructor <;> rintro ⟨x, hx⟩ <;> use -x <;> intro i <;> specialize hx i
  · rwa [←neg_neg # f i, neg_le_neg_iff]
  · rwa [neg_le_neg_iff]

end Order

namespace Finset

variable {α β γ : Type*} {s : Finset α}

section

variable {α : Type*} [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
variable {β : Type*} [hb₁ : LinearOrder β] [hb₂ : Semiring β]
  [hb₃ : AddLeftMono β] [hb₄ : AddLeftReflectLE β] [hb₇ : IsOrderedAddMonoid β]
variable {s : Finset α}

omit ha₂ ha₃ in
theorem le_sum_of_mem {f : α → β} {x : α}
(h₁ : ∀ x ∈ s, 0 ≤ f x) (h₂ : x ∈ s) : f x ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction
  · simp at h₂
  clear! s
  nm y s h₃ ih
  simp at h₁ h₂
  rcases h₁ with ⟨h₁, h₄⟩
  specialize ih h₄
  rw [sum_insert h₃]
  rcases h₂ with rfl | h₂
  · rw [le_add_iff_nonneg_right]
    exact sum_nonneg h₄
  specialize ih h₂
  apply ih.trans
  rwa [le_add_iff_nonneg_left]

end

theorem card_filter_add_card_filter_not {p : α → Prop} [hp : DecidablePred p] :
(s.filter p).card + (s.filter (¬p ·)).card = s.card := by
  classical
  induction s using Finset.induction
  · simp
  clear! s
  nm x s hx ih
  rw [card_insert_of_notMem hx, ←ih]; clear ih
  have h₁ : ∀ p [DecidablePred p], x ∉ s.filter p; simp [hx]
  by_cases h : p x
  · simp [filter_insert, h, card_insert_of_notMem # h₁ p]; ring_nf
  · simp [filter_insert, h, card_insert_of_notMem # h₁ (¬p ·)]; ring_nf

theorem card_filter_range_le_of_le {p : ℕ → Prop} {i j : ℕ} [hp : DecidablePred p]
(h : i ≤ j) : (Finset.range i |>.filter p).card ≤ (Finset.range j |>.filter p).card := by
  apply Finset.card_le_card
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.range_add]
  rw [Finset.filter_union]
  simp

theorem Ico_add_right {n m k : ℕ} (h : n ≤ m) : Ico n (m + k) = Ico n m ∪ Ico m (m + k) := by
  ext; simp; omega

theorem card_filter_range_add {p : ℕ → Prop} {n k : ℕ} [hp : DecidablePred p] :
{i ∈ Finset.range (n + k) | p i}.card = {i ∈ Finset.range n | p i}.card +
{i ∈ Finset.Ico n (n + k) | p i}.card := by
  simp_rw [range_eq_Ico]
  rw [Ico_add_right # by simp]
  rw [filter_union, card_union_of_disjoint]
  rw [Finset.disjoint_iff_ne]
  intro; simp; omega

theorem card_eq_one_iff_exiu : s.card = 1 ↔ ∃! x, x ∈ s := by
  rw [card_eq_one]
  apply exists_congr; intro x
  simp [Finset.ext_iff]
  grind

theorem le_sum_range {a : ℕ → ℝ} {N n : ℕ} (h : n < N) :
|a n| ≤ ∑ i ∈ range N, |a i| := by
  obtain ⟨s, h₁, h₂⟩ : ∃ (s : Finset ℕ), n ∉ s ∧ range N = insert n s
  · use range N |>.erase n; simp; rw [insert_erase]; simpa
  simp [h₂, sum_insert h₁]; apply sum_nonneg; simp

theorem single_le_sum_of_canonicallyOrdered : ∀ {ι M : Type*} [inst : AddCommMonoid M]
  [inst_1 : PartialOrder M] [H : CanonicallyOrderedAdd M]
  {f : ι → M} {s : Finset ι} {i : ι}, i ∈ s → f i ≤ ∑ j ∈ s, f j :=
fun {ι} {M} [AddCommMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M] {f} {s} {i} hi ↦
  CanonicallyOrderedAddCommMonoid.single_le_sum hi

end Finset

namespace List

variable {α β : Type*} {xs ys : List α}

attribute [simp] count_eq_zero

theorem nodup_filterMap_iff [ha : DecidableEq α] {f : α → Option β} :
(xs.filterMap f).Nodup ↔ ∀ x ∈ xs, ∀ y, f x = some y → xs.count x ≤ 1 ∧
∀ x' ∈ xs, f x' = some y → x = x' := by
  classical
  induction xs <;> simp
  nm x xs ih
  simp [filterMap, count_cons]
  split <;> simp [ih] <;> clear ih
  · nm o h₁; clear o
    constructor
    · intro h₂
      simp [h₁]
      intro a h₃ b h₄
      split_ifs with hx <;> simp
      · subst hx; simp [h₁] at h₄
      · exact h₂ _ h₃ _ h₄
    · intro ⟨h₂, h₃⟩ a h₄ b h₅
      specialize h₃ _ h₄ _ h₅
      rcases h₃ with ⟨h₃, h₆, h₇⟩
      split_ifs at h₃ with hx
      · subst hx; simp [h₁] at h₅
      · use h₃
  nm o y h₁; clear o
  simp [h₁]
  constructor
  · intro ⟨h₂, h₃⟩
    refine' ⟨⟨_, _⟩, _⟩
    · intro hx
      specialize h₂ _ hx
      exact h₂ h₁
    · intro a h₄ h₅
      specialize h₂ _ h₄
      contradiction
    · intro a h₄ b h₅
      specialize h₃ _ h₄ _ h₅
      rcases h₃ with ⟨h₃, h₆⟩
      split_ifs with hx
      · subst hx
        simp [h₁] at h₅
        subst h₅
        simp [h₂ _ h₄] at h₁
      refine' ⟨h₃, _, h₆⟩
      rintro rfl
      specialize h₂ _ h₄
      contradiction
  · intro ⟨⟨h₂, h₃⟩, h₆⟩
    constructor
    · intro a h₄ h₅
      specialize h₃ _ h₄ h₅
      subst h₃
      contradiction
    · intro a h₇ b h₈
      specialize h₆ _ h₇ _ h₈
      rcases h₆ with ⟨h₆, h₉, H₁⟩
      refine' ⟨_, H₁⟩
      split_ifs at h₆ with H₂
      · subst H₂; contradiction
      · exact h₆

end List

namespace L04Aux

def eventually (p : ℕ → Prop) : Prop :=
  ∃ N, ∀ n, N ≤ n → p n

def tendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε, 0 < ε → eventually (|a · - L| < ε)

def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, tendsTo a L

noncomputable
def lub (a : ℕ → ℝ) : ℝ :=
  ⨆ i, a i

def series (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

def AbsConv (a : ℕ → ℝ) : Prop :=
  converges # series (|a ·|)

def Infp (a : ℕ → ℝ) (p : ℝ → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ p (a n)

open Classical in noncomputable
def mkSubseq (a : ℕ → ℝ) (p : ℝ → Prop) (n : ℕ) : ℕ :=
  match n with
  | 0 => Nat.find! (p # a ·)
  | n + 1 =>
    let k := mkSubseq a p n
    k + 1 + Nat.find! (p # a # k + 1 + ·)

noncomputable
def limit (a : ℕ → ℝ) : ℝ :=
  Classical.epsilon # tendsTo a

def Subseq (σ : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → σ i < σ j

def monoLe (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≤ j → a i ≤ a j

def monoLt (a : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → a i < a j

def monoGe (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≤ j → a j ≤ a i

def monoGt (a : ℕ → ℝ) : Prop :=
  ∀ i j, i < j → a j < a i

def boundedBy (a : ℕ → ℝ) (m : ℝ) : Prop :=
  ∀ n, |a n| ≤ m

def bounded (a : ℕ → ℝ) : Prop :=
  ∃ m, boundedBy a m

def isCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i j, N ≤ i → N ≤ j → |a i - a j| < ε

def isCauchyAlt₁ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - a N| < ε

open Classical in
@[simp] noncomputable
def bwSeq (a : ℕ → ℝ) (y₁ y₂ : ℚ) (n : ℕ) : ℚ × ℚ := match n with
| 0 => (y₁, y₂)
| n + 1 => let y := (y₁ + y₂) / 2
  if {i | y₁ ≤ a i ∧ a i ≤ y}.Infinite
  then bwSeq a y₁ y n else bwSeq a y y₂ n

open Classical in noncomputable
def bwLimit (a : ℕ → ℝ) (M : ℚ) : ℝ :=
  if h : IsCauSeq abs (bwSeq a (-M) M · |>.1)
  then Real.mk # .mk _ h else 0

open Classical in noncomputable
def bwSubseq (a : ℕ → ℝ) (M : ℚ) (n : ℕ) : ℕ :=
  Classical.epsilon # λ i => (∀ k < n, bwSubseq a M k < i) ∧
  let (y₁, y₂) := bwSeq a (-M) M n
  y₁ ≤ a i ∧ a i ≤ y₂

noncomputable
def bounds (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  lub |(a # n + ·)|

def CondConv (a : ℕ → ℝ) : Prop :=
  converges (series a) ∧ ¬AbsConv a

namespace CondConv

noncomputable
def σp (a : ℕ → ℝ) : ℕ → ℕ :=
  mkSubseq a (0 ≤ ·)

noncomputable
def σn (a : ℕ → ℝ) : ℕ → ℕ :=
  mkSubseq a (· < 0)

noncomputable
def ap (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a # σp a n

noncomputable
def an (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a # σn a n

noncomputable
def M (a : ℕ → ℝ) : ℝ :=
  limit # series a

def fgCnd (F : ℝ → ℝ) (a : ℕ → ℝ) (f g : ℕ → ℕ) : Prop :=
  (∀ (n : ℕ), f n + g n = n) ∧ (∀ (i j : ℕ), i ≤ j → f i ≤ f j) ∧
  (∀ (i j : ℕ), i ≤ j → g i ≤ g j) ∧ (∀ (n : ℕ), ∃ k, n ≤ f k) ∧ (∀ (n : ℕ), ∃ k, n ≤ g k) ∧
  ∀ (n : ℕ), series (F # a ·) n = series (F # ap a ·) (f n) + series (F # an a ·) (g n)

noncomputable
def fAux (F : ℝ → ℝ) (a : ℕ → ℝ) : ℕ → ℕ :=
  Classical.epsilon # λ f => ∃ g, fgCnd F a f g

noncomputable
def gAux (F : ℝ → ℝ) (a : ℕ → ℝ) : ℕ → ℕ :=
  Classical.epsilon # λ g => fgCnd F a (fAux F a) g

noncomputable
def f (a : ℕ → ℝ) : ℕ → ℕ :=
  fAux id a

noncomputable
def g (a : ℕ → ℝ) : ℕ → ℕ :=
  gAux id a

noncomputable
def f' (a : ℕ → ℝ) : ℕ → ℕ :=
  fAux abs a

noncomputable
def g' (a : ℕ → ℝ) : ℕ → ℕ :=
  gAux abs a

end CondConv

-----

theorem series_drop_eq {a N} :
series (a # N + ·) = λ n => series a (N + n) - series a N := by
  ext n
  simp_rw [series]
  trans ∑ k ∈ Finset.Ico N (N + n), a k
  · simp [Finset.sum_Ico_eq_sum_range]
  · simp [Finset.sum_Ico_eq_sub]

theorem tendsTo_add {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ + a₂) (L₁ + L₂) := by
  intro e he
  dsimp
  specialize h₁ (e / 2) (by simpa)
  specialize h₂ (e / 2) (by simpa)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  use max N₁ N₂
  intro n hn
  specialize h₁ n # le_of_max_le_left hn
  specialize h₂ n # le_of_max_le_right hn
  calc
    _ = |(a₁ n - L₁) + (a₂ n - L₂)| := by ring_nf
    _ ≤ |a₁ n - L₁| + |a₂ n - L₂| := by apply abs_add_le
  linarith

theorem tendsTo_neg {a L} (h : tendsTo a L) : tendsTo (-a) (-L) := by
  intro e he; specialize h e he; obtain ⟨N, h⟩ := h
  use N; intro n hn; specialize h n hn; simp
  convert h using 1; rw [←abs_neg, add_comm]; simp; rfl

theorem tendsTo_sub {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ - a₂) (L₁ - L₂) :=
  tendsTo_add h₁ # tendsTo_neg h₂

theorem tendsTo_drop_iff' {a L k} : tendsTo (a # · + k) L ↔ tendsTo a L := by
  constructor
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp at h
    use N + k
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    specialize h (n + N) (by linarith)
    ring_nf at h ⊢
    exact h
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp
    use N
    intro n hn
    specialize h (n + k) (by linarith)
    exact h

theorem tendsTo_drop_iff {a L k} : tendsTo (a # k + ·) L ↔ tendsTo a L := by
  simp_rw [add_comm k, tendsTo_drop_iff']

theorem tendsTo_drop_of {a L k} (h : tendsTo a L) : tendsTo (a # k + ·) L :=
  tendsTo_drop_iff.mpr h

theorem tendsTo_const {L} : tendsTo (λ _ => L) L := by
  intro e he; use 0; simpa

theorem tendsTo_unique {a L₁ L₂}
(h₁ : tendsTo a L₁) (h₂ : tendsTo a L₂) : L₁ = L₂ := by
  by_contra! h₃
  wlog h₄ : L₁ < L₂ with ih
  · push_neg at h₄; apply ne_symm' at h₃
    apply ih h₂ h₁ h₃; exact lt_of_le_of_ne h₄ h₃
  clear h₃
  generalize he : (L₂ - L₁) / 2 = e
  have h₅ : 0 < e; linarith
  specialize h₁ e (by linarith)
  specialize h₂ e (by linarith)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  specialize h₁ (max N₁ N₂) (by simp)
  specialize h₂ (max N₁ N₂) (by simp)
  generalize a (max N₁ N₂) = x at h₁ h₂
  replace h₁ := abs_lt.mp h₁ |>.2
  replace h₂ := abs_lt.mp h₂ |>.1
  simp at h₂
  linarith

@[simp]
theorem tendsTo_const_iff {L M} : tendsTo (λ _ => L) M ↔ L = M := by
  have h₁ := @tendsTo_const L
  symm; constructor; rintro rfl; exact h₁
  intro h₂; exact tendsTo_unique h₁ h₂

theorem series_drop_tendsTo_of {a L N} (h : tendsTo (series a) L) :
tendsTo (series (a # N + ·)) (L - series a N) := by
  rw [series_drop_eq]; apply tendsTo_sub # tendsTo_drop_of h; simp

theorem series_drop_tendsTo_iff {a L N} :
tendsTo (series (a # N + ·)) L ↔ tendsTo (series a) (L + series a N) := by
  rw [series_drop_eq]
  constructor <;> intro h
  · nth_rw 1 [show series a = (λ n => series a n - series a N + series a N) by simp]
    apply tendsTo_add _ # by simp
    rwa [←tendsTo_drop_iff (a := λ n => series a n - series a N) (k := N)]
  · rw [show L = L + series a N - series a N by simp]
    apply tendsTo_add _ # by simp
    exact tendsTo_drop_of h

theorem converges_series_drop_iff {a N} :
converges (series (a # N + ·)) ↔ converges (series a) := by
  constructor <;> rintro ⟨L, h⟩
  · rw [series_drop_tendsTo_iff] at h; exact ⟨_, h⟩
  · use L - series a N; simpa [series_drop_tendsTo_iff]

theorem absConv_drop_of {a N} (h : AbsConv a) : AbsConv (a # N + ·) := by
  unfold AbsConv at h ⊢; rwa [converges_series_drop_iff (a := (|a ·|))]

theorem absConv_drop_iff {a N} : AbsConv (a # N + ·) ↔ AbsConv a := by
  exact converges_series_drop_iff (a := (|a ·|))

@[simp]
theorem neg_series' {a} : -series a = series (-a) := by
  ext n; simp [series]

@[simp]
theorem converges_neg {a} : converges (-a) ↔ converges a := by
  constructor <;> rintro ⟨L, h⟩ <;> use -L <;> convert tendsTo_neg h; simp

theorem absConv_neg {a} : AbsConv (-a) ↔ AbsConv a := by
  simp [AbsConv]

theorem infp_of_imp {a} {p₁ p₂ : ℝ → Prop} (h₁ : Infp a p₁)
(h₂ : ∀ n, p₁ (a n) → p₂ (a n)) : Infp a p₂ := by
  intro N; specialize h₁ N; choose n h₁ h₃ using h₁; use n, h₁, h₂ _ h₃

theorem subseq_iff_lt_add_one {σ : ℕ → ℕ} :
Subseq σ ↔ ∀ n, σ n < σ (n + 1) := by
  constructor
  · intro h n
    apply h
    simp
  intro h k n h₁
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁; clear h₁
  induction n generalizing k
  · apply h
  nm n ih
  simp [←add_assoc]
  apply ih _ |>.trans
  apply h

theorem subseq_mkSubseq {a p} : Subseq (mkSubseq a p) := by
  rw [subseq_iff_lt_add_one]
  intro n
  rw [mkSubseq]
  omega

theorem limit_eq_of_tendsTo {a L} (h : tendsTo a L) : limit a = L :=
  epsilon_eq_of h # λ _ h₁ => tendsTo_unique h₁ h

theorem tendsTo_limit_of_tendsTo {a L} (h : tendsTo a L) : tendsTo a (limit a) := by
  rwa [limit_eq_of_tendsTo h]

theorem tendsTo_limit_of_converges {a} (h : converges a) : tendsTo a (limit a) := by
  obtain ⟨L, h⟩ := h; exact tendsTo_limit_of_tendsTo h

theorem exi_mkSubseq_eq_of_apply {a p n} (h : Infp a p)
(h₁ : p (a n)) : ∃ k, mkSubseq a p k = n := by
  induction n using Nat.strong_induction_on generalizing a
  nm n ih
  by_cases h₂ : ∀ k < n, ¬p (a k)
  · use 0
    rw [mkSubseq]
    rw [Nat.find!_eq_iff, if_pos ⟨_, h₁⟩]
    exact ⟨h₁, h₂⟩
  push_neg at h₂
  replace h₂ : ∃ k, k < n ∧ p (a k) ∧ ∀ r, k < r → r < n → ¬p (a r)
  · choose k hk h₂ using h₂
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
    have h₃ : ∃ d, p # a # k + n - d
    · use n
      simpa
    replace h₃ := Nat.find!_spec' h₃
    generalize Nat.find! (λ d => p # a # k + n - d) = d at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    use k + n - d, by omega, h₃
    intro r h₅ h₆ h₇
    rw [Nat.lt_succ_iff] at h₆
    obtain ⟨w, h₈⟩ := Nat.exists_eq_add_of_le h₆
    clear h₆
    have h₆ : r = k + n - w; omega
    rw [h₆] at h₇
    specialize h₄ _ h₇
    omega
  choose k h₂ h₃ h₄ using h₂
  specialize @ih k (by omega) a h h₃
  choose i ih using ih
  use i + 1
  rw [mkSubseq, ih]; clear ih
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₂; clear h₂
  ring_nf at h₁ ⊢
  simp
  rw [Nat.find!_eq_iff]
  rw [if_pos ⟨_, h₁⟩]
  use h₁
  intro w hw
  apply h₄ <;> omega

@[simp]
theorem series_zero {a} : series a 0 = 0 := by
  simp [series]

theorem series_succ {a n} : series a (n + 1) = series a n + a n := by
  simp [series, Finset.sum_range_succ]

theorem subseq_lt_of_lt {σ i j} (h₁ : Subseq σ)  (h₂ : i < j) : σ i < σ j :=
  h₁ _ _ h₂

theorem subseq_le_of_le {σ i j} (h₁ : Subseq σ)  (h₂ : i ≤ j) : σ i ≤ σ j := by
  rw [le_iff_eq_or_lt] at h₂
  rcases h₂ with rfl | h₂; rfl
  exact le_of_lt # subseq_lt_of_lt h₁ h₂

theorem lt_of_subseq_lt {σ i j} (h₁ : Subseq σ) (h₂ : σ i < σ j) : i < j := by
  contrapose! h₂; exact subseq_le_of_le h₁ h₂

theorem subseq_lt_iff {σ i j} (h₁ : Subseq σ) : σ i < σ j ↔ i < j :=
  ⟨lt_of_subseq_lt h₁, subseq_lt_of_lt h₁⟩

theorem subseq_nat_le_subseq_iff {σ n m} (h : Subseq σ) : σ n ≤ σ m ↔ n ≤ m := by
  unfold Subseq at h
  obtain (h₁ | rfl | h₁) := lt_trichotomy n m
  on_goal 2 => simp
  all_goals specialize h _ _ h₁
  · simp [le_of_lt h, le_of_lt h₁]
  · rw [iff_iff_not']; simp [h, h₁]

theorem subseq_eq_of_eq {σ : ℕ → ℕ} {i j} (h₂ : i = j) : σ i = σ j := by
  rw [h₂]

theorem eq_of_subseq_eq {σ i j} (h₁ : Subseq σ) (h₂ : σ i = σ j) : i = j := by
  contrapose! h₂
  rw [ne_iff_lt_or_gt] at h₂ ⊢
  rcases h₂ with h₂ | h₂
  · left; exact subseq_lt_of_lt h₁ h₂
  · right; exact subseq_lt_of_lt h₁ h₂

theorem subseq_eq_iff {σ i j} (h₁ : Subseq σ) : σ i = σ j ↔ i = j :=
  ⟨eq_of_subseq_eq h₁, subseq_eq_of_eq⟩

theorem subseq_card_filter_range_eq {a : ℕ → ℝ} {p : ℝ → Prop} {σ : ℕ → ℕ} {n k : ℕ}
[hp : DecidablePred p] (h₁ : Subseq σ) (h₂ : ∀ n, p (a n) ↔ ∃ k, σ k = n)
(h₃ : σ k = n) : {k ∈ Finset.range n | p (a k)}.card = k := by
  induction k generalizing n
  · simp
    simp [h₂]
    rintro k hk r rfl
    subst h₃
    simp [subseq_lt_iff h₁] at hk
  nm k ih
  have h₄ : σ k ≤ n
  · simp [←h₃, subseq_nat_le_subseq_iff h₁]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₄; clear h₄
  specialize ih rfl
  rw [Finset.card_filter_range_add, ih]; clear ih
  simp
  rw [Finset.card_eq_one_iff_exiu]
  use σ k
  simp
  split_ands
  · rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp [subseq_eq_iff h₁] at h₃
  · rw [h₂]
    use k
  intro r h₄ h₅ h₆
  rw [←h₃] at h₅
  rw [h₂] at h₆
  obtain ⟨r, rfl⟩ := h₆
  rw [subseq_nat_le_subseq_iff h₁] at h₄
  rw [subseq_lt_iff h₁] at h₅
  rw [subseq_eq_iff h₁]
  omega

theorem exi_fn_series_of_subseq_cover {a : ℕ → ℝ} {p : ℝ → Prop} {σ₁ σ₂ : ℕ → ℕ}
{F : ℝ → ℝ}
(h₁ : Subseq σ₁) (h₂ : Subseq σ₂)
(h₃ : ∀ n, p (a n) ↔ ∃ k, σ₁ k = n)
(h₄ : ∀ n, ¬p (a n) ↔ ∃ k, σ₂ k = n) :
∃ (f g : ℕ → ℕ), (∀ n, f n + g n = n) ∧
(∀ i j, i ≤ j → f i ≤ f j) ∧ (∀ i j, i ≤ j → g i ≤ g j) ∧
(Infp a p → ∀ n, ∃ k, n ≤ f k) ∧ (Infp a (¬p ·) → ∀ n, ∃ k, n ≤ g k) ∧
(∀ n, series (F # a ·) n = series (F # a # σ₁ ·) (f n) + series (F # a # σ₂ ·) (g n)) := by
  classical
  use λ n => Finset.range n |>.filter (λ n => p (a n)) |>.card
  use λ n => Finset.range n |>.filter (λ n => ¬p (a n)) |>.card
  split_ands
  · intro n; convert Finset.card_filter_add_card_filter_not; simp
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | p (a i)}.card; linarith
    simp
    use k + r
    simpa
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    dsimp
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | ¬p (a i)}.card; linarith
    simp
    use k + r
    simpa
  intro n
  induction n
  · simp
  nm n ih
  simp_rw [series_succ, Finset.range_add_one, Finset.filter_insert]
  by_cases h : p (a n) <;> simp [h]
  · rw [series_succ]
    rw [h₃] at h
    choose k h using h
    suffices : F (a # σ₁ {n ∈ Finset.range n | p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq h₁ h₃ h
  · rw [series_succ]
    rw [h₄] at h
    choose k h using h
    suffices : F (a # σ₂ {n ∈ Finset.range n | ¬p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq (p := (¬p ·)) h₂ h₄ h

theorem exi_add_of_infp {a p N} (h : Infp a p) : ∃ n, p (a # N + n) := by
  specialize h N
  choose n h₁ h₂ using h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁
  use n

theorem exi_of_infp {a p} (h : Infp a p) : ∃ n, p (a n) := by
  convert exi_add_of_infp h (N := 0); simp

theorem mkSubseq_spec {a p n} (h : Infp a p) : p # a # mkSubseq a p n := by
  cases n <;> rw [mkSubseq]
  · exact Nat.find!_spec (p := (p # a ·)) # exi_of_infp h
  nm n; apply Nat.find!_spec (p := λ k => p (a (mkSubseq a p n + 1 + k)))
  exact exi_add_of_infp h

theorem apply_of_mkSubseq_eq {a p n k} (h : Infp a p)
(h₁ : mkSubseq a p k = n) : p (a n) := by
  subst h₁; exact mkSubseq_spec h

theorem apply_iff_exi_mkSubseq_eq {a p n} (h : Infp a p) : p (a n) ↔ ∃ k, mkSubseq a p k = n :=
  ⟨exi_mkSubseq_eq_of_apply h, λ ⟨_, h₁⟩ => apply_of_mkSubseq_eq h h₁⟩

theorem monoLe_iff_le_succ {a} : monoLe a ↔ ∀ n, a n ≤ a (n + 1) := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
  induction n; simp; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans # h _

theorem monoLt_iff_lt_succ {a} : monoLt a ↔ ∀ n, a n < a (n + 1) := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
  induction n; simp [h]; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans # h _

theorem monoGe_iff_succ_le {a} : monoGe a ↔ ∀ n, a (n + 1) ≤ a n := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
  induction n; simp; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans' # h _

theorem monoGt_iff_succ_lt {a} : monoGt a ↔ ∀ n, a (n + 1) < a n := by
  use λ h n => h n (n + 1) # by simp
  intro h k n hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
  induction n; simp [h]; nm n ih
  rw [←Nat.add_assoc]
  exact ih.trans' # h _

theorem monoLe_series_of_nonneg {a} (h : ∀ n, 0 ≤ a n) : monoLe (series a) := by
  rw [monoLe_iff_le_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGe_series_of_nonpos {a} (h : ∀ n, a n ≤ 0) : monoGe (series a) := by
  rw [monoGe_iff_succ_le]; intro n; rw [series_succ]; linarith [h n]

theorem monoLt_series_of_pos {a} (h : ∀ n, 0 < a n) : monoLt (series a) := by
  rw [monoLt_iff_lt_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGt_series_of_neg {a} (h : ∀ n, a n < 0) : monoGt (series a) := by
  rw [monoGt_iff_succ_lt]; intro n; rw [series_succ]; linarith [h n]

theorem monoLe_of_monoLt {a} (h : monoLt a) : monoLe a := by
  intro i j h₁; rw [le_iff_eq_or_lt] at h₁; rcases h₁ with rfl | h₁
  rfl; apply le_of_lt; apply h; exact h₁

theorem monoGe_of_monoGt {a} (h : monoGt a) : monoGe a := by
  intro i j h₁; rw [le_iff_eq_or_lt] at h₁; rcases h₁ with rfl | h₁
  rfl; apply le_of_lt; apply h; exact h₁

theorem limit_le_of_forall_le {a L K} (h₁ : tendsTo a L) (h₂ : ∀ n, a n ≤ K) : L ≤ K := by
  by_contra! h₃; specialize h₁ ((L - K) / 2) # by linarith
  obtain ⟨N, h₁⟩ := h₁; specialize h₁ N # by rfl
  specialize h₂ N; rw [abs_lt] at h₁; linarith

theorem le_limit_of_forall_le {a L K} (h₁ : tendsTo a L) (h₂ : ∀ n, K ≤ a n) : K ≤ L := by
  have h₃ := limit_le_of_forall_le (K := -K) # tendsTo_neg h₁; simp at h₃; exact h₃ h₂

@[simp]
theorem monoLe_series_abs {a : ℕ → ℝ} : monoLe # series (|a ·|) := by
  simp [monoLe_iff_le_succ, series_succ]

theorem tendsTo_abs {a L} (h : tendsTo a L) : tendsTo (|a ·|) |L| := by
  intro e he; specialize h e he; obtain ⟨N, h⟩ := h
  use N; intro n hn; specialize h n hn; dsimp
  apply lt_of_le_of_lt _ h; apply abs_abs_sub_abs_le

@[simp]
theorem monoLe_neg {a} : monoLe (-a) ↔ monoGe a := by
  unfold monoLe monoGe; simp

@[simp]
theorem monoLt_neg {a} : monoLt (-a) ↔ monoGt a := by
  unfold monoLt monoGt; simp

@[simp]
theorem monoGe_neg {a} : monoGe (-a) ↔ monoLe a := by
  unfold monoLe monoGe; simp

@[simp]
theorem monoGt_neg {a} : monoGt (-a) ↔ monoLt a := by
  unfold monoLt monoGt; simp

theorem le_limit_of_monoLe' {a L n} (h₁ : monoLe a) (h₂ : tendsTo a L) : a n ≤ L := by
  by_contra! h₃
  specialize h₂ ((a n - L) / 2) (by linarith)
  choose N h₂ using h₂
  specialize h₂ (N + n) (by linarith)
  have h₄ : a n ≤ a (N + n)
  · apply h₁; simp
  rw [abs_of_pos # by linarith] at h₂
  linarith

theorem limit_le_of_monoGe' {a L n} (h₁ : monoGe a) (h₂ : tendsTo a L) : L ≤ a n := by
  replace h₁ : monoLe (-a); simpa
  replace h₂ := tendsTo_neg h₂
  suffices h : (-a) n ≤ -L
  · simp at h; exact h
  exact le_limit_of_monoLe' h₁ h₂

theorem le_limit_of_monoLe {a L} (h₁ : monoLe a) (h₂ : tendsTo a L) : ∀ n, a n ≤ L :=
  λ _ => le_limit_of_monoLe' h₁ h₂

theorem limit_le_of_monoGe {a L} (h₁ : monoGe a) (h₂ : tendsTo a L) : ∀ n, L ≤ a n :=
  λ _ => limit_le_of_monoGe' h₁ h₂

theorem isCauchy_iff_alt₁ {a} : isCauchy a ↔ isCauchyAlt₁ a := by
  constructor <;> intro h e he
  · specialize h e he
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h N n (by rfl) hn
    rwa [abs_sub_comm]
  · specialize h (e / 2) # by positivity
    obtain ⟨N, h⟩ := h
    use N
    intro i j hi hj
    exact Real.abs_sub_lt_of_lt_lt_half (h i hi) (h j hj)

theorem bounded_of_isCauchy {a} (h : isCauchy a) : bounded a := by
  rw [isCauchy_iff_alt₁] at h
  specialize h 1 # by norm_num
  obtain ⟨N, h⟩ := h
  use 1 + |a N| + ∑ i ∈ Finset.range N, |a i|
  intro n
  have h₁ : 0 ≤ ∑ i ∈ Finset.range N, |a i|; positivity
  by_cases hn : n < N
  · have h₂ : |a n| ≤ ∑ i ∈ Finset.range N, |a i|
    · exact Finset.le_sum_range hn
    suffices h₃ : 0 ≤ 1 + |a N|; linarith
    positivity
  push_neg at hn
  specialize h n hn
  suffices : |a n| - |a N| < 1; linarith
  apply lt_of_le_of_lt _ h
  apply abs_sub_abs_le_abs_sub

theorem bwSeq_fst_lt_snd' {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 < (bwSeq a y₁ y₂ n).2 := by
  induction n generalizing y₁ y₂ <;> simp; exact hy
  nm n ih; split_ifs <;> apply ih <;> linarith

theorem fst_lt_snd_of_bwSeq_eq {a : ℕ → ℝ} {y₁ y₂ y₁' y₂' : ℚ} {n : ℕ} (hy : y₁ < y₂)
(h : bwSeq a y₁ y₂ n = (y₁', y₂')) : y₁' < y₂' := by
  rw [Prod.fst_eq_of_eq_mk h, Prod.snd_eq_of_eq_mk h]
  exact bwSeq_fst_lt_snd' hy

theorem bwSeq_add {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n k : ℕ} (hy : y₁ < y₂) :
bwSeq a y₁ y₂ (n + k) = bwSeq a (bwSeq a y₁ y₂ n).1 (bwSeq a y₁ y₂ n).2 k := by
  generalize hr : bwSeq a y₁ y₂ n = r
  rcases r with ⟨y₁', y₂'⟩
  dsimp
  induction n generalizing y₁ y₂ y₁' y₂'
  · simp at hr; simp [hr]
  nm n ih
  simp at hr
  simp [Nat.succ_add]
  split_ifs at hr ⊢ with h₁
  all_goals apply ih; linarith; exact hr

theorem infinite_between_of_bwSeq_eq {a : ℕ → ℝ} {y₁ y₂ y₁' y₂' : ℚ} {n : ℕ}
(hy : y₁ < y₂) (ha : {i | y₁ ≤ a i ∧ a i ≤ y₂}.Infinite)
(hr : bwSeq a y₁ y₂ n = (y₁', y₂')) : {i | y₁' ≤ a i ∧ a i ≤ y₂'}.Infinite := by
  induction n generalizing y₁ y₂ y₁' y₂'
  · simp at hr
    simp [hr] at ha
    exact ha
  nm n ih
  simp at hr
  split_ifs at hr with h₁ <;> apply ih (by linarith) _ hr <;> clear ih
  · exact h₁
  clear! n
  simp at h₁
  rw [Set.finite_iff_bddAbove] at h₁
  obtain ⟨N, h₁⟩ := h₁
  rw [Set.infinite_iff_exists_gt] at ha
  simp at ha
  replace h₁ : ∀ n, N < n → a n < y₁ ∨ (↑y₁ + ↑y₂) / 2 < a n
  · intro n
    specialize @h₁ n
    simp at h₁
    rw [or_iff_not_imp_left]
    intro h₂ h₃
    simp at h₃
    contrapose! h₁
    use h₃
  apply Set.infinite_of_forall_exists_gt
  intro n
  specialize ha # N + n + 1
  obtain ⟨k, ⟨ha₁, ha₂⟩, hk⟩ := ha
  use k
  refine ⟨?_, by linarith⟩
  simp
  specialize h₁ k (by linarith)
  rcases h₁ with h₁ | h₁; linarith
  constructor <;> linarith

theorem infinite_between_of_bwSeq_eq_of_abs_lt {a : ℕ → ℝ} {M y₁ y₂ : ℚ} {n : ℕ}
(h : ∀ n, |a n| < M) (hr : bwSeq a (-M) M n = (y₁, y₂)) :
{i | y₁ ≤ a i ∧ a i ≤ y₂}.Infinite := by
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0
    simp at h; exact h
  have hM : -M < M; linarith
  apply infinite_between_of_bwSeq_eq hM _ hr
  apply Set.infinite_of_forall_exists_gt
  clear! n
  intro n
  simp
  use n + 1
  simp
  specialize h (n + 1)
  rw [abs_lt] at h
  constructor <;> linarith

theorem bwSubseq_cnd' {a : ℕ → ℝ} {M : ℚ} {n : ℕ} (h : ∀ n, |a n| < M) :
∃ i, (∀ k < n, bwSubseq a M k < i) ∧
let (y₁, y₂) := bwSeq a (-M) M n
y₁ ≤ a i ∧ a i ≤ y₂ := by
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  induction n
  · use 0
    simp
    specialize h 0
    rw [abs_lt] at h
    constructor <;> linarith
  nm n ih
  have h₁ := Classical.epsilon_spec ih
  generalize h₂ : Classical.epsilon (λ i =>
    (∀ k < n, bwSubseq a M k < i) ∧
    match bwSeq a (-M) M n with
    | (y₁, y₂) => ↑y₁ ≤ a i ∧ a i ≤ ↑y₂) = i at h₁
  rcases h₁ with ⟨h₁, h₃⟩
  generalize hr : bwSeq a (-M) M n = r at h₃ ⊢
  rcases r with ⟨y₁, y₂⟩
  simp at h₃
  rcases h₃ with ⟨h₃, h₄⟩
  have hy := fst_lt_snd_of_bwSeq_eq hM hr
  rw [bwSeq_add hM, hr]
  dsimp only
  generalize hr' : bwSeq a y₁ y₂ 1 = r'
  rcases r' with ⟨y₁', y₂'⟩
  dsimp
  have hR : bwSeq a (-M) M (n + 1) = (y₁', y₂')
  · rwa [bwSeq_add hM, hr]
  have H := infinite_between_of_bwSeq_eq_of_abs_lt h hR
  generalize hN : 1 + ∑ k ∈ Finset.range (n + 1), bwSubseq a M k = N
  rw [Set.infinite_iff_exists_gt] at H
  specialize H N
  simp at H
  obtain ⟨m, H, hm⟩ := H
  use m
  refine ⟨?_, H⟩
  intro k hk
  apply hm.trans'
  rw [←hN]
  rw [Nat.lt_one_add_iff]
  replace hk : k ∈ Finset.range (n + 1); simpa
  exact Finset.single_le_sum_of_canonicallyOrdered hk

theorem bwSubseq_cnd {a : ℕ → ℝ} {M : ℚ} {n : ℕ} (h : ∀ n, |a n| < M) :
(∀ k < n, bwSubseq a M k < bwSubseq a M n) ∧
let (y₁, y₂) := bwSeq a (-M) M n
y₁ ≤ a (bwSubseq a M n) ∧ a (bwSubseq a M n) ≤ y₂ := by
  have h₁ := @bwSubseq_cnd' a M n h
  have h₂ := Classical.epsilon_spec h₁
  rw [←bwSubseq] at h₂; exact h₂

theorem bwSubseq_lt_of_lt {a : ℕ → ℝ} {M : ℚ} {i j : ℕ} (h : ∀ n, |a n| < M)
(h₁ : i < j) : bwSubseq a M i < bwSubseq a M j := by
  obtain ⟨h₂, h₃, h₄⟩ := @bwSubseq_cnd a M i h
  obtain ⟨h₅, h₆, h₇⟩ := @bwSubseq_cnd a M j h
  specialize h₅ i h₁
  linarith

theorem subseq_bwSubseq {a : ℕ → ℝ} {M : ℚ} (h : ∀ n, |a n| < M) :
Subseq # bwSubseq a M := λ _ _ => bwSubseq_lt_of_lt h

theorem le_bwSeq_fst {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(hy : y₁ < y₂) : y₁ ≤ (bwSeq a y₁ y₂ n).1 := by
  induction n generalizing y₁ y₂; rfl
  nm n ih
  simp
  split_ifs with h₁
  · apply ih; linarith
  trans (y₁ + y₂) / 2; linarith
  apply ih; linarith

theorem bwSeq_fst_le_of_le {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n m : ℕ}
(hy : y₁ < y₂) (hn : m ≤ n) :
(bwSeq a y₁ y₂ m).1 ≤ (bwSeq a y₁ y₂ n).1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ m = r
  rcases r with ⟨y₁', y₂'⟩
  apply le_bwSeq_fst
  rw [Prod.fst_eq_of_eq_mk hr, Prod.snd_eq_of_eq_mk hr]
  exact bwSeq_fst_lt_snd' hy

theorem bwSeq_snd_sub_fst_eq {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).2 - (bwSeq a y₁ y₂ n).1 = (y₂ - y₁) / 2 ^ n := by
  induction n generalizing y₁ y₂; simp
  nm n ih
  simp only [bwSeq]
  split_ifs with h₁
  all_goals
    apply (ih # by linarith).trans
    rw [pow_succ']
    ring_nf

theorem bwSeq_snd_le {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(hy : y₁ < y₂) : (bwSeq a y₁ y₂ n).2 ≤ y₂ := by
  induction n generalizing y₁ y₂; simp
  nm n ih
  simp
  split_ifs with h₁
  · trans (y₁ + y₂) / 2
    · apply ih; linarith
    linarith
  apply ih; linarith

theorem bwSeq_add_fst_sub_lt {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n k : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ (n + k)).1 - (bwSeq a y₁ y₂ n).1 < (y₂ - y₁) / 2 ^ n := by
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ n = r
  rcases r with ⟨y₁', y₂'⟩
  dsimp
  apply lt_of_lt_of_le
  rotate_left; apply le_of_eq # bwSeq_snd_sub_fst_eq (a := a) hy
  simp [hr]
  have hy' := fst_lt_snd_of_bwSeq_eq hy hr
  exact lt_of_lt_of_le (bwSeq_fst_lt_snd' hy') (bwSeq_snd_le hy')

theorem isCauSeq_bwSeq_fst {a : ℕ → ℝ} {y₁ y₂ : ℚ}
(hy : y₁ < y₂) : IsCauSeq abs (bwSeq a y₁ y₂ · |>.1) := by
  have hy' : (y₁ : ℝ) < y₂; simpa
  generalize hd : y₂ - y₁ = d
  have H₁ : 0 < d; linarith
  intro ε hε
  replace hε : 0 < (ε : ℝ); simpa
  obtain ⟨N, hN⟩ : ∃ (n : ℕ), d / 2 ^ n < ε
  · by_cases h₂ : d ≤ ε; use 1
    · simp; calc
      d / 2 ≤ ε / 2 := by linarith
      _ < _ := by linarith
    push_neg at h₂
    rw [←Real.ratCast_lt] at h₂
    suffices h₁ : ∃ (r : ℝ), 0 < r ∧ (d : ℝ) / 2 ^ r < ε
    · obtain ⟨r, hr, h₁⟩ := h₁
      obtain ⟨n, hn⟩ := exists_nat_gt r
      use n
      rw [←Real.ratCast_lt] at H₁ ⊢
      push_cast at H₁ ⊢
      apply h₁.trans'; clear h₁
      simp_rw [div_eq_mul_inv, mul_lt_mul_iff_right₀ H₁]
      rw [inv_lt_inv₀] <;> try positivity
      rw [←Real.rpow_natCast]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hn
    use Real.logb 2 (d / ε) + 1
    constructor
    · apply lt_add_of_le_of_pos _ # by norm_num
      apply Real.logb_nonneg # by norm_num
      rw [one_le_div₀ hε]; exact le_of_lt h₂
    rw [Real.rpow_add # by norm_num]
    rw [Real.rpow_logb] <;> try first | positivity | norm_num
    rw [div_mul, div_div_cancel₀] <;> try positivity
    linarith
  use N
  intro n (hn : N ≤ n)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  dsimp
  rw [abs_of_nonneg]
  rotate_left
  · exact sub_nonneg_of_le # bwSeq_fst_le_of_le hy # by simp
  apply bwSeq_add_fst_sub_lt hy |>.trans
  rwa [hd]

theorem isCauSeq_bwSeq_fst_of_abs_lt {a : ℕ → ℝ} {M : ℚ}
(h : ∀ n, |a n| < M) : IsCauSeq abs (bwSeq a (-M) M · |>.1) := by
  apply isCauSeq_bwSeq_fst
  suffices h : 0 < M; linarith
  have h₁ := pos_of_abs_lt # h 0
  simp at h₁; exact h₁

theorem bwLimit_eq_of {a : ℕ → ℝ} {M : ℚ} (h : ∀ n, |a n| < M) :
bwLimit a M = Real.mk (.mk _ # isCauSeq_bwSeq_fst_of_abs_lt h) := by
  rw [bwLimit]; generalize_proofs; split_ifs; rfl; contradiction

theorem bwSeq_fst_le_bwLimit {a : ℕ → ℝ} {M : ℚ} {n} (h : ∀ n, |a n| < M) :
(bwSeq a (-M) M n).1 ≤ bwLimit a M := by
  rw [bwLimit_eq_of h]
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  change Real.mk ⟨_, _⟩ ≤ Real.mk ⟨_, _⟩
  simp
  apply CauSeq.le_of_exists
  use n
  rintro i (hi : n ≤ i)
  dsimp
  exact bwSeq_fst_le_of_le hM hi

theorem bwSeq_fst_lt_snd {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n m : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 < (bwSeq a y₁ y₂ m).2 := by
  by_cases hn : n ≤ m
  · exact lt_of_le_of_lt (bwSeq_fst_le_of_le hy hn) (bwSeq_fst_lt_snd' hy)
  replace hn : m ≤ n; linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ m = r
  rcases r with ⟨y₁', y₂'⟩
  have hy' := fst_lt_snd_of_bwSeq_eq hy hr
  exact lt_of_lt_of_le (bwSeq_fst_lt_snd' hy') (bwSeq_snd_le hy')

theorem bwLimit_le_bwSeq_snd {a : ℕ → ℝ} {M : ℚ} {n} (h : ∀ n, |a n| < M) :
bwLimit a M ≤ (bwSeq a (-M) M n).2 := by
  rw [bwLimit_eq_of h]
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  change Real.mk ⟨_, _⟩ ≤ Real.mk ⟨_, _⟩
  simp
  apply CauSeq.le_of_exists
  use n
  rintro i (hi : n ≤ i)
  exact le_of_lt # bwSeq_fst_lt_snd hM

theorem bwSeq_fst_eq_snd_sub {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 = (bwSeq a y₁ y₂ n).2 - (y₂ - y₁) / 2 ^ n := by
  linarith [@bwSeq_snd_sub_fst_eq a y₁ y₂ n hy]

theorem bwSeq_snd_eq_fst_sub {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).2 = (bwSeq a y₁ y₂ n).1 + (y₂ - y₁) / 2 ^ n := by
  simp [bwSeq_fst_eq_snd_sub hy]

theorem exi_converges_subseq_of_bounded {a} (h : bounded a) :
∃ σ, Subseq σ ∧ converges (a ∘ σ) := by
  obtain ⟨M', h⟩ := h
  unfold boundedBy at h
  obtain ⟨M, h₁⟩ := exists_rat_gt M'
  replace h : ∀ n, |a n| < M
  · intro n; specialize h n; linarith
  clear! M'
  let σ := bwSubseq a M
  have hσ : Subseq σ := subseq_bwSubseq h
  use σ, subseq_bwSubseq h, bwLimit a M
  have hM' : 0 < M; have h₁ := pos_of_abs_lt # h 0; simp at h₁; exact h₁
  have hM : -M < M; linarith
  intro ε hε
  dsimp
  obtain ⟨N, hN⟩ := exists_nat_gt # (M * 2) / ε
  use N
  intro n hn
  obtain ⟨-, h₂, h₃⟩ := @bwSubseq_cnd a M n h
  change _ ≤ a (σ n) at h₂
  change a (σ n) ≤ _ at h₃
  have h₄ := @bwSeq_fst_le_bwLimit a M n h
  have h₅ := @bwLimit_le_bwSeq_snd a M n h
  rw [abs_lt]
  have H : (↑M + ↑M) / 2 ^ n < ε
  · rw [div_lt_comm₀] <;> try positivity
    have h₆ : 2 ^ N ≤ 2 ^ n
    · exact Nat.pow_le_pow_right (by norm_num) hn
    replace h₆ : (2 ^ N : ℝ) ≤ 2 ^ n; exact_mod_cast h₆
    apply lt_of_lt_of_le _ h₆
    clear h₆
    trans (N : ℝ); rwa [←mul_two]
    suffices h₆ : N < 2 ^ N; exact_mod_cast h₆
    exact Nat.lt_two_pow_self
  constructor
  · simp; apply lt_of_le_of_lt h₅
    rw [bwSeq_snd_eq_fst_sub hM]; simp; linarith
  · suffices : a (σ n) - ↑(bwSeq a (-M) M n).1 < ε; linarith
    rw [bwSeq_fst_eq_snd_sub hM]; simp; linarith

theorem isCauchy_of_converges {a} (h : converges a) : isCauchy a := by
  rw [isCauchy_iff_alt₁]
  obtain ⟨L, h⟩ := h
  intro e he
  specialize h (e / 2) (by positivity)
  obtain ⟨N, h⟩ := h
  use N
  dsimp at h
  intro n hn
  exact Real.abs_sub_lt_of_lt_lt_half (h n hn) # h N # by rfl

theorem nat_le_of_forall_lt_apply_succ {σ : ℕ → ℕ} {n}
(h : ∀ n, σ n < σ (n + 1)) : n ≤ σ n := by
  induction n; simp; nm n ih; rw [Nat.succ_le_iff]; exact lt_of_le_of_lt ih # h _

theorem nat_le_of_subseq {σ n} (h : Subseq σ) : n ≤ σ n := by
  apply nat_le_of_forall_lt_apply_succ; intro k; apply h; simp

theorem tendsTo_of_isCauchy_and_subseq_tendsTo {a σ L}
(hσ : Subseq σ) (ha : isCauchy a) (h : tendsTo (a ∘ σ) L) : tendsTo a L := by
  intro e he
  specialize ha (e / 2) # by positivity
  obtain ⟨N₁, ha⟩ := ha
  specialize h (e / 2) # by positivity
  obtain ⟨N₂, h⟩ := h
  use N₁ + N₂
  intro n hn
  have h₁ : N₁ + N₂ ≤ σ (N₁ + N₂) := nat_le_of_subseq hσ
  apply abs_sub_lt_trans_half # a # σ # N₁ + N₂
  · apply ha <;> linarith
  · apply h; linarith

theorem converges_of_isCauchy {a} (h : isCauchy a) : converges a := by
  have h₁ := bounded_of_isCauchy h
  obtain ⟨σ, hσ, L, h₂⟩ := exi_converges_subseq_of_bounded h₁
  use L, tendsTo_of_isCauchy_and_subseq_tendsTo hσ h h₂

theorem isCauchy_iff_converges {a} : isCauchy a ↔ converges a :=
  ⟨converges_of_isCauchy, isCauchy_of_converges⟩

theorem converges_iff_isCauchy {a} : converges a ↔ isCauchy a :=
  isCauchy_iff_converges.symm

theorem le_lub_of_bounded_top {a : ℕ → ℝ} {n : ℕ}
(ha : ∃ m, ∀ n, a n ≤ m) : a n ≤ lub a := by
  obtain ⟨m, ha⟩ := ha; apply le_ciSup; use m
  intro x; simp; rintro i rfl; apply ha

theorem lub_le_of_le {a m} (h : ∀ i, a i ≤ m) : lub a ≤ m := ciSup_le h

theorem exi_lub_sub_lt_of_bounded_top {a : ℕ → ℝ} {ε : ℝ}
(ha : ∃ m, ∀ n, a n ≤ m) (he : 0 < ε) : ∃ n, lub a - a n < ε := by
  replace ha := λ n => le_lub_of_bounded_top (n := n) ha
  by_contra! h₁; replace h₁ : ∀ n, a n ≤ lub a - ε
  intro n; linarith [h₁ n]; linarith [lub_le_of_le h₁]

theorem isCauchy_of_monoLe_and_bounded_top {a}
(h₁ : monoLe a) (h₂ : ∃ M, ∀ n, a n ≤ M) : isCauchy a := by
  rw [isCauchy_iff_alt₁]
  intro e he
  have h₃ := λ n => le_lub_of_bounded_top (n := n) h₂
  obtain ⟨N, h₄⟩ := exi_lub_sub_lt_of_bounded_top h₂ he
  use N
  intro n hN
  have h₅ : a N ≤ a n := h₁ _ _ hN
  rw [abs_of_nonneg # by linarith]
  linarith [h₃ n]

theorem converges_of_monoLe_and_bounded_top {a}
(h₁ : monoLe a) (h₂ : ∃ M, ∀ n, a n ≤ M) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoLe_and_bounded_top h₁ h₂

@[simp]
theorem monoLe_series_abs' {a : ℕ → ℝ} : monoLe # series |a| :=
  monoLe_series_abs

@[simp]
theorem isCauchy_neg {a} : isCauchy (-a) ↔ isCauchy a := by
  simp [isCauchy_iff_converges]

theorem isCauchy_of_monoGe_and_bounded_bottom {a}
(h₁ : monoGe a) (h₂ : ∃ M, ∀ n, M ≤ a n) : isCauchy a := by
  rw [←monoLe_neg] at h₁
  replace h₂ : ∃ M, ∀ n, (-a) n ≤ M
  · dsimp; obtain ⟨M, h₂⟩ := h₂; use -M
    intro n; linarith [h₂ n]
  rw [←isCauchy_neg]
  exact isCauchy_of_monoLe_and_bounded_top h₁ h₂

theorem converges_of_monoGe_and_bounded_bottom {a}
(h₁ : monoGe a) (h₂ : ∃ M, ∀ n, M ≤ a n) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoGe_and_bounded_bottom h₁ h₂

theorem exi_lt_of_monoGe_and_not_converges {a}
(h₁ : monoGe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, a N < L := by
  contrapose! h₂; apply converges_of_monoGe_and_bounded_bottom h₁ ⟨L, h₂⟩

theorem exi_gt_of_monoLe_and_not_converges {a}
(h₁ : monoLe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, L < a N := by
  contrapose! h₂; apply converges_of_monoLe_and_bounded_top h₁ ⟨L, h₂⟩

theorem not_of_lt_mkSubseq_zero {a p n}
(h : n < mkSubseq a p 0) : ¬p (a n) := by
  simp [mkSubseq] at h; exact Nat.find!_min h

theorem not_of_between_mkSubseq {a p k} n (H : Infp a p)
(h₁ : mkSubseq a p n < k) (h₂ : k < mkSubseq a p (n + 1)) : ¬p (a k) := by
  intro h₃
  replace h₃ := exi_mkSubseq_eq_of_apply H h₃
  obtain ⟨k, rfl⟩ := h₃
  rw [subseq_lt_iff subseq_mkSubseq] at h₁ h₂
  omega

theorem filter_range_mkSubseq_succ {a p n} [hp : DecidablePred p] (H : Infp a p) :
(List.range (mkSubseq a p # n + 1) |>.filter (p # a ·)) =
(List.range (mkSubseq a p n) |>.filter (p # a ·)) ++ [mkSubseq a p n] := by
  have h₁ : mkSubseq a p n < mkSubseq a p (n + 1)
  · apply subseq_lt_of_lt subseq_mkSubseq; simp
  obtain ⟨k, h₂⟩ := Nat.exists_eq_add_of_lt h₁
  rw [h₂]; replace h₂ : k + mkSubseq a p n < mkSubseq a p (n + 1); omega
  induction k
  · simp [List.range_succ]; exact mkSubseq_spec H
  nm k ih
  rw [←ih # by omega]; clear ih
  nth_rw 1 [List.range_succ]
  ring_nf; simp
  apply not_of_between_mkSubseq n H <;> omega

theorem tendsTo_zero_of_converges_series {a} (h : converges (series a)) : tendsTo a 0 := by
  choose S h using h
  intro e he
  simp
  unfold eventually
  specialize h (e / 2) (by positivity)
  choose N h using h
  dsimp at h
  use N
  intro n hn
  have h₁ := h n hn
  have h₂:= h (n + 1) (by omega)
  clear h
  rw [series_succ] at h₂
  replace h₂ : |series a n - S + a n| < e / 2; ring_nf at h₂ ⊢; exact h₂
  generalize series a n - S = x at h₁ h₂
  by_contra! h₃
  suffices : e < e; linarith
  calc
  _ ≤ |a n| := h₃
  _ = |a n + x - x| := by simp
  _ ≤ |a n + x| + |x| := by rw [sub_eq_add_neg]; apply abs_add_le _ _ |>.trans; simp
  _ < _ := by rw [add_comm _ x]; linarith

theorem bddBelow_of_converges {a} (h : converges a) : BddBelow (Set.range a) := by
  obtain ⟨L, h⟩ := h
  specialize h 1 (by norm_num)
  simp [bddBelow_range]
  obtain ⟨N, h⟩ := h
  generalize hm : (List.range N |>.map a |>.cons (L - 1) |>.min?.get!) = m
  simp at hm
  use m
  intro i
  cases h₁ : List.map a (List.range N) |>.min? <;> simp [h₁] at hm
  · simp at h₁
    subst h₁ hm
    specialize h i (by simp)
    rw [abs_lt] at h
    linarith
  nm m; subst hm
  simp [List.min?_eq_some_iff₁] at h₁
  rcases h₁ with ⟨⟨j, h₁, rfl⟩, h₂⟩
  by_cases h₃ : i < N
  · exact inf_le_of_right_le # h₂ i h₃
  push_neg at h₃
  specialize h i h₃
  apply inf_le_of_left_le
  rw [abs_lt] at h
  linarith

theorem bddAbove_of_converges {a} (h : converges a) : BddAbove (Set.range a) := by
  replace h : converges (-a); simpa
  replace h := bddBelow_of_converges h
  rwa [←bddBelow_range_neg]

theorem converges_of_tendsTo {a L} (h : tendsTo a L) : converges a := ⟨_, h⟩

theorem le_lub_of_tendsTo {a L} (h : tendsTo a L) :
(∀ i, a i ≤ lub a) ∧ L ≤ lub a := by
  apply and_of
  · intro i; unfold lub
    apply le_ciSup_of_le _ i (by rfl)
    apply bddAbove_of_converges # converges_of_tendsTo h
  intro h₁
  by_contra! h₂
  generalize lub a = m at h₁ h₂
  specialize h (L - m) (by linarith)
  obtain ⟨N, h⟩ := h
  specialize h N (by rfl)
  specialize h₁ N
  rw [abs_lt] at h
  linarith

theorem tendsTo_lub_seq_of_nonneg {a L} (h₁ : tendsTo a L) :
tendsTo (λ n => lub # (a # n + ·)) L := by
  intro e he
  dsimp
  suffices h : eventually # λ n => lub (a # n + · ) - L < e
  · choose N h using h
    use N
    intro n hn
    specialize h n hn
    rwa [abs_of_nonneg]
    simp
    apply le_lub_of_tendsTo _ |>.2
    exact tendsTo_drop_of h₁
  simp_rw [sub_lt_iff_lt_add']
  specialize h₁ (e / 2) (by positivity)
  choose N h₁ using h₁
  use N
  intro n hn
  dsimp at h₁
  simp_rw [abs_sub_lt_iff'] at h₁
  choose h₂ h₁ using h₁; clear h₂
  replace h₁ : ∀ k, (a # n + ·) k < L + e / 2
  · dsimp; intro k; exact h₁ (n + k) (by omega)
  apply lt_of_le_of_lt (b := L + e / 2)
  rotate_left; linarith
  apply csSup_le # Set.range_nonempty _
  simp at h₁ ⊢
  intro k; exact le_of_lt # h₁ k

theorem tendsTo_bounds_of_tendsTo {a L} (h : tendsTo a L) : tendsTo (bounds a) |L| :=
  @tendsTo_lub_seq_of_nonneg |a| |L| # tendsTo_abs h

theorem tendsTo_iff_eps_lt_one {a L} :
tendsTo a L ↔ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (N : ℕ),
∀ (n : ℕ), N ≤ n → |a n - L| < ε := by
  use λ h e h₁ _ => h e h₁
  intro h e he
  specialize h (min e # 1 / 2) (by simpa) (by norm_num)
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  simp at h
  exact h.1

theorem le_of_subseq_le {σ i j} (h₁ : Subseq σ) (h₂ : σ i ≤ σ j) : i ≤ j := by
  contrapose! h₂; exact subseq_lt_of_lt h₁ h₂

theorem subseq_le_iff {σ i j} (h₁ : Subseq σ) : σ i ≤ σ j ↔ i ≤ j :=
  ⟨le_of_subseq_le h₁, subseq_le_of_le h₁⟩

@[simp]
theorem bounds_neg {a} : bounds (-a) = bounds a := by
  ext n; unfold bounds; simp; change lub |-_| = _; rw [abs_neg]

theorem abs_le_bounds_of_tendsTo {a L n} (h : tendsTo a L) : |a n| ≤ bounds a n := by
  apply le_csSup
  · apply bddAbove_of_converges
    apply converges_of_tendsTo (L := |L|)
    apply tendsTo_abs
    exact tendsTo_drop_of h
  simp; use 0; rfl

theorem bounds_le_bounds_of_tendsTo {a L k n}
(h₁ : tendsTo a L) (h₂ : k ≤ n) : bounds a n ≤ bounds a k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₂; clear h₂
  unfold bounds lub iSup
  apply csSup_le_csSup
  · apply bddAbove_of_converges
    apply converges_of_tendsTo (L := |L|)
    apply tendsTo_abs
    exact tendsTo_drop_of h₁
  · apply Set.range_nonempty
  dsimp; intro i; simp; intro j h₂; use n + j; grind

theorem bounds_nonneg_of_tendsTo {a L n} (h : tendsTo a L) : 0 ≤ bounds a n := by
  trans |L|; simp
  replace h := tendsTo_drop_of (k := n) # tendsTo_abs h
  exact le_lub_of_tendsTo h |>.2

theorem series_add {a n k} : series a (n + k) =
series a n + series (a # n + ·) k := by
  simp [series, Finset.sum_range_add]

theorem abs_bounds_of_tendsTo {a L n} (h : tendsTo a L) : |bounds a n| = bounds a n := by
  apply abs_of_nonneg; exact bounds_nonneg_of_tendsTo h

namespace CondConv

variable {a : ℕ → ℝ} (H : CondConv a)
include H

theorem converges_series : converges (series a) := H.1
theorem not_absConv : ¬AbsConv a := H.2

theorem drop {N} : CondConv (a # N + ·) := by
  unfold CondConv at H ⊢; rwa [converges_series_drop_iff, absConv_drop_iff]

omit H in
theorem drop_iff {N} : CondConv (a # N + ·) ↔ CondConv a := by
  unfold CondConv; rw [converges_series_drop_iff, absConv_drop_iff]

omit H in
theorem neg_iff : CondConv (-a) ↔ CondConv a := by
  unfold CondConv; rw [←neg_series', converges_neg, absConv_neg]

theorem infp_pos : Infp a (0 < ·) := by
  intro N
  by_contra! h₃; push_neg at h₃
  generalize hb : (a # N + ·) = b
  have h₄ : CondConv b; rwa [←hb, drop_iff]
  have h₅ : |b| = -b
  · subst hb
    rw [abs_of_nonpos]
    intro n
    apply h₃
    simp
  have h₆ := h₄.1
  have h₇ : ¬converges (series b)
  · rw [←converges_neg, neg_series', ←h₅]; exact h₄.2
  contradiction

theorem infp_neg : Infp a (· < 0) := by
  intro N; rw [←neg_iff] at H
  have h₁ := infp_pos H N
  simp at h₁; exact h₁

theorem infp_nonneg : Infp a (0 ≤ ·) := by
  apply infp_of_imp (infp_pos H); intro n; apply le_of_lt

theorem infp_nonpos : Infp a (· ≤ 0) := by
  apply infp_of_imp (infp_neg H); intro n; apply le_of_lt

omit H in
theorem subseq_σp (a : ℕ → ℝ) : Subseq (σp a) :=
  subseq_mkSubseq

omit H in
theorem subseq_σn (a : ℕ → ℝ) : Subseq (σn a) :=
  subseq_mkSubseq

theorem tendsTo_series : tendsTo (series a) (M a) :=
  tendsTo_limit_of_converges H.converges_series

theorem σp_spec {n : ℕ} : 0 ≤ a n ↔ ∃ k, σp a k = n :=
  apply_iff_exi_mkSubseq_eq H.infp_nonneg

theorem σn_spec {n : ℕ} : a n < 0 ↔ ∃ k, σn a k = n :=
  apply_iff_exi_mkSubseq_eq H.infp_neg

theorem σp_spec' : ∀ n, 0 ≤ a n ↔ ∃ k, σp a k = n :=
  λ _ => H.σp_spec

theorem σn_spec' : ∀ n, a n < 0 ↔ ∃ k, σn a k = n :=
  λ _ => H.σn_spec

theorem ap_nonneg {n : ℕ} : 0 ≤ ap a n :=
  H.σp_spec.mpr ⟨_, rfl⟩

theorem an_neg {n : ℕ} : an a n < 0 :=
  H.σn_spec.mpr ⟨_, rfl⟩

theorem an_nonpos {n : ℕ} : an a n ≤ 0 :=
  le_of_lt H.an_neg

theorem ap_fn_nonneg : 0 ≤ ap a :=
  λ _ => H.ap_nonneg

theorem an_fn_neg : an a < 0 := by
  rw [Pi.lt_def]; use λ _ => H.an_nonpos; use 0, H.an_neg

theorem an_fn_nonpos : an a ≤ 0 :=
  le_of_lt H.an_fn_neg

theorem abs_ap {n} : |ap a n| = ap a n :=
  abs_of_nonneg H.ap_nonneg

theorem abs_an {n} : |an a n| = -an a n :=
  abs_of_neg H.an_neg

theorem abs_ap_fn : |ap a| = ap a :=
  abs_of_nonneg # H.ap_fn_nonneg

theorem abs_an_fn : |an a| = -an a :=
  abs_of_neg # H.an_fn_neg

theorem series_ap_nonneg {n : ℕ} : 0 ≤ series (ap a) n :=
  Finset.sum_nonneg # λ _ _ => H.ap_nonneg

theorem series_an_nonpos {n : ℕ} : series (an a) n ≤ 0 :=
  Finset.sum_nonpos # λ _ _ => H.an_nonpos

theorem series_ap_fn_nonneg : 0 ≤ series (ap a) :=
  λ _ => H.series_ap_nonneg

theorem series_an_fn_nonpos : series (an a) ≤ 0 :=
  λ _ => H.series_an_nonpos

theorem exi_fgCnd {F} : ∃ f g, fgCnd F a f g := by
  obtain ⟨f, g, hfg, hf, hg, Hf, Hg, Hfg⟩ :=
    exi_fn_series_of_subseq_cover (F := F) (subseq_σp a) (subseq_σn a)
    H.σp_spec' # by simp; exact H.σn_spec'
  use f, g, hfg, hf, hg, Hf H.infp_nonneg, Hg # by simp [H.infp_neg], Hfg

theorem fgCnd_fAux_gAux {F} : fgCnd F a (fAux F a) (gAux F a) :=
  Classical.epsilon_spec # Classical.epsilon_spec H.exi_fgCnd

theorem fAux_add_gAux {F n} : fAux F a n + gAux F a n = n :=
  H.fgCnd_fAux_gAux.1 n

theorem fAux_le_of_le {F i j} (h : i ≤ j) : fAux F a i ≤ fAux F a j :=
  H.fgCnd_fAux_gAux.2.1 i j h

theorem gAux_le_of_le {F i j} (h : i ≤ j) : gAux F a i ≤ gAux F a j :=
  H.fgCnd_fAux_gAux.2.2.1 i j h

theorem exi_fAux_ge {F n} : ∃ k, n ≤ fAux F a k :=
  H.fgCnd_fAux_gAux.2.2.2.1 n

theorem exi_gAux_ge {F n} : ∃ k, n ≤ gAux F a k :=
  H.fgCnd_fAux_gAux.2.2.2.2.1 n

theorem series_eq_fAux_add_gAux {F n} : series (F # a ·) n =
series (F # ap a ·) (fAux F a n) + series (F # an a ·) (gAux F a n) :=
  H.fgCnd_fAux_gAux.2.2.2.2.2 n

theorem fgCnd_f_g : fgCnd id a (f a) (g a) :=
  H.fgCnd_fAux_gAux

theorem f_add_g {n} : f a n + g a n = n :=
  H.fAux_add_gAux

theorem f_le_of_le {i j} (h : i ≤ j) : f a i ≤ f a j :=
  H.fAux_le_of_le h

theorem g_le_of_le {i j} (h : i ≤ j) : g a i ≤ g a j :=
  H.gAux_le_of_le h

theorem exi_f_ge {n} : ∃ k, n ≤ f a k :=
  H.exi_fAux_ge

theorem exi_g_ge {n} : ∃ k, n ≤ g a k :=
  H.exi_gAux_ge

theorem series_eq_f_add_g {n} : series a n =
series (ap a) (f a n) + series (an a) (g a n) := by
  convert H.series_eq_fAux_add_gAux <;> rfl

theorem fgCnd_f'_g' : fgCnd abs a (f' a) (g' a) :=
  H.fgCnd_fAux_gAux

theorem f'_add_g' {n} : f' a n + g' a n = n :=
  H.fAux_add_gAux

theorem f'_le_of_le {i j} (h : i ≤ j) : f' a i ≤ f' a j :=
  H.fAux_le_of_le h

theorem g'_le_of_le {i j} (h : i ≤ j) : g' a i ≤ g' a j :=
  H.gAux_le_of_le h

theorem exi_f'_ge {n} : ∃ k, n ≤ f' a k :=
  H.exi_fAux_ge

theorem exi_g'_ge {n} : ∃ k, n ≤ g' a k :=
  H.exi_gAux_ge

theorem series_eq_f'_add_g' {n} : series |a| n =
series |ap a| (f' a n) + series |an a| (g' a n) :=
  H.series_eq_fAux_add_gAux (F := abs)

theorem monoLe_series_ap : monoLe # series # ap a :=
  monoLe_series_of_nonneg H.ap_fn_nonneg

theorem monoGt_series_an : monoGt # series # an a :=
  monoGt_series_of_neg # λ _ => H.an_neg

theorem monoGe_series_an : monoGe # series # an a :=
  monoGe_of_monoGt H.monoGt_series_an

theorem not_converges_series_ap_or_an :
¬converges (series # ap a) ∨ ¬converges (series # an a) := by
  rw [←not_and_iff_or]
  rintro ⟨⟨X, h₇⟩, ⟨Y', h₈⟩⟩
  generalize hY : -Y' = Y
  rw [neg_eq_iff_eq_neg] at hY
  subst hY
  have hX : 0 ≤ X := le_limit_of_forall_le h₇ H.series_ap_fn_nonneg
  have hY : 0 ≤ Y
  · suffices : -Y ≤ 0; linarith
    exact limit_le_of_forall_le h₈ H.series_an_fn_nonpos
  have h₉ : ∀ n, series |a| n ≤ X + Y
  · intro n
    have H₁ : monoLe # series |an a|
    · apply monoLe_series_abs
    have H₂ : tendsTo |series # an a| Y
    · rw [show Y = |-Y| by rw [abs_neg, abs_of_nonneg hY]]
      exact tendsTo_abs h₈
    have H₃ : ∀ n, series |ap a| n ≤ X
    · rw [H.abs_ap_fn]; exact le_limit_of_monoLe H.monoLe_series_ap h₇
    have H₄ : ∀ n, series |an a| n ≤ Y
    · rw [H.abs_an_fn]; intro k
      rw [←neg_series']; apply neg_le_of_neg_le
      apply limit_le_of_monoGe H.monoGe_series_an h₈
    rw [H.series_eq_f'_add_g']
    linarith [H₃ (f' a n), H₄ (g' a n)]
  have H₁ : converges # series |a|
  · apply converges_of_monoLe_and_bounded_top # by simp
    use X + Y, h₉
  exact H.not_absConv H₁

theorem not_converges_series_ap : ¬converges (series # ap a) := by
  have h₇ := H.not_converges_series_ap_or_an
  by_contra h₈
  simp [h₈] at h₇
  choose X h₈ using h₈
  have H₁ : 0 ≤ X := le_limit_of_forall_le h₈ H.series_ap_fn_nonneg
  obtain ⟨N₁, hN₁⟩ := exi_lt_of_monoGe_and_not_converges
    H.monoGe_series_an h₇ # M a - (X + 1)
  have h₁ := H.tendsTo_series
  specialize h₁ 1 # by norm_num
  choose N₃ h₁ using h₁
  obtain ⟨N₂, hN₂⟩ := H.exi_g_ge (n := N₁ + N₃)
  replace hN₁ : series (an a) (g a N₂) < M a - (X + 1)
  · apply lt_of_le_of_lt _ hN₁; apply H.monoGe_series_an; omega
  have H₃ : ∀ n, series (ap a) n ≤ X
  · intro n; apply le_limit_of_monoLe H.monoLe_series_ap h₈
  have H₄ : g a N₂ ≤ N₂
  · have := H.f_add_g (n := N₂); omega
  specialize h₁ N₂ # by linarith
  rw [abs_sub_lt_iff'] at h₁
  replace h₁ := h₁.1
  rw [H.series_eq_f_add_g] at h₁
  contrapose! h₁; clear h₁
  suffices : series (ap a) (f a N₂) ≤ (X + 1) - 1; linarith
  apply H₃ _ |>.trans; linarith

theorem not_converges_series_an : ¬converges (series # an a) := by
  by_contra h₈
  choose Y' h₈ using h₈
  generalize hY : -Y' = Y
  rw [neg_eq_iff_eq_neg] at hY
  subst hY
  have H₁ : 0 ≤ Y
  · suffices : -Y ≤ 0; linarith
    apply limit_le_of_forall_le h₈ H.series_an_fn_nonpos
  obtain ⟨N₁, hN₁⟩ := exi_gt_of_monoLe_and_not_converges
    H.monoLe_series_ap H.not_converges_series_ap # M a + (Y + 1)
  choose N₃ h₁ using H.tendsTo_series 1 # by norm_num
  obtain ⟨N₂, hN₂⟩ := H.exi_f_ge (n := N₁ + N₃)
  replace hN₁ : M a + (Y + 1) < series (ap a) (f a N₂)
  · apply lt_of_lt_of_le hN₁; apply H.monoLe_series_ap; omega
  have H₃ : ∀ n, -Y ≤ series (an a) n
  · intro n; apply limit_le_of_monoGe H.monoGe_series_an h₈
  have H₄ : f a N₂ ≤ N₂
  · have := H.f_add_g (n := N₂); omega
  specialize h₁ N₂ # by linarith
  rw [abs_sub_lt_iff'] at h₁
  replace h₁ := h₁.2
  rw [H.series_eq_f_add_g] at h₁
  contrapose! h₁; clear h₁
  suffices : 1 - (Y + 1) ≤ series (an a) (g a N₂); linarith
  apply H₃ _ |>.trans'; linarith

theorem exi_ap_gt L : ∃ n, L < series (ap a) n :=
  exi_gt_of_monoLe_and_not_converges H.monoLe_series_ap H.not_converges_series_ap L

theorem exi_an_lt L : ∃ n, series (an a) n < L :=
  exi_lt_of_monoGe_and_not_converges H.monoGe_series_an H.not_converges_series_an L

omit H in
theorem neg_of_lt_σp_zero {n} (h : n < σp a 0) : a n < 0 := by
  linarith [not_of_lt_mkSubseq_zero h]

omit H in
theorem nonneg_of_lt_σn_zero {n} (h : n < σn a 0) : 0 ≤ a n := by
  linarith [not_of_lt_mkSubseq_zero h]

theorem sum_map_filter_range_σp {n} :
(List.range (σp a n) |>.filter (0 ≤ a ·) |>.map a).sum = series (ap a) n := by
  induction n
  · simp; convert List.sum_nil; simp; exact λ _ => neg_of_lt_σp_zero
  nm n ih; simp [series_succ, ←ih]; unfold ap σp
  simp [filter_range_mkSubseq_succ H.infp_nonneg]

theorem sum_map_filter_range_σn {n} :
(List.range (σn a n) |>.filter (a · < 0) |>.map a).sum = series (an a) n := by
  induction n
  · simp; convert List.sum_nil; simp; exact λ _ => nonneg_of_lt_σn_zero
  nm n ih; simp [series_succ, ←ih]; unfold an σn
  simp [filter_range_mkSubseq_succ H.infp_neg]

theorem exi_ap_map_range_gt L :
∃ n, L < (List.range n |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  choose n h₁ using H.exi_ap_gt L; use σp a n; rwa [H.sum_map_filter_range_σp]

theorem exi_an_map_range_lt L :
∃ n, (List.range n |>.filter (a · < 0) |>.map a |>.sum) < L := by
  choose n h₁ using H.exi_an_lt L; use σn a n; rwa [H.sum_map_filter_range_σn]

theorem tendsTo_zero : tendsTo a 0 :=
  tendsTo_zero_of_converges_series H.converges_series

theorem bounds_tendsTo_zero : tendsTo (bounds a) 0 := by
  rw [←abs_zero]; exact tendsTo_bounds_of_tendsTo H.tendsTo_zero

theorem exi_ap_map_range_drop_gt L k :
∃ n, L < (List.range n |>.map (k + ·) |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  replace H := H.drop (N := k)
  choose n h₁ using H.exi_ap_map_range_gt L
  use n
  convert h₁ using 2
  clear h₁
  induction n
  · rfl
  nm n ih
  simp [List.range_succ]
  rw [ih]; clear ih
  grind

theorem exi_an_map_range_drop_lt L k :
∃ n, (List.range n |>.map (k + ·) |>.filter (a · < 0) |>.map a |>.sum) < L := by
  replace H := H.drop (N := k)
  choose n h₁ using H.exi_an_map_range_lt L
  use n
  convert h₁ using 2
  clear h₁
  induction n
  · rfl
  nm n ih
  simp [List.range_succ]
  rw [ih]; clear ih
  grind

theorem exi_add_ap_map_range_drop_gt s L k :
∃ n, L < s + (List.range n |>.map (k + ·) |>.filter (0 ≤ a ·) |>.map a |>.sum) := by
  simp_rw [←sub_lt_iff_lt_add']; apply H.exi_ap_map_range_drop_gt

theorem exi_add_an_map_range_drop_lt s L k :
∃ n, s + (List.range n |>.map (k + ·) |>.filter (a · < 0) |>.map a |>.sum) < L := by
  simp_rw [←lt_sub_iff_add_lt']; apply H.exi_an_map_range_drop_lt

end CondConv

def Rment (σ : ℕ → ℕ) : Prop :=
  σ.Bijective

noncomputable
def rinv (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon $ λ k => σ k = n

noncomputable
def mkRmentP (a : ℕ → ℝ) (is : List ℕ) : ℕ :=
  Nat.find! $ λ i => i ∉ is ∧ 0 ≤ a i

noncomputable
def mkRmentN (a : ℕ → ℝ) (is : List ℕ) : ℕ :=
  Nat.find! $ λ j => j ∉ is ∧ a j < 0

noncomputable
def mkRmentList1 (a : ℕ → ℝ) (is : List ℕ) : List ℕ :=
  is ++ [mkRmentP a is, mkRmentN a is]

noncomputable
def mkRmentSum (a : ℕ → ℝ) (is : List ℕ) : ℝ :=
  is.map a |>.sum

def mkRmentLeNCnd (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (N : ℕ) : Prop :=
  0 ≤ a N ∧ ∀ r, N ≤ r → 0 ≤ a r → r ∉ is ∧ a r < 1 / (n + 2)

def mkRmentGeNCnd (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (N : ℕ) : Prop :=
  a N < 0 ∧ ∀ r, N ≤ r → a r < 0 → r ∉ is ∧ -1 / (n + 2) < a r

noncomputable
def mkRmentLeN (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! $ mkRmentLeNCnd a n is

noncomputable
def mkRmentGeN (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! $ mkRmentGeNCnd a n is

noncomputable
def mkRmentLeF (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : List ℕ :=
  List.range k |>.map (mkRmentLeN a n is + ·) |>.filter (0 ≤ a ·)

noncomputable
def mkRmentGeF (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : List ℕ :=
  List.range k |>.map (mkRmentGeN a n is + ·) |>.filter (a · < 0)

def mkRmentLeKCnd (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : Prop :=
  L - 1 / (n + 2) < mkRmentSum a is + (mkRmentLeF a n is k |>.map a |>.sum)

def mkRmentGeKCnd (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : Prop :=
  mkRmentSum a is + (mkRmentGeF a n is k |>.map a |>.sum) < L + 1 / (n + 2)

noncomputable
def mkRmentLeK (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! $ mkRmentLeKCnd a L n is

noncomputable
def mkRmentGeK (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! $ mkRmentGeKCnd a L n is

noncomputable
def mkRmentLe (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  mkRmentLeF a n is $ mkRmentLeK a L n is

noncomputable
def mkRmentGe (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  mkRmentGeF a n is $ mkRmentGeK a L n is

noncomputable
def mkRmentIte (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  is ++ if mkRmentSum a is ≤ L - 1 / (n + 2) then mkRmentLe a L n is
  else if L + 1 / (n + 2) ≤ mkRmentSum a is then mkRmentGe a L n is
  else []

noncomputable
def mkRmentList (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n + 1 => mkRmentIte a L n $ mkRmentList1 a $ mkRmentList a L n

noncomputable
def mkRment (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  (mkRmentList a L (n + 1))[n]!

noncomputable
def mkRmentLen (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  mkRmentList a L n |>.length

-----

theorem rment_eq_iff {σ n m} (h : Rment σ) : σ n = σ m ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁; exact h.1 h₁

theorem rinv_cancel_left {σ n} (h : Rment σ) : rinv σ (σ n) = n := by
  simp [rinv, rment_eq_iff h]

theorem rinv_cancel_right {σ n} (h : Rment σ) : σ (rinv σ n) = n := by
  unfold rinv
  apply Classical.epsilon_spec (p := λ k => σ k = n)
  apply h.2

theorem rment_rinv {σ} (h : Rment σ) : Rment (rinv σ) := by
  constructor
  · intro n m h₁
    replace h₁ := congrArg σ h₁
    simp_rw [rinv_cancel_right h] at h₁
    exact h₁
  · intro n
    use σ n
    rw [rinv_cancel_left h]

theorem tendsTo_rment_of {a σ L} (h₁ : Rment σ)
(h₂ : tendsTo a L) : tendsTo (a $ σ ·) L := by
  intro e he
  dsimp
  specialize h₂ e he
  choose N h₂ using h₂
  dsimp at h₂
  use ∑ i ∈ Finset.range N, rinv σ i + 1
  intro n hn
  apply h₂; clear h₂
  by_contra! h₃
  have h₄ : rinv σ (σ n) ≤ ∑ i ∈ Finset.range N, rinv σ i
  · apply Finset.le_sum_of_mem <;> simp [h₃]
  rw [rinv_cancel_left h₁] at h₄
  omega

theorem tendsTo_rment_iff {a σ L} (h₁ : Rment σ) :
tendsTo (a $ σ ·) L ↔ tendsTo a L := by
  symm; use tendsTo_rment_of h₁
  intro h₂
  replace h₂ := tendsTo_rment_of (rment_rinv h₁) h₂
  simp_rw [rinv_cancel_right h₁] at h₂
  exact h₂

theorem converges_rment_of {a σ} (h₁ : Rment σ)
(h₂ : converges a) : converges (a $ σ ·) := by
  choose L h₂ using h₂; use L, tendsTo_rment_of h₁ h₂

theorem converges_rment_iff {a σ} (h₁ : Rment σ) :
converges (a $ σ ·) ↔ converges a := by
  apply exists_congr; simp [tendsTo_rment_iff h₁]

@[simp]
theorem le_length_mkRmentList {a L n} : n ≤ (mkRmentList a L n).length := by
  induction n; simp; unfold mkRmentList mkRmentIte mkRmentList1; grind

@[simp]
theorem le_mkRmentLen {a L n} : n ≤ mkRmentLen a L n :=
  le_length_mkRmentList

theorem mkRmentList_prefix {a L k n} (h : k ≤ n) : mkRmentList a L k <+: mkRmentList a L n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n; rfl; rw [Nat.add_succ, mkRmentList]
  unfold mkRmentList1 mkRmentIte; grind

theorem getElem!_mkRmentList_eq_getElem {a L n k} (h : k < n) :
(mkRmentList a L n)[k]! = (mkRmentList a L n)[k]'(lt_of_lt_of_le h $ by simp) := by
  rw [List.getElem!_eq_getElem]

@[simp]
theorem lt_length_mkRmentList_succ {a L n} : n < (mkRmentList a L (n + 1)).length := by
  apply lt_of_lt_of_le (b := n + 1) <;> simp

@[simp]
theorem lt_mkRmentLen_succ {a L n} : n < mkRmentLen a L (n + 1) :=
  lt_length_mkRmentList_succ

theorem mkRment_eq_getElem {a L n} :
mkRment a L n = (mkRmentList a L (n + 1))[n]'(by simp) := by
  rw [mkRment, getElem!_mkRmentList_eq_getElem]; simp

theorem getElem_mkRmentList_eq_of_lt {a L n m k} (h₁ : k < n) (h₂ : k < m) :
(mkRmentList a L n)[k]'(lt_of_lt_of_le h₁ $ by simp) =
(mkRmentList a L m)[k]'(lt_of_lt_of_le h₂ $ by simp) := by
  wlog h₃ : n < m; grind; apply List.IsPrefix.getElem $ mkRmentList_prefix $ le_of_lt h₃

theorem getElem!_mkRmentList_eq_of_lt {a L n m k} (h₁ : k < n) (h₂ : k < m) :
(mkRmentList a L n)[k]! = (mkRmentList a L m)[k]! := by
  rw [getElem!_mkRmentList_eq_getElem h₁, getElem!_mkRmentList_eq_getElem h₂]
  exact getElem_mkRmentList_eq_of_lt h₁ h₂

theorem mkRmentP_spec' {a is} (H : CondConv a) :
(mkRmentP a is ∉ is ∧ 0 ≤ a (mkRmentP a is)) ∧ ∀ k, k ∉ is ∧ 0 ≤ a k → mkRmentP a is ≤ k := by
  apply Nat.find!_spec' (p := λ i => i ∉ is ∧ 0 ≤ a i)
  choose n h₁ h₂ using H.infp_nonneg $ is.sum + 1
  refine ⟨n, ?_, h₂⟩
  intro h₃
  replace h₄ := List.le_sum_of_mem h₃
  omega

theorem mkRmentN_spec' {a is} (H : CondConv a) :
(mkRmentN a is ∉ is ∧ a (mkRmentN a is) < 0) ∧ ∀ k, k ∉ is ∧ a k < 0 → mkRmentN a is ≤ k := by
  apply Nat.find!_spec' (p := λ i => i ∉ is ∧ a i < 0)
  choose n h₁ h₂ using H.infp_neg $ is.sum + 1
  refine ⟨n, ?_, h₂⟩
  intro h₃
  replace h₄ := List.le_sum_of_mem h₃
  omega

theorem mkRmentP_spec {a is} (H : CondConv a) :
mkRmentP a is ∉ is ∧ 0 ≤ a (mkRmentP a is) := mkRmentP_spec' H |>.1

theorem mkRmentN_spec {a is} (H : CondConv a) :
mkRmentN a is ∉ is ∧ a (mkRmentN a is) < 0 := mkRmentN_spec' H |>.1

@[simp]
theorem mem_mkRmentList_succ {a L n} : n ∈ mkRmentList a L (n + 1) := by
  induction n using Nat.strong_induction_on
  nm n ih
  by_cases h₁ : n ∈ mkRmentList a L n
  · apply List.IsPrefix.mem h₁
    apply mkRmentList_prefix
    simp
  unfold mkRmentList
  generalize h_is : mkRmentList a L n = is at h₁ ⊢
  apply List.mem_append_left
  apply List.mem_append_right
  simp
  have h₂ : ∀ k < n, k ∈ is
  · intro k hk
    specialize ih k hk
    apply List.IsPrefix.mem ih
    rw [←h_is]
    apply mkRmentList_prefix
    omega
  simp_rw [eq_comm (a := n)]
  by_cases h₃ : 0 ≤ a n
  · rw [mkRmentP, Nat.find!_eq_iff, if_pos ⟨n, by grind⟩]; grind
  · rw [mkRmentN, Nat.find!_eq_iff, if_pos ⟨n, by grind⟩]; grind

theorem getElem_mkRmentList_of_le.proof₁ {a L n₁ n₂ k} (h₁ : n₁ ≤ n₂)
(h₂ : k < (mkRmentList a L n₁).length) : k < (mkRmentList a L n₂).length :=
  lt_of_lt_of_le h₂ $ List.IsPrefix.length_le $ mkRmentList_prefix h₁

theorem getElem_mkRmentList_of_le {a L n₁ n₂ k} {hh : k < (mkRmentList a L n₁).length}
(h : n₁ ≤ n₂) : (mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k]'
(getElem_mkRmentList_of_le.proof₁ h hh) := by
  apply List.IsPrefix.getElem $ mkRmentList_prefix h

theorem getElem_mkRmentList_eq {a L n₁ n₂ k}
{hh₁ : k < (mkRmentList a L n₁).length} {hh₂ : k < (mkRmentList a L n₂).length} :
(mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k] := by
  rcases lt_trichotomy n₁ n₂ with h₁ | rfl | h₁; on_goal 2 => rfl
  · exact getElem_mkRmentList_of_le $ le_of_lt h₁
  · exact getElem_mkRmentList_of_le (le_of_lt h₁) |>.symm

@[simp]
theorem getElem_mkRmentList_eq_iff_true {a L n₁ n₂ k}
{hh₁ : k < (mkRmentList a L n₁).length} {hh₂ : k < (mkRmentList a L n₂).length} :
(mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k] ↔ True := by
  simp; exact getElem_mkRmentList_eq

@[simp]
theorem mkRmentList_zero {a L} : mkRmentList a L 0 = [] := rfl

theorem mkRmentP_notMem {a is} (H : CondConv a) : mkRmentP a is ∉ is :=
  mkRmentP_spec H |>.1

theorem mkRmentN_notMem {a is} (H : CondConv a) : mkRmentN a is ∉ is :=
  mkRmentN_spec H |>.1

theorem mkRmentP_nonneg {a is} (H : CondConv a) : 0 ≤ a (mkRmentP a is) :=
  mkRmentP_spec H |>.2

theorem mkRmentN_neg {a is} (H : CondConv a) : a (mkRmentN a is) < 0 :=
  mkRmentN_spec H |>.2

theorem mkRmentP_ne_mkRmentN {a is} (H : CondConv a) : mkRmentP a is ≠ mkRmentN a is := by
  have := @mkRmentP_nonneg a is H; have := @mkRmentN_neg a is H; grind

@[simp]
theorem nodup_mkRmentLe {a L n is} : (mkRmentLe a L n is).Nodup := by
  unfold mkRmentLe mkRmentLeF
  rw [←List.filterMap_eq_filter, List.filterMap_map]
  simp; rw [List.nodup_filterMap_iff]; grind

@[simp]
theorem nodup_mkRmentGe {a L n is} : (mkRmentGe a L n is).Nodup := by
  unfold mkRmentGe mkRmentGeF
  rw [←List.filterMap_eq_filter, List.filterMap_map]
  simp; rw [List.nodup_filterMap_iff]; grind

theorem mkRmentLeK_spec' {a L n is} (H : CondConv a) :
mkRmentLeKCnd a L n is (mkRmentLeK a L n is) ∧
∀ k, mkRmentLeKCnd a L n is k → mkRmentLeK a L n is ≤ k :=
  Nat.find!_spec' $ H.exi_add_ap_map_range_drop_gt _ _ _

theorem mkRmentGeK_spec' {a L n is} (H : CondConv a) :
mkRmentGeKCnd a L n is (mkRmentGeK a L n is) ∧
∀ k, mkRmentGeKCnd a L n is k → mkRmentGeK a L n is ≤ k :=
  Nat.find!_spec' $ H.exi_add_an_map_range_drop_lt _ _ _

theorem mkRmentLeK_spec {a L n is} (H : CondConv a) : L - 1 / (n + 2) < mkRmentSum a is +
(mkRmentLeF a n is (mkRmentLeK a L n is) |>.map a |>.sum) :=
  mkRmentLeK_spec' H |>.1

theorem mkRmentGeK_spec {a L n is} (H : CondConv a) : mkRmentSum a is +
(mkRmentGeF a n is (mkRmentGeK a L n is) |>.map a |>.sum) < L + 1 / (n + 2) :=
  mkRmentGeK_spec' H |>.1

theorem mkRmentLeN_spec' {a n is} (H : CondConv a) :
mkRmentLeNCnd a n is (mkRmentLeN a n is) ∧
∀ k, mkRmentLeNCnd a n is k → mkRmentLeN a n is ≤ k := by
  apply Nat.find!_spec'
  generalize hN₁ : is.sum + 1 = N₁
  choose N₂ h₁ using tendsTo_zero_of_converges_series H.converges_series
    (1 / (n + 2)) (by subst hN₁; positivity)
  simp at h₁
  choose N₃ h₂ h₃ using H.infp_nonneg (N₁ + N₂)
  use N₃, h₃
  intro r hr h₄
  split_ands
  · intro h₅
    replace h₅ := List.le_sum_of_mem h₅
    omega
  specialize h₁ r (by omega)
  rw [abs_of_nonneg h₄] at h₁
  apply lt_of_lt_of_le h₁
  simp

theorem mkRmentGeN_spec' {a n is} (H : CondConv a) :
mkRmentGeNCnd a n is (mkRmentGeN a n is) ∧
∀ k, mkRmentGeNCnd a n is k → mkRmentGeN a n is ≤ k := by
  apply Nat.find!_spec'
  generalize hN₁ : is.sum + 1 = N₁
  choose N₂ h₁ using tendsTo_zero_of_converges_series H.converges_series
    (1 / (n + 2)) (by subst hN₁; positivity)
  simp at h₁
  choose N₃ h₂ h₃ using H.infp_neg (N₁ + N₂)
  use N₃, h₃
  intro r hr h₄
  split_ands
  · intro h₅
    replace h₅ := List.le_sum_of_mem h₅
    omega
  specialize h₁ r (by omega)
  rw [abs_of_neg h₄, neg_lt] at h₁
  apply lt_of_le_of_lt _ h₁
  field_simp
  rfl

theorem mkRmentLeN_spec {a n is} (H : CondConv a) : 0 ≤ a (mkRmentLeN a n is) ∧
∀ r, mkRmentLeN a n is ≤ r → 0 ≤ a r → r ∉ is ∧ a r < 1 / (n + 2) :=
  mkRmentLeN_spec' H |>.1

theorem mkRmentGeN_spec {a n is} (H : CondConv a) : a (mkRmentGeN a n is) < 0 ∧
∀ r, mkRmentGeN a n is ≤ r → a r < 0 → r ∉ is ∧ -1 / (n + 2) < a r :=
  mkRmentGeN_spec' H |>.1

theorem notMem_mkRmentLe_of_mem {a L n is i} (H : CondConv a)
(h : i ∈ is) : i ∉ mkRmentLe a L n is := by
  simp [mkRmentLe, mkRmentLeF]
  rintro k h₁ rfl
  have h₂ := @mkRmentLeN_spec a n is H |>.2 (mkRmentLeN a n is + k) (by omega)
  simp [h] at h₂; exact h₂

theorem notMem_mkRmentGe_of_mem {a L n is i} (H : CondConv a)
(h : i ∈ is) : i ∉ mkRmentGe a L n is := by
  simp [mkRmentGe, mkRmentGeF]
  rintro k h₁ rfl
  have h₂ := @mkRmentGeN_spec a n is H |>.2 (mkRmentGeN a n is + k) (by omega)
  simp [h] at h₂; exact h₂

theorem nodup_mkRmentList {a L n} (H : CondConv a) : (mkRmentList a L n).Nodup := by
  induction n; simp
  nm n ih
  unfold mkRmentList
  generalize h₁ : mkRmentList a L n = is at ih ⊢
  unfold mkRmentList1
  have h₂ := @mkRmentP_notMem a is H
  have h₃ := @mkRmentN_notMem a is H
  generalize h₄ : is ++ [mkRmentP a is, mkRmentN a is] = is₁
  unfold mkRmentIte
  rw [List.nodup_append]
  apply and_of
  · subst h₄
    rw [List.nodup_append]
    use ih
    simp [mkRmentP_ne_mkRmentN H]
    intro i hi
    split_ands
    · contrapose! hi
      subst hi
      exact mkRmentP_notMem H
    · contrapose! hi
      subst hi
      exact mkRmentN_notMem H
  intro h₅
  split_ifs with h₆ h₇ <;> simp <;> intro i
  · exact notMem_mkRmentLe_of_mem H
  · exact notMem_mkRmentGe_of_mem H

theorem mkRment_eq_iff {a L i j} (H : CondConv a) : mkRment a L i = mkRment a L j ↔ i = j := by
  symm; constructor; rintro rfl; rfl; intro h
  by_contra! h₁
  wlog h₂ : i < j with ih
  · push_neg at h₂; apply ih H h.symm $ ne_symm' h₁; grind
  clear h₁
  simp_rw [mkRment_eq_getElem] at h
  have h₃ : i + 1 ≤ j + 1; omega
  rw [getElem_mkRmentList_of_le h₃] at h
  have h₄ := List.eq_of_getElem_and_nodup h $ nodup_mkRmentList H
  omega

theorem rment_mkRment {a L} (h : CondConv a) : Rment (mkRment a L) := by
  constructor
  · intro i j h₁; rw [mkRment_eq_iff h] at h₁; exact h₁
  intro j
  simp_rw [mkRment_eq_getElem]
  change ∃ i, _
  suffices h : ∃ i, (mkRmentList a L (j + i + 1))[i]'
    (by apply lt_of_lt_of_le (b := j + i + 1) (by omega) (by simp)) = j
  · obtain ⟨i, h⟩ := h
    use i
    convert h using 1
    rw [getElem_mkRmentList_eq_of_lt] <;> omega
  suffices h : ∃ (i : ℕ) (h : _), (mkRmentList a L (j + 1))[i]'h = j
  · choose i h₁ h₂ using h
    use i
    convert h₂ using 1
    symm
    apply List.IsPrefix.getElem
    apply mkRmentList_prefix
    omega
  rw [←List.mem_iff_getElem]
  simp

theorem series_mkRment_eq_sum {a L n} :
series (λ i => a $ mkRment a L i) n = (mkRmentList a L n |>.take n |>.map a |>.sum) := by
  simp [mkRment_eq_getElem, series]
  induction n
  · simp
  nm n ih
  simp
  rw [Finset.sum_range_succ, ih]; clear ih
  simp
  congr 1
  have h₁ : mkRmentList a L n <+: mkRmentList a L (n + 1)
  · apply mkRmentList_prefix
    simp
  obtain ⟨ys, h₁⟩ := h₁
  rw [←h₁]
  clear h₁
  simp

theorem take_length_mkRmentList {a L n is} (h : mkRmentList a L n = is) :
(mkRmentList a L is.length).take is.length = is := by
  generalize h₁ : mkRmentList a L is.length = is₁
  have h₂ : n ≤ is.length
  · simp [←h]
  have h₃ : is <+: is₁
  · subst h h₁; exact mkRmentList_prefix h₂
  obtain ⟨xs, rfl⟩ := h₃
  simp

@[simp]
theorem take_mkRmentLen_mkRmentList {a L n} :
(mkRmentList a L $ mkRmentLen a L n).take (mkRmentLen a L n) = mkRmentList a L n :=
  take_length_mkRmentList rfl

@[simp]
theorem mkRmentLeF_zero {a n is} : mkRmentLeF a n is 0 = [] := rfl

@[simp]
theorem mkRmentGeF_zero {a n is} : mkRmentGeF a n is 0 = [] := rfl

theorem abs_map_sum_mkRmentLe_sub_lt {a L is} {n : ℕ} (H : CondConv a)
(h₁ : mkRmentSum a is ≤ L - (n + 2 : ℝ)⁻¹) :
|(is.map a |>.sum) + (mkRmentLe a L n is |>.map a |>.sum) - L| ≤ (n + 2 : ℝ)⁻¹ := by
  rw [←mkRmentSum, mkRmentLe]
  generalize hs : (mkRmentLeF a n is (mkRmentLeK a L n is) |>.map a).sum = s
  generalize hk : mkRmentLeK a L n is = k at hs
  choose h₂ h₃ using @mkRmentLeK_spec' a L n is H
  simp [mkRmentLeKCnd, hk, hs] at h₂
  rw [hk] at h₃
  change ∀ r, _ at h₃
  generalize hd : (n + 2 : ℝ)⁻¹ = d at h₁ h₂ ⊢
  generalize hs₀ : mkRmentSum a is = s₀ at h₁ ⊢
  have hd₁ : 0 < d; subst hd; positivity
  suffices h : L - d ≤ s₀ + s ∧ s₀ + s ≤ L
  · rw [abs_sub_le_iff]; split_ands <;> linarith
  split_ands; linarith
  rw [hs₀] at h₂
  cases k
  · simp at hs; linarith
  nm k
  specialize h₃ k
  simp [mkRmentLeKCnd, hs₀] at h₃
  simp [mkRmentLeF, List.range_succ] at hs
  rw [←mkRmentLeF] at hs
  generalize hs' : (mkRmentLeF a n is k |>.map a |>.sum) = s' at h₃ hs
  rw [hd] at h₃
  simp [List.filter_cons] at hs
  choose h₄ h₅ h₆ using @mkRmentLeN_spec a n is H
  generalize hN : mkRmentLeN a n is = N at hs h₄ h₅ h₆
  split_ifs at hs with h₇
  rotate_left
  · simp at hs; linarith
  suffices h : a (N + k) ≤ d
  · simp at hs; linarith
  specialize h₆ (N + k) (by omega) h₇
  simp [hd] at h₆
  exact le_of_lt h₆

theorem abs_map_sum_mkRmentGe_sub_lt {a L is} {n : ℕ} (H : CondConv a)
(h₁ : L + (n + 2 : ℝ)⁻¹ ≤ mkRmentSum a is) :
|(is.map a |>.sum) + (mkRmentGe a L n is |>.map a |>.sum) - L| ≤ (n + 2 : ℝ)⁻¹ := by
  rw [←mkRmentSum, mkRmentGe]
  generalize hs : (mkRmentGeF a n is (mkRmentGeK a L n is) |>.map a).sum = s
  generalize hk : mkRmentGeK a L n is = k at hs
  choose h₂ h₃ using @mkRmentGeK_spec' a L n is H
  simp [mkRmentGeKCnd, hk, hs] at h₂
  rw [hk] at h₃
  change ∀ r, _ at h₃
  generalize hd : (n + 2 : ℝ)⁻¹ = d at h₁ h₂ ⊢
  generalize hs₀ : mkRmentSum a is = s₀ at h₁ ⊢
  have hd₁ : 0 < d; subst hd; positivity
  suffices h : L ≤ s₀ + s ∧ s₀ + s ≤ L + d
  · rw [abs_sub_le_iff]; split_ands <;> linarith
  symm; split_ands; linarith
  rw [hs₀] at h₂
  cases k
  · simp at hs; linarith
  nm k
  specialize h₃ k
  simp [mkRmentGeKCnd, hs₀] at h₃
  simp [mkRmentGeF, List.range_succ] at hs
  rw [←mkRmentGeF] at hs
  generalize hs' : (mkRmentGeF a n is k |>.map a |>.sum) = s' at h₃ hs
  rw [hd] at h₃
  simp [List.filter_cons] at hs
  choose h₄ h₅ h₆ using @mkRmentGeN_spec a n is H
  generalize hN : mkRmentGeN a n is = N at hs h₄ h₅ h₆
  split_ifs at hs with h₇
  rotate_left
  · simp at hs; linarith
  suffices h : -d < a (N + k)
  · simp at hs; linarith
  specialize h₆ (N + k) (by omega) h₇
  simp [neg_div, hd] at h₆
  exact h₆

theorem abs_map_sum_mkRmentIte_sub_lt {a L n is} (H : CondConv a) :
|(mkRmentIte a L n is |>.map a |>.sum) - L| ≤ 1 / (n + 2) := by
  rw [mkRmentIte]; simp; split_ifs with h₁ h₂
  · exact abs_map_sum_mkRmentLe_sub_lt H h₁
  · exact abs_map_sum_mkRmentGe_sub_lt H h₂
  · simp [mkRmentSum] at h₁ h₂; simp [abs_le]; split_ands <;> linarith

theorem abs_map_sum_mkRmentList_sub_lt {a L n} (H : CondConv a) (hn : n ≠ 0) :
|(mkRmentList a L n |>.map a |>.sum) - L| ≤ 1 / (n + 1) := by
  cases n; simp at hn
  simp [mkRmentList]
  convert abs_map_sum_mkRmentIte_sub_lt H using 1
  grind

theorem abs_series_mkRment_mkRmentLen_sub_lt {a L n} (H : CondConv a) (hn : n ≠ 0) :
|series (a $ mkRment a L ·) (mkRmentLen a L n) - L| ≤ 1 / (n + 1) := by
  convert @abs_map_sum_mkRmentList_sub_lt a L n H hn using 3
  dsimp [series, mkRmentLen]
  rw [List.sum_map_eq_sum_getElem_finset_range]
  apply Finset.sum_congr rfl
  intro i h₁
  simp at h₁
  simp [h₁]
  rw [mkRment_eq_getElem]
  congr 1
  simp

theorem subseq_exi_ge {σ n} (h : Subseq σ) : ∃ k, n ≤ σ k :=
  ⟨n, nat_le_of_subseq h⟩

theorem subseq_exi_gt {σ n} (h : Subseq σ) : ∃ k, n < σ k := by
  choose k hk using subseq_exi_ge h (n := n)
  use σ $ k + 1
  apply lt_of_le_of_lt hk
  apply lt_of_le_of_lt $ nat_le_of_subseq h
  simp [subseq_lt_iff h]

theorem subseq_exi_ge_and_between_of_le {σ n i} (h₁ : Subseq σ) (h₂ : σ n ≤ i) :
∃ k, n ≤ k ∧ σ k ≤ i ∧ i < σ (k + 1) := by
  have h₃ : ∃ k, i < σ k
  · apply subseq_exi_gt
    intro i j h₃
    simpa [subseq_lt_iff h₁]
  generalize hk : Nat.find! (λ k => i < σ k) = k
  choose h₄ h₅ using Nat.find!_spec' h₃
  rw [hk] at h₄ h₅
  clear h₃ hk
  cases k
  · have h₆ : σ n < σ 0; linarith
    simp [subseq_lt_iff h₁] at h₆
  nm k
  have h₆ := h₅ k
  simp at h₆
  refine ⟨k, ?_, h₆, h₄⟩
  by_contra! h₃
  rw [←Nat.add_one_le_iff, ←subseq_le_iff h₁] at h₃
  linarith

@[simp]
theorem mkRmentLen_lt_succ {a L n} : mkRmentLen a L n < mkRmentLen a L (n + 1) := by
  simp [mkRmentLen]; rw [mkRmentList, mkRmentIte]
  simp; apply Nat.lt_add_right; simp [mkRmentList1]

@[simp]
theorem subseq_mkRmentLen {a L} : Subseq (mkRmentLen a L) := by
  intro i j h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h; clear h
  induction j
  · simp
  nm n ih
  apply ih.trans; clear ih
  rw [←Nat.add_assoc]
  simp

@[simp]
theorem take_mkRmentLen_mkRmentList_add {a L n k} :
(mkRmentList a L $ n + k).take (mkRmentLen a L n) = mkRmentList a L n := by
  choose xs h using @mkRmentList_prefix a L n (n + k) (by omega); simp [←h, mkRmentLen]

theorem mem_mkRmentList_of_lt {a L n k} (h : k < n) : k ∈ mkRmentList a L n := by
  rw [←Nat.add_one_le_iff] at h
  have h₁ := @mem_mkRmentList_succ a L k
  apply List.IsPrefix.mem h₁
  exact mkRmentList_prefix h

theorem le_mkRmentP_mkRmentList {a L n} (H : CondConv a) :
n ≤ mkRmentP a (mkRmentList a L n) := by
  have h := @mkRmentP_spec a (mkRmentList a L n) H |>.1
  contrapose! h; exact mem_mkRmentList_of_lt h

theorem le_mkRmentN_mkRmentList {a L n} (H : CondConv a) :
n ≤ mkRmentN a (mkRmentList a L n) := by
  have h := @mkRmentN_spec a (mkRmentList a L n) H |>.1
  contrapose! h; exact mem_mkRmentList_of_lt h

theorem nonneg_of_mem_mkRmentLe {a L n is i} (h : i ∈ mkRmentLe a L n is) : 0 ≤ a i := by
  simp [mkRmentLe, mkRmentLeF] at h; exact h.2

theorem neg_of_mem_mkRmentGe {a L n is i} (h : i ∈ mkRmentGe a L n is) : a i < 0 := by
  simp [mkRmentGe, mkRmentGeF] at h; exact h.2

theorem abs_series_add_sum_mkRmentList_sub_lt.aux₁ {a L n N k i j s₀ s s₁ is is₁ d}
(H : CondConv a)
(h₂ : mkRmentSum a (mkRmentList a L n) = s₀)
(h₁ : mkRmentList a L n = is)
(_hN : is.length = N)
(h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹)
(ha : tendsTo a 0)
(hi : mkRmentP a is = i)
(hj : mkRmentN a is = j)
(h₄ : is ++ [i, j] = is₁)
(hs : mkRmentSum a is₁ = s)
(hd : (n + 2 : ℝ)⁻¹ = d)
(hs₁ : (mkRmentLe a L n is₁ |>.map a |>.take k |>.sum) = s₁)
(H₂ : s ≤ L - d) : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹ := by
  rw [abs_of_nonneg]
  rotate_left
  · rw [←hs₁]
    apply List.sum_nonneg
    intro r hr
    replace hr := List.mem_of_mem_take hr
    simp at hr
    rcases hr with ⟨x, hr, rfl⟩
    exact nonneg_of_mem_mkRmentLe hr
  rw [←hs₁]
  apply List.sum_take_le_of_nonneg _ |>.trans _
  · simp
    intro y hy
    exact nonneg_of_mem_mkRmentLe hy
  clear! s₁ k
  have hN' : mkRmentLen a L n = N
  · rwa [mkRmentLen, h₁]
  have H₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L (n + 1) H (by simp)
  rw [series_mkRment_eq_sum] at H₃
  rw [take_mkRmentLen_mkRmentList] at H₃
  rw [mkRmentList, h₁, mkRmentIte] at H₃
  rw [mkRmentList1, hi, hj, h₄, hs] at H₃
  simp at H₃
  rw [hd, if_pos H₂, ←mkRmentSum, hs] at H₃
  rw [show (n + 1 + 1 : ℝ) = n + 2 by ring_nf, hd] at H₃
  generalize hs₁ : (mkRmentLe a L n is₁ |>.map a).sum = s₁ at H₃ ⊢
  rw [abs_le] at H₃
  replace H₃ := H₃.2
  have H₄ : s₀ + a i + a j = s
  · rw [←hs, mkRmentSum, ←h₄]
    simp
    rw [←h₂, h₁, mkRmentSum, add_assoc]
  have H₅ : L - (n + 1 : ℝ)⁻¹ ≤ s₀
  · rw [abs_le] at h₃; linarith
  have H₆ : L - 2 * bounds a n - (n + 1 : ℝ)⁻¹ ≤ s
  · rw [←H₄]
    suffices : -bounds a n + -bounds a n ≤ a i + a j; linarith
    apply add_le_add
    · rw [neg_le]
      trans bounds a i
      · rw [←bounds_neg]
        change (-a) i ≤ _
        apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo $ tendsTo_neg ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hi, ←h₁]
      exact le_mkRmentP_mkRmentList H
    · rw [neg_le]
      trans bounds a j
      · rw [←bounds_neg]
        change (-a) j ≤ _
        apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo $ tendsTo_neg ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hj, ←h₁]
      exact le_mkRmentN_mkRmentList H
  linarith

theorem abs_series_add_sum_mkRmentList_sub_lt.aux₂ {a L n N k i j s₀ s s₁ is is₁ d}
(H : CondConv a)
(h₂ : mkRmentSum a (mkRmentList a L n) = s₀)
(h₁ : mkRmentList a L n = is)
(_hN : is.length = N)
(h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹)
(ha : tendsTo a 0)
(hi : mkRmentP a is = i)
(hj : mkRmentN a is = j)
(h₄ : is ++ [i, j] = is₁)
(hs : mkRmentSum a is₁ = s)
(hd : (n + 2 : ℝ)⁻¹ = d)
(hs₁ : (mkRmentGe a L n is₁ |>.map a |>.take k |>.sum) = s₁)
(H₂ : L + d ≤ s) : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹ := by
  rw [abs_of_nonpos]
  rotate_left
  · rw [←hs₁]
    apply List.sum_nonpos
    intro r hr
    replace hr := List.mem_of_mem_take hr
    simp at hr
    rcases hr with ⟨x, hr, rfl⟩
    exact le_of_lt $ neg_of_mem_mkRmentGe hr
  rw [neg_le, ←hs₁]
  apply List.le_sum_take_of_nonpos _ |>.trans' _
  · simp
    intro y hy
    exact le_of_lt $ neg_of_mem_mkRmentGe hy
  clear! s₁ k
  have hN' : mkRmentLen a L n = N
  · rwa [mkRmentLen, h₁]
  have H₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L (n + 1) H (by simp)
  rw [series_mkRment_eq_sum] at H₃
  rw [take_mkRmentLen_mkRmentList] at H₃
  rw [mkRmentList, h₁, mkRmentIte] at H₃
  rw [mkRmentList1, hi, hj, h₄, hs] at H₃
  simp at H₃
  rw [hd] at H₃
  have hd₀ : 0 < d
  · rw [←hd]; positivity
  rw [if_neg $ by linarith] at H₃
  rw [if_pos H₂] at H₃
  rw [←mkRmentSum, hs] at H₃
  rw [show (n + 1 + 1 : ℝ) = n + 2 by ring_nf, hd] at H₃
  generalize hs₁ : (mkRmentGe a L n is₁ |>.map a).sum = s₁ at H₃ ⊢
  rw [abs_le] at H₃
  replace H₃ := H₃.1
  have H₄ : s₀ + a i + a j = s
  · rw [←hs, mkRmentSum, ←h₄]
    simp
    rw [←h₂, h₁, mkRmentSum, add_assoc]
  have H₅ : s₀ ≤ L + (n + 1 : ℝ)⁻¹
  · rw [abs_le] at h₃; linarith
  have H₆ : s ≤ L + 2 * bounds a n + (n + 1 : ℝ)⁻¹
  · rw [←H₄]
    suffices : a i + a j ≤ bounds a n + bounds a n; linarith
    apply add_le_add
    · trans bounds a i
      · apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hi, ←h₁]
      exact le_mkRmentP_mkRmentList H
    · trans bounds a j
      · apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hj, ←h₁]
      exact le_mkRmentN_mkRmentList H
  linarith

theorem abs_series_add_sum_mkRmentList_sub_lt {a L n N k}
(H : CondConv a) (hN : mkRmentLen a L n = N) (hn : n ≠ 0) :
|series (a $ mkRment a L ·) N + (mkRmentList a L (n + 1) |>.drop N |>.take k
|>.map a |>.sum) - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  generalize hs₀ : series (a $ mkRment a L ·) N = s₀
  have h₂ : mkRmentSum a (mkRmentList a L n) = s₀
  · subst hs₀ hN
    rw [series_mkRment_eq_sum, mkRmentSum]
    congr
    rw [take_mkRmentLen_mkRmentList]
  rw [mkRmentLen] at hN
  generalize h₁ : mkRmentList a L n = is at hN hs₀
  rw [mkRmentList, h₁]
  have h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹
  · have h₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L n H hn
    simp [mkRmentLen, h₁, hN, hs₀] at h₃
    exact h₃
  rw [mkRmentIte, mkRmentList1, ←hN]
  simp
  have ha := H.tendsTo_zero
  have hb₀ : 0 ≤ bounds a n
  · exact bounds_nonneg_of_tendsTo H.tendsTo_zero
  have hb₁ : |s₀ - L + a (mkRmentP a is)| ≤ |s₀ - L| + bounds a n
  · apply abs_add_le _ _ |>.trans
    simp
    obtain ⟨⟨h₄, h₅⟩, h₆⟩ := @mkRmentP_spec' a is H
    apply abs_le_bounds_of_tendsTo ha |>.trans
    apply bounds_le_bounds_of_tendsTo ha
    rw [←h₁]; exact le_mkRmentP_mkRmentList H
  have hb₂ : |s₀ - L + a (mkRmentP a is) + a (mkRmentN a is)| ≤ |s₀ - L| + 2 * bounds a n
  · apply abs_add_le _ _ |>.trans
    suffices : |a $ mkRmentN a is| ≤ bounds a n; linarith
    obtain ⟨⟨h₄, h₅⟩, h₆⟩ := @mkRmentN_spec' a is H
    apply abs_le_bounds_of_tendsTo ha |>.trans
    apply bounds_le_bounds_of_tendsTo ha
    rw [←h₁]; exact le_mkRmentN_mkRmentList H
  have H₁ : 0 ≤ (n + 1 : ℝ)⁻¹; positivity
  cases k
  · simp
    linarith
  nm k
  cases k
  · simp; ring_nf at H₁ h₃ hb₁ ⊢; linarith
  nm k
  simp
  generalize hx : mkRmentP a is = i at hb₁ hb₂ ⊢
  generalize hy : mkRmentN a is = j at hb₂ ⊢
  generalize h₄ : is ++ [i, j] = is₁
  generalize hs : mkRmentSum a is₁ = s
  generalize hd : (n + 2 : ℝ)⁻¹ = d
  generalize hs₁ : ((if s ≤ L - d then mkRmentLe a L n is₁ else if L + d ≤ s
    then mkRmentGe a L n is₁ else []) |>.map a |>.take k |>.sum) = s₁
  suffices h : |s₀ - L + a i + a j + s₁| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹
  · ring_nf at h ⊢; exact h
  apply abs_add_le _ _ |>.trans
  suffices : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹; linarith
  split_ifs at hs₁ with H₂ H₃
  · exact abs_series_add_sum_mkRmentList_sub_lt.aux₁
      H h₂ h₁ hN h₃ ha hx hy h₄ hs hd hs₁ H₂
  · apply abs_series_add_sum_mkRmentList_sub_lt.aux₂
      H h₂ h₁ hN h₃ ha hx hy h₄ hs hd hs₁ H₃
  simp at hs₁; subst hs₁; simp; positivity

theorem abs_series_mkRment_sub_lt_of_between {a L n i} (H : CondConv a)
(hn : n ≠ 0) (h₁ : mkRmentLen a L n ≤ i) (h₂ : i < mkRmentLen a L (n + 1)) :
|series (a $ mkRment a L ·) i - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  rw [series_add]
  generalize hN : mkRmentLen a L n = N at h₂ ⊢
  apply @abs_series_add_sum_mkRmentList_sub_lt a L n N i H hN hn |>.trans'
  apply le_of_eq
  congr
  rw [series, List.sum_map_eq_sum_toFinset]
  rotate_left
  · apply List.nodup_take
    apply List.nodup_drop
    exact nodup_mkRmentList H
  induction i
  · simp [←hN]
  nm i ih
  specialize ih $ by omega
  rw [Finset.sum_range_succ, ih]
  clear ih
  rw [List.take_succ]
  simp
  rw [Finset.sum_union]
  rotate_left
  · simp
    intro j h₃
    simp_rw [Option.toList]
    split; simp
    nm x k h₄; clear x
    simp
    rintro rfl
    rw [List.mem_take_iff_getElem] at h₃
    choose r₁ hr₁ h₃ using h₃
    rw [min_eq_left $ by grind] at hr₁
    rw [List.getElem?_eq_some_iff] at h₄
    choose h₅ h₄ using h₄
    rw [←h₃] at h₄
    rw [List.getElem_drop] at h₄
    have h₅ : mkRmentList a L (n + 1) |>.Nodup; exact nodup_mkRmentList H
    rw [h₅.getElem_inj_iff] at h₄
    omega
  simp
  simp_rw [Option.toList]
  split
  · nm x h₁; clear x
    exfalso
    suffices : N + i < (mkRmentList a L $ n + 1).length; grind
    clear h₁
    rw [mkRmentLen] at h₂
    omega
  nm x j h₁; clear x
  simp
  congr
  rw [mkRment_eq_getElem]
  rw [List.getElem?_eq_some_iff] at h₁
  choose h₃ h₁ using h₁
  subst h₁
  rw [mkRmentLen] at h₂
  symm
  apply List.IsPrefix.getElem
  apply mkRmentList_prefix
  have : n ≤ N; simp [←hN];
  omega

theorem abs_series_mkRment_sub_lt_of_le {a L n i} (H : CondConv a)
(hn : n ≠ 0) (h : mkRmentLen a L n ≤ i) :
|series (a $ mkRment a L ·) i - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  choose k hk h₁ h₂ using subseq_exi_ge_and_between_of_le (by simp) h
  apply abs_series_mkRment_sub_lt_of_between H (by omega) h₁ h₂ |>.trans
  apply add_le_add
  · simp; exact bounds_le_bounds_of_tendsTo H.tendsTo_zero hk
  field_simp; norm_cast; simp
  exact hk

theorem tendsTo_series_mkRment {a L} (H : CondConv a) :
tendsTo (series $ λ i => a $ mkRment a L i) L := by
  rw [tendsTo_iff_eps_lt_one]
  intro ε hε hε'
  obtain ⟨N₁, hN₁⟩ : ∃ (N : ℕ), ∀ n, N ≤ n → 1 / (n + 1) < ε / 16
  · obtain ⟨N, hN⟩ := exists_nat_ge (ε / 16)⁻¹
    use N
    intro n hn
    rw [div_lt_iff₀] <;> try positivity
    field_simp at hN ⊢
    apply lt_of_le_of_lt hN
    rw [mul_lt_mul_iff_right₀ hε]
    norm_cast; omega
  choose N₂ hN₂ using H.bounds_tendsTo_zero (ε / 32) (by positivity)
  simp at hN₂
  generalize hn₁ : N₁ + N₂ + 1 = n₁
  use mkRmentLen a L n₁
  intro n hn
  have h₁ : n₁ ≤ n
  · apply hn.trans'; simp
  specialize hN₁ n₁ (by omega)
  specialize hN₂ n₁ (by omega)
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  apply abs_series_mkRment_sub_lt_of_le H (by omega) hn |>.trans
  rw [abs_bounds_of_tendsTo H.tendsTo_zero] at hN₂
  simp at hN₁; linarith

open CondConv in
theorem exi_rment_tendsTo_of_condConv {a L} (H : CondConv a) :
∃ σ, Rment σ ∧ tendsTo (series (a $ σ ·)) L :=
  ⟨_, rment_mkRment H, tendsTo_series_mkRment H⟩
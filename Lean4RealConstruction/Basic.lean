import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Paperproof

open Set Classical

structure myReal (Q) [Field Q] [LinearOrder Q] [IsStrictOrderedRing Q] [Archimedean Q] [MulArchimedean Q] where
  cut : Set Q
  I : cut.Nonempty ∧ cut ≠ (univ : Set Q)
  II {p q} : p ∈ cut → q < p → q ∈ cut
  III {p} : p ∈ cut → ∃ r ∈ cut, p < r

namespace myReal

variable {Q : Type*} [Field Q] [LinearOrder Q] [IsStrictOrderedRing Q] [Archimedean Q] [MulArchimedean Q] {α β γ : myReal Q} {p q r : Q}

theorem eq_hom : ∀ {α β : myReal Q}, α.cut = β.cut → α = β
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

-- 接下來，我們對 myReal 做一些介面操作，讓我們只需要關心 cut 即可。

instance instMembership : Membership (Q) (myReal Q) := ⟨fun α q => q ∈ α.cut⟩

@[ext]
protected theorem ext (h : ∀ s, s ∈ α ↔ s ∈ β) : α = β := eq_hom <| Set.ext h

@[simp]
protected theorem mem_mk {t : Set Q} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl

@[simp]
protected theorem mem_sets : p ∈ α.cut ↔ p ∈ α :=
  Iff.rfl

theorem II_imp_1 {p q} : p ∈ α → q ∉ α → p < q := by
  intro pα; contrapose!
  intro le_q_p; cases lt_or_eq_of_le le_q_p with
  | inl h => exact α.II pα h | inr h => exact h ▸ pα

theorem II_imp_2 {r s} : r ∉ α → r < s → s ∉ α :=
  fun nrα lt_r_s sα => nrα <| α.II sα lt_r_s

def subset_def (α β : myReal Q) : Prop := α.cut ⊆ β.cut

instance : HasSubset (myReal Q) := ⟨ subset_def ⟩

theorem subset_hom : (α.cut ⊆ β.cut) = (α ⊆ β) := rfl

instance : LE (myReal Q) := ⟨ fun α β => α ⊆ β ⟩

theorem le_hom : (α.cut ≤ β.cut) ↔ (α ≤ β) := Iff.rfl

noncomputable instance : LinearOrder (myReal Q) where
  le_refl α := le_hom.mp <| subset_refl α.cut
  le_trans _ _ _ le_α_β le_β_γ := le_hom.mp <| le_trans (le_hom.mpr le_α_β) (le_hom.mpr le_β_γ)
  le_antisymm _ _ le_α_β le_β_α := eq_hom <| subset_antisymm (le_hom.mpr le_α_β) (le_hom.mpr le_β_α)
  le_total α β := by
    -- 假設 α ≰ β。
    refine or_iff_not_imp_left.mpr fun (nle_α_β : ¬∀ p ∈ α, p ∈ β) => ?_
    -- 這代表有 p ∈ α, p ∉ β
    push_neg at nle_α_β ; let ⟨p, pα, npβ⟩ := nle_α_β
    -- 若 q ∈ β, 有 q < p，因此由 II 得 q ∈ α。
    exact fun q qβ => α.II pα <| II_imp_1 qβ npβ
  toDecidableLE := decRel LE.le

theorem lt_hom : (α.cut ⊂ β.cut) ↔ (α < β) := Iff.rfl

def myRat (p : Q) : myReal Q where
  cut := {q | q < p}
  I := ⟨ -- 由 Ordered Ring 的性質得 I。
    ⟨p-1, sub_lt_self p <| zero_lt_one⟩,
    (ne_univ_iff_exists_notMem _).mpr ⟨p+1, not_lt_of_gt <| lt_add_of_pos_right p <| zero_lt_one⟩⟩
  -- 由 partial order 的 transitivity 得 II。
  II := fun lt_p_0 lt_q_p => lt_trans lt_q_p lt_p_0
  -- 由 Ordered Field 的稠密性得 III。
  III lt_p_0 := by
    let ⟨r, lt_p_r, lt_r_0⟩ := exists_between lt_p_0
    exact ⟨r, lt_r_0, lt_p_r⟩

lemma le_of_rat_le : p ≤ q → myRat p ≤ myRat q :=
  fun le_p_q _ lt_r_p => lt_of_lt_of_le lt_r_p le_p_q

lemma lt_of_rat_lt : p < q → myRat p < myRat q := by
  intro lt_p_q
  use le_of_rat_le <| le_of_lt lt_p_q
  refine not_subset_iff_exists_mem_notMem.mpr ?_
  let ⟨r, lt_p_r, lt_r_q⟩ := exists_between lt_p_q
  use r, lt_r_q, II_imp_2 (lt_self_iff_false p).mp lt_p_r

lemma rat_le_of_le : myRat p ≤ myRat q → p ≤ q := le_of_forall_lt

lemma rat_lt_of_lt : myRat p < myRat q → p < q := Iio_ssubset_Iio_iff.mp

lemma rat_lt_iff_mem {p : Q} {α : myReal Q} : p ∈ α ↔ myRat p < α :=
  ⟨fun pα => ⟨fun _ lt_q_p => α.II pα lt_q_p,
    not_subset_iff_exists_mem_notMem.mpr ⟨p, pα, (lt_self_iff_false p).mp⟩⟩,
  fun lt_rp_α => by
    let ⟨le_p_α, ⟨q, qα, nlt_q_p⟩⟩ := ssubset_iff_exists.mp lt_rp_α
    let ⟨r, rα, lt_q_r⟩ := α.III qα
    exact α.II rα <| lt_of_le_of_lt (le_of_not_gt nlt_q_p) lt_q_r
  ⟩

lemma rat_ge_of_notMem {p : Q} {α : myReal Q} : p ∉ α → α ≤ myRat p :=
  fun npα _ qα => II_imp_1 qα npα

lemma notMem_of_rat_ge : α ≤ myRat p → p ∉ α := by
  contrapose! ; exact rat_lt_iff_mem.mp

lemma exists_rat_between : (α < β) → ∃ q, α < myRat q ∧ myRat q < β := by
  intro lt_α_β
  have ⟨le_α_β, p, pβ, npα⟩ := ssubset_iff_exists.mp lt_α_β
  let ⟨q, qβ, lt_p_q⟩ := β.III pβ
  exact ⟨q, lt_of_le_of_lt (rat_ge_of_notMem npα) (lt_of_rat_lt lt_p_q), rat_lt_iff_mem.mp qβ⟩

instance : Zero (myReal Q) := ⟨ myRat 0 ⟩

instance : One (myReal Q) := ⟨ myRat 1 ⟩

noncomputable instance : DistribLattice (myReal Q) := instDistribLatticeOfLinearOrder

instance : Inhabited (myReal Q) where default := 0

/-- 當 A 非空且有上界時，其聯集構造出的 myReal -/
noncomputable def sSup_of_valid {A : Set (myReal Q)} (hne : A.Nonempty) (hbd : BddAbove A) : myReal Q := {
  cut := ⋃ α : A, α.1.cut
  I := by
    -- 因為 A 為 nonempty，令 α₀ ∈ A。因為 A is bounded above，令 β 為其 upper bound。
    let ⟨α₀, α₀A⟩ := hne ; let ⟨β, βuA⟩ := hbd
    constructor
    . -- 首先，因為 α₀ 為 nonempty，⋃A 為 nonempty。
      exact nonempty_iUnion.mpr ⟨⟨α₀, α₀A⟩, α₀.I.left⟩
    . -- 因為 α ⊆ β ∀ α ∈ A，有 ⋃A ⊆ β。
      have le_UA_β : ⋃ α : A, α.1.cut ⊆ β.cut := iUnion_subset fun ⟨x, xA⟩ => βuA xA
      -- 因此由 β ≠ ℚ 得 ⋃A ≠ ℚ
      exact fun eq_UA_U => β.I.2 <| univ_subset_iff.mp (eq_UA_U ▸ le_UA_β)
  II {p q} pγ lt_qp := by
    rcases pγ with ⟨a₁, ⟨α₁, (eq_α₁_a : α₁.1.cut = a₁)⟩, pα₁⟩
    subst eq_α₁_a
    have : q ∈ α₁.1 := α₁.1.II pα₁ lt_qp
    exact mem_iUnion_of_mem α₁ this
  III {p} pγ := by
    rcases pγ with ⟨a₁, ⟨α₁, (eq_α₁_a : α₁.1.cut = a₁)⟩, pα₁⟩; subst eq_α₁_a
    let ⟨r, rh, lt_pr⟩ := α₁.1.III pα₁
    use r, mem_iUnion_of_mem α₁ rh, lt_pr
}

noncomputable def my_sSup (A : Set (myReal Q)) : myReal Q :=
  if h : A.Nonempty ∧ BddAbove A then sSup_of_valid h.1 h.2 else default

noncomputable instance : SupSet (myReal Q) := ⟨ my_sSup ⟩

theorem le_csSup (A : Set (myReal Q)) (h_ne : A.Nonempty) (h_bd : BddAbove A) :
    ∀ α ∈ A, α ≤ my_sSup A := by
  intro α hα
  -- 關鍵步驟：展開 my_sSup 並根據 if 條件拆分邏輯
  unfold my_sSup
  split_ifs with h_cond
  · -- Case 1: 條件成立 (h_cond : A.Nonempty ∧ BddAbove A)
    -- 這時 my_sSup A 會變成 sSup_of_valid h_cond.1 h_cond.2
    simp only [sSup_of_valid, iUnion_coe_set]
    intro q hq
    exact mem_iUnion_of_mem α (mem_iUnion_of_mem hα hq)
  · -- Case 2: 條件不成立 (但這與我們的前提 h_ne, h_bd 矛盾)
    exfalso
    exact h_cond ⟨h_ne, h_bd⟩

theorem csSup_le (A : Set (myReal Q)) (h_ne : A.Nonempty) (h_bd : BddAbove A) :
    my_sSup A ∈ (lowerBounds <| upperBounds <| A) := by
  intro δ; contrapose!
  unfold my_sSup
  split_ifs with h_cond
  . rw [sSup_of_valid]
    intro lt_δ_γ
    rcases ssubset_iff_exists.mp <| lt_hom.mp <| lt_δ_γ with
      ⟨le_δ_γ, s, ⟨a, ⟨α, (eq_α_a : α.1.cut = a)⟩, sa⟩, nsδ⟩ ; subst eq_α_a
    --have : δ < α.1 := lt_of_not_ge fun le_α_δ => nsδ (le_α_δ sa)
    exact fun δuA => nsδ (δuA α.2 <| sa)
  . -- Case 2: 條件不成立 (但這與我們的前提 h_ne, h_bd 矛盾)
    exfalso
    exact h_cond ⟨h_ne, h_bd⟩

noncomputable instance : SupSet (myReal Q) := ⟨ my_sSup ⟩

noncomputable instance : ConditionallyCompleteLattice (myReal Q) :=
  conditionallyCompleteLatticeOfLatticeOfsSup (myReal Q)
    (fun s hbd hne  => ⟨le_csSup s hne hbd, csSup_le s hne hbd⟩)

def add (α β : myReal Q) : myReal Q where
  cut := {q | ∃ r ∈ α, ∃ s ∈ β, q = r + s}
  I := by
    constructor
    . exact ⟨α.I.1.choose + β.I.1.choose, _, α.I.1.choose_spec, _, β.I.1.choose_spec, rfl⟩
    . let ⟨r', nr'α⟩ := ne_univ_iff_exists_notMem _ |>.mp α.I.2
      let ⟨s', ns'β⟩ := ne_univ_iff_exists_notMem _ |>.mp β.I.2
      have : ∀ r ∈ α, ∀ s ∈ β, r + s < r' + s' := fun _ rα _ sβ =>
        add_lt_add (II_imp_1 rα nr'α) (II_imp_1 sβ ns'β)
      exact ne_univ_iff_exists_notMem _ |>.mpr ⟨r' + s', fun ⟨r,rα,s,sβ,eq_r's'_rs⟩ =>
        (lt_self_iff_false _) |>.mp <| eq_r's'_rs ▸ (this r rα s sβ)⟩
  II {p q} := by
    intro ⟨r, rα, s, sβ, eq_p_rs⟩ lt_q_p
    use q-s, ?_, s, sβ, ?_
    . exact α.II rα <| sub_right_lt_of_lt_add <| eq_p_rs ▸ lt_q_p
    . exact (sub_add_cancel q s).symm
  III {p} := by
    intro ⟨r, rα, s, sβ, eq_p_rs⟩
    let ⟨t, tα, lt_r_t⟩ := α.III rα
    have : p < t + s := eq_p_rs ▸ (add_lt_add_iff_right s).mpr lt_r_t
    refine ⟨t+s, ⟨t, tα, s, sβ, rfl⟩, this⟩

instance : Add (myReal Q) := {add}

lemma zero_add_le (α : myReal Q) : 0 + α ≤ α :=
  fun _ ⟨_, r0, s, sα, eq_q_rs⟩ => α.II sα <| zero_add s ▸ eq_q_rs ▸ add_lt_add_left r0 s

lemma zero_add_ge (α : myReal Q) : α ≤ 0 + α := by
  intro p pα
  let ⟨r, rα, lt_p_s⟩ := α.III pα
  have : p - r < 0 := sub_neg.mpr lt_p_s
  exact ⟨p-r, this, r, rα, (sub_add_cancel p r).symm⟩

protected def _neg (α : myReal Q) : Set Q := {p | ∃ r > 0, -p-r ∉ α}

protected lemma _neg_mem_iff : p ∈ α → -p ∉ myReal._neg α  := by
  intro pα; change ¬∃ r > 0, -(-p)-r ∉ α; push_neg
  exact fun r r_pos => (α.II pα <| (neg_neg p).symm ▸ sub_lt_self p r_pos)

def neg (α : myReal Q) : myReal Q where
  cut := myReal._neg α
  I := by
    constructor
    . let ⟨s, nsα⟩ := ne_univ_iff_exists_notMem _ |>.mp α.I.2
      let p := -s-1
      use p, 1, zero_lt_one' Q
      have : -p-1 =s := by ring
      exact this ▸ nsα
    . let ⟨q, qα⟩ := α.I.1
      refine ne_univ_iff_exists_notMem _ |>.mpr ⟨-q, myReal._neg_mem_iff qα⟩
  II {p q} := by
    intro ⟨r, r_pos, nβp⟩ lt_q_p
    have : -q-r > -p-r := sub_lt_sub_right (neg_lt_neg lt_q_p) r
    exact ⟨r, r_pos, II_imp_2 nβp this⟩
  III {p} := by
    intro ⟨r, r_pos, nβp⟩
    let t := p + r/2
    have h1 : r/2 > 0 := half_pos r_pos
    have h2 : t > p := lt_add_of_pos_right p <| h1
    have h3 : -t-(r/2) = -p-r := by ring
    exact ⟨t, ⟨r/2, h1, h3 ▸ nβp⟩, h2⟩

instance : Neg (myReal Q) := ⟨ neg ⟩

lemma add_comm_le (α β : myReal Q) : α + β ≤ β + α := fun _ ⟨r, rα, s, sβ, eq_q_rs⟩ =>
  ⟨s, sβ, r, rα, add_comm r s ▸ eq_q_rs⟩

instance : AddCommMonoid (myReal Q) where
  add_comm α β := le_antisymm (add_comm_le α β) (add_comm_le β α)
  add_assoc α β γ := le_antisymm
    (fun _ ⟨_, ⟨r, rα, s, sβ, rfl⟩, t, tγ, eq_q_r't⟩ => ⟨r, rα, s+t, ⟨s, sβ, t, tγ, rfl⟩, add_assoc r s t ▸ eq_q_r't⟩)
    (fun _ ⟨r, rα, _, ⟨s, sβ, t, tγ, rfl⟩, eq_q_r't⟩ => ⟨r+s, ⟨r, rα, s, sβ, rfl⟩, t, tγ, add_assoc r s t ▸ eq_q_r't⟩)
  zero_add α := le_antisymm (zero_add_le α) (zero_add_ge α)
  add_zero α := le_antisymm
    (le_trans (add_comm_le α 0) (zero_add_le α))
    (le_trans (zero_add_ge α) (add_comm_le 0 α))
  nsmul := nsmulRec


instance : IsOrderedAddMonoid (myReal Q) where
  add_le_add_left _ _ le_α_β _ :=
    fun _ ⟨r, rα, s, sγ, eq_p_rs⟩ => ⟨r, le_α_β rα, s, sγ, eq_p_rs⟩

instance : AddCommGroup (myReal Q) where
  neg_add_cancel α := by
    apply le_antisymm
    .
      intro p ⟨r, ⟨t, t_pos, nβtα⟩, s, sα, eq_p_rs⟩
      have : -r ∉ α := II_imp_2 nβtα  <| (sub_lt_self (-r) t_pos)
      have : s < -r := II_imp_1 sα this
      have : r + s < 0 := lt_neg_iff_add_neg'.mp this
      exact eq_p_rs ▸ this
    .
      intro ν (lt_ν_0 : ν < 0)
      let w := -(ν/2)
      have h1 : w > 0 := by
        ring_nf!
        have : -1/2 < 0 := Int.sign_eq_neg_one_iff_neg.mp rfl
        linarith only [this, lt_ν_0]
      have h2 : ∃ s ∉ α, s - w ∈ α := by
        by_contra!
        have f : ∀ s ∉ α, ∀ n : ℕ, s - (n • w) ∉ α := by
          intro s nsα n; induction n with
          | zero => exact zero_nsmul w ▸ (sub_zero s).symm ▸ nsα
          | succ k kswα =>
            have eq : s - (k + 1) • w = s - k•w - w := by ring
            exact eq ▸ this _ kswα
        have ff : ∀ q, q ∉ α := by
          intro q qα
          let ⟨s, nsα⟩ := ne_univ_iff_exists_notMem _ |>.mp α.I.2
          let ⟨n, le_sq_nw⟩ := Archimedean.arch (s-q) h1
          have : s - n • w ≤ q := by linarith only [le_sq_nw]
          have nswα := f s nsα n
          cases le_iff_eq_or_lt.mp this with
          | inl eq => exact (eq ▸ nswα) qα
          | inr lt => exact II_imp_2 nswα lt qα
        exact not_nonempty_iff.mpr (Subtype.isEmpty_of_false ff) (Nonempty.to_subtype α.I.1)
        --exact not_nonempty
      let ⟨s, nsα, swα⟩ := h2
      have : s = -(-s-w)-(w) := by ring
      have : -s-w ∈ -α := ⟨w, h1, this ▸ nsα⟩
      use -s-w, this, s-w, swα; ring
  zsmul := zsmulRec

theorem my_zero_lt_one : (0 : myReal Q) < (1 : myReal Q) := by
  constructor
  . intro q q0; exact lt_trans q0 <| zero_lt_one' Q
  . change ¬∀ p ∈ (1 : myReal Q), p ∈ (0 : myReal Q) ; push_neg
    let ⟨r, lt_0_r, lt_r_1⟩ := exists_between <| zero_lt_one' Q
    use r, lt_r_1, Std.not_gt_of_lt lt_0_r

instance : ZeroLEOneClass (myReal Q) := ⟨ le_of_lt my_zero_lt_one ⟩

-- 先定義正實數的子類型
def myRealPos (Q : Type*) [Field Q] [LinearOrder Q] [IsStrictOrderedRing Q] [Archimedean Q] [MulArchimedean Q] := {α : myReal Q // 0 < α}

instance : One (myRealPos Q) := ⟨ ⟨1, my_zero_lt_one⟩ ⟩

-- 因為我們已經證明 R 是 OrderedMonoid，因此正實數相加仍為正實數。
instance : Add (myRealPos Q) :=
  ⟨ fun α β => ⟨α.val + β.val, add_pos α.2 β.2⟩ ⟩

variable {α β γ : myRealPos Q}

theorem eq_hom_pos : ∀ {α β : myRealPos Q}, α.val = β.val → α = β
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance instMembershipPos : Membership (Q) (myRealPos Q) := ⟨fun α q => q ∈ α.val⟩

@[ext]
theorem myRealPos.ext (h : ∀ s, s ∈ α ↔ s ∈ β) : α = β := eq_hom_pos <| myReal.ext h

@[simp]
theorem myRealPos.mem_sets : p ∈ α.val ↔ p ∈ α :=
  Iff.rfl

instance : LE (myRealPos Q) := ⟨ fun α β => α.val ≤ β.val ⟩

theorem le_hom_pos : (α.val ≤ β.val) = (α ≤ β) := rfl

noncomputable instance : LinearOrder (myRealPos Q) where
  le_refl α := le_hom_pos (Q := Q) ▸ le_refl α.val
  le_trans _ _ _ le_α_β le_β_γ := le_hom_pos (Q := Q) ▸ le_trans le_α_β le_β_γ
  le_antisymm _ _ le_α_β le_β_α := eq_hom_pos (Q := Q) <| le_antisymm le_α_β le_β_α
  le_total α β := le_hom_pos (Q := Q) ▸ le_total α.val β.val
  toDecidableLE := decRel LE.le

def mul_real_pos (α β : myRealPos Q) : myRealPos Q where
  val := {
    cut := {p | ∃ r ∈ α, ∃ s ∈ β, r > 0 ∧ s > 0 ∧ p ≤ r*s}
    I := by
      constructor
      .
        let ⟨r, lt_0_rr, lt_rr_α⟩ := exists_rat_between α.2
        let ⟨s, lt_0_rs, lt_rs_β⟩ := exists_rat_between β.2
        refine ⟨r*s, r, rat_lt_iff_mem.mpr lt_rr_α, s, rat_lt_iff_mem.mpr lt_rs_β,
            rat_lt_of_lt lt_0_rr, rat_lt_of_lt lt_0_rs, le_refl _⟩
      .
        let ⟨r, nrα⟩ := ne_univ_iff_exists_notMem _ |>.mp α.1.I.2
        let ⟨s, nsβ⟩ := ne_univ_iff_exists_notMem _ |>.mp β.1.I.2
        refine (ne_univ_iff_exists_notMem _).mpr ⟨r*s, ?_⟩
        rw [mem_setOf]; push_neg
        intro r' r'α s' s'β r'_pos s'_pos
        exact mul_lt_mul_of_pos' (II_imp_1 r'α nrα) (II_imp_1 s'β nsβ)
          s'_pos <| lt_trans r'_pos (II_imp_1 r'α nrα)
    II := fun ⟨r, rα, s, sβ, r_pos, s_pos, le_p_rs⟩ lt_q_p =>
      ⟨r, rα, s, sβ, r_pos, s_pos, le_of_lt <| lt_of_lt_of_le lt_q_p le_p_rs⟩
    III {p} := by
      intro ⟨r, rα, s, sβ, r_pos, s_pos, le_p_rs⟩
      let ⟨r', r'α, lt_r_r'⟩ := α.1.III rα
      let ⟨s', s'β, lt_s_s'⟩ := β.1.III sβ
      have r'_pos : r' > 0 := lt_trans r_pos lt_r_r'
      refine ⟨r'*s', ⟨r', r'α, s', s'β,
        r'_pos, lt_trans s_pos lt_s_s', le_refl _⟩, lt_of_le_of_lt le_p_rs
          <| mul_lt_mul_of_pos' lt_r_r' lt_s_s' s_pos (lt_trans r_pos lt_r_r')⟩
  }
  property := by
    let ⟨r, lt_0_rr, lt_rr_α⟩ := exists_rat_between α.2
    let ⟨s, lt_0_rs, lt_rs_β⟩ := exists_rat_between β.2
    have lt_0_r : 0 < r := rat_lt_of_lt lt_0_rr
    have lt_0_s : 0 < s := rat_lt_of_lt lt_0_rs
    have lt_r_α : r ∈ α := rat_lt_iff_mem.mpr lt_rr_α
    have lt_s_β : s ∈ β := rat_lt_iff_mem.mpr lt_rs_β
    have lt_0_rs : 0 < r*s := mul_pos lt_0_r lt_0_s
    refine ssubset_iff_exists.mpr ⟨fun p lt_p_0 => ⟨r, lt_r_α, s, lt_s_β,
      lt_0_r, lt_0_s, le_of_lt <| lt_trans lt_p_0 <| lt_0_rs⟩, ?_⟩
    refine ⟨r*s, ⟨r, lt_r_α, s, lt_s_β, lt_0_r, lt_0_s, le_refl _⟩,
      Std.not_gt_of_lt lt_0_rs⟩


instance : Mul (myRealPos Q) := ⟨ mul_real_pos ⟩

lemma mul_comm_le (α β : myRealPos Q) : α * β ≤ β * α :=
  fun _ ⟨r, rα, s, sβ, r_pos, s_pos, le_p_rs⟩ => ⟨s, sβ, r, rα, s_pos, r_pos, mul_comm r s ▸ le_p_rs⟩

lemma one_mul_le (α : myRealPos Q) : 1 * α ≤ α :=
  fun _ ⟨_, lt_r_1, _, sα, _, s_pos, le_p_rs⟩ =>
    α.1.II sα <| lt_of_le_of_lt le_p_rs <| (mul_lt_iff_lt_one_left s_pos).mpr lt_r_1

lemma exists_pos_of_mem : p ∈ α → ∃ p' ∈ α, 0 < p' ∧ p < p' := by
  intro pα
  -- 首先，取 0⋆ < r⋆ < α 和 p⋆ < s⋆ < α。
  let ⟨r, lt_0_rr, lt_rr_α⟩ := exists_rat_between α.2
  let ⟨s, sα, lt_p_s⟩ := α.1.III pα
  -- 令 t⋆ = r⋆ ⊔ s⋆. 有 0 < t⋆, p⋆ < t⋆ 和 t⋆ < α。
  refine ⟨max r s, ((max_choice r s).elim
    (fun eq_r => eq_r.symm ▸ rat_lt_iff_mem.mpr lt_rr_α)
    (fun eq_s => eq_s.symm ▸ sα)),
    lt_sup_of_lt_left <| rat_lt_of_lt lt_0_rr,
    lt_sup_of_lt_right lt_p_s⟩

lemma one_mul_ge (α : myRealPos Q) : α ≤ 1 * α := by
  -- 我覺得這想法用 rational number 的 copy 表述比較好，因此特別用註解，比較一下。
  intro p pα
  -- 首先，取 0⋆ < r⋆ < α 和 p⋆ < s⋆ < α。
  let ⟨r, lt_0_rr, lt_rr_α⟩ := exists_rat_between α.2
  let ⟨s, sα, lt_p_s⟩ := α.1.III pα
  -- 令 t⋆ = r⋆ ⊔ s⋆. 有 0 < t⋆, p⋆ < t⋆ 和 t⋆ < α。
  let t := max r s
  have lt_0_t : 0 < t := lt_sup_of_lt_left <| rat_lt_of_lt lt_0_rr
  have lt_p_t : p < t := lt_sup_of_lt_right lt_p_s
  have tα : t ∈ α := (((max_choice r s).elim
    (fun eq_r => eq_r.symm ▸ rat_lt_iff_mem.mpr lt_rr_α)
    (fun eq_s => eq_s.symm ▸ sα)) : max r s ∈ α )
  -- 取 t⋆ < q⋆ < α, 此時 0⋆ < q⋆。
  let ⟨q, qα, lt_t_q⟩ := α.1.III tα
  have lt_0_q : 0 < q := lt_trans lt_0_t lt_t_q
  -- 因此，有 p⋆ < t⋆ = t⋆/q⋆ * q⋆，其中 0⋆ < t⋆/q⋆ < 1⋆ 和 q⋆ < α。
  have lt_tdq_1 : t/q < 1 := (div_lt_one₀ lt_0_q).mpr lt_t_q
  have lt_0_tdq : 0 < t/q := div_pos lt_0_t lt_0_q
  refine ⟨t/q, lt_tdq_1, q, qα, lt_0_tdq, lt_0_q, le_of_lt <| lt_of_lt_of_le lt_p_t
    (Eq.trans (div_self (ne_of_lt lt_0_q).symm ▸ mul_comm_div t q q) <| mul_one t).ge⟩
  -- 故 p ∈ 1⋆ * α
  -- 寫完之後，我覺得後半段還是用 cut 比較自然，不過前面的 idea 相當重要。

instance : CommMonoid (myRealPos Q) where
  mul_comm α β := le_antisymm (mul_comm_le α β) (mul_comm_le β α)
  mul_assoc α β γ := le_antisymm
    (fun p ⟨r', ⟨r, rα, s, sβ, r_pos, s_pos, le_r'_rs⟩, t, tγ, r'_pos, t_pos, le_p_r't⟩ =>
      ⟨r, rα, s*t, ⟨s, sβ, t, tγ, s_pos, t_pos, le_refl _⟩, r_pos, mul_pos s_pos t_pos,
        le_trans (le_trans le_p_r't <| (mul_le_mul_iff_of_pos_right t_pos).mpr le_r'_rs) (mul_assoc r s t).le⟩)
    (fun p ⟨r, rα, s', ⟨s, sβ, t, tγ, s_pos, t_pos, le_s'_st⟩, r_pos, s'_pos, le_p_rs'⟩ =>
      ⟨r*s, ⟨r, rα, s, sβ, r_pos, s_pos, le_refl _⟩, t, tγ, mul_pos r_pos s_pos, t_pos,
        le_trans (le_trans le_p_rs' <| (mul_le_mul_iff_of_pos_left r_pos).mpr le_s'_st) (mul_assoc r s t).ge⟩)
  one_mul α := le_antisymm (one_mul_le α) (one_mul_ge α)
  mul_one α := le_antisymm
    (le_trans (mul_comm_le α 1) (one_mul_le α))
    (le_trans (one_mul_ge α) (mul_comm_le 1 α))

lemma rational_sq_near_one {Q : Type*} [Field Q] [LinearOrder Q] [IsStrictOrderedRing Q] {ε : Q} (hε : 1 < ε) : ∃ k : Q, 1 < k ∧ k * k < ε := by
  use 1 + min 1 ((ε-1)/4) ;
  have : (ε-1)/4 > 0 := by linarith only [hε]
  have eq_1 : min 1 ((ε-1)/4) > 0 := by positivity
  have eq_2 : min 1 ((ε-1)/4) ≤ ((ε-1)/4) := min_le_right 1 ((ε - 1) / 4)
  have eq_3 : min 1 ((ε-1)/4) ≤ 1 := min_le_left 1 ((ε - 1) / 4)
  have eq_4 : min 1 ((ε-1)/4) * min 1 ((ε-1)/4) ≤ min 1 ((ε-1)/4) := (mul_le_iff_le_one_right eq_1).mpr eq_3
  constructor
  . linarith only [eq_1]
  . calc
    (1 + min _ _) * (1 + min _ _)
      = 1 + 2 * min 1 ((ε-1)/4) + min 1 ((ε-1)/4) * min 1 ((ε-1)/4) := by ring
    _ ≤ 1 + 2 * ((ε-1)/4) + ((ε-1)/4) := by linarith only [eq_2, eq_4]
    _ < ε := by linarith only [hε]

lemma inv_mem {α : myRealPos Q} : p > 0 → p ∈ α → p⁻¹ ∉ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} ∪ {p : Q | p ≤ 0} := by
  simp only [mem_union, mem_setOf] ; push_neg
  intro p_pos pα ; constructor
  . intro _ lt_1_r;
    apply α.1.II pα ; field_simp ; exact lt_1_r
  . exact inv_pos.mpr p_pos

lemma pos_mem_inv {α : myRealPos Q} : p > 0 → p ∈ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} ∪ {p : Q | p ≤ 0} → p ∈ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} := by
  intro p_pos pβ
  have : ∀ {A B : Set Q}, ∀ {x : Q}, x ∈ A ∪ B → x ∉ B → x ∈ A := by intro _ _ _ ; rw [mem_union]; tauto
  exact this pβ (fun p_nonneg => (lt_self_iff_false _).mp <| lt_of_le_of_lt p_nonneg p_pos)

lemma inv_prop : (0 : myReal Q).cut ⊂ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} ∪ {p : Q | p ≤ 0} := by
  refine ssubset_iff_exists.mpr ⟨fun p lt_p_0 => mem_union_right _ (le_of_lt lt_p_0), ?_⟩
  refine ⟨0, mem_union_right _ (le_refl 0), notMem_of_rat_ge (le_refl _)⟩

def inv_real_pos (α : myRealPos Q) : myRealPos Q where
    val := {
      cut := {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} ∪ {p : Q | p ≤ 0}
      I := by
        refine ⟨nonempty_of_ssubset' inv_prop, ?_⟩
        apply (ne_univ_iff_exists_notMem _).mpr
        let ⟨q, lt_0_rq, lt_rq_α⟩ := exists_rat_between α.2
        exact ⟨q⁻¹, inv_mem (rat_lt_of_lt lt_0_rq) (rat_lt_iff_mem.mpr lt_rq_α)⟩
      II := by
        intro p q pβ lt_q_p; by_cases h : q ≤ 0
        . exact mem_union_right _ h
        . rw [not_le] at h
          have lt_0_p : 0 < p := lt_trans h lt_q_p
          have : p ∈ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} := pos_mem_inv lt_0_p pβ
          rcases this with ⟨r, lt_1_r, npiriα⟩
          refine mem_union_left _ <| ⟨r, lt_1_r, II_imp_2 npiriα ?_⟩
          field_simp; exact lt_q_p
      III := by
        intro p pβ ; by_cases h : p > 0
        . have : p ∈ {p | ∃ r > 1, p⁻¹ * r⁻¹ ∉ α} := pos_mem_inv h pβ
          rcases this with ⟨r, lt_1_r, npiriα⟩
          let ⟨t, lt_1_t, lt_tt_r⟩ := rational_sq_near_one lt_1_r
          use p*t; refine ⟨mem_union_left _ ?_, (lt_mul_iff_one_lt_right h).mpr lt_1_t⟩
          use t, lt_1_t ; rw [mul_inv] ; apply II_imp_2 npiriα
          field_simp ; exact pow_two t ▸ lt_tt_r
        .
          rw [not_lt] at h
          let ⟨q, nqα⟩ := (ne_univ_iff_exists_notMem _).mp α.1.I.2
          have q_pos : q > 0 := rat_lt_of_lt <| lt_of_lt_of_le α.2 (rat_ge_of_notMem nqα)
          have qs_pos : q + 1 > 0 := lt_trans q_pos <| lt_add_one q
          have nqsα : q + 1 ∉ α := II_imp_2 nqα (lt_add_one q)
          refine ⟨(q + 1)⁻¹, mem_union_left _ ⟨(q + 1) * q⁻¹, ?_, ?_⟩, lt_of_le_of_lt h <| inv_pos.mpr qs_pos⟩
          field_simp; exact lt_add_one q
          have : (q + 1)⁻¹⁻¹ * ((q + 1) * q⁻¹)⁻¹ = q := by field
          exact this.symm ▸ nqα
    }
    property := inv_prop

instance : Inv (myRealPos Q) := ⟨ inv_real_pos ⟩

instance : CommGroup (myRealPos Q) where
  inv_mul_cancel α := by
    apply le_antisymm
    . intro p ⟨r, rαi, s, sα, r_pos, s_pos, le_p_rs⟩
      have nsiαi : s⁻¹ ∉ α⁻¹ := inv_mem s_pos sα
      have lt_r_si : r < s⁻¹ := II_imp_1 rαi nsiαi
      apply lt_of_le_of_lt le_p_rs
      rw [← inv_mul_cancel₀ (ne_of_gt s_pos)]; gcongr
    .
      intro ν lt_ν_1
      by_cases h : ν > 0
      . --
        let ⟨w, lt_1_w, lt_ww_vi⟩ := rational_sq_near_one <| (one_lt_inv₀ h).mpr lt_ν_1
        have w_pos : w > 0 := by positivity
        have lt_ww_vi : ν < (w * w)⁻¹ := lt_inv_of_lt_inv₀ (mul_pos w_pos w_pos) lt_ww_vi
        have : ∃ s ∉ α, s * w⁻¹ ∈ α := by
          by_contra!
          have h1 : ∀ s ∉ α, ∀ n, w⁻¹ ^ n * s ∉ α := by
            intro s nsα n ; induction n with
            | zero => rw [pow_zero, one_mul] ; exact nsα
            | succ n nwinsα =>
              rw [pow_succ, mul_assoc, mul_comm _ s, ← mul_assoc]
              exact this _ nwinsα
          have h2 : ∀ q > 0, q ∉ α := by
            intro q q_pos
            let ⟨s, nsα⟩ := (ne_univ_iff_exists_notMem _).mp α.1.I.2
            let ⟨n, le_sqi_wn⟩ := MulArchimedean.arch (s*q⁻¹) lt_1_w
            have s_pos : s > 0 := rat_lt_of_lt (lt_of_lt_of_le α.2 <| rat_ge_of_notMem nsα)
            have wni_pos : (w ^ n)⁻¹ > 0 := inv_pos.mpr <| pow_pos w_pos n
            have : w⁻¹ ^ n * s ≤ q := by rw [inv_pow]; calc
              (w ^ n)⁻¹ * s
                = (w ^ n)⁻¹ * s * (q⁻¹ * q) := by rw [inv_mul_cancel₀ (ne_of_gt q_pos), mul_one]
              _ = (w ^ n)⁻¹ * (s * q⁻¹) * q := by ring
              _ ≤ (w ^ n)⁻¹ * (w ^ n) * q := by gcongr
              _ = q := by rw [inv_mul_cancel₀ (ne_of_gt <| pow_pos w_pos n), one_mul]
            cases eq_or_lt_of_le this with
            | inl eq => exact eq ▸ h1 s nsα n
            | inr l => exact II_imp_2 (h1 s nsα n) l
          let ⟨p, lt_0_rp, lt_rp_α⟩ := exists_rat_between α.2
          exact h2 p (rat_lt_of_lt lt_0_rp) (rat_lt_iff_mem.mpr lt_rp_α)
        let ⟨s, nsα, swiα⟩ := this
        have : (s * w)⁻¹ ∈ α⁻¹ := by
          left ; use w, lt_1_w ;
          rw [inv_inv, mul_assoc, mul_inv_cancel₀ (ne_of_gt w_pos), mul_one]
          exact nsα
        have s_pos : s > 0 := rat_lt_of_lt (lt_of_lt_of_le α.2 <| rat_ge_of_notMem nsα)
        use (s * w)⁻¹, this, s * w⁻¹, swiα, ?_, ?_, ?_
        positivity ; positivity
        apply le_of_lt; calc
          ν < s * s⁻¹ * (w * w)⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt s_pos), one_mul]; exact lt_ww_vi
          _ = (s * w)⁻¹ * (s * w⁻¹) := by ring
      . rw [not_lt] at h
        exact rat_lt_iff_mem.mpr (lt_of_le_of_lt (le_of_rat_le h) (_ : myRealPos Q).2)

theorem mul_add_pos (α β γ : myRealPos Q) : α * (β + γ) = α * β + α * γ := by
  apply le_antisymm
  .
    intro p ⟨r, rα, _, ⟨s, sβ, t, tγ, rfl⟩, r_pos, sat_pos, le_p_rsat⟩
    let ⟨s', s'β, s'_pos, lt_s_s'⟩ := exists_pos_of_mem sβ
    let ⟨t', t'γ, t'_pos, lt_t_t'⟩ := exists_pos_of_mem tγ
    refine ⟨p-r*t, ⟨r, rα, s', s'β, r_pos, s'_pos, ?_⟩,
      r*t, ⟨r, rα, t', t'γ, r_pos, t'_pos, ?_⟩, ?_⟩
    .
      have h1 : p - r*t ≤ r*s := tsub_le_iff_right.mpr <| mul_add r s t ▸ le_p_rsat
      have h2 : r*s < r*s' := (mul_lt_mul_iff_right₀ r_pos).mpr lt_s_s'
      exact le_of_lt <| lt_of_le_of_lt h1 h2
    . exact le_of_lt <| (mul_lt_mul_iff_right₀ r_pos).mpr lt_t_t'
    . exact (sub_add_cancel p (r * t)).symm
  .
    intro p ⟨q', ⟨q, qα, r, rβ, q_pos, r_pos, le_q'_qr⟩,
      s', ⟨s, sα, t, tγ, s_pos, t_pos, le_s'_st⟩, eq_p_q'as'⟩
    have h1 : q ≤ max q s := le_max_left q s
    have h2 : s ≤ max q s := le_max_right q s
    refine ⟨max q s, ((max_choice q s).elim
      (fun eq_q => eq_q.symm ▸ qα) (fun eq_s => eq_s.symm ▸ sα)),
        r+t, ⟨r, rβ, t, tγ, rfl⟩, lt_of_lt_of_le q_pos h1, add_pos r_pos t_pos, ?_⟩
    calc
      p ≤ q*r + s*t := by linarith only [eq_p_q'as', le_q'_qr, le_s'_st]
      _ ≤ max q s * r + max q s * t := by gcongr
      _ = max q s * (r + t) := by ring

variable {α β γ : myReal Q}

noncomputable def nnmul (α β : myReal Q) : myReal Q :=
  if h : α > 0 ∧ β > 0 then (⟨α, h.1⟩ * ⟨β, h.2⟩ : myRealPos Q).1
  else 0

lemma nnmul_of_pos (h : α > 0 ∧ β > 0) : nnmul α β = (⟨α, h.1⟩ * ⟨β, h.2⟩ : myRealPos Q).1 := by
  unfold nnmul ; split_ifs ; rfl

lemma nnmul_of_nonpos (h : α ≤ 0 ∨ β ≤ 0) : nnmul α β = 0 := by
  unfold nnmul ; split_ifs with h';
  . have ⟨α_pos, β_pos⟩ := h'
    exfalso; cases h with
      |inl α_nonpos => exact (lt_self_iff_false _).mp <| lt_of_lt_of_le α_pos α_nonpos
      |inr β_nonpos => exact (lt_self_iff_false _).mp <| lt_of_lt_of_le β_pos β_nonpos
  . rfl

lemma nnmul_nn : nnmul α β ≥ 0 := by
  by_cases h : α > 0 ∧ β > 0
  . rw [nnmul_of_pos h]; refine le_of_lt (_ : myRealPos Q).property
  . simp only [not_and_or, not_lt] at h
    cases h with
    | inl lα => rw [nnmul_of_nonpos (Or.inl lα)]
    | inr lβ => rw [nnmul_of_nonpos (Or.inr lβ)]

lemma zero_nnmul : nnmul 0 α = 0 := nnmul_of_nonpos <| Or.inl <| le_refl <| 0

lemma nnmul_zero : nnmul α 0 = 0 := nnmul_of_nonpos <| Or.inr <| le_refl <| 0

lemma pos_to_real_to_pos {α : myRealPos Q} {h : α.val > (0 : myReal Q)} : ↑⟨α.val, h⟩ = α := rfl

lemma add_to_pos (hα : α > 0) (hβ : β > 0) : (⟨α + β, add_pos hα hβ⟩ : myRealPos Q) = (⟨α, hα⟩ + ⟨β, hβ⟩ : myRealPos Q) := by rfl

lemma nnmul_comm : nnmul α β = nnmul β α := by
  by_cases h : α > 0 ∧ β > 0
  . rw [nnmul_of_pos h, nnmul_of_pos h.symm, mul_comm]
  . simp only [not_and_or, not_lt] at h
    rw [nnmul_of_nonpos h, nnmul_of_nonpos h.symm]

lemma nnmul_assoc : nnmul (nnmul α β) γ = nnmul α (nnmul β γ) := by
  by_cases h : α > 0 ∧ β > 0 ∧ γ > 0
  . rw [nnmul_of_pos ⟨h.1, h.2.1⟩, nnmul_of_pos ⟨(_ : myRealPos Q).property, h.2.2⟩,
    nnmul_of_pos h.2, nnmul_of_pos ⟨h.1, (_ : myRealPos Q).property⟩,
    pos_to_real_to_pos, pos_to_real_to_pos, mul_assoc]
  .
    simp only [not_and_or, not_lt] at h
    cases h with
    | inl lα => simp only [nnmul_of_nonpos (Or.inl lα), zero_nnmul]
    | inr lβlγ =>
      rw [nnmul_of_nonpos lβlγ, nnmul_zero]
      cases lβlγ with
      | inl lβ => rw [nnmul_of_nonpos (Or.inr lβ), zero_nnmul]
      | inr lγ => rw [nnmul_of_nonpos (Or.inr lγ)]

lemma nnmul_nn_add (nnβ : β ≥ 0) (nnγ : γ ≥ 0) : nnmul α (β + γ) = nnmul α β + nnmul α γ := by
  by_cases h : α > 0 ∧ β > 0 ∧ γ > 0
  .
    rw [nnmul_of_pos ⟨h.1, add_pos h.2.1 h.2.2⟩, add_to_pos h.2.1 h.2.2, mul_add_pos,
    nnmul_of_pos ⟨h.1, h.2.1⟩, nnmul_of_pos ⟨h.1, h.2.2⟩] ; rfl
  .
    simp only [not_and_or, not_lt] at h
    cases h with
    | inl lα => simp only [nnmul_of_nonpos (Or.inl lα), zero_add];
    | inr lβlγ => cases lβlγ with
      | inl lβ => have := eq_of_le_of_ge lβ nnβ; rw [this, zero_add, nnmul_zero, zero_add]
      | inr lγ => have := eq_of_le_of_ge lγ nnγ; rw [this, add_zero, nnmul_zero, add_zero]

lemma one_nnmul (h : 0 ≤ α) : nnmul 1 α = α := by
  cases lt_or_eq_of_le h with
  | inl pos =>
    rw [nnmul_of_pos ⟨my_zero_lt_one, pos⟩]
    change ((1 : myRealPos Q) * _).val = α
    rw [one_mul]
  | inr ze => rw [← ze, nnmul_zero]


-- 搞定好 0 的部分的乘法定律後，我們直接用正部和負部來定實數乘法

noncomputable instance : Mul (myReal Q) where
  mul α β := nnmul α⁺ β⁺ - nnmul α⁺ β⁻ - nnmul α⁻ β⁺ + nnmul α⁻ β⁻

-- 這個實數乘法天然的將 ≥ 0 和 ≤ 0 的 case 囊括進去。
lemma mul_eq_nnmul (nnα : α ≥ 0) (nnβ : β ≥ 0) : α * β = nnmul α β := by
  change nnmul α⁺ β⁺ - nnmul α⁺ β⁻ - nnmul α⁻ β⁺ + nnmul α⁻ β⁻ = _
  -- 因為 α ≥ 0 和 β ≥ 0，有 α⁺ = α. β⁺ = β 和 α⁻ = 0, β⁻ = 0。
  simp only [posPart_eq_self.mpr nnα, posPart_eq_self.mpr nnβ,
    negPart_eq_zero.mpr nnα, negPart_eq_zero.mpr nnβ]
  -- 那麼該式的其餘項會變成 0，因為非負實數乘法中，乘以 0 也是 0。
  simp only [nnmul_zero, zero_nnmul, sub_zero, add_zero]

-- 這也代表其具有 OrderedRing 的單調性質。
lemma mul_nn (nnα : α ≥ 0) (nnβ : β ≥ 0) : α * β ≥ 0 := by
  rw [mul_eq_nnmul nnα nnβ]; exact nnmul_nn

-- 並且，僅依賴加法交換群性質，因此天然具備乘法交換律。
noncomputable instance : CommMagma (myReal Q) where
  mul_comm α β := by calc
    α * β
      = nnmul α⁺ β⁺ - nnmul α⁺ β⁻ - nnmul α⁻ β⁺ + nnmul α⁻ β⁻ := rfl
    _ = nnmul β⁺ α⁺ - nnmul β⁻ α⁺ - nnmul β⁺ α⁻ + nnmul β⁻ α⁻ := by simp only [nnmul_comm];
    _ = nnmul β⁺ α⁺ - nnmul β⁺ α⁻ - nnmul β⁻ α⁺ + nnmul β⁻ α⁻ := by abel
    _ = β * α := rfl

-- 同時這個乘法設計為 (α⁺ - α⁻)(β⁺ - β⁻) 的分配律展開。我們接下來證明，這天然具備分配律。
lemma add_pn_decomp (β γ : myReal Q) : (β + γ)⁺ + (β⁻ + γ⁻) = (β + γ)⁻ + (β⁺ + γ⁺) := by calc
  (β + γ)⁺ + (β⁻ + γ⁻)
    = (β + γ)⁺ - (β + γ)⁻ - (β⁺ - β⁻) - (γ⁺ - γ⁻) + β⁺ + γ⁺ + (β + γ)⁻ := by abel
  _ = (β + γ)⁻ + (β⁺ + γ⁺) := by simp only [posPart_sub_negPart]; abel

noncomputable instance : LeftDistribClass (myReal Q) where
  left_distrib α β γ := by
    let P := fun α : myReal Q => posPart_nonneg α
    let N := fun α : myReal Q => negPart_nonneg α
    let A := fun {a b} (h1 : 0 ≤ a) (h2 : 0 ≤ b) => add_nonneg (α := myReal Q) h1 h2
    calc
      α * (β + γ)
        = nnmul α⁺ (β + γ)⁺ - nnmul α⁺ (β + γ)⁻ - nnmul α⁻ (β + γ)⁺ + nnmul α⁻ (β + γ)⁻ := rfl
      _ = (nnmul α⁺ (β + γ)⁺ + (nnmul α⁺ β⁻ + nnmul α⁺ γ⁻)) - (nnmul α⁺ (β + γ)⁻ + (nnmul α⁺ β⁺ + nnmul α⁺ γ⁺)) -
          (nnmul α⁻ (β + γ)⁺ + (nnmul α⁻ β⁻ + nnmul α⁻ γ⁻)) + (nnmul α⁻ (β + γ)⁻ + (nnmul α⁻ β⁺ + nnmul α⁻ γ⁺)) +
          (nnmul α⁺ β⁺ - nnmul α⁺ β⁻ - nnmul α⁻ β⁺ + nnmul α⁻ β⁻) + (nnmul α⁺ γ⁺ - nnmul α⁺ γ⁻ - nnmul α⁻ γ⁺ + nnmul α⁻ γ⁻) := by abel
      _ = (nnmul α⁺ β⁺ - nnmul α⁺ β⁻ - nnmul α⁻ β⁺ + nnmul α⁻ β⁻) + (nnmul α⁺ γ⁺ - nnmul α⁺ γ⁻ - nnmul α⁻ γ⁺ + nnmul α⁻ γ⁻) := by
        -- 對每個部分套用分配律後，套用 lemma，再化簡。
        simp only [← nnmul_nn_add (N β) (N γ), ← nnmul_nn_add (P _) (A (N β) (N γ)), ← nnmul_nn_add (P β) (P γ), ← nnmul_nn_add (N _) (A (P β) (P γ)),
        add_pn_decomp]; abel
      _ = α * β + α * γ := rfl

noncomputable instance : Distrib (myReal Q) where
  left_distrib
  right_distrib α β γ := by rw [mul_comm, mul_add, mul_comm, mul_comm γ β]

lemma zero_mul_real (α : myReal Q) : 0 * α = 0 := by calc
  0 * α
    = 0 * α + 0 * α - 0 * α := by abel
  _ = (0 + 0) * α - 0 * α := by rw [add_mul]
  _ = 0 * α - 0 * α := by rw [zero_add]
  _ = 0 := by rw [sub_self]

noncomputable instance : NonUnitalNonAssocCommRing (myReal Q) where
  zero_mul := zero_mul_real
  mul_zero α := by rw [mul_comm, zero_mul_real]

-- 那麼，運用分配律、正部/負部性質、單調性，以及非負乘法的結合律，我們有結合律。
noncomputable instance : Semigroup (myReal Q) where
  mul_assoc α β γ := by
    let P := fun α : myReal Q => posPart_nonneg α
    let N := fun α : myReal Q => negPart_nonneg α
    let M := fun {a b} (h1 : 0 ≤ a) (h2 : 0 ≤ b) => mul_nn (Q := Q) h1 h2
    rw [← posPart_sub_negPart α, ← posPart_sub_negPart β, ← posPart_sub_negPart γ]
    simp only [mul_sub, sub_mul]
    rw [
      mul_eq_nnmul (M (P _) (P _)) (P _), mul_eq_nnmul (M (P _) (N _)) (P _), mul_eq_nnmul (M (N _) (P _)) (P _), mul_eq_nnmul (M (N _) (N _)) (P _),
      mul_eq_nnmul (M (P _) (P _)) (N _), mul_eq_nnmul (M (P _) (N _)) (N _), mul_eq_nnmul (M (N _) (P _)) (N _), mul_eq_nnmul (M (N _) (N _)) (N _),
      mul_eq_nnmul (P _) (M (P _) (P _)), mul_eq_nnmul (P _) (M (P _) (N _)), mul_eq_nnmul (P _) (M (N _) (P _)), mul_eq_nnmul (P _) (M (N _) (N _)),
      mul_eq_nnmul (N _) (M (P _) (P _)), mul_eq_nnmul (N _) (M (P _) (N _)), mul_eq_nnmul (N _) (M (N _) (P _)), mul_eq_nnmul (N _) (M (N _) (N _)),
    ]
    simp only [mul_eq_nnmul (P _) (P _), mul_eq_nnmul (P _) (N _), mul_eq_nnmul (N _) (P _), mul_eq_nnmul (N _) (N _)]
    simp only [nnmul_assoc]

lemma one_mul (α : myReal Q) : 1 * α = α := by
  rw [← posPart_sub_negPart α, mul_sub]
  rw [mul_eq_nnmul zero_le_one (posPart_nonneg _), mul_eq_nnmul zero_le_one (negPart_nonneg _)]
  rw [one_nnmul (posPart_nonneg _), one_nnmul (negPart_nonneg _)]

noncomputable instance : CommSemiring (myReal Q) where
  one_mul
  mul_one α := by rw [mul_comm, one_mul]

noncomputable def inv_real (α : myReal Q) : myReal Q :=
  if h : α > 0 then (⟨α, h⟩⁻¹ : myRealPos Q).val
  else if h : α < 0 then -((⟨-α, neg_pos.mpr h⟩⁻¹ : myRealPos Q).val)
  else 0

noncomputable instance : Inv (myReal Q) where
  inv := inv_real

lemma inv_case1 (h : α > 0) : α⁻¹ = (⟨α, h⟩⁻¹ : myRealPos Q).val := by
  change inv_real _ = _ ; unfold inv_real ; split_ifs ; rfl

lemma inv_case2 (h : α < 0) : α⁻¹ = -((⟨-α, neg_pos.mpr h⟩⁻¹ : myRealPos Q).val) := by
  change inv_real _ = _ ; unfold inv_real ; split_ifs with h'
  exfalso ; exact (lt_self_iff_false _).mp <| lt_trans h' h ; rfl

noncomputable instance : Field (myReal Q) where
  inv_zero := by
    change inv_real 0 = 0 ; unfold inv_real ; split_ifs with h
    exfalso; exact (lt_self_iff_false _).mp h ; rfl
  mul_inv_cancel α ne_α_0 := by
    cases lt_or_gt_of_ne ne_α_0 with
    | inl α_neg =>
      have nα_pos := neg_pos.mpr α_neg
      rw [inv_case2 α_neg, mul_neg, ← neg_mul]
      rw [mul_eq_nnmul (le_of_lt <| nα_pos) (le_of_lt (_ : myRealPos Q).2)]
      rw [nnmul_of_pos ⟨nα_pos, (_ : myRealPos Q).2⟩]
      rw [pos_to_real_to_pos, mul_inv_cancel]; rfl
    | inr α_pos =>
      rw [inv_case1 α_pos]
      rw [mul_eq_nnmul (le_of_lt <| α_pos) (le_of_lt (_ : myRealPos Q).2)]
      rw [nnmul_of_pos ⟨α_pos, (_ : myRealPos Q).2⟩]
      rw [pos_to_real_to_pos, mul_inv_cancel]; rfl
  exists_pair_ne := ⟨0, 1, ne_of_lt my_zero_lt_one⟩
  nnqsmul := _
  qsmul := _

-- 回顧若我們有 0 < α 且 0 < β，則 0 < α * β。
lemma mul_pos_real (hα : 0 < α) (hβ : 0 < β) : 0 < α * β := by
  rw [mul_eq_nnmul (le_of_lt <| hα) (le_of_lt hβ), nnmul_of_pos ⟨hα, hβ⟩]
  refine (_ : myRealPos Q).2

lemma mul_pos_mono_left (hα : 0 < α) (h : β < γ) : α*β < α*γ := by
  have : γ - β > 0 := sub_pos.mpr h
  have : α * (γ - β) > 0 := mul_pos_real hα this
  have : α * (γ - β) + α * β > α * β := lt_add_of_pos_of_le this (le_refl _)
  calc
    α * β
      < α * (γ - β) + α * β := this
    _ = α * γ := by ring

noncomputable instance : IsStrictOrderedRing (myReal Q) where
  mul_lt_mul_of_pos_left _ α_pos _ _ lt_β_γ := mul_pos_mono_left α_pos lt_β_γ
  mul_lt_mul_of_pos_right _ α_pos _ _ lt_β_γ := by simp only [mul_comm, mul_pos_mono_left α_pos lt_β_γ]


-- 最後一步：有理數的 homomorphism。
-- 我們將使用 myRat 作為 homomorphism。注意我們已經證明其保序性
#check rat_lt_of_lt
#check lt_of_rat_lt

theorem rat_add_eq_add (p q : Q) : myRat (p + q) = myRat p + myRat q := by
  apply le_antisymm
  .
    intro x (lt_x_pq : x < p + q)
    use p - (p + q - x)/2, ?_ , q - (p + q - x)/2, ?_, ?_
    change p - (p + q - x)/2 < p ; linarith only [lt_x_pq]
    change q - (p + q - x)/2 < q ; linarith only [lt_x_pq]
    ring
  .
    intro x ⟨r, lt_r_p, s, lt_s_p, eq_x_rs⟩
    exact eq_x_rs ▸ add_lt_add lt_r_p lt_s_p

-- 要證明這個對應關係是線性的，我們還是得照定義來。
-- 首先，我們論證 > 0 的情形。
lemma rat_mul_eq_mulpos (hp : p > 0) (hq : q > 0) :
  (⟨myRat (p * q), lt_of_rat_lt <| mul_pos hp hq⟩ : myRealPos Q) = (⟨myRat p, lt_of_rat_lt hp⟩ * ⟨myRat q, lt_of_rat_lt hq⟩ : myRealPos Q) := by
    apply le_antisymm
    .
      intro x (lt_x_pq : x < p * q); by_cases h : x > 0
      .
        -- 若 x < p * q，有 x * q⁻¹ < p
        have : x * q⁻¹ < p := (mul_inv_lt_iff₀ hq).mpr lt_x_pq
        -- 取 x * q⁻¹ < t < p，有 x * q⁻¹ * t⁻¹ < 1 i.e. x * t⁻¹ < q。
        let ⟨t, lt_xqi_t, lt_t_p⟩ := exists_between this
        have t_pos : t > 0 := lt_trans (mul_pos h <| inv_pos.mpr hq) lt_xqi_t
        have lt_xti_q : x * t⁻¹ < q := by field_simp ; exact (mul_inv_lt_iff₀ hq).mp lt_xqi_t
        -- 故，因為 x > 0 由 0 < t < p 得結論。
        use t, lt_t_p, x*t⁻¹, lt_xti_q, t_pos, mul_pos h <| inv_pos.mpr t_pos
        field_simp ; rfl
      .
        rw [not_lt] at h
        -- 若 x ≤ 0，則取 0 < r < p 和 0 < s < q，得 x < r * s。
        let ⟨r, r_pos, lt_r_p⟩ := exists_between hp
        let ⟨s, s_pos, lt_s_q⟩ := exists_between hq
        use r, lt_r_p, s, lt_s_q, r_pos, s_pos, le_trans h <| le_of_lt <| mul_pos r_pos s_pos
    .
      intro x ⟨r, lt_r_p, s, lt_s_q, r_pos, s_pos, le_x_rs⟩
      exact lt_of_le_of_lt le_x_rs <| mul_lt_mul lt_r_p (le_of_lt lt_s_q) s_pos (le_of_lt hp)

-- 再把 0 納入考量。
lemma rat_mul_eq_nnmul (hp : p ≥ 0) (hq : q ≥ 0) : myRat (p*q) = nnmul (myRat p) (myRat q) := by
  by_cases h : p > 0 ∧ q > 0
  .
    have : myRat p > 0 ∧ myRat q > 0 := ⟨lt_of_rat_lt h.1, lt_of_rat_lt h.2⟩
    rw [nnmul_of_pos this, ← rat_mul_eq_mulpos h.1 h.2]
  .
    simp only [not_and_or, not_lt] at h ; cases h with
    | inl pn =>
      rw [le_antisymm pn hp, zero_mul q] ; exact zero_nnmul.symm
    | inr qn =>
      rw [le_antisymm qn hq, mul_zero p] ; exact nnmul_zero.symm

-- 理論上來說，下面這三個 lemma 在保序性和線性的加法性質都證完後，就自動證明完了，但我們還是描述一下。
lemma rat_posPart_eq (p : Q) : (myRat p)⁺ = myRat p⁺ := by
  by_cases h : p ≥ 0
  . rw [posPart_eq_self.mpr h, posPart_eq_self.mpr (le_of_rat_le h)]
  . have h : p ≤ 0 := le_of_lt (not_le.mp h)
    rw [posPart_eq_zero.mpr h, posPart_eq_zero.mpr (le_of_rat_le h)] ; rfl

lemma rat_neg_eq_neg (p : Q) : myRat (-p) = -myRat p := by
  have : myRat (-p) + myRat p = 0 := by rw [← rat_add_eq_add, neg_add_cancel]; rfl
  exact eq_neg_of_add_eq_zero_left this

lemma rat_negPart_eq (p : Q) : (myRat p)⁻ = myRat p⁻ := by
  by_cases h : p ≥ 0
  . rw [negPart_eq_zero.mpr h, negPart_eq_zero.mpr (le_of_rat_le h)] ; rfl
  . have h : p ≤ 0 := le_of_lt (not_le.mp h)
    rw [negPart_eq_neg.mpr h, negPart_eq_neg.mpr (le_of_rat_le h), rat_neg_eq_neg];

-- 有了這些 lemma，能證明線性的乘法性質。
theorem rat_mul_eq_mul (p q : Q) : myRat (p * q) = myRat p * myRat q := by
  let P := fun α : Q => posPart_nonneg α
  let N := fun α : Q => negPart_nonneg α
  calc
    myRat (p * q)
    -- 我們依照正部、負部展開有理數。
      = myRat ((p⁺ - p⁻) * (q⁺ - q⁻)) := by simp only [posPart_sub_negPart]
    _ = myRat ((p⁺ * q⁺) + - (p⁺ * q⁻) + - (p⁻ * q⁺) + (p⁻ * q⁻)) := by congr; ring
    -- 而若干個有理數相加的對應實數，為若干個有理數的對應實數相加。
    _ = myRat (p⁺ * q⁺) - myRat (p⁺ * q⁻) - myRat (p⁻ * q⁺) + myRat (p⁻ * q⁻) := by simp only [rat_add_eq_add, rat_neg_eq_neg]; rfl
    -- 有理數正部、負部都非負，而非負有理數乘積的對應實數，為非負有理數對應實數的非負乘積。
    _ = nnmul (myRat p⁺) (myRat q⁺) - nnmul (myRat p⁺) (myRat q⁻) - nnmul (myRat p⁻) (myRat q⁺) + nnmul (myRat p⁻) (myRat q⁻) := by
      rw [rat_mul_eq_nnmul (P _) (P _), rat_mul_eq_nnmul (P _) (N _), rat_mul_eq_nnmul (N _) (P _), rat_mul_eq_nnmul (N _) (N _)]
    -- 而有理數的正部 / 負部的對應實數，是有理數的對應實數的正部 / 負部。
    _ = nnmul (myRat p)⁺ (myRat q)⁺ - nnmul (myRat p)⁺ (myRat q)⁻ - nnmul (myRat p)⁻ (myRat q)⁺ + nnmul (myRat p)⁻ (myRat q)⁻ := by simp only [← rat_posPart_eq, ← rat_negPart_eq]
    -- 化簡至此，已是實數乘法的定義。
    _ = myRat p * myRat q := by rfl
--

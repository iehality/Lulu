import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Sym.Sym2

/-! ## Ordering-/

namespace IsTotal

variable {α : Type*} {R : α → α → Prop} [IsTotal α R]

lemma of_not : ¬R a b → R b a := by rcases total (r := R) a b <;> simp [*]

end IsTotal

/-! ## Sub-$\mathbb{N}$ -/

class SubNat (α : Type*) where
  f : α → ℕ
  f_inj : Function.Injective f

attribute [simp] SubNat.f_inj

instance : SubNat ℕ where
  f := id
  f_inj := by exact fun ⦃_ _⦄ a ↦ a

instance : SubNat ℤ where
  f := Encodable.encode
  f_inj := Encodable.encode_injective

instance : SubNat (ZMod n) :=
  match n with
  | 0     =>
    { f := Encodable.encode (α := ℤ)
      f_inj := Encodable.encode_injective (α := ℤ) }
  | _ + 1 =>
    { f := ZMod.val
      f_inj := ZMod.val_injective _ }

instance [NeZero n] : SubNat (ZMod n) where
  f := ZMod.val
  f_inj := ZMod.val_injective n

namespace SubNat

variable {α} [SubNat α]

@[simp] lemma eq_iff {a b : α} : f a = f b ↔ a = b := f_inj.eq_iff

def Le (a b : α) : Prop := f a ≤ f b

instance : IsLinearOrder α Le where
  refl a := by simp [Le]
  trans _ _ _ := le_trans
  antisymm _ _ hij hji := f_inj.eq_iff.mp (le_antisymm hij hji)
  total _ _ := le_total _ _

instance : DecidableRel (Le : α → α → Prop) := fun i j ↦
  if h : f i ≤ f j then .isTrue h else .isFalse h

end SubNat

/-! ## Dihedral Groups -/

namespace DihedralGroup

def act {n} : DihedralGroup n → ZMod n → ZMod n
  | r i,  j => i + j
  | sr i, j => - i - j

@[simp] lemma act_one (i : ZMod n) : (1 : DihedralGroup n).act i = i := by simp [one_def, act]

@[simp] lemma act_add (a b : DihedralGroup n) (i : ZMod n) : (a * b).act i = a.act (b.act i) := by
  match a, b with
  | r j₁,  r j₂  => simp [act, add_assoc]
  | r j₁,  sr j₂ => simp [act]; ring
  | sr j₁, r j₂  => simp [act]; ring
  | sr j₁, sr j₂ => simp [act]; ring

instance : MulAction (DihedralGroup n) (ZMod n) where
  smul := act
  one_smul := act_one
  mul_smul := act_add

@[simp] lemma r_smul (i j : ZMod n) : r i • j = i + j := rfl

@[simp] lemma sr_smul (i j : ZMod n) : sr i • j = - i - j := rfl

def rev (n : ℕ) : DihedralGroup n := sr 0

lemma sr_eq_rev_mul (i : ZMod n) : sr i = rev n * r i := by simp [rev]

@[simp] lemma rev_smul (i : ZMod n) : rev n • i = -i := by simp [rev]

@[simp] lemma rev_smul_rev : rev n • rev n = 1 := by simp [rev, one_def]

end DihedralGroup

/-! ## Action and Orbit -/

namespace MulAction

section monoid

variable {M α : Type*} [DecidableEq α]

variable [Monoid M] [MulAction M α]

def actf (a : M) (s : Finset α) : Finset α := s.image fun t ↦ a • t

lemma actf_one (s : Finset α) : actf (1 : M) s = s := by simp [actf]

lemma actf_mul (a b : M) (s : Finset α) : actf (a * b) s = actf a (actf b s) := by
  ext; simp [actf, MulAction.mul_smul]

instance : MulAction M (Finset α) where
  smul := actf
  one_smul := actf_one
  mul_smul := actf_mul

lemma smul_def (a : M) (s : Finset α) : a • s = s.image fun t ↦ a • t := rfl

@[simp] lemma nonempty_smul_iff {a : M} {s : Finset α} : (a • s).Nonempty ↔ s.Nonempty := by
  simp [smul_def]

lemma image_smul [DecidableEq β] (f : α → β) (a : M) (s : Finset α) :
    (a • s).image f = s.image fun x ↦ f (a • x) := by ext x; simp [smul_def]

end monoid

section orbit

variable {G α} [Group G] [MulAction G α]

variable (G)

inductive OrbitEquiv : α → α → Prop where
  | intro (g : G) (a : α) : OrbitEquiv a (g • a)

variable {G}

local infix:60 " 〜 " => OrbitEquiv G

namespace OrbitEquiv

@[simp, refl] lemma refl (a : α) : a 〜 a := by simpa using intro (1 : G) a

@[symm] lemma symm (a b : α) : a 〜 b → b 〜 a
  | intro g _ => by simpa using intro (g⁻¹) (g • a)

@[trans] lemma trans (a b c : α) : a 〜 b → b 〜 c → a 〜 c
  | intro g _, intro h _ => by simpa [MulAction.mul_smul] using intro (h * g) a

variable (G α)

def setoid : Setoid α where
  r := OrbitEquiv G
  iseqv := { refl := OrbitEquiv.refl, symm := OrbitEquiv.symm _ _, trans := OrbitEquiv.trans _ _ _ }

end OrbitEquiv

variable (G α)

abbrev Orbit := Quotient (OrbitEquiv.setoid G α)

variable {G α}

namespace Orbit

lemma of_eq_of {a b : α} : (⟦a⟧ : Orbit G α) = ⟦b⟧ ↔ a 〜 b := Quotient.eq

end Orbit

end orbit

end MulAction

/-! ## List -/

namespace List

variable {α : Type*}

def wh (f : ℕ → α) : ℕ → List α
  | 0     => []
  | n + 1 => f n :: wh f n

@[simp] lemma length_wh (f : ℕ → α) (n) : (wh f n).length = n := by
  induction n <;> simp [wh, *]

lemma mem_wh_iff {a : α} {f : ℕ → α} {n} : a ∈ wh f n ↔ ∃ i < n, a = f i := by
  induction n
  · simp [wh]
  case succ n ih =>
    constructor
    · rintro (_ | h)
      · exact ⟨_, by simp, rfl⟩
      · rcases ih.mp (by assumption) with ⟨i, hi, rfl⟩
        exact ⟨i, Nat.lt_add_right 1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have : i ≤ n := Nat.le_of_lt_succ hi
      rcases this with (rfl | hii)
      · simp [wh]
      · right
        exact ih.mpr ⟨i, Nat.lt_add_one_of_le hii, rfl⟩

def rotations (l : List α) : List (List α) := wh l.rotate l.length

lemma mem_rotations {l : List α} (hl : l.length > 0) (i : ℕ): l.rotate i ∈ l.rotations :=
  mem_wh_iff.mpr ⟨i % l.length, Nat.mod_lt i hl, by simp [List.rotate_mod]⟩

@[simp] lemma length_rotations (l : List α) : l.rotations.length = l.length := by simp [rotations]

theorem mem_of_cons_subset {a : α} {l₁ l₂ : List α} : a :: l₁ ⊆ l₂ → a ∈ l₂ :=
  fun h ↦ h (mem_cons_self a l₁)

lemma subset_or_mem_of_subset_cons {l₁ l₂ : List α} : l₁ ⊆ a :: l₂ → l₁ ⊆ l₂ ∨ a ∈ l₁ := by
  by_cases ha : a ∈ l₁
  · intro _; right; assumption
  · intro h; left
    intro x hx
    have : x = a ∨ x ∈ l₂ := by simpa [ha] using h hx
    rcases this with (rfl | h)
    · contradiction
    · assumption

/-! ### Bisubset and Its Normal Form -/

section Bisubset

structure Bisubset (l₁ l₂ : List α) : Prop where
  left : l₁ ⊆ l₂
  right : l₂ ⊆ l₁

infix:45 " ⊆⊇ " => Bisubset

namespace Bisubset

variable {l k m : List α}

@[refl, simp] protected lemma refl (l : List α) : l ⊆⊇ l := ⟨by simp, by simp⟩

@[symm] lemma symm : l ⊆⊇ k → k ⊆⊇ l := by rintro ⟨h₁, h₂⟩; exact ⟨h₂, h₁⟩

lemma symm_iff : l ⊆⊇ k ↔ k ⊆⊇ l := ⟨symm, symm⟩

@[trans] lemma trans : l ⊆⊇ k → k ⊆⊇ m → l ⊆⊇ m := by
  rintro ⟨hlk, hkl⟩ ⟨hkm, hmk⟩; exact ⟨Subset.trans hlk hkm, Subset.trans hmk hkl⟩

instance : Trans (Bisubset : List α → List α → Prop) (Bisubset : List α → List α → Prop) (Bisubset : List α → List α → Prop) :=
  ⟨trans⟩

lemma iff : l ⊆⊇ k ↔ (∀ x, x ∈ l ↔ x ∈ k) := by
  constructor
  · rintro ⟨hlk, hkl⟩ x; exact ⟨@hlk x, @hkl x⟩
  · intro h;
    exact ⟨fun x hx ↦ (h x).mp hx, fun x hx ↦ (h x).mpr hx⟩

lemma iff_toFinset [DecidableEq α] : l ⊆⊇ k ↔ l.toFinset = k.toFinset := by
  simp [iff, Finset.ext_iff]

end Bisubset

lemma Perm.bisubset {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁ ⊆⊇ l₂ := by simp [Bisubset.iff, h.mem_iff]

@[simp] lemma bisubset_nil_iff {l : List α} : l ⊆⊇ [] ↔ l = [] := by simp [Bisubset.iff, eq_nil_iff_forall_not_mem]

@[simp] lemma mergeSort_bisubset (r : α → α → Bool) (l : List α) : l.mergeSort r ⊆⊇ l := (l.mergeSort_perm r).bisubset

@[simp] lemma dedup_bisubset [DecidableEq α] (l : List α) : l.dedup ⊆⊇ l := Bisubset.iff.mpr (by simp)

lemma Bisubset.pos_length_iff (h : l ⊆⊇ k) : 0 < l.length ↔ 0 < k.length := by
  match l, k with
  | [], [] => simp
  | [], b :: k => simp [Bisubset.symm_iff] at h
  | a :: l, [] => simp at h
  | a :: l, b :: k => simp

lemma cons_bisubset_cons_iff_bisubset (hal : a ∉ l) (hak : a ∉ k) : a :: l ⊆⊇ a :: k ↔ l ⊆⊇ k := by
  constructor
  · rintro ⟨hlk, hkl⟩
    have slk : l ⊆ k := by
      simpa [hal] using show l ⊆ k ∨ a ∈ l from subset_or_mem_of_subset_cons (by simpa using hlk)
    have skl : k ⊆ l := by
      simpa [hak] using show k ⊆ l ∨ a ∈ k from subset_or_mem_of_subset_cons (by simpa using hkl)
    exact ⟨slk, skl⟩
  · rintro ⟨slk, skl⟩
    exact ⟨cons_subset_cons a slk, cons_subset_cons a skl⟩

lemma eq_of_pairwise_of_nodup_of_bisubset (R : α → α → Prop) [as : IsAntisymm α R] {l₁ l₂ : List α} (h : l₁ ⊆⊇ l₂)
  (hN₁ : l₁.Nodup) (hN₂ : l₂.Nodup)
  (hP₁ : l₁.Pairwise R) (hP₂ : l₂.Pairwise R) : l₁ = l₂ := by
  match l₁, l₂ with
  |      [],      [] => rfl
  |      [], b :: l₂ => simp [Bisubset.symm_iff] at h
  | a :: l₁,      [] => simp at h
  | a :: l₁, b :: l₂ =>
    have ⟨ha, hP₁'⟩ : (∀ x ∈ l₁, R a x) ∧ Pairwise R l₁ := List.pairwise_cons.mp hP₁
    have ⟨hb, hP₂'⟩ : (∀ x ∈ l₂, R b x) ∧ Pairwise R l₂ := List.pairwise_cons.mp hP₂
    have ⟨na, hN₁'⟩ : (∀ x ∈ l₁, a ≠ x) ∧ l₁.Nodup := List.pairwise_cons.mp hN₁
    have ⟨nb, hN₂'⟩ : (∀ x ∈ l₂, b ≠ x) ∧ l₂.Nodup := List.pairwise_cons.mp hN₂
    have : a = b := by
      have : a = b ∨ a ∈ l₂ := by simpa using mem_of_cons_subset h.left
      rcases this with (_ | hal₂)
      · assumption
      have : b = a ∨ b ∈ l₁ := by simpa using mem_of_cons_subset h.right
      rcases this with (_ | hbl₁)
      · symm; assumption
      have hab : R a b := ha b hbl₁
      have hba : R b a := hb a hal₂
      exact antisymm hab hba
    rcases this with rfl
    have : l₁ = l₂ :=
      eq_of_pairwise_of_nodup_of_bisubset R
        (cons_bisubset_cons_iff_bisubset
          (fun a_1 ↦ na a a_1 rfl) (fun ha ↦ nb a ha rfl) |>.mp h) hN₁' hN₂' hP₁' hP₂'
    rw [this]

variable [DecidableEq α] [SubNat α]

def normalize (l : List α) : List α := l.dedup.mergeSort fun a b ↦ SubNat.Le b a

@[simp] lemma normalize_nodup (l : List α) : (normalize l).Nodup :=
  l.nodup_dedup.perm (l.dedup.mergeSort_perm _).symm

@[simp] lemma normalize_bisubset (l₁ l₂ : List α) : normalize l₁ ⊆⊇ normalize l₂ ↔ l₁ ⊆⊇ l₂ := by
  simp [Bisubset.iff, normalize]

@[simp] lemma bisubset_normalize (l : List α) : normalize l ⊆⊇ l := calc
  normalize l ⊆⊇ l.dedup := mergeSort_bisubset _ _
  _           ⊆⊇ l       := by simp

lemma bisubset_normalize_uniq
  {l₁ l₂ : List α} (e : l₁ ⊆⊇ l₂) : l₁.normalize = l₂.normalize :=
    eq_of_pairwise_of_nodup_of_bisubset (R := fun a b ↦ (SubNat.Le b a : Bool))
      (as := ⟨fun a b hab hba ↦ antisymm (by simpa using hba) (by simpa using hab)⟩)
      (by simpa) (by simp) (by simp)
      (by apply sorted_mergeSort ?_ ?_ l₁.dedup
          · intro a b c; simp
            intro hba hcb; exact le_trans hcb hba
          · intro a b; simpa using Nat.le_total _ _)
      (by apply sorted_mergeSort ?_ ?_ l₂.dedup
          · intro a b c; simp
            intro hba hcb; exact le_trans hcb hba
          · intro a b; simpa using le_total _ _)

@[simp] lemma normalize_pos_length_iff {l : List α} :
    0 < l.normalize.length ↔ 0 < l.length := Bisubset.pos_length_iff (by simp)

end Bisubset

/-! $R$-Minimal Element -/

section rMin

variable (R : α → α → Prop) [DecidableRel R]

def rMin (R : α → α → Prop) [DecidableRel R] : (l : List α) → l.length > 0 → α
  |          [], h => by simp at h
  |         [a], _ => a
  | a :: b :: l, _ =>
    let m := rMin R (b :: l) (by simp)
    if R a m then a else m

@[simp] lemma rMin_in (l : List α) (hl : l.length > 0) :
    rMin R l hl ∈ l := by
  match l with
  |          [] => simp at hl
  |         [a] => simp [rMin]
  | a :: b :: l =>
    by_cases hR : R a (rMin R (b :: l) (by simp))
    · simp [rMin, hR]
    · simp [rMin, hR, rMin_in (b :: l) (by simp)]

lemma rMin_minimal [IsLinearOrder α R] (l : List α) (hl : l.length > 0) {a} (ha : a ∈ l) :
    R (rMin R l hl) a := by
  match l with
  |          [] => simp at hl
  |         [b] =>
    have : a = b := by simpa using ha
    simp [rMin, this, refl]
  | b :: c :: l =>
    let m := rMin R (c :: l) (by simp)
    suffices R (if R b m then b else m) a by simpa
    have : a = b ∨ a ∈ c :: l := by simpa using ha
    rcases this with (rfl | ha)
    · by_cases hRam : R a m
      · simp [hRam, refl]
      · simp [hRam, IsTotal.of_not hRam]
    · have hRma : R m a := rMin_minimal (c :: l) (by simp) (by simp [ha])
      by_cases hRbm : R b m
      · simp [hRbm, IsTrans.trans _ _ _ hRbm hRma]
      · simp [hRbm, hRma]

variable {R}

lemma eq_rMin_iff [IsLinearOrder α R] {l : List α} {hl : l.length > 0} :
    m = rMin R l hl ↔ m ∈ l ∧ (∀ a ∈ l, R m a) := by
  constructor
  · rintro rfl; exact ⟨by simp, fun _ ↦ rMin_minimal R l hl⟩
  · rintro ⟨hml, hmR⟩
    exact antisymm
      (show R m (rMin R l hl) from hmR _ (by simp))
      (show R (rMin R l hl) m from rMin_minimal R l hl hml)

lemma Bisubset.rMin_uniq [IsLinearOrder α R]
    {l₁ l₂ : List α} (h : l₁ ⊆⊇ l₂) {h₁ : l₁.length > 0} :
    rMin R l₁ h₁ = rMin R l₂ ((pos_length_iff h).mp h₁) := eq_rMin_iff.mpr
  ⟨h.left (by simp), fun a ha ↦ rMin_minimal R l₁ h₁ (h.right ha)⟩

end rMin

end List

/-! ## Finset -/

namespace Finset

variable {α : Type*} [DecidableEq α]

def qRec {β : Sort*} (F : List α → β)
    (hF : ∀ l₁ l₂, l₁ ⊆⊇ l₂ → F l₁ = F l₂) : Finset α → β
  | ⟨s, _⟩ => Quotient.liftOn s F fun l₀ l₁ e ↦ hF l₀ l₁ e.bisubset

@[simp] lemma qRec_toFinset {β : Sort*} (F : List α → β)
    (hF : ∀ l₁ l₂, l₁ ⊆⊇ l₂ → F l₁ = F l₂)
    (l : List α) : qRec F hF l.toFinset = F l := calc
  qRec F hF l.toFinset = F l.dedup := Quotient.liftOn_mk (s := List.isSetoid α) _ (fun l₀ l₁ e ↦ hF l₀ l₁ e.bisubset) _
  _                    = F l       := hF _ _ (by simp)

lemma qInd {P : Finset α → Prop} (h : ∀ l : List α, P l.toFinset) : ∀ s : Finset α, P s
  | ⟨s, hs⟩ => by
    induction' s using Quotient.ind with l
    have : ⟨⟦l⟧, hs⟩ = l.toFinset := by ext x; simp
    rw [this]
    exact h l

def norm [SubNat α] : Finset α → List α := qRec (fun l ↦ l.normalize) (fun _ _ ↦ List.bisubset_normalize_uniq)

@[simp] lemma finset_norm_eq_normalize [SubNat α] (l : List α) : l.toFinset.norm = l.normalize := by simp [norm]

#eval ({2, -7, 9, 3, 14} : Finset (ZMod 12)).norm

variable (R : α → α → Prop) [IsLinearOrder α R] [DecidableRel R]

def rMin? (s : Finset α) : Option α := qRec
  (fun l ↦ if h : l.length > 0 then some (l.rMin R h) else none)
  (fun l₁ l₂ h ↦ by
    by_cases hl₁ : l₁.length > 0
    · simp [hl₁, h.pos_length_iff.mp hl₁, h.rMin_uniq]
    · have : l₁ = [] := by simpa using hl₁
      rcases this
      have : l₂ = [] := List.bisubset_nil_iff.mp h.symm
      rcases this; simp) s

lemma rMin?_isSome_of_nonempty {s : Finset α} (hs : s.Nonempty) : (s.rMin? R).isSome := by
  induction' s using qInd with l
  simpa [rMin?] using show 0 < l.length from List.length_pos.mpr (by simpa using hs)

def rMin (s : Finset α) (hs : s.Nonempty) : α := (s.rMin? R).get (rMin?_isSome_of_nonempty R hs)

variable {R}

@[simp] lemma toFinset_rMin (l : List α) (hl : l.toFinset.Nonempty) :
    l.toFinset.rMin R hl = l.rMin R (List.length_pos.mpr (by simpa using hl)) := by
  simp [rMin, rMin?]

@[simp] lemma rMin_in (s : Finset α) (hs : s.Nonempty) : s.rMin R hs ∈ s := by
  induction' s using qInd; simp

lemma rMin_minimal (s : Finset α) (hs : s.Nonempty) {a} (ha : a ∈ s) :
    R (rMin R s hs) a := by
  induction' s using qInd with l;
  simp [List.rMin_minimal R _ _ (show a ∈ l by simpa using ha)]

end Finset

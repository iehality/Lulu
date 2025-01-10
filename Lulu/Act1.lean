import Lulu.Prologue
import Mathlib.Data.Finset.Lattice.Fold
/-! Pitch-Class Set Theory -/

namespace Lulu

abbrev Duodecimal := ZMod 12

abbrev Serie (n : ℕ) := List (ZMod n)

abbrev NormalForm (n : ℕ) := Finset (ZMod n)

abbrev Form (G : Type*) [Group G] (n : ℕ) [MulAction G (ZMod n)] := MulAction.Orbit G (NormalForm n)

abbrev PrimeForm (n : ℕ) := Form (DihedralGroup n) n

syntax "𝓈[" term,* "]" : term

variable {n : ℕ}

macro_rules
  | `(𝓈[$terms:term,*, $term:term]) => `($term :: 𝓈[$terms,*])
  | `(𝓈[$term:term]) => `($term :: List.nil)
  | `(𝓈[]) => `(List.nil)

def rdist (i j : ZMod n) : ℕ :=
  if j.val ≥ i.val then j.val - i.val else n + j.val - i.val

namespace Serie

def intervals : Serie n → List ℕ
  | []          => []
  | [_]         => []
  | i :: j :: s => (i - j).val :: intervals (j :: s)

#eval intervals (𝓈[2, 1, 4, 0] : Serie 12)
#eval intervals (𝓈[2, 13, 16] : Serie 12)

def indices (s : Serie n) : List ℕ := (intervals s).tails.map List.sum

#eval (𝓈[0, 1, 2] : Serie 12).normalize
#eval indices (𝓈[0, 1, 9, 2] : Serie 12).normalize
#eval indices (𝓈[1, 2, 0] : Serie 12)
#eval indices (𝓈[2, 0, 1] : Serie 12)

#eval indices (𝓈[2, 1, 0] : Serie 12).normalize
#eval indices (𝓈[1, 0, 2] : Serie 12)
#eval indices (𝓈[0, 2, 1] : Serie 12)

#eval intervals (𝓈[8, 9, 0, 4] : Serie 12)
#eval intervals (𝓈[9, 0] : Serie 12)

def IdxLex (s₁ s₂ : Serie n) : Prop := indices s₁ ≤ indices s₂

instance : IsPreorder (Serie n) IdxLex where
  refl s := le_refl (indices s)
  trans _ _ _ := le_trans

instance : DecidableRel (IdxLex : Serie n → Serie n → Prop) := fun s₁ s₂ ↦
  if h : indices s₁ ≤ indices s₂ then .isTrue h else .isFalse h

def rotationNorm (s : Serie n) : Serie n :=
  if h : s = [] then [] else
  List.rMin IdxLex s.rotations (by simp[List.length_pos.mpr h])

#eval rotationNorm (𝓈[4, 8, 12, 14] : Serie 12)

def atune (s : Serie n) : Serie n :=
  if h : s = [] then [] else
  let a := s.getLast h
  s.map (· - a)

#eval atune (𝓈[2, 3, 4, 8] : Serie 12)

#eval rotationNorm (𝓈[8, 9, 0, 4] : Serie 12)

end Serie

namespace NormalForm

def norm (s : NormalForm n) : Serie n := Serie.rotationNorm (Finset.norm s)

#eval ({7, 2, 8, 9, 3} : NormalForm 12).norm

#eval (DihedralGroup.sr (4 : ZMod 12) • {7, 2, 8, 9, 3} : NormalForm 12).norm

end NormalForm

#check Multiset.instRepr

namespace PrimeForm

def mk (s : NormalForm n) : PrimeForm n := ⟦s⟧

syntax "𝓅[" term,* "]" : term

variable {n : ℕ}

macro_rules
  | `(𝓅[$terms:term,*]) => `(PrimeForm.mk {$terms:term,*})

def normFinset : PrimeForm n → Finset (NormalForm n) :=
  Quotient.lift
    (fun s ↦ (s.image fun i ↦ DihedralGroup.r (-i) • s) ∪ (s.image fun i ↦ DihedralGroup.sr (-i) • s))
    (fun s t hst ↦ by
      match hst with
      | .intro (DihedralGroup.r k) s =>
        simp [←MulAction.mul_smul, MulAction.image_smul]
      | .intro (DihedralGroup.sr k) a =>
        have : ∀ x : ZMod n, k + (-k - x) = -x := fun x ↦ by ring
        simp [←MulAction.mul_smul, MulAction.image_smul, this, Finset.union_comm])

def σ := normFinset (⟦{11, 2, 3, 7}⟧ : PrimeForm 12)

/-! TODO: remove `unquot` -/
unsafe def norm (s : PrimeForm n) : Serie n :=
  let L := (s.normFinset.image NormalForm.norm).val.unquot
  if hL : L.length > 0 then
    Serie.atune (L.rMin Serie.IdxLex hL)
  else []

#eval norm (𝓅[11, 2, 3, 7] : PrimeForm 12)
#eval norm (𝓅[0,3,4,5,8] : PrimeForm 12)


end PrimeForm

end Lulu

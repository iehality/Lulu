import Lulu.Prologue

/-! Normal Form and Prime Form -/

namespace Lulu

abbrev Duodecimal := ZMod 12

/-! ## Series on $\mathbb{Z}/12\mathbb{Z}$ -/

abbrev Serie (n : ℕ) := List (ZMod n)

syntax "𝓈[" term,* "]" : term

variable {n : ℕ}

macro_rules
  | `(𝓈[$terms:term,*, $term:term]) => `($term :: 𝓈[$terms,*])
  |                `(𝓈[$term:term]) => `($term :: List.nil)
  |                          `(𝓈[]) => `(List.nil)

namespace Serie

def intervals : Serie n → List ℕ
  |          [] => []
  |         [_] => []
  | i :: j :: s => (i - j).val :: intervals (j :: s)

def indices (s : Serie n) : List ℕ := (intervals s).tails.map List.sum

def IdxLex (s₁ s₂ : Serie n) : Prop := indices s₁ ≤ indices s₂

instance : IsPreorder (Serie n) IdxLex where
  refl s := le_refl (indices s)
  trans _ _ _ := le_trans

instance : DecidableRel (IdxLex : Serie n → Serie n → Prop) := fun s₁ s₂ ↦
  if h : indices s₁ ≤ indices s₂ then .isTrue h else .isFalse h

def rotationNorm (s : Serie n) : Serie n :=
  if h : s = [] then [] else
  List.rMin IdxLex s.rotations (by simp[List.length_pos.mpr h])

def atune (s : Serie n) : Serie n :=
  if h : s = [] then [] else
  let a := s.getLast h
  s.map (· - a)

def dAtune (g : DihedralGroup n) (s : Serie n) : DihedralGroup n × Serie n :=
  if h : s = [] then (1, []) else
  let a := s.getLast h
  (.r (-a) * g, s.map (· - a))

end Serie

/-! ## Normal Form -/

abbrev NormalForm (n : ℕ) := Finset (ZMod n)

namespace NormalForm

syntax "𝓃[" term,* "]" : term

macro_rules
  | `(𝓃[$terms:term,*]) => `({$terms:term,*})

def norm (s : NormalForm n) : Serie n := Serie.rotationNorm (Finset.norm s)

end NormalForm

/-! ## Prime Form -/

abbrev Form (G : Type*) [Group G] (n : ℕ) [MulAction G (ZMod n)] := MulAction.Orbit G (NormalForm n)

abbrev SemiprimeForm (n : ℕ) := Form (MZMod n) n

abbrev PrimeForm (n : ℕ) := Form (DihedralGroup n) n

namespace SemiprimeForm

def mk (s : NormalForm n) : SemiprimeForm n := ⟦s⟧

syntax "𝓈𝓅[" term,* "]" : term

macro_rules
  | `(𝓈𝓅[$terms:term,*]) => `(PrimeForm.mk {$terms:term,*})

/-
def normFinset : SemiprimeForm n → Finset (NormalForm n) :=
  Quotient.lift
    (fun s ↦ (s.image fun i ↦ MZMod.ofZMod (-i) • s))
    (fun s t hst ↦ by
      match hst with
      |  .intro i s => { simp [←MulAction.mul_smul, MulAction.image_smul] })
-/

end SemiprimeForm

namespace PrimeForm

def mk (s : NormalForm n) : PrimeForm n := ⟦s⟧

syntax "𝓅[" term,* "]" : term

macro_rules
  | `(𝓅[$terms:term,*]) => `(PrimeForm.mk {$terms:term,*})

def normFinset : PrimeForm n → Finset (NormalForm n) :=
  Quotient.lift
    (fun s ↦ (s.image fun i ↦ DihedralGroup.r (-i) • s) ∪ (s.image fun i ↦ DihedralGroup.sr (-i) • s))
    (fun s t hst ↦ by
      match hst with
      |  .intro (DihedralGroup.r k) s =>
        simp [←MulAction.mul_smul, MulAction.image_smul]
      | .intro (DihedralGroup.sr k) a =>
        have : ∀ x : ZMod n, k + (-k - x) = -x := fun x ↦ by ring
        simp [←MulAction.mul_smul, MulAction.image_smul, this, Finset.union_comm])

/-! TODO: remove `unquot` -/
unsafe def norm (s : PrimeForm n) : Serie n :=
  let L := (s.normFinset.image NormalForm.norm).val.unquot
  if hL : L.length > 0 then
    Serie.atune (L.rMin Serie.IdxLex hL)
  else []

def snormf : Serie n → List (DihedralGroup n × Serie n) := fun s ↦
  (s.map fun i ↦ (DihedralGroup.r (-i), DihedralGroup.r (-i) • s)) ++
  (s.map fun i ↦ (DihedralGroup.sr (-i), DihedralGroup.sr (-i) • s))

def snorm (s : Serie n) : DihedralGroup n × Serie n :=
  let L := snormf s |>.map fun ⟨g, l⟩ ↦ ⟨g, NormalForm.norm l.toFinset⟩
  if hL : L.length > 0 then
    let ⟨g, l⟩ := L.rMin' Serie.IdxLex Prod.snd hL
    Serie.dAtune g l
  else (1, [])

#eval norm (𝓅[11, 2, 3, 7] : PrimeForm 12)

#eval norm (𝓅[0,3,4,5,8] : PrimeForm 12)

#eval snorm ([0,3,4,5,8] : Serie 12)

end PrimeForm

end Lulu

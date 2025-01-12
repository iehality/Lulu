import Lulu.Prologue
import Lulu.Widget.MusicXML

inductive BinTree where
  | nil : BinTree
  | zero : BinTree → BinTree
  | one : BinTree → BinTree

namespace Lulu

namespace Pitch

def mk (s : Septimal) (a : ℤ) (n : ℕ) : Pitch := ⟨s, a, n⟩

end Pitch

section notations

open Lean PrettyPrinter Delaborator SubExpr
open Septimal

declare_syntax_cat altered

declare_syntax_cat pitch

syntax "⤫pitch[" num "|"  pitch "]" : term

syntax "♭c" : altered
syntax "♮c" : altered
syntax "♯c" : altered
syntax "♭d" : altered
syntax "♮d" : altered
syntax "♯d" : altered
syntax "♭e" : altered
syntax "♮e" : altered
syntax "♯e" : altered
syntax "♭f" : altered
syntax "♮f" : altered
syntax "♯f" : altered
syntax "♭g" : altered
syntax "♮g" : altered
syntax "♯g" : altered
syntax "♭a" : altered
syntax "♮a" : altered
syntax "♯a" : altered
syntax "♭b" : altered
syntax "♮b" : altered
syntax "♯b" : altered

syntax altered: pitch

macro_rules
  | `(⤫pitch[$n:num | ♭c]) => `(Pitch.mk .c (-1) $n)
  | `(⤫pitch[$n:num |   ♮c]) => `(Pitch.mk .c 0 $n)
  | `(⤫pitch[$n:num | ♯c]) => `(Pitch.mk .c 1 $n)
  | `(⤫pitch[$n:num | ♭d]) => `(Pitch.mk .d (-1) $n)
  | `(⤫pitch[$n:num |   ♮d]) => `(Pitch.mk .d 0 $n)
  | `(⤫pitch[$n:num | ♯d]) => `(Pitch.mk .d 1 $n)
  | `(⤫pitch[$n:num | ♭e]) => `(Pitch.mk .e (-1) $n)
  | `(⤫pitch[$n:num |   ♮e]) => `(Pitch.mk .e 0 $n)
  | `(⤫pitch[$n:num | ♯e]) => `(Pitch.mk .e 1 $n)
  | `(⤫pitch[$n:num | ♭f]) => `(Pitch.mk .f (-1) $n)
  | `(⤫pitch[$n:num |   ♮f]) => `(Pitch.mk .f 0 $n)
  | `(⤫pitch[$n:num | ♯f]) => `(Pitch.mk .f 1 $n)
  | `(⤫pitch[$n:num | ♭g]) => `(Pitch.mk .g (-1) $n)
  | `(⤫pitch[$n:num |   ♮g]) => `(Pitch.mk .g 0 $n)
  | `(⤫pitch[$n:num | ♯g]) => `(Pitch.mk .g 1 $n)
  | `(⤫pitch[$n:num | ♭a]) => `(Pitch.mk .a (-1) $n)
  | `(⤫pitch[$n:num |   ♮a]) => `(Pitch.mk .a 0 $n)
  | `(⤫pitch[$n:num | ♯a]) => `(Pitch.mk .a 1 $n)
  | `(⤫pitch[$n:num | ♭b]) => `(Pitch.mk .b (-1) $n)
  | `(⤫pitch[$n:num |   ♮b]) => `(Pitch.mk .b 0 $n)
  | `(⤫pitch[$n:num | ♯b]) => `(Pitch.mk .b 1 $n)

#check ⤫pitch[2 | ♭a]

end notations

namespace Notation

inductive BasicVerticalAttriv where

inductive BasicHorizontalAttriv where
  | slur (n : ℕ)
  | tie (n : ℕ)

end Notation

inductive Notation (π : Type*) (V H : Type*) where
  | pitch (p : π)
  | horizontal (attr : Array H) (sub : List (Notation π V H))
  | vertical (attr : Array V) (sub : List (Notation π V H))

abbrev BasicNotation := Notation Pitch Notation.BasicVerticalAttriv Notation.BasicHorizontalAttriv

namespace Notation

partial def divisions : Notation n V H → ℕ
  |          pitch _ => 1
  | horizontal _ sub => sub.length * sub.foldl (fun ih ν ↦ Nat.lcm ih ν.divisions) 1
  |   vertical _ sub => sub.length * sub.foldl (fun ih ν ↦ Nat.lcm ih ν.divisions) 1

def cons (ν : Notation n V H) : Notation n V H → Notation n V H
  |          pitch p => pitch p
  | horizontal a sub => horizontal a (ν :: sub)
  |   vertical a sub => vertical a (ν :: sub)

section notations

open Lean PrettyPrinter Delaborator SubExpr
open Septimal

declare_syntax_cat hattr
declare_syntax_cat hattrs
declare_syntax_cat ntt_raw
declare_syntax_cat ntt

syntax "⤫ntt[" num "|"  ntt "]" : term

syntax "(" ntt,* ")" : ntt_raw
syntax "{" ntt,* "}" : ntt_raw
syntax pitch : ntt_raw

syntax ntt_raw ("#" num)?  : ntt

#check Array.foldrM

/-
macro_rules
  | `(⤫ntt[$n:num | ( $ν:ntt,* )]) => do
    let v ← ν.getElems.foldrM (β := Lean.TSyntax _) (init := ← `([])) (fun μ ih ↦
    `(⤫ntt[$n:num | $μ] :: $ih))
    `(horizontal #[] $v)
  | `(⤫ntt[$n:num | { $ν:ntt,* }]) => do
    let v ← ν.getElems.foldrM (β := Lean.TSyntax _) (init := ← `([])) (fun μ ih ↦ `(⤫ntt[$n:num | $μ] :: $ih))
    `(vertical #[] $v)
  | `(⤫ntt[$n:num | $p:pitch]) => `(pitch ⤫pitch[$n:num | $p])
-/

macro_rules
  | `(⤫ntt[$_:num |                               ()]) => `(horizontal #[] [])
  | `(⤫ntt[$n:num |                   ( $μ:ntt_raw )]) => `(horizontal #[] [⤫ntt[$n:num | $μ:ntt_raw]])
  | `(⤫ntt[$n:num |         ( $μ:ntt_raw, $ν:ntt,* )]) => `(cons ⤫ntt[$n:num | $μ:ntt_raw] ⤫ntt[$n:num | ($ν,*)])
  | `(⤫ntt[$_:num |           ( $μ:ntt_raw #$m:num )]) => `(horizontal #[] [⤫ntt[$m:num | $μ:ntt_raw]])
  | `(⤫ntt[$_:num | ( $μ:ntt_raw #$m:num, $ν:ntt,* )]) => `(cons ⤫ntt[$m:num | $μ:ntt_raw] ⤫ntt[$m:num | ($ν,*)])
  | `(⤫ntt[$_:num |                               {}]) => `(vertical #[] [])
  | `(⤫ntt[$n:num |                   { $μ:ntt_raw }]) => `(vertical #[] [⤫ntt[$n:num | $μ:ntt_raw]])
  | `(⤫ntt[$n:num |         { $μ:ntt_raw, $ν:ntt,* }]) => `(cons ⤫ntt[$n:num | $μ:ntt_raw] ⤫ntt[$n:num | {$ν,*}])
  | `(⤫ntt[$_:num |           { $μ:ntt_raw #$m:num }]) => `(vertical #[] [⤫ntt[$m:num | $μ:ntt_raw]])
  | `(⤫ntt[$_:num | { $μ:ntt_raw #$m:num, $ν:ntt,* }]) => `(cons ⤫ntt[$m:num | $μ:ntt_raw] ⤫ntt[$m:num | {$ν,*}])
  | `(⤫ntt[$n:num |                         $p:pitch]) => `(pitch ⤫pitch[$n:num | $p])

#check ⤫ntt[4 | (♮a)]
#check (⤫ntt[4 | {♮a#2, ♭e, (♭b#8, ♭f, {})}] : BasicNotation)


end notations

end Notation


end Lulu

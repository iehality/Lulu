import Lulu.Prologue

/-! ## XML -/

inductive XML where
  | raw (str : String) : XML
  | tag (s : String) (args : Array (String × String)) (elems : Array XML)
  | val (s : String) (args : Array (String × String)) (val : String)

structure XMLWithHeader where
  version : String := "1.0"
  encoding : String := "UTF-8"
  x : XML

class ToXML (α : Type*) where
  toXML : α → XML

namespace XML

partial def toStringAux (n : ℕ) : XML → String
  | .raw s =>
    let indent := String.replicate (2 * n) ' '
    indent ++ s
  | .tag s args elems =>
    let indent := String.replicate (2 * n) ' '
    indent ++ "<" ++ s ++ args.foldl (fun ih (r, v) ↦ ih ++ " " ++ r ++ "=" ++ "\"" ++ v ++ "\"") "" ++ ">"
    ++ elems.foldl (fun ih r ↦
      ih
      ++ "\n" ++ r.toStringAux (n + 1)) ""
    ++ "\n" ++ indent ++ "</" ++ s ++ ">"
  | .val s args v =>
    let indent := String.replicate (2 * n) ' '
    indent ++ "<" ++ s ++ args.foldl (fun ih (r, v) ↦ ih ++ " " ++ r ++ "=" ++ v) "" ++ ">"
    ++  v
    ++ "</" ++ s ++ ">"

protected def toString (x : XML) : String := x.toStringAux 0

instance : ToString XML := ⟨XML.toString⟩

def h (version : String := "1.0") (encoding : String := "UTF-8") (x : XML) : XMLWithHeader where
  version := version
  encoding := encoding
  x := x

end XML

namespace XMLWithHeader

protected def toString : XMLWithHeader → String
  | ⟨v, e, x⟩ => "<?xml version=\"" ++ v ++ "\" encoding=\"" ++ e ++ "\"?>\n" ++ toString x

instance : ToString XMLWithHeader := ⟨XMLWithHeader.toString⟩

end XMLWithHeader

namespace Lulu

/-! Basic Notational Types -/

inductive Septimal
  | c
  | d
  | e
  | f
  | g
  | a
  | b

namespace Septimal

def toStr : Septimal → String
  | c => "C"
  | d => "D"
  | e => "E"
  | f => "F"
  | g => "G"
  | a => "A"
  | b => "B"

instance : ToString Septimal := ⟨toStr⟩

end Septimal

inductive Dynamics where
  | pp
  | p
  | f
  | ff

namespace Dynamics

def toStr : Dynamics → String
  |  p => "p"
  | pp => "pp"
  |  f => "f"
  | ff => "ff"

instance : ToString Dynamics := ⟨toStr⟩

end Dynamics

inductive Duodecimal.Key
  | cFlat
  | c
  | cSharp
  | dFlat
  | d
  | dSharp
  | eFlat
  | e
  | fFlat
  | f
  | fSharp
  | gFlat
  | g
  | gharp
  | aFlat
  | a
  | aSharp
  | bFlat
  | b
  | bSharp

namespace Duodecimal

def toneNotation : Fin 12 → String
  | 0 => "C"
  | 1 => "♯C/♭D"
  | 2 => "D"
  | 3 => "♯D/♭E"
  | 4 => "E"
  | 5 => "F"
  | 6 => "♯F/♭G"
  | 7 => "G"
  | 8 => "♯G/♭A"
  | 9 => "A"
  | 10 => "♯A/♭B"
  | 11 => "B"

end Duodecimal

inductive Clef where
  | g : Clef  -- 𝄞
  | f : Clef -- 𝄢
  | c : Clef -- 𝄡
  | percussion : Clef

namespace Clef

instance : ToString Clef := ⟨fun s ↦
  match s with
  | .g => "g"
  | .f => "f"
  | .c => "c"
  | .percussion => "percussion"⟩

notation "𝄞" => Clef.g
notation "𝄢" => Clef.f
notation "𝄡" => Clef.c

end Clef

/-! ## MusicXML -/

namespace MusicXML

open ToXML

instance : ToXML Dynamics := ⟨fun d ↦
  XML.tag (toString d) #[] #[]
  ⟩

/-! ### Partwise / Part
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/measure-partwise/ -/

namespace ScorePartwise

/-! #### Part / Measure (partwise)
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/measure-partwise/ -/

namespace Part

namespace Measure

/-! ##### Attributes
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/attributes/ -/

inductive Attributes.Elems where
  | divisions (d : ℕ := 1)
  | key (k : ℤ)
  | time (beats : ℕ) (beatType : ℕ)
  | clef (sign : Clef) (line : ℕ :=
    match sign with
    | .g => 2
    | .f => 4
    | .c => 3
    | _  => 0)

instance : ToXML Attributes.Elems := ⟨fun e ↦
  match e with
  | .divisions d =>
    XML.val "divisions" #[] (toString d)
  | .key k =>
    XML.tag "key" #[] #[
      XML.val "fifths" #[] (toString k)
    ]
  | .time beats beatType =>
    XML.tag "time" #[] #[
      XML.val "beats" #[] (toString beats),
      XML.val "beat-type" #[] (toString beatType)
    ]
  | .clef sign line =>
    XML.tag "clef" #[] #[
      XML.val "sign" #[] (toString sign),
      XML.val "line" #[] (toString line)
    ]
  ⟩

structure Attributes where
  elems : Array Attributes.Elems

instance : ToXML Attributes := ⟨fun a ↦
  match a with
  | ⟨e⟩ =>
    XML.tag "attributes" #[] (e.map toXML)
  ⟩

/-! ##### Note
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/note/ -/

namespace Note

namespace Notations

structure Tuplet where
  number : ℕ
  placement : String := "above"
  type : String

end Notations

inductive Notations.Elems where
  | tied (t : String)
  | slur (s : String)
  | tuplet (t : Notations.Tuplet)

instance : ToXML Notations.Elems := ⟨fun e ↦
  match e with
  | .tied t =>
    XML.tag "tie" #[("type", t)] #[]
  | .slur s =>
    XML.tag "slur" #[("type", s)] #[]
  | .tuplet ⟨number, placement, type⟩ =>
    XML.tag "tuplet" #[("number", toString number), ("placement", placement), ("type", type)] #[]
  ⟩

structure Notations where
  elems : Array Notations.Elems

instance : ToXML Notations := ⟨fun a ↦
  match a with
  | ⟨e⟩ =>
    XML.tag "notations" #[] (e.map toXML)
  ⟩

/-
namespace Lyric

inductive Syllabric where
  | single
  | begin
  | end
  | middle

instance : ToString Syllabric := ⟨fun t ↦
  match t with
  | .single => "single"
  | .begin  => "begin"
  | .end    => "end"
  | .middle => "middle"⟩

end Lyric

structure Lyric where
  text : String
  syllabrc : Lyric.Syllabric
-/

end Note

inductive Note.Elems where
  | pitch (step : Septimal) (alter : ℤ) (octave : ℕ)
  | rest
  | duration (d : ℕ)
  | notations (n : Note.Notations)
  | tie (type : String)

instance : ToXML Note.Elems := ⟨fun e ↦
  match e with
  | .pitch step alter octave =>
    XML.tag "pitch" #[] #[
      XML.val "step" #[] (toString step),
      XML.val "alter" #[] (toString alter),
      XML.val "octave" #[] (toString octave)
    ]
  | .rest =>
    XML.tag "rest" #[("measure", "yes")] #[]
  | .duration d =>
    XML.val "duration" #[] (toString d)
  | .notations n =>
    toXML n
  | .tie t =>
    XML.tag "tie" #[("type", t)] #[]
  ⟩

structure Note where
  elems : Array Note.Elems

instance : ToXML Note := ⟨fun a ↦
  match a with
  | ⟨e⟩ =>
    XML.tag "note" #[] (e.map toXML)
  ⟩

end Measure

structure Measure where
  number : ℕ
  attributes : Measure.Attributes
  elems : Array Measure.Note

instance : ToXML Measure := ⟨fun m ↦
  match m with
  | ⟨n, a, e⟩ =>
    XML.tag "measure" #[("number", toString n)] (#[toXML a] ++ (e.map toXML))
  ⟩

end Part

structure Part where
  id : String
  elems : Array Part.Measure

instance : ToXML Part := ⟨fun m ↦
  match m with
  | ⟨i, e⟩ =>
    XML.tag "part" #[("id", toString i)] (e.map toXML)
  ⟩

namespace PartList

structure ScorePart where
  id : String
  partName : String

instance : ToXML ScorePart := ⟨fun s ↦
  match s with
  | ⟨i, n⟩ =>
    XML.tag "score-part" #[("id", toString i)] #[
      XML.val "part-name" #[] n
    ]
  ⟩

end PartList

structure PartList where
  elems : Array PartList.ScorePart

instance : ToXML PartList := ⟨fun l ↦
  match l with
  | ⟨e⟩ =>
    XML.tag "part-list" #[] (e.map toXML)
  ⟩

end ScorePartwise

structure ScorePartwise where
  version : String := "4.0"
  partList : ScorePartwise.PartList
  part : Array ScorePartwise.Part

instance : ToXML ScorePartwise := ⟨fun s ↦
  match s with
  | ⟨v, l, p⟩ =>
    XML.tag "score-partwise" #[("version", v)]
      (#[toXML l] ++ p.map toXML)
  ⟩

end MusicXML

structure MusicXML where
  scorePartwise : MusicXML.ScorePartwise

instance : ToXML MusicXML := ⟨fun m ↦
  match m with
  | ⟨s⟩ => ToXML.toXML s
  ⟩

instance : ToString MusicXML := ⟨fun m ↦ toString (ToXML.toXML m).h⟩

end Lulu

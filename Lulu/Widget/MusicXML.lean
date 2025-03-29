import Lulu.Prologue

/-! ## XML -/

inductive XML where
  | raw (str : String)
  | val (val : String)
  | tag (s : String) (args : Array (String × String)) (elems : Array XML)

structure XMLWithHeader where
  version : String := "1.0"
  encoding : String := "UTF-8"
  x : XML

class ToXML (α : Type*) where
  toXML : α → XML

namespace XML

private def initialTag (s : String) (args : Array (String × String)) : String :=
  "<" ++ s ++ args.foldl (fun ih (r, v) ↦ ih ++ " " ++ r ++ "=" ++ "\"" ++ v ++ "\"") "" ++ ">"

private def terminalTag (s : String) : String :=
  "</" ++ s ++ ">"

private def emptyTag (s : String) (args : Array (String × String)) : String :=
  "<" ++ s ++ args.foldl (fun ih (r, v) ↦ ih ++ " " ++ r ++ "=" ++ "\"" ++ v ++ "\"") "" ++ "/>"

partial def toStringAux (x : XML) (n : ℕ) : String :=
  let indent := String.replicate (2 * n) ' '
  match x with
  | .raw s =>
    indent ++ s
  | .val v =>
    indent ++ v
  | .tag s args #[] =>
    indent ++ emptyTag s args
  | .tag s args #[.val v] =>
    indent ++ initialTag s args ++ v ++ terminalTag s
  | .tag s args elems =>
    indent ++ initialTag s args
    ++
    elems.foldl (fun ih r ↦
      ih
      ++
      "\n"
      ++
      r.toStringAux (n + 1)) ""
    ++
    "\n"
    ++
    indent ++ terminalTag s

protected def toString (x : XML) : String := x.toStringAux 0

instance : ToString XML := ⟨XML.toString⟩

def h (version : String := "1.0") (encoding : String := "UTF-8") (x : XML) : XMLWithHeader where
  version := version
  encoding := encoding
  x := x

instance : ToXML ℕ := ⟨fun n ↦ .val (toString n)⟩

instance : ToXML ℤ := ⟨fun i ↦ .val (toString i)⟩

instance : ToXML String := ⟨.val⟩

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

protected def toString : Septimal → String
  | c => "C"
  | d => "D"
  | e => "E"
  | f => "F"
  | g => "G"
  | a => "A"
  | b => "B"

instance : ToString Septimal := ⟨Septimal.toString⟩

instance : ToXML Septimal := ⟨fun s ↦ .val s.toString⟩

end Septimal

inductive Dynamics where
  | pp
  | p
  | f
  | ff

namespace Dynamics

protected def toString : Dynamics → String
  |  p => "p"
  | pp => "pp"
  |  f => "f"
  | ff => "ff"

instance : ToString Dynamics := ⟨Dynamics.toString⟩

instance : ToXML Dynamics := ⟨fun d ↦ XML.tag d.toString #[] #[]⟩

end Dynamics

structure GeneralizedPitch (α : Type*) where
  step : α
  alter : ℤ
  octave : ℕ

abbrev Pitch := GeneralizedPitch Septimal

namespace GeneralizedPitch

protected def toString [ToString α] : GeneralizedPitch α → String
  | ⟨s, a, o⟩ =>
    match a with
    | 0 => "♮" ++ toString s ++ toString o
    | .negSucc i => String.replicate (i + 1) '♭' ++ toString s ++ toString o
    | .ofNat (i + 1) => String.replicate (i + 1) '♯' ++ toString s ++ toString o

instance [ToString α] : ToString  (GeneralizedPitch α) := ⟨GeneralizedPitch.toString⟩

instance : ToXML Pitch := ⟨fun p ↦
  match p with
  | ⟨step, alter, octave⟩ =>
    XML.tag "pitch" #[] #[
      XML.tag "step" #[] #[ToXML.toXML step],
      XML.tag "alter" #[] #[ToXML.toXML alter],
      XML.tag "octave" #[] #[ToXML.toXML octave]
    ]
  ⟩

end GeneralizedPitch

inductive Clef where
  | g : Clef  -- 𝄞
  | f : Clef -- 𝄢
  | c : Clef -- 𝄡
  | percussion : Clef



namespace Clef

instance : ToXML Clef := ⟨fun s ↦
            match s with
  |          .g => .val "g"
  |          .f => .val "f"
  |          .c => .val "c"
  | .percussion => .val "percussion"⟩

notation "𝄞" => Clef.g
notation "𝄢" => Clef.f
notation "𝄡" => Clef.c

end Clef

inductive NoteType
  | d1024
  | d512
  | d256
  | d128
  | d64
  | d32
  | d16
  | e
  | q
  | h
  | w
  | b
  | l
  | m

/-! Length of time when quarter note is set as 1. -/
structure QLength where
  val : ℚ

namespace NoteType

notation "𝅘𝅥𝅲" => d128
notation "𝅘𝅥𝅱" => d64
notation "𝅘𝅥𝅰" => d32
notation "𝅘𝅥𝅯" => d16
notation "𝅘𝅥𝅮" => e
notation "𝅘𝅥" => q
notation "𝅗𝅥" => h
notation "𝅝" => w
notation "𝅜" => b

instance : ToString NoteType := ⟨fun n ↦
  match n with
  | d1024 => "1024th"
  |  d512 => "512th"
  |  d256 => "256th"
  |  d128 => "𝅘𝅥𝅲"
  |   d64 => "𝅘𝅥𝅱"
  |   d32 => "𝅘𝅥𝅰"
  |   d16 => "𝅘𝅥𝅯"
  |     e => "𝅘𝅥𝅮"
  |     q => "𝅘𝅥"
  |     h => "𝅗𝅥"
  |     w => "𝅝"
  |     b => "𝅜"
  |     l => "long"
  |     m => "maxima"⟩

instance : ToXML NoteType := ⟨fun n ↦
  match n with
  | .d1024 => .val "1024th"
  |  .d512 => .val "512th"
  |  .d256 => .val "256th"
  |  .d128 => .val "128th"
  |   .d64 => .val "64th"
  |   .d32 => .val "32th"
  |   .d16 => .val "16th"
  |     .e => .val "eighth"
  |     .q => .val "quarer"
  |     .h => .val "half"
  |     .w => .val "whole"
  |     .b => .val "breve"
  |     .l => .val "long"
  |     .m => .val "maxima"⟩

def qToneLength : NoteType → QLength
  | d1024 => ⟨1/256⟩
  |  d512 => ⟨1/128⟩
  |  d256 => ⟨1/64⟩
  |  d128 => ⟨1/32⟩
  |   d64 => ⟨1/16⟩
  |   d32 => ⟨1/8⟩
  |   d16 => ⟨1/4⟩
  |     e => ⟨1/2⟩
  |     q => ⟨1⟩
  |     h => ⟨2⟩
  |     w => ⟨4⟩
  |     b => ⟨8⟩
  |     l => ⟨16⟩
  |     m => ⟨32⟩

instance : Coe NoteType QLength := ⟨qToneLength⟩

end NoteType

namespace QLength

def noteType (r : QLength) : NoteType :=
  if r.val ≤ NoteType.d1024.qToneLength.val then NoteType.d1024 else
  if r.val ≤ NoteType.d512.qToneLength.val then NoteType.d512 else
  if r.val ≤ NoteType.d256.qToneLength.val then NoteType.d256 else
  if r.val ≤ 𝅘𝅥𝅲.qToneLength.val then 𝅘𝅥𝅲 else
  if r.val ≤ 𝅘𝅥𝅱.qToneLength.val then 𝅘𝅥𝅱 else
  if r.val ≤ 𝅘𝅥𝅰.qToneLength.val then 𝅘𝅥𝅰 else
  if r.val ≤ 𝅘𝅥𝅯.qToneLength.val then 𝅘𝅥𝅯 else
  if r.val ≤ 𝅘𝅥𝅮.qToneLength.val then 𝅘𝅥𝅮 else
  if r.val ≤ 𝅘𝅥.qToneLength.val then 𝅘𝅥 else
  if r.val ≤ 𝅗𝅥.qToneLength.val then 𝅗𝅥 else
  if r.val ≤ 𝅝.qToneLength.val then 𝅝 else
  if r.val ≤ 𝅜.qToneLength.val then 𝅜 else
  if r.val ≤ NoteType.l.qToneLength.val then NoteType.l else
  NoteType.m

instance : Coe QLength NoteType := ⟨noteType⟩

end QLength

/-! ## MusicXML -/

namespace MusicXML

open ToXML

structure Duration where
  duration : ℕ

instance : ToXML Duration := ⟨fun d ↦
  match d with
  | ⟨duration⟩ => XML.tag "duration" #[] #[toXML duration]
  ⟩

/-! ### Partwise
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/measure-partwise/ -/

namespace ScorePartwise

/-! #### Part / Measure (partwise)
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/measure-partwise/ -/

namespace Part

namespace Measure

/-! ##### Attributes
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/attributes/ -/

inductive Attributes.Elems where
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
  | .key k =>
    XML.tag "key" #[] #[
      XML.tag "fifths" #[] #[toXML k]
    ]
  | .time beats beatType =>
    XML.tag "time" #[] #[
      XML.tag "beats" #[] #[toXML beats],
      XML.tag "beat-type" #[] #[toXML beatType]
    ]
  | .clef sign line =>
    XML.tag "clef" #[] #[
      XML.tag "sign" #[] #[toXML sign],
      XML.tag "line" #[] #[toXML line]
    ]
  ⟩

structure Attributes where
  divisions : ℕ := 1
  elems : Array Attributes.Elems := #[]

instance : ToXML Attributes := ⟨fun a ↦
  match a with
  | ⟨divisions, elems⟩ =>
    XML.tag "attributes" #[] (
      #[XML.tag "divisions" #[] #[toXML divisions]] ++
      elems.map toXML)
  ⟩

/-! ##### Note
  https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/note/ -/

namespace Note

namespace Notations

structure Tuplet where
  number : ℕ
  type : String

structure NestedTuplet where
  number : ℕ
  type : String
  actualNumber : ℕ
  actualType : NoteType
  normalNumber : ℕ
  normalType : NoteType

structure Slur where
  number : ℕ
  type : String

end Notations

inductive Notations.Elems where
  | tied (t : String)
  | slur (s : Notations.Slur)
  | tuplet (t : Notations.Tuplet)
  | nestedTuplet (t : Notations.NestedTuplet)

instance : ToXML Notations.Elems := ⟨fun e ↦
  match e with
  | .tied t =>
    XML.tag "tied" #[("type", t)] #[]
  | .slur ⟨number, type⟩ =>
    XML.tag "slur" #[("number", toString number), ("type", type)] #[]
  | .tuplet ⟨number, type⟩ =>
    XML.tag "tuplet" #[("number", toString number), ("type", type)] #[]
  | .nestedTuplet ⟨number, type, actualNumber, actualType, normalNumber, normalType⟩ =>
    XML.tag "tuplet" #[("number", toString number), ("type", type)] #[
      XML.tag "tuplet-actual" #[] #[
        XML.tag "tuplet-number" #[] #[toXML actualNumber],
        XML.tag "tuplet-type" #[] #[toXML actualType]
      ],
      XML.tag "tuplet-normal" #[] #[
        XML.tag "tuplet-number" #[] #[toXML normalNumber],
        XML.tag "tuplet-type" #[] #[toXML normalType]
      ]
    ]
  ⟩

structure Notations where
  elems : Array Notations.Elems

instance : ToXML Notations := ⟨fun a ↦
  match a with
  | ⟨e⟩ =>
    XML.tag "notations" #[] (e.map toXML)
  ⟩

/-! https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/beam/ -/
structure Beam where
  value : String
  number : ℕ := 1

structure TimeModification where
  actualNotes : ℕ
  normalNotes : ℕ
  normalType : NoteType

instance : ToXML TimeModification := ⟨fun t ↦
  match t with
  | ⟨a, n, nt⟩ =>
    XML.tag "time-modification" #[] #[
      XML.tag "actual-notes" #[] #[toXML a],
      XML.tag "normal-notes" #[] #[toXML n]--,
      --XML.tag "normal-type" #[] #[toXML nt]
    ]
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
  | dot
  | tie (type : String)
  | type (n : NoteType) -- https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/type/
  | timeModification (t : TimeModification) -- https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/time-modification/
  | stem (s : String) -- "up", "down", "none", "double" https://www.w3.org/2021/06/musicxml40/musicxml-reference/elements/stem/
  | beam (b : Note.Beam)
  | notations (n : Note.Notations)

instance : ToXML Note.Elems := ⟨fun e ↦
  match e with
  | .dot =>
    XML.tag "dot" #[] #[]
  | .type n =>
    XML.tag "type" #[] #[toXML n]
  | .timeModification t =>
    toXML t
  | .stem s =>
    XML.tag "stem" #[] #[toXML s]
  | .beam ⟨value, number⟩ =>
    XML.tag "beam" #[("number", toString number)] #[toXML value]
  | .notations n =>
    toXML n
  | .tie t =>
    XML.tag "tie" #[("type", t)] #[]
  ⟩

structure Tone where
  pitch : Pitch
  duration : Duration
  elems : Array Note.Elems := #[]

instance : ToXML Tone := ⟨fun a ↦
  match a with
  | ⟨pitch, duration, elems⟩ =>
    XML.tag "note" #[] (
      #[toXML pitch] ++
      #[toXML duration] ++
      elems.map toXML)
  ⟩

structure Rest where
  measure : String := "yes"
  duration : Duration
  elems : Array Note.Elems := #[]

instance : ToXML Rest := ⟨fun a ↦
  match a with
  | ⟨measure, duration, elems⟩ =>
    XML.tag "note" #[] (
      #[XML.tag "rest" #[("measure", measure)] #[]] ++
      #[toXML duration] ++
      elems.map toXML)
  ⟩

structure Chord where
  pitch : Pitch
  duration : Duration
  elems : Array Note.Elems := #[]

instance : ToXML Chord := ⟨fun a ↦
  match a with
  | ⟨pitch, duration, elems⟩ =>
    XML.tag "note" #[] (
      #[XML.tag "chord" #[] #[]] ++
      #[toXML pitch] ++
      #[toXML duration] ++
      elems.map toXML)
  ⟩

inductive Note where
  | raw (s : String)
  | tone (t : Tone)
  | rest (r : Rest)
  | chord (c : Chord)

instance : ToXML Note := ⟨fun n ↦
  match n with
  | .raw s => .raw s
  | .tone t => toXML t
  | .rest r => toXML r
  | .chord c => toXML c
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
    XML.tag "part" #[("id", i)] (e.map toXML)
  ⟩

namespace PartList

structure ScorePart where
  id : String
  partName : String

instance : ToXML ScorePart := ⟨fun s ↦
  match s with
  | ⟨i, n⟩ =>
    XML.tag "score-part" #[("id", i)] #[
      XML.tag "part-name" #[] #[toXML n]
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

namespace MusicXML.ScorePartwise.Part.Measure

namespace Note

inductive HorizontalProperty.Sign where
  | star | continue | end

structure HorizontalProperty where
  beam   : Array (ℕ × HorizontalProperty.Sign)
  tuplet : Array (ℕ × HorizontalProperty.Sign)
  slur   : Array (ℕ × HorizontalProperty.Sign)

namespace HorizontalProperty

def addBeam (p : ℕ × Sign) : HorizontalProperty → HorizontalProperty
  | ⟨b, t, s⟩ => ⟨b.push p, t, s⟩

def addTuplet (p : ℕ × Sign) : HorizontalProperty → HorizontalProperty
  | ⟨b, t, s⟩ => ⟨b.push p, t, s⟩

end HorizontalProperty

end Note

end MusicXML.ScorePartwise.Part.Measure

end Lulu

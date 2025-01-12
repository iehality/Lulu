import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

structure MusicXML where
  musicXML : String
  deriving ToJson, FromJson, Inhabited

@[widget_module]
def SheetMusicDisplay : Component MusicXML where
  javascript := include_str ".." / ".." / ".lake" / "build" / "js" / "SheetMusicDisplay.js"

import Lulu.Widget.Display
import Lulu.Widget.MusicXML

open Lean ProofWidgets
open scoped ProofWidgets.Jsx

namespace Lulu

def test : MusicXML :=
  ⟨
    {
      partList :=
        ⟨
          #[
            {
              id := "P1",
              partName := "Music"
            }
          ]
        ⟩,
      part :=
        #[
          {
            id := "P1",
            elems :=
              #[
                {
                  number := 1,
                  attributes :=
                    ⟨
                      #[
                        .divisions 24,
                        .key 0,
                        .time 4 4,
                        .clef 𝄞
                      ]
                    ⟩
                  elems :=
                    #[
                      { elems :=
                          #[
                            .pitch .c 0 4,
                            .duration 4
                          ]
                      },
                      { elems :=
                          #[
                            .pitch .b (-1) 4,
                            .duration 16
                          ]
                      }
                    ]
                }
              ]
          }
        ]
    }
  ⟩

#eval test

#html <SheetMusicDisplay musicXML={toString test} />

end Lulu

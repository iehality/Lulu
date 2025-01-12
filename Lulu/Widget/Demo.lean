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
                    {
                      divisions := 24,
                      elems := #[
                          .key (-4),
                          .time 8 8,
                          .clef 𝄞
                        ]
                    }
                  elems :=
                    #[
                      .tone {
                        pitch := ⟨.c, 0, 4⟩
                        duration := ⟨4⟩
                      },
                     .rest {
                        duration := ⟨16⟩
                      },
                     .tone {
                        pitch := ⟨.c, -1, 5⟩
                        duration := ⟨16⟩
                      },
                     .chord {
                        pitch := ⟨.e, 0, 4⟩
                        duration := ⟨16⟩
                      },
                     .chord {
                        pitch := ⟨.d, -2, 5⟩
                        duration := ⟨16⟩
                      },
                     .chord {
                        pitch := ⟨.g, 1, 5⟩
                        duration := ⟨16⟩
                      },
                     .chord {
                        pitch := ⟨.a, 0, 5⟩
                        duration := ⟨16⟩
                      },
                     .tone {
                        pitch := ⟨.a, 2, 3⟩
                        duration := ⟨16⟩
                        elems := #[
                          .tie "start",
                          .notations ⟨#[
                            .tied "start"
                          ]⟩
                        ]
                      },
                     .tone {
                        pitch := ⟨.a, 2, 3⟩
                        duration := ⟨32⟩
                        elems := #[
                          .tie "stop",
                          .notations ⟨#[
                            .tied "stop"
                          ]⟩
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

def tuplet : MusicXML :=
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
                    {
                      divisions := 6
                    }
                  elems :=
                    #[
                     .tone {
                        pitch := ⟨.a, -1, 4⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "begin"
                          },
                          .notations ⟨#[
                            .tuplet {
                              number := 1
                              type := "start"
                             },
                            .slur {
                              number := 1
                              type := "start"
                            }
                          ]⟩
                        ]
                      },
                     .tone {
                        pitch := ⟨.e, 0, 5⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "continue"
                          },
                          .tie "start",
                          .notations { elems := #[
                            .tied "start"
                          ] }
                        ]
                      },
                     .tone {
                        pitch := ⟨.e, 0, 5⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "continue"
                          },
                          .tie "stop",
                          .notations { elems := #[
                            .tied "stop"
                          ] }
                        ]
                      },
                     .tone {
                        pitch := ⟨.f, -1, 4⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "continue"
                          },
                          .notations ⟨#[
                          ]⟩
                        ]
                      },
                     .tone {
                        pitch := ⟨.d, 1, 4⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "continue"
                          },
                          .notations ⟨#[
                          ]⟩
                        ]
                      },
                     .tone {
                        pitch := ⟨.c, 0, 5⟩
                        duration := ⟨1⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .timeModification {
                            actualNotes := 6
                            normalNotes := 4
                            normalType := 𝅘𝅥𝅯
                           },
                          .beam {
                            number := 1,
                            value := "end"
                          },
                          .notations ⟨#[
                            .tuplet {
                              number := 1,
                              type := "stop"
                             },
                            .slur {
                              number := 1,
                              type := "stop"
                             }
                          ]⟩
                        ]
                      }
                    ]
                }
              ]
          }
        ]
    }
  ⟩

#eval tuplet

#html <SheetMusicDisplay musicXML={toString tuplet} />



end Lulu

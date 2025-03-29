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
                          .dot,
                          .notations ⟨#[
                            .tied "start"
                          ]⟩
                        ]
                      },
                     .tone {
                        pitch := ⟨.a, 2, 3⟩
                        duration := ⟨32⟩
                        elems := #[
                          .type 𝅘𝅥𝅯,
                          .dot,
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

def dot : MusicXML :=
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
      part :=#[
        {
          id := "P1",
          elems :=
            #[
              {
                number := 1
                attributes := { divisions := 1 }
                elems :=
                  #[
                    .tone
                      {
                        pitch := ⟨.c, 0, 4⟩
                        duration := ⟨1⟩
                        elems :=
                          #[
                            .type 𝅘𝅥𝅯,
                            .notations
                              ⟨
                                #[
                                  .tied "stop"
                                ]
                              ⟩
                          ]
                     }
                  ]
             }   ]
        }
      ]
    }
  ⟩

#eval dot

#html <SheetMusicDisplay musicXML={toString dot} />

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

def nestedTuplet : MusicXML :=
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
      part :=#[
        {
          id := "P1",
          elems :=
            #[
              {
                number := 1
                attributes := { divisions := 18 }
                elems :=
                  #[

.tone {
  pitch := ⟨.c, 0, 4⟩
  duration := ⟨9⟩
  elems :=
    #[
      .type 𝅘𝅥𝅮,
      .timeModification {
        actualNotes := 3
        normalNotes := 2
        normalType := 𝅘𝅥𝅮
      },
      .notations ⟨#[
        .tuplet {
          number := 1
          type := "start"
        }
      ]⟩
    ]
},

.tone {
  pitch := ⟨.g, 0, 4⟩
  duration := ⟨9⟩
  elems :=
    #[
      .type 𝅘𝅥𝅮,
      .timeModification {
        actualNotes := 3
        normalNotes := 2
        normalType := 𝅘𝅥𝅮
      },
      .notations ⟨#[
      ]⟩
    ]
},

.tone {
  pitch := ⟨.c, 0, 6⟩
  duration := ⟨3⟩
  elems :=
    #[
      .type 𝅘𝅥𝅯,
      .timeModification {
        actualNotes := 3
        normalNotes := 2
        normalType := 𝅘𝅥𝅯
      },
      .notations ⟨#[
        .nestedTuplet {
          number := 2
          type := "start"
          actualNumber := 3
          actualType := 𝅘𝅥𝅯
          normalNumber := 2
          normalType := 𝅘𝅥𝅯
        }
      ]⟩
    ]
},

.tone {
  pitch := ⟨.b, 0, 5⟩
  duration := ⟨3⟩
  elems :=
    #[
      .type 𝅘𝅥𝅯,
      .timeModification {
        actualNotes := 3
        normalNotes := 2
        normalType := 𝅘𝅥𝅯
      },
      .notations ⟨#[]⟩
    ]
},

.tone {
  pitch := ⟨.a, 0, 5⟩
  duration := ⟨3⟩
  elems :=
    #[
      .type 𝅘𝅥𝅯,
      .timeModification {
        actualNotes := 3
        normalNotes := 2
        normalType := 𝅘𝅥𝅯
      },
      .notations ⟨#[
        .tuplet {
          number := 1
          type := "stop"
        },
        .tuplet {
          number := 2
          type := "stop"
        }
      ]⟩
    ]
}

]}]}]}⟩

#eval nestedTuplet

#html <SheetMusicDisplay musicXML={toString nestedTuplet} />

def nestedTupletr : MusicXML :=
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
      part :=#[
        {
          id := "P1",
          elems :=
            #[
              {
                number := 1
                attributes := { divisions := 24 }
                elems :=
                  #[
.raw r#"
   <note>
      <pitch>
         <step>C</step>
         <octave>5</octave>
      </pitch>
      <duration>24</duration>
      <voice>1</voice>
      <type>quarter</type>
      <time-modification>
         <actual-notes>3</actual-notes>
         <normal-notes>2</normal-notes>
      </time-modification>
      <stem default-y="-50">down</stem>
      <notations>
         <tuplet bracket="yes" number="1" placement="above" type="start"/>
      </notations>
   </note>
   <note>
      <pitch>
         <step>B</step>
         <octave>4</octave>
      </pitch>
      <duration>24</duration>
      <voice>1</voice>
      <type>quarter</type>
      <time-modification>
         <actual-notes>3</actual-notes>
         <normal-notes>2</normal-notes>
      </time-modification>
      <stem default-y="-55">down</stem>
   </note>
   <note>
      <pitch>
         <step>A</step>
         <octave>4</octave>
      </pitch>
      <duration>8</duration>
      <voice>1</voice>
      <type>eighth</type>
      <time-modification>
         <actual-notes>9</actual-notes>
         <normal-notes>4</normal-notes>
         <normal-type>quarter</normal-type>
      </time-modification>
      <stem default-y="10">up</stem>
      <beam number="1">begin</beam>
      <notations>
         <tuplet number="2" bracket="no" placement="above" type="start">
            <tuplet-actual>
               <tuplet-number>3</tuplet-number>
               <tuplet-type>eighth</tuplet-type>
            </tuplet-actual>
            <tuplet-normal>
               <tuplet-number>1</tuplet-number>
               <tuplet-type>quarter</tuplet-type>
            </tuplet-normal>
         </tuplet>
      </notations>
   </note>
   <note>
      <pitch>
         <step>G</step>
         <octave>4</octave>
      </pitch>
      <duration>8</duration>
      <voice>1</voice>
      <type>eighth</type>
      <time-modification>
         <actual-notes>9</actual-notes>
         <normal-notes>4</normal-notes>
         <normal-type>quarter</normal-type>
      </time-modification>
      <stem default-y="8">up</stem>
      <beam number="1">continue</beam>
   </note>
   <note>
      <pitch>
         <step>F</step>
         <octave>4</octave>
      </pitch>
      <duration>8</duration>
      <voice>1</voice>
      <type>eighth</type>
      <time-modification>
         <actual-notes>9</actual-notes>
         <normal-notes>4</normal-notes>
         <normal-type>quarter</normal-type>
      </time-modification>
      <stem default-y="5">up</stem>
      <beam number="1">end</beam>
      <notations>
         <tuplet number="1" type="stop"/>
         <tuplet number="2" type="stop"/>
      </notations>
   </note>
"#
                  ]
             }   ]
        }
      ]
    }
  ⟩

#eval nestedTupletr

#html <SheetMusicDisplay musicXML={toString nestedTupletr} />

def sample1 : String :=
r#"
<?xml version="1.0" ?>
<score-partwise>
    <part-list>
        <score-part id="P1">
            <part-name>Piano</part-name>
        </score-part>
    </part-list>
    <part id="P1">
        <measure number="1">
            <attributes>
                <divisions>6</divisions>
                <time>
                    <beats>2</beats>
                    <beat-type>4</beat-type>
                </time>
            </attributes>
            <note>
                <pitch>
                    <step>C</step>
                    <octave>5</octave>
                </pitch>
                <duration>4</duration>
                <type>quarter</type>
                <time-modification>
                    <actual-notes>3</actual-notes>
                    <normal-notes>2</normal-notes>
                </time-modification>
                <notations>
                    <tuplet type="start"/>
                </notations>
            </note>
            <note>
                <pitch>
                    <step>C</step>
                    <octave>5</octave>
                </pitch>
                <duration>1</duration>
                <type>16th</type>
                <time-modification>
                    <actual-notes>3</actual-notes>
                    <normal-notes>2</normal-notes>
                </time-modification>
            </note>
            <note>
                <pitch>
                    <step>C</step>
                    <octave>5</octave>
                </pitch>
                <duration>3</duration>
                <type>eighth</type>
                <dot/>
                <time-modification>
                    <actual-notes>3</actual-notes>
                    <normal-notes>2</normal-notes>
                </time-modification>
            </note>
            <note>
                <pitch>
                    <step>C</step>
                    <octave>5</octave>
                </pitch>
                <duration>4</duration>
                <type>quarter</type>
                <time-modification>
                    <actual-notes>3</actual-notes>
                    <normal-notes>2</normal-notes>
                </time-modification>
                <notations>
                    <tuplet type="stop"/>
                </notations>
            </note>
        </measure>
    </part>
</score-partwise>
"#

#html <SheetMusicDisplay musicXML={sample1} />

end Lulu

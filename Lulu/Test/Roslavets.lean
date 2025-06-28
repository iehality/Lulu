import Lulu.PitchClass

namespace Lulu

open PrimeForm

def C : Fin 12 := 0
def Cis : Fin 12 := 1
def Ces : Fin 12 := -1
def D : Fin 12 := 2
def Dis : Fin 12 := 3
def Des : Fin 12 := 1
def E : Fin 12 := 4
def Eis : Fin 12 := 5
def Ees : Fin 12 := 3
def F : Fin 12 := 5
def Fis : Fin 12 := 6
def Fes : Fin 12 := 4
def G : Fin 12 := 7
def Gis : Fin 12 := 8
def Ges : Fin 12 := 6
def A : Fin 12 := 9
def Ais : Fin 12 := 10
def Aes : Fin 12 := 8
def B : Fin 12 := 11
def Bis : Fin 12 := 12
def Bes : Fin 12 := 10

-- Roslavets, Два сочинения (1915), I
#eval (𝓅[Bes, Eis, Gis, B, Ees, G, D] : PrimeForm 12).norm
#eval (𝓅[Ais, E, Aes, Cis, C, Ees, G] : PrimeForm 12).norm
#eval (𝓅[D, Bes, Fis, B, Des, F, Gis] : PrimeForm 12).norm

#eval snorm ([Bes, Eis, Gis, B, Ees, G, D] : Serie 12)
#eval snorm ([Ais, E, Aes, Cis, C, Ees, G] : Serie 12)
#eval snorm ([D, Bes, Fis, B, Des, F, Gis] : Serie 12)

end Lulu

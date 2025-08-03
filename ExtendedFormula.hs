module ExtendedFormula where

import Formula


import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow ((&&&), second)
import Data.List (intercalate)

{-
Reprezentarea extinsă a formulelor este necesară întrucât vom începe să eliminăm
literali din formule, dar algoritmii de rezolvare necesită atât forma curentă
a clauzelor cât și forma originală.

Prin urmare, în locul unei simple mulțimi de clauze, ca în etapa 1, utilizăm un 
tablou asociativ (Map), în care cheile sunt clauzele curente, supuse procesului 
de eliminare, iar valorile sunt clauzele originale. Fiecărei clauze curente îi 
corespunde clauza originală din care a fost obținută prin eliminare.

În continuare, vom denumi formulele din etapa 1 (Formula) formule
simple, în opoziție cu formulele extinse definite aici (ExtendedFormula).
-}
type ExtendedFormula = Map Clause Clause

{-
O acțiune efectuată asupra unei formule poate fi:

* Unit literal clause: eliminarea unicului literal dintr-o clauză unitară.
  "clause" reprezintă clauza originală din care s-a obținut clauza unitară.
  De exemplu, dacă din clauza originală {1, 2} s-a obținut clauza unitară {1}
  printr-o acțiune anterioară, acțiunea curentă de eliminare a clauzei unitare 
  {1} este Unit 1 {1, 2}, și nu Unit 1 {1}, întrucât informația ar fi devenit
  redundantă!
* Pure literal: eliminarea unui literal pur.
* Decide literal: eliminarea unui literal oarecare.
* NOP: operație fără efect.
-}
data Action
    = Unit   { getLiteral :: Literal, getClause :: Clause }
    | Pure   { getLiteral :: Literal }
    | Decide { getLiteral :: Literal }
    | NOP
    deriving (Show, Eq)

{-
Istoricul acțiunilor efectuate, începând cu cea mai recentă acțiune (sens
anticronologic).

Fiecare acțiune apare în pereche cu formula pe care a produs-o. Utilizăm o 
listă în regim de stivă, și nu o mulțime, întrucât ordinea temporală este
relevantă. Prima pereche corespunde celei mai recente acțiuni.
-}
type History = [(Action, ExtendedFormula)]

{-
Determină reprezentarea extinsă a unei formule simple. Inițial, înainte de vreo 
eliminare, cheile și valorile lor coincid.

>>> extendFormula $ toFormula [[1], [-2, 3]]
fromList [(fromList [-2,3],fromList [-2,3]),(fromList [1],fromList [1])]
-}
extendFormula :: Formula -> ExtendedFormula
extendFormula = Map.fromSet id

{-
Omologul lui toFormula din etapa 1.

>>> toExtendedFormula [[1], [-2, 3]]
fromList [(fromList [-2,3],fromList [-2,3]),(fromList [1],fromList [1])]
-}
toExtendedFormula :: [[Literal]] -> ExtendedFormula
toExtendedFormula = extendFormula . toFormula

{-
Determină formula simplă aferentă unei formule extinse. De interes este
varianta curentă a formulei extinse, surprinsă de chei, care reflectă acțiunile 
realizate, nu varianta originală, surprinsă de valori.

>>> baseFormula $ toExtendedFormula [[1], [-2, 3]]
fromList [fromList [-2,3],fromList [1]]
-}
baseFormula :: ExtendedFormula -> Formula
baseFormula = Map.keysSet

{-
Permite vizualizarea mai lizibilă a unui istoric de acțiuni, aplicând
constructorul de date HV asupra istoricului. Sunt evidențiate formulele produse
de acțiuni, surprinse de cheile tablourilor.

>>> HV [(NOP, toExtendedFormula [[1], [-2, 3]]), (NOP, toExtendedFormula [[4]])]
NOP => [[-2,3],[1]]
NOP => [[4]]
-}
newtype HistoryVisualizer = HV History
instance Show HistoryVisualizer where
    show (HV history) =
        intercalate "\n" $
        map (\(action, formula) ->
            show action ++ " => " ++
            show (toLiteralLists (baseFormula formula)))
        history

{-
*** TODO ***

Implementați funcționala promote, care promovează o funcție care operează pe o
o formulă simplă, la o funcție care operează pe o formulă extinsă. Funcționala
ne ajută să reutilizăm anumite funcții definite pe formule simple, fără a fi
nevoiți să le redefinim de la zero pentru formule extinse.

CONSTRÂNGERI:

* Utilizați stilul point-free.

Hint: Scrieți mai întâi funcția point-wise, și apoi vedeți cum puteți elimina
parametrii formali.

Exemple:

>>> promote formulaLiterals $ toExtendedFormula [[1, 2], [-2]]
fromList [-2,1,2]
-}
promote :: (Formula -> a) -> ExtendedFormula -> a
promote = (. baseFormula)

{-
*** TODO ***

Implementați funcția eliminate, care elimină un literal asumat adevărat dintr-o 
formulă extinsă. La nivelul cheilor, acest lucru înseamnă că:

* Toate clauzele care conțin literalul dispar.
* Toate aparițiile complementului literalului din clauzele rămase dispar.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe tablouri
  și funcțiile definite mai sus.
* Utilizați stilul point-free în prametrul formulă; puteți explicita totuși
  parametrul literal.

Exemple:

>>> eliminate 1 $ toExtendedFormula [[1, 2], [-1, 3]]
fromList [(fromList [3],fromList [-1,3])]

Mai sus, clauza {1, 2} dispare, iar din caluza { -1, 3} dispare literalul -1.

>>> eliminate (-1) $ toExtendedFormula [[1, 2], [-1, 3]]
fromList [(fromList [2],fromList [1,2])]

Mai sus, clauza { -1, 3} dispare, iar din caluza {1, 2} dispare literalul 1.
-}
eliminate :: Literal -> ExtendedFormula -> ExtendedFormula
eliminate literal = Map.foldrWithKey (\key val acc ->
        if Set.member literal key then acc
        else Map.insert (Set.delete (complement literal) key) val acc) Map.empty

{-
*** TODO ***

Implementați funcția firstPureLiteral, care determină primul literal pur dintr-o
formulă extinsă, dacă acesta există. Primul literal înseamnă cel mai mic, din 
perspectiva mulțimilor ordonate.

Reflectați dacă implementarea voastră desfășoară calcule doar până la 
determinarea primului literal pur sau îi determină nenecesar pe toți.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați funcția isPureLiteral din etapa 1.
* Utilizați funcția promote de mai sus.

Hint: Funcționalele pe mulțimi vizitează elementele în ordinea naturală.

Exemple:

>>> firstPureLiteral $ toExtendedFormula [[1], [-1]]
Nothing

>>> firstPureLiteral $ toExtendedFormula [[1, 2, 3], [2, -3]]
Just 1

Mai sus, 1 și 2 sunt literali puri, dar primul (cel mai mic) este 1.

>>> firstPureLiteral $ toExtendedFormula [[1, -2, -3], [-1, -2, -3]]
Just (-3)

Mai sus, -3 și -2 sunt literali puri, dar primul (cel mai mic) este -3.
-}
firstPureLiteral :: ExtendedFormula -> Maybe Literal
firstPureLiteral formula = Set.foldr
		(\literal acc -> if (promote (isPureLiteral literal)) formula then Just literal else acc)
		Nothing
		(Map.foldrWithKey (\key val acc -> Set.union key acc) Set.empty formula)

{-
*** TODO ***

Implementați funcția firstUnitClause, care determină prima clauză unitară 
dintr-o formulă extinsă, dacă aceasta există. Prima clauză înseamnă cea mai 
mică, din perspectiva mulțimilor ordonate. Mai precis, în caz afirmativ, 
funcția întoarce o pereche cu unicul literal al clauzei unitare, și clauza
originală din care s-a obținut clauza unitară. Clauza unitară este cheie, iar 
cea originală, valoare.

Reflectați dacă implementarea voastră desfășoară calcule doar până la 
determinarea primei clauze unitare sau le determină nenecesar pe toate.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe tablouri
  și funcțiile definite mai sus.
* Utilizați stitlul point-free.
* Utilizați funcția isUnitClause din etapa 1.

Hints:

* Funcționalele pe tablouri vizitează intrările în ordinea naturală a cheilor.
* Funcționala Map.foldrWithKey.

Exemple:

>>> firstUnitClause $ toExtendedFormula [[1, 2], [1, 3]]
Nothing

>>> firstUnitClause $ toExtendedFormula [[1], [-1, 2]]
Just (1,fromList [1])

>>> firstUnitClause $ eliminate 1 $ toExtendedFormula [[1], [-1, 2]]
Just (2,fromList [-1,2])

Mai sus, după eliminarea lui 1, obținem clauza unitară {2}, care corespunde
clauzei originale { -1, 2}.
-}
firstUnitClause :: ExtendedFormula -> Maybe (Literal, Clause)
firstUnitClause = Map.foldrWithKey (\key val acc -> if isUnitClause key then Just (Set.elemAt 0 key, val) else acc) Nothing

{-
*** TODO ***

Următoarele trei funcții trebuie toate implementate ca aplicații ale funcției 
process:

* decide
* processPureLiterals
* processUnitClauses.

Determinați parametrii formali pe care ar trebui să-i primească process pentru 
a dispune de toate informațiile necesare. Ideal, dacă surprindeți acoperitor în 
process părțile comune celor trei funcții de mai sus, acestea ar trebui să 
devină one-liners. Funcția process nu este punctată de sine stătător.

Hint: Pentru gestiunea conținutului unui (Maybe a), vă poate fi utilă funcția 
maybe.
-}
process :: (ExtendedFormula -> Maybe p)
		-> (p -> ExtendedFormula -> ExtendedFormula)
		-> (p -> Action)
		-> History
		-> History
process finder updater mkAction history =
	let latestForm = snd (head history)
	in case (finder latestForm) of
		Nothing -> history
		Just p -> (mkAction p, updater p latestForm) : history

{-
*** TODO ***

Implementați funcția decide, care elimină primul (cel mai mic) literal dintr-o
formulă extinsă.

Funcția primește ca parametru un istoric de acțiuni, care posedă pe prima 
poziție cea mai recentă intrare, și întoarce noul istoric, obținut prin 
adăugarea unei acțiuni Decide corespunzătoare, împreună cu formula extinsă pe 
care o produce.

CONSTRÂNGERI:

* Întreaga implementare trebuie să constituie o aplicație parțială a funcției
  process.
* Utilizați stilul point-free.

Exemple:

>>> HV $ decide [(NOP, toExtendedFormula [[1, -2, 3], [-3, -1, 2]])]
Decide {getLiteral = -3} => [[-2,1]]
NOP => [[-3,-1,2],[-2,1,3]]

Mai sus, se decide eliminarea celui mai mic literal, -3.
-}
decide :: History -> History
decide = process
		 (Set.lookupMin . promote formulaLiterals)
		 (\literal formula -> eliminate literal formula)
		 Decide

{-
*** TODO ***

Implementați funcția processPureLiterals, care, repetat, determină și elimină
primul (cel mai mic) literal pur dintr-o formulă extinsă. Prelucrarea continuă 
până când niciun literal pur nu mai este găsit. Este posibil ca literali care
inițial nu erau puri să devină puri după eliminarea altora.

Funcția primește ca parametru un istoric de acțiuni, care posedă pe prima 
poziție cea mai recentă intrare, și întoarce noul istoric, obținut prin 
adăugarea unei acțiuni Pure corespunzătoare, împreună cu formula extinsă pe 
care o produce.

CONSTRÂNGERI:

* Întreaga implementare trebuie să constituie o aplicație parțială a funcției
  process.
* Utilizați stilul point-free.
* Utilizați funcția firstPureLiteral.

Exemple:

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [2, 3], [-3, 4], [-4, 3]])]
Pure {getLiteral = 2} => [[-4,3],[-3,4]]
Pure {getLiteral = 1} => [[-4,3],[-3,4],[2,3]]
NOP => [[-4,3],[-3,4],[1,2],[2,3]]

Mai sus, primul literal pur este 1, și este eliminat. Apoi, primul literal pur
devine 2, eliminat și el.

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [1]])]
Pure {getLiteral = 1} => []
NOP => [[1],[1,2]]

Mai sus, este eliminat primul literal pur, 1, lucru care conduce și la 
dispariția implicită a literalului pur 2. Prin urmare, nu se mai adaugă (Pure 2)
la istoric.

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [-2, 3], [-3, -2]])]
Pure {getLiteral = -2} => []
Pure {getLiteral = 1} => [[-3,-2],[-2,3]]
NOP => [[-3,-2],[-2,3],[1,2]]

Mai sus, 1 este inițial singurul literal pur, și este eliminat. Apoi, -2, care
inițial nu era pur, devine pur, și este eliminat. Exemplul demonstrează 
necesitatea prelucrării repetate a formulei.
-}
processPureLiterals :: History -> History
processPureLiterals = until
						(maybe True (const False) . firstPureLiteral . snd . head)
						(process firstPureLiteral (\literal formula -> eliminate literal formula) 
						Pure)


{-
*** TODO ***

Implementați funcția processUnitClauses, care, repetat, determină și elimină
prima (cea mai mică) clauză unitară dintr-o formulă extinsă. Prelucrarea 
continuă până când nicio clauză unitară nu mai este găsită. Este posibil ca 
clauze care inițial nu erau unitare să devină unitare după eliminarea unor 
literali.

Funcția primește ca parametru un istoric de acțiuni, care posedă pe prima 
poziție cea mai recentă intrare, și întoarce noul istoric, obținut prin 
adăugarea unei acțiuni Unit corespunzătoare, împreună cu formula extinsă pe 
care o produce.

CONSTRÂNGERI:

* Întreaga implementare trebuie să constituie o aplicație parțială a funcției
  process.
* Utilizați stilul point-free.
* Utilizați funcția firstUnitClause.

Exemple:

>>> HV $ processUnitClauses [(NOP, toExtendedFormula [[1, 2], [1, 3], [2], [3]])]
Unit {getLiteral = 3, getClause = fromList [3]} => []
Unit {getLiteral = 2, getClause = fromList [2]} => [[1,3],[3]]
NOP => [[1,2],[1,3],[2],[3]]

Mai sus, prima clauză unitară este {2}, și este eliminată. Apoi, prima clauză 
unitară devine {3}, eliminată și ea.

>>> HV $ processUnitClauses [(NOP, toExtendedFormula [[1], [-2, -1]])]
Unit {getLiteral = -2, getClause = fromList [-2,-1]} => []
Unit {getLiteral = 1, getClause = fromList [1]} => [[-2]]
NOP => [[-2,-1],[1]]

Mai sus, {1} este inițial singura clauză unitară, și este eliminată. Apoi, 
clauza { -2, -1}, care inițial nu era unitară, devine unitară după eliminarea
literalului 1 din formulă, și este eliminată. Încă o dată, observați că în 
acțiunea Unit este stocată clauza originală { -2, -1} din care s-a obținut 
clauza unitară { -2}, nu clauza unitară în sine. Exemplul demonstrează 
necesitatea prelucrării repetate a formulei.
-}
processUnitClauses :: History -> History
processUnitClauses = until
						(maybe True (const False) . firstUnitClause . snd . head)
						(process firstUnitClause (\(lit, _) formula -> eliminate lit formula)
						(\(lit, orig) -> Unit lit orig))

{-
Exemplu de formulă
-}
formulaExample :: Formula
formulaExample = toFormula [[-4, -2, 3], [-3, 1, 2], [-1, 4]]

{-
Exemplu de istoric pentru formula de mai sus.

>>> HV historyExample
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]

Inițial, nu există nici clauze unitare, și nici literali puri; prin urmare, 
prima acțiune trebuie să fie o decizie. Se observă că, în urma celor trei 
acțiuni, se obține formula vidă, care este satisfiabilă, la fel ca formula 
originală. A fost suficient să asumăm adevărați literalii -4, -3 și -1.
-}
historyExample :: History
historyExample =
    processPureLiterals $
    processUnitClauses $
    decide [(NOP, extendFormula formulaExample)]

{-
*** TODO ***

Implementați funcția backtrackToUnitClause, care se întoarce în istoric la cel
mai distant punct din trecut în care cluaza primită ca parametru este unitară. 
Cu alte cuvinte, dacă parcurgem lista cronologic, de la originea temporală 
(ultima intrare) către prezent (prima intrare), punctul de interes este primul 
întâlnit cu proprietatea de mai sus. În plus, în noul istoric obținut, funcția 
adaugă noua clauză de ca și cum ar fi fost prezentă din start în formulă. 
Efectul acțiunilor păstrate în istoric trebuie reprodus asupra noii clauze.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe liste
  și funcțiile definite mai sus.
* Utilizați stilul point-free în prametrul istoric; puteți explicita totuși
  parametrul clauză.

Exemple:

>>> HV $ backtrackToUnitClause (toClause [4, 5]) historyExample
Decide {getLiteral = -4} => [[-3,1,2],[-1],[5]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4],[4,5]]

Mai sus, se revine la acțiunea (Decide (-4)), anulându-se efectul acțiunilor 
mai recente (Pure (-3)) și (Unit (-1) { -1, 4}). Aceasta este prima acțiune în
sens cronologic care face ca clauza {4, 5} să devină unitară. Ea ar fi rămas
unitară și după acțiunile mai recente (Unit (-1) { -1, 4}) și (Pure (-3)), dar 
dorim să ne întoarcem cât de mult posibil în trecut. În plus, versiunile 
clauzei {4, 5} sunt adăugate la versiunile formulei inițiale.
-}
backtrackToUnitClause :: Clause -> History -> History
backtrackToUnitClause clause = snd . foldr combine (clause, [])
  where
    combine (action, formula) acc@(clause', history) = case action of
        NOP -> buildNewAcc clause'
        _
            | isUnitClause clause' -> acc
            | otherwise -> buildNewAcc $
                           Set.delete (complement (getLiteral action)) clause'
      where
        buildNewAcc cls =
            (cls, (action, Map.insert cls clause formula) : history)

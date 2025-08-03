module Solver where

import Formula
import ExtendedFormula

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map

{-
Permite vizualizarea mai lizibilă a rezultatului funcției solve de mai jos,
având tipul (Maybe Interpretation, History).

>>> RV (Just $ Set.fromList [1, 2], historyExample)
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]
-----
Just (fromList [1,2])
-}
newtype ResultVisualizer = RV (Maybe Interpretation, History)
instance Show ResultVisualizer where
    show (RV (mInterpretation, history)) =
        show (HV history) ++ "\n-----\n" ++ show mInterpretation

{-
*** TODO ***

Implementați funcția resolve, care rezolvă două clauze, pe baza literalului 
primit ca parametru, care apare garantat în prima clauză. Se disting următoarele
situații:

* Dacă complementul literalului nu apare în cea de-a doua clauză, funcția o 
  întoarce pe aceasta nemodificată.
* Dacă complementul literalului apare în cea de-a doua clauză, funcția întoarce
  reuniunea celor două clauze, din care se înlătură literalul și complementul 
  său.

Exemple:

>>> resolve 1 (toClause [1, 2]) (toClause [3])
fromList [3]

>>> resolve 1 (toClause [1, 2]) (toClause [1, 3])
fromList [1,3]

>>> resolve 1 (toClause [1, 2]) (toClause [-1, 3])
fromList [2,3]

>>> resolve (-1) (toClause [-1, 2]) (toClause [1, 3, 4])
fromList [2,3,4]
-}
resolve :: Literal -> Clause -> Clause -> Clause
resolve literal clause1 clause2
  | not (Set.member (complement literal) clause2) = clause2
  | otherwise =
      let c1' = Set.delete literal clause1
          c2' = Set.delete (complement literal) clause2
      in  Set.union c1' c2'

{-
*** TODO ***

Implementați funcția learn, care învață o nouă clauză în baza unei clauze 
curente și a unei liste de acțiuni în sens anticronologic, corespunzătoare unui
istoric din etapa 2. Se disting următoarele situații:

* Orice acțiune diferită de Unit este ignorată.
* O acțiune Unit impune rezolvarea clauzei originale stocate în acțiune cu 
  clauza curentă, în baza literalului stocat de asemenea în acțiune, producând
  o nouă clauză curentă.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe liste
  și funcțiile definite mai sus.
* Utilizați stilul point-free.
* Utilizați funcția resolve.

Exemple:

>>> learn (toClause [1, 2]) [Unit (-1) (toClause [-1, 3])]
fromList [2,3]

>>> learn (toClause [1, 2]) [Unit (-1) (toClause [-1, 3]), Unit (-2) (toClause [-2, 4])]
fromList [3,4]

>>> learn (toClause [1, 2]) [Pure 2, Decide 1]
fromList [1,2]
-}
unitPair :: Action -> Maybe (Literal, Clause)
unitPair (Unit l c) = Just (l, c)
unitPair _ = Nothing

learn :: Clause -> [Action] -> Clause
learn initClause = 
	foldl (\cl (lit, orig) -> resolve lit orig cl) initClause . mapMaybe unitPair

{-
*** TODO ***

Implementați funcția satisfy, care primește ca parametru o formulă simplă, ca 
în etapa 1, și încearcă să o satisfacă, întorcând o pereche cu o intepretare 
opțională, prezentă doar dacă formula este satisfiabilă, și istoricul curent.

Algoritmul de satisfacere este următorul:

1. Se prelucrează toate clauzele unitare (funcția processUnitClauses).
2. Dacă formula devine vidă, formula originală este satisfiabilă și se 
   construiește interpretarea utilizând istoricul curent. STOP.
3. Dacă formula conține clauza vidă (conflict), se învață o nouă clauză 
   (funcția learn).
   3a. Dacă clauza învățată este vidă, formula este nesatisfiabilă. STOP.
   3b. Altfel, se revine în istoric la cel mai distant punct în care clauza
       învățată este unitară (funcția backtrackToUnitClause), și se sare la 
       pasul 1.
4. Se prelucrează toți literalii puri (funcția processPureLiterals) și se sare 
   la pasul 1.
5. Numai dacă nu există literali puri, se asumă cel mai mic literal (funcția 
   decide) și se sare la pasul 1.

CONSTRÂNGERI:

* Utilizați gărzi și pattern guards (vedeți descrierea laboratorului 6).

Exemple:

>>> RV $ satisfy $ toFormula [[1, 2], [-1]]
Unit {getLiteral = 2, getClause = fromList [1,2]} => []
Unit {getLiteral = -1, getClause = fromList [-1]} => [[2]]
NOP => [[-1],[1,2]]
-----
Just (fromList [-1,2])

Mai sus, două acțiuni Unit satisfac formula, iar interpretarea este { -1, 2}.

>>> RV $ satisfy $ toFormula [[1, 2, 3], [2, -3], [-1]]
Pure {getLiteral = 2} => []
Unit {getLiteral = -1, getClause = fromList [-1]} => [[-3,2],[2,3]]
NOP => [[-3,2],[-1],[1,2,3]]
-----
Just (fromList [-1,2])

Mai sus, existența clauzei unitare { -1} impune mai întâi acțiunea aferentă,
după care este posibilă eliminarea literalului pur 2, care satisface formula.

>>> RV $ satisfy formulaExample
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]
-----
Just (fromList [-4,-3,-1])

Mai sus, este reluat exemplul din scheletul etapei 2, în care se evidențiază
aceeași secvență de acțiuni.

>>> RV $ satisfy $ toFormula [[-1, -2, 3], [-1, 4, -3], [-1, -4, 5], [-1, -5, -3], [1, 2, 4]]
Unit {getLiteral = 1, getClause = fromList [1,2,4]} => []
Decide {getLiteral = -2} => [[1]]
Decide {getLiteral = -3} => [[-2,-1],[1,2]]
Decide {getLiteral = -4} => [[-3,-1],[-2,-1,3],[1,2]]
Decide {getLiteral = -5} => [[-4,-1],[-3,-1,4],[-2,-1,3],[1,2,4]]
NOP => [[-5,-3,-1],[-4,-1,5],[-3,-1,4],[-2,-1,3],[1,2,4]]
-----
Just (fromList [-5,-4,-3,-2,1])

>>> RV $ satisfy $ toFormula [[1], [-1]]
Unit {getLiteral = -1, getClause = fromList [-1]} => [[]]
NOP => [[-1],[1]]
-----
Nothing

Mai sus, se învață clauza vidă, deci formula este nesatisfiabilă.

>>> RV $ satisfy $ toFormula [[-7, 1], [-5, 1], [-3, 4], [3, -4], [-1, 2], [1, 2], [5, 7, -2], [-6, 1, -2], [6, -1, -2]]
Unit {getLiteral = -3, getClause = fromList [-3,4]} => []
Decide {getLiteral = -4} => [[-3]]
Unit {getLiteral = 6, getClause = fromList [-2,-1,6]} => [[-4,3],[-3,4]]
Unit {getLiteral = 2, getClause = fromList [-1,2]} => [[-4,3],[-3,4],[6]]
Unit {getLiteral = 1, getClause = fromList [-5,1]} => [[-4,3],[-3,4],[-2,6],[2]]
Unit {getLiteral = 5, getClause = fromList [5,7]} => [[-6,-2,1],[-4,3],[-3,4],[-2,-1,6],[-1,2],[1],[1,2]]
Decide {getLiteral = -7} => [[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5],[-1,2],[1,2],[5]]
NOP => [[-7,1],[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5,7],[-1,2],[1,2],[5,7]]
-----
Just (fromList [-7,-4,-3,1,2,5,6])

Exemplul de mai sus este cel din enunț, în care se învață clauza {5, 7}. Pentru 
completitudine, mai jos este istoricul intermediar obținut exact înainte de 
backtracking, declanșat de obținerea unei clauze vide.

Unit {getLiteral = -1, getClause = fromList [-1,2]} => [[],[-4,3],[-3,4]]
Unit {getLiteral = -2, getClause = fromList [-2,5,7]} => [[-4,3],[-3,4],[-1],[1]]
Decide {getLiteral = -5} => [[-4,3],[-3,4],[-2],[-2,-1],[-1,2],[1,2]]
Decide {getLiteral = -6} => [[-5,1],[-4,3],[-3,4],[-2,-1],[-2,5],[-1,2],[1,2]]
Decide {getLiteral = -7} => [[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5],[-1,2],[1,2]]
NOP => [[-7,1],[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5,7],[-1,2],[1,2]]
-}

buildInterp :: History -> Interpretation
buildInterp hist =
	Set.fromList
		[ x | (act, _) <- hist, x <- case act of
			Unit x _ -> [x]
			Pure x   -> [x]
			Decide x -> [x]
			NOP      -> []
		]

initialHistory :: Formula -> History
initialHistory formula = [(NOP, extendFormula formula)]

go :: History -> (Maybe Interpretation, History)
go history =
	let
		hUnit   = processUnitClauses history
		ef1     = snd (head hUnit)
		f1      = baseFormula ef1

		emptyCs = [c | c <- Set.toList f1, Set.null c]
	in
	if Set.null f1 then
		(Just (buildInterp hUnit), hUnit)

	else if not (null emptyCs) then
		let
			c0      = head emptyCs
			learned = learn c0 (map fst hUnit)
		in
		if Set.null learned
			then (Nothing, hUnit)
			else go (backtrackToUnitClause learned hUnit)

	else
		let hPure = processPureLiterals hUnit
		in if hPure /= hUnit
			then go hPure
			else go (decide hUnit)

satisfy :: Formula -> (Maybe Interpretation, History)
satisfy formula = go (initialHistory formula)

{-
Clasă ale cărei instanțe reprezintă probleme reductibile la SAT.

Clasa este parametrizată cu variabila de tip problem, și conține două funcții:

* encode transformă o instanță a problemei într-o instanță SAT, construind 
  formula corespunzătoare.
* decode transformă o interpretare în soluția problemei originale.

Variabila de tip problem referă o instanță a unei probleme, care conține
informații atât despre intrare, utilizată de encode și de decode, cât și despre 
ieșire, populată de decode. Prezența informațiilor despre ieșire în cadrul
aceleiași reprezentări care conține și informațiile despre intrare poate fi 
utilă, de exemplu, dacă se impune o soluție parțială încă de dinaintea 
codificării.
-}
class Reducible problem where
    encode :: problem -> Formula
    decode :: Interpretation -> problem -> problem

{-
Permite rezolvarea unei probleme prin reducere la și apoi de la SAT.
-}
reduceSolve :: Reducible problem => problem -> Maybe problem
reduceSolve problem = fmap (`decode` problem) $ fst $ satisfy $ encode problem

{-
Tipuri de date necesare reprezentării problemei 3-colorare.

* Node este tipul unui nod din graf.
* Graph este reprezentarea unui graf neorientat, ca mulțimi de noduri și de 
  muchii.
* Color denotă cele trei culori posibile.
* ThreeColoring este reprezentarea unei instanțe a problemei 3-colorare,
  în care câmpul graph desemnează intrarea, iar coloring, ieșirea. Cu toate
  că nu vom utiliza această facilitate în temă, câmpul coloring ar putea fi
  parțial populat încă de la început, înainte de reducerea la SAT, dacă se 
  dorește impunerea a priori a unor culori asupra anumitor noduri.
-}
type Node = Int

data Graph = Graph
    { nodes :: Set Node
    , edges :: Set (Node, Node)
    } deriving (Show, Eq)

data Color = Red | Green | Blue
    deriving (Show, Eq)

type Coloring = Map Node Color

data ThreeColoring = ThreeColoring
    { graph    :: Graph     -- intrarea
    , coloring :: Coloring  -- ieșirea
    } deriving (Show, Eq)

{-
*** TODO ***

Instanțiați clasa Reducible cu tipul ThreeColoring, implementând funcțiile
encode și decode, utilizând principiile din enunț.
-}
instance Reducible ThreeColoring where
{-
>>> toLiteralLists $ encode $ ThreeColoring graph2 Map.empty
[[-23,-22],[-23,-21],[-23,-13],[-22,-21],[-22,-12],[-21,-11],[-13,-12],[-13,-11],[-12,-11],[11,12,13],[21,22,23]]

>>> toLiteralLists $ encode $ ThreeColoring graph3 Map.empty
[[-33,-32],[-33,-31],[-33,-23],[-33,-13],[-32,-31],[-32,-22],[-32,-12],[-31,-21],[-31,-11],[-23,-22],[-23,-21],[-23,-13],[-22,-21],[-22,-12],[-21,-11],[-13,-12],[-13,-11],[-12,-11],[11,12,13],[21,22,23],[31,32,33]]
-}
    -- encode :: ThreeColoring -> Formula
    encode problem = undefined
    
{-
>>> coloring $ decode (Set.fromList [-23,-22,-13,-11,12,21]) $ ThreeColoring graph2 Map.empty
fromList [(1,Green),(2,Red)]

>>> coloring $ decode (Set.fromList [-33,-32,-23,-21,-12,-11,13,22,31]) $ ThreeColoring graph3 Map.empty
fromList [(1,Blue),(2,Green),(3,Red)]
-}
    -- decode :: Interpretation -> ThreeColoring -> ThreeColoring
    decode interpretation problem = undefined

{-
Exemple de grafuri neorientate.

>>> reduceSolve $ ThreeColoring graph2 Map.empty
Just (ThreeColoring {graph = Graph {nodes = fromList [1,2], edges = fromList [(1,2)]}, coloring = fromList [(1,Green),(2,Red)]})

>>> reduceSolve $ ThreeColoring graph3 Map.empty
Just (ThreeColoring {graph = Graph {nodes = fromList [1,2,3], edges = fromList [(1,2),(1,3),(2,3)]}, coloring = fromList [(1,Blue),(2,Green),(3,Red)]})
-}
graph2 :: Graph
graph2 = Graph
    { nodes = Set.fromList [1, 2]
    , edges = Set.fromList [(1, 2)]
    }

graph3 :: Graph
graph3 = Graph
    { nodes = Set.fromList [1, 2, 3]
    , edges = Set.fromList [(1, 2), (1, 3), (2, 3)]
    }

module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace

{-
O variabilă booleană este reprezentată printr-un întreg pozitiv: 1, 2 etc.

type introduce un sinonim de tip, similar cu typedef din C.
-}
type Variable = Int

{-
Un literal boolean desemnează o variabilă sau negația acesteia.

Este reprezentat printr-un întreg nenul: 1, 2, -1, -2 etc. Polaritatea 
literalului este surprinsă de semnul întregului; de exemplu, literalul 1 
desemnează variabila 1, iar literalul -1, negația acesteia. Întregul 0 este
exclus pentru că ar împiedica distingerea polarităților.
-}
type Literal = Int

{-
O clauză este o disjuncție de literali.

Este reprezentată ca o mulțime ordonată de literali. Această 
reprezentare surprinde natural unicitatea și irelevanța ordinii literalilor din 
clauză, și permite căutarea eficientă.
-}
type Clause = Set Literal

{-
O formulă CNF este o conjuncție de clauze.

Este reprezentată ca o mulțime ordonată de clauze.
-}
type Formula = Set Clause

{-
O interpretare este o mulțime de literali asumați adevărați.

De exemplu, interpretarea {1, -2} asumă că literalii 1 și -2 sunt adevărați,
adică variabila 1 este adevărată, și variabila 2, falsă.
-}
type Interpretation = Set Literal

{-
Construiește o clauză dintr-o listă de literali.
-}
toClause :: [Literal] -> Clause
toClause = Set.fromList

{-
Construiește o formulă dintr-o listă de liste de literali.
-}
toFormula :: [[Literal]] -> Formula
toFormula = Set.fromList . map toClause

{-
Transformă o formulă într-o listă de liste de literali, pentru lizibilitate.
-}
toLiteralLists :: Formula -> [[Literal]]
toLiteralLists = map Set.toList . Set.toList

{-
*** TODO ***

Implementați funcția literalVariable, care determină variabila referită de un
literal.

CONSTRÂNGERI:

* Utilizați stilul point-free.

Exemple:

>>> literalVariable 1
1

>>> literalVariable (-1)
1

Observați plasarea lui (-1) între paranteze. Absența lor, ca în
literalVariable -1, ar fi determinat scăderea lui 1 din literalVariable, 
operație fără sens.
-}
literalVariable :: Literal -> Variable
literalVariable = abs

{-
*** TODO ***

Implementați funcția isPositive, care verifică dacă polaritatea unui literal 
este pozitivă.

CONSTRÂNGERI:

* Utilizați stilul point-free.

Exemple:

>>> isPositive 1
True

>>> isPositive (-1)
False
-}
isPositive :: Literal -> Bool
isPositive = (> 0)

{-
*** TODO ***

Implementați funcția isNegative, care verifică dacă polaritatea unui literal 
este negativă.

CONSTRÂNGERI:

* Utilizați stilul point-free.

Exemple:

>>> isNegative 1
False

>>> isNegative (-1)
True
-}
isNegative :: Literal -> Bool
isNegative = (< 0)

{-
*** TODO ***

Implementați funcția complement, care determină literalul complementar.

CONSTRÂNGERI:

* Utilizați stilul point-free.

Exemple:

>>> complement 1
-1

>>> complement (-1)
1
-}
complement :: Literal -> Literal
complement = (* (-1))

{-
*** TODO ***

Implementați funcția formulaLiterals, care determină mulțimea tuturor 
literalilor dintr-o formulă.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free.

Exemple:

>>> formulaLiterals $ toFormula [[1, -2, 3], [-1, 2, 3]]
fromList [-2,-1,1,2,3]

Observați cum literalii sunt implicit ordonați în mulțime.
-}
formulaLiterals :: Formula -> Set Literal
formulaLiterals = Set.foldr Set.union Set.empty

{-
*** TODO ***

Implementați funcția clauseVariables, care determină mulțimea tuturor 
variabilelor dintr-o clauză.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free.

Exemple:

>>> clauseVariables $ toClause [1, -2, -1]
fromList [1,2]
-}
clauseVariables :: Clause -> Set Variable
clauseVariables = Set.map literalVariable

{-
*** TODO ***

Implementați funcția formulaVariables, care determină mulțimea tuturor 
variabilelor dintr-o formulă.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free.

Exemple:

>>> formulaVariables $ toFormula [[1, -2], [-1, 2, 3]]
fromList [1,2,3]
-}
formulaVariables :: Formula -> Set Variable
formulaVariables = clauseVariables.formulaLiterals

{-
*** TODO ***

Implementați funcția isPureLiteral, care verifică dacă un literal este pur 
într-o formulă, în sensul absenței complementului său din acea formulă.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free în parametrul formulă; puteți totuși explicita
  parametrul literal.

Exemple:

>>> isPureLiteral 1 $ toFormula [[1, -2, 3], [-1, 2, 3]]
False

>>> isPureLiteral 2 $ toFormula [[1, -2], [-1, 2, 3]]
False

>>> isPureLiteral 3 $ toFormula [[1, -2, 3], [-1, 2, 3]]
True

>>> isPureLiteral 3 $ toFormula [[1, -2], [-1, 2, 3]]
True
-}
isPureLiteral :: Literal -> Formula -> Bool
isPureLiteral literal = not . Set.member (complement literal) . formulaLiterals

{-
*** TODO ***

Implementați funcția isUnitClause, care verifică dacă o clauză este unitară,
i.e., conține un singur literal

CONSTRÂNGERI:

* Utilizați stilul point-free.

Exemple:

>>> isUnitClause $ toClause [1]
True

>>> isUnitClause $ toClause [1, 2]
False
-}
isUnitClause :: Clause -> Bool
isUnitClause = (== 1) . Set.size

{-
*** TODO ***

Implementați funcția isValidClause, care verifică dacă o clauză este 
întotdeauna adevărată, în sensul că ea conține atât un literal, cât și 
complementul acestuia.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați secțiuni, adică aplicații parțiale infixate, de forma (x `f`) sau
  (`f` y).

Hint: funcționala any.

Exemple:

>>> isValidClause $ toClause []
False

>>> isValidClause $ toClause [-1, 1, 2]
True

>>> isValidClause $ toClause [1, 2]
False
-}
isValidClause :: Clause -> Bool
isValidClause clause = Set.foldr (\l acc -> (complement l `Set.member` clause) || acc) False clause

{-
*** TODO ***

Implementați funcția isValidFormula, care verifică dacă o formulă este 
întotdeauna adevărată, în sensul că toate clauzele sale sunt întotdeauna
adevărate.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free.

Hint: funcționala all.

Exemple:

>>> isValidFormula $ toFormula []
True

>>> isValidFormula $ toFormula [[1, -1, 2], [-2, 2, 3]]
True

>>> isValidFormula $ toFormula [[1, -1, 2], [-2, 3]]
False
-}
isValidFormula :: Formula -> Bool
isValidFormula = Set.foldr (\elem acc -> isValidClause(elem) && acc) True

{-
*** TODO ***

Implementați funcția satisfiesFormula, care verifică dacă o interpretare 
satisface o formulă, în sensul că, asumând adevărați literalii din 
interpretare, formula este adevărată.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free în parametrul formulă; puteți totuși explicita
  parametrul interpretare.

Exemple:

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2]]
True

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2], [2]]
False

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2], [-2]]
True
-}
satisfiesFormula :: Interpretation -> Formula -> Bool
satisfiesFormula interpretation = Set.foldr (\cl acc -> (Set.foldr (\el a -> Set.member el interpretation || a) False cl) && acc) True 

{-
*** TODO ***

Implementați funcția interpretations, care generează lista tuturor 
interpretărilor aferente unei mulțimi de variabile.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.
* Utilizați stilul point-free.
* Utilizați list comprehensions.

Exemple:

>>> interpretations $ Set.empty
[fromList []]

>>> interpretations $ Set.fromList [1]
[fromList [1],fromList [-1]]

>>> interpretations $ Set.fromList [1, 2]
[fromList [1,2],fromList [-2,1],fromList [-1,2],fromList [-2,-1]]
-}
interpretations :: Set Variable -> [Interpretation]
interpretations = Set.foldr
  (\v acc -> [Set.insert v interpretation | interpretation <- acc] ++ [Set.insert (-v) interpretation | interpretation <- acc])
  [Set.empty]

{-
*** TODO ***

Implementați funcția isSatisfiable, care verifică dacă o formulă este 
satisfiabilă, adică adevărată în cel puțin o interepretare.

CONSTRÂNGERI:

* Evitați recursivitatea explicită, valorificând funcționalele pe mulțimi
  și funcțiile definite mai sus.

Exemple:

>>> isSatisfiable $ toFormula [[1, 2], [-2]]
True

>>> isSatisfiable $ toFormula [[1], [-1]]
False

>>> isSatisfiable $ toFormula []
True

>>> isSatisfiable $ toFormula [[]]
False

ÎNTREBĂRI:

1. Cum contribuie evaluarea leneșă la explorarea eficientă a interpretărilor?
2. Ce s-ar fi întâmplat dacă interpretations întorcea o mulțime (Set) de 
   interpretări în locul unei liste? Utilizați modulul Debug.Trace, deja 
   importat, pentru a vizualiza interpretările generate în cele două situații.
   
   Pentru a simula întoarcerea unui mulțimi din interpretations este suficient 
   să aplicați Set.fromList asupra listei întoarse de implementarea curentă în 
   corpul lui isSatisfiable.

RĂSPUNS: ...
-}
isSatisfiable :: Formula -> Bool
isSatisfiable formula = any (`satisfiesFormula` formula) (interpretations (formulaVariables formula))

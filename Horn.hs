import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Bits
import Data.ArAlex
import Data.Char
import Data.Typeable
import Data.List

data Formula = Predicate Name [Term] | Negation Formula
               | Conj [Formula] | Disj [Formula]
               | Implies Formula Formula | Equiv Formula Formula
               | ForAll Variable Formula | Exists Variable Formula

data Term = Function Name [Term] | Var [Char]
type Name = [Char]
type Variable = [Char]

type ClauseFormEquivalent = [Clause]
type Clause = [Literal]
data Literal = Pos Name [Term] | Neg Name [Term]

instance Show Formula where
    show (Predicate n terms) = "Predicate " ++ (show n) ++ " " ++ (show terms)
    show (Conj formulas) = "Conj " ++ (show formulas)
    show (Disj formulas) = "Disj " ++ (show formulas)
    show (Negation formula) = "Negation " ++ (show formula)
    show (ForAll v formula) = "ForAll " ++ (show v) ++ " (" ++ (show formula) ++ ")"
    show (Exists v formula) = "Exists " ++ (show v) ++ " (" ++ (show formula) ++ ")"

instance Show Term where
    show (Function n terms) = "Function " ++ (show n) ++ " " ++ (show terms)
    show (Var c) = "Var " ++ (show c)

instance Show Literal where
    show (Pos n terms) = "Pos " ++ (show n) ++ (show terms)
    show (Neg n terms) = "Neg " ++ (show n) ++ (show terms)


-- Eliminate Implication/Equivalences
------------------------------------------------------------------------------------------------------------------------
eliminate1 :: Formula -> Formula

eliminate1 f@(Predicate n terms) = f
eliminate1 (Negation f) = (Negation (eliminate1 f))
eliminate1 (Conj formulas) = Conj (map eliminate1 formulas)
eliminate1 (Disj formulas) = Disj (map eliminate1 formulas)
eliminate1 (ForAll v f) = ForAll v (eliminate1 f)
eliminate1 (Exists v f) = Exists v (eliminate1 f)
eliminate1 (Implies f1 f2) = Disj [Negation (eliminate1 f1), eliminate1 f2]
eliminate1 (Equiv f1 f2) = 
   let (e1, e2) = (eliminate1 f1, eliminate1 f2)
       in Conj [Disj [Negation e1, e2], Disj [Negation e2, e1]]

--Inward Propagation of Negations
------------------------------------------------------------------------------------------------------------------------       
propagate :: Formula -> Formula
negatef :: Formula -> Formula

propagate f@(Predicate n terms) = f
propagate (Negation f) = negatef f
propagate (Conj formulas) = Conj (map propagate formulas)
propagate (Disj formulas) = Disj (map propagate formulas)
propagate (ForAll v f) = ForAll v (propagate f)
propagate (Exists v f) = Exists v (propagate f)

negatef f@(Predicate n terms) = (Negation f)
negatef (Negation f) = propagate f
negatef (Conj formulas) = Disj (map negatef formulas)
negatef (Disj formulas) = Conj (map negatef formulas)
negatef (ForAll v f) = Exists v (negatef f)
negatef (Exists v f) = ForAll v (negatef f)

--Standardize Variables
------------------------------------------------------------------------------------------------------------------------
addNum c list num
    | elem c list = addNum ((init c) ++ (show num)) list (num + 1)
    | otherwise = c

anInit c list
    | elem c list = addNum (c ++ (show 0)) list 1
    | otherwise = c

checkNum c list num
    | elem (c ++ (show num)) list = checkNum c list (num + 1)
    | otherwise = (c ++ (show (num - 1)))

cnInit c list
    | elem (c ++ (show 0)) list = checkNum c list 1
    | otherwise = c

checkTerm (Var c) list = (Var (anInit c list),[anInit c list])
checkTerm (Function n terms) list = (Function n (fst (readTerms terms list)), list ++ (snd (readTerms terms list)))

readTerms [] list = ([],list)
readTerms (t:terms) list = (([fst (checkTerm t list)]) ++ (fst (readTerms terms list)) , snd (checkTerm t list) )

readFormulas [] list = ([],list)
readFormulas (f:formulas) list = ( ([fst constdv] ++ (fst (readFormulas formulas (snd constdv) ))), (snd (readFormulas formulas (snd constdv) ) ))
                            where constdv = standardizev (f,list)

standardizev (Predicate n terms, list) = (Predicate n (fst continue), list ++ (snd continue))
                                    where continue = (readTerms terms list)

standardizev (ForAll v f, list)  = (ForAll checkV (fst (standardizev (f,list))), (snd (standardizev (f,list))))
                                where checkV = cnInit v (snd (standardizev (f,list)))
standardizev (Exists v f, list)  = (Exists checkV (fst (standardizev (f,list))), (snd (standardizev (f,list))))
                                where checkV = cnInit v (snd (standardizev (f,list)))

standardizev (Conj formulas, list)  = (Conj (fst (readFormulas formulas list)), (snd (readFormulas formulas list)))
standardizev (Disj formulas, list)  = (Disj (fst (readFormulas formulas list)), (snd (readFormulas formulas list)))
standardizev (Negation f, list)  = (Negation (fst continue), (snd continue))
                                where continue = (standardizev (f,list))

stanvInit formula = fst (standardizev (formula,[]))

--Eliminate Existential Quanitifiers
------------------------------------------------------------------------------------------------------------------------

inSkolemVars [] = []
inSkolemVars (u:unilist) = [Var u] ++ (inSkolemVars unilist)

skolemVar unilist eqlist = (Function ("skolem" ++ (head eqlist)) (inSkolemVars unilist), (unilist, [show ( (read (head eqlist) :: Integer) + 1)] ++ (tail eqlist)))

readVar (Var c) unilist eqlist
    | elem c eqlist = skolemVar unilist eqlist
    | otherwise = (Var c, (unilist, eqlist) )
readVar (Function n terms) unilist eqlist = (Function n (fst (skolemTerm terms unilist eqlist)) , (unilist, snd (snd (skolemTerm terms unilist eqlist) ) ) )

skolemTerm [] unilist eqlist = ([],(unilist,eqlist))
skolemTerm (t:terms) unilist eqlist = ( ([fst (readVar t unilist eqlist)]) ++ (fst (skolemTerm terms unilist (snd (snd (readVar t unilist eqlist))))), (unilist, snd (snd (skolemTerm terms unilist (snd (snd (readVar t unilist eqlist)))))) )

moreFormulas [] unilist eqlist = ([],(unilist,eqlist))
moreFormulas (f:formulas) unilist eqlist = (([fst (elimExists (f,(unilist, eqlist)))] ++ (fst recurMF)), (unilist, (snd (snd recurMF)) ))
                                    where recurMF = moreFormulas formulas (fst (snd (elimExists (f,(unilist, eqlist))))) (snd (snd (elimExists (f,(unilist, eqlist)))))

elimExists (Predicate n terms, (unilist, eqlist)) = (Predicate n (fst (skolemTerm terms unilist eqlist)), (unilist, snd (snd (skolemTerm terms unilist eqlist))) )
elimExists (Negation f, (unilist, eqlist)) = (Negation (fst (elimExists (f,(unilist,eqlist)))), (unilist, snd (snd (elimExists (f,(unilist,eqlist)))) ))
elimExists (Conj formulas, (unilist, eqlist)) = (Conj (fst (moreFormulas formulas unilist eqlist)),(unilist, snd (snd (moreFormulas formulas unilist eqlist))))
elimExists (Disj formulas, (unilist, eqlist)) = (Disj (fst (moreFormulas formulas unilist eqlist)),(unilist, snd (snd (moreFormulas formulas unilist eqlist))))
elimExists (ForAll v f, (unilist, eqlist)) = (ForAll v (fst conEE),(unilist ++ [v], (snd (snd conEE))))
                                    where conEE = elimExists (f, (unilist ++ [v], eqlist) )
elimExists (Exists v f, (unilist, eqlist)) = elimExists (f,(unilist,eqlist ++ [v]))

elimExistsInit formula = fst (elimExists (formula,([],["0"])))

--Eliminate Universal Quanitifiers
------------------------------------------------------------------------------------------------------------------------

elimUni f@(Predicate n terms) = f
elimUni (Negation f) = Negation (elimUni f)
elimUni (Conj formulas) = Conj (map elimUni formulas)
elimUni (Disj formulas) = Disj (map elimUni formulas)
elimUni (ForAll v f) = elimUni f

-- CNF
------------------------------------------------------------------------------------------------------------------------

checkConj (Conj formulas) = inConj formulas
checkConj (Negation f) = [Negation (flatten f)]
checkConj f@(Predicate n terms) = [f]
checkConj (Disj formulas) = [flatten (Disj formulas)]

inConj [] = []
inConj (f:formulas) = checkConj f ++ inConj formulas 

checkInDisj (Conj formulas) = [Conj (inConj formulas)]
checkInDisj (Negation f) = [Negation (flatten f)]
checkInDisj f@(Predicate n terms) = [f]
checkInDisj (Disj formulas) = inDisj formulas

inDisj :: [Formula] -> [Formula]

inDisj [] = []
inDisj (f:formulas) = checkInDisj f ++ inDisj formulas

-- Remove inner Disj and inner Conj
flatten f@(Predicate n terms) = f
flatten (Negation f) = Negation (flatten f)
flatten (Conj formulas) = Conj (inConj formulas)
flatten (Disj formulas) = Disj (inDisj formulas)


isConj (Conj _) = True
isConj _ = False

conjInLayer [] = False
conjInLayer (f:formulas) = isConj f || conjInLayer formulas

propConj :: Formula -> [Formula] -> [Formula]
propConj (Conj (c:cf)) formulas = [Disj ([c] ++ formulas)] ++ propConj (Conj cf) formulas
propConj _ formulas = []

inConjDisj :: [Formula] -> Formula -> [Formula] -> [Formula]
inConjDisj before present [] = propConj present (before)
inConjDisj before present after
    | isConj present = propConj present (before ++ after)
    | otherwise = inConjDisj (before ++ [present]) (head after) (tail after)

checkCiD formulas
    | conjInLayer formulas = flattenConjInDisj (Conj (inConjDisj [] (head formulas) (tail formulas)))
    | otherwise = Disj (map flattenConjInDisj formulas)

--Propagate out Conj in Disj
flattenConjInDisj f@(Predicate n terms) = f
flattenConjInDisj (Negation f) = Negation (flattenConjInDisj f)
flattenConjInDisj (Conj formulas) = Conj (map flattenConjInDisj formulas)
flattenConjInDisj (Disj formulas) = (checkCiD formulas)

flattenInit formula = flatten(flattenConjInDisj (flatten formula))

-- Clause-Form Equivalent
------------------------------------------------------------------------------------------------------------------------

convertLit (Predicate n terms) = Pos n terms
convertLit (Negation (Predicate n terms)) = Neg n terms

convertClause (Disj f) = map convertLit f
convertClause f = [convertLit f]

convertCFE (Conj f) = map convertClause f
convertCFE _ = []

formulaToCFE formula = convertCFE (flattenInit (elimUni (elimExistsInit (stanvInit (propagate (eliminate1 formula))))))



-------------------------------------------------------------------------------------------------------------------------
-- Puzzle examples to use as input
-------------------------------------------------------------------------------------------------------------------------

-- Puzzle 1

-- Tati is a member of: [First, Second, Third, Fourth]
l1 = (Disj [(Predicate "Tati" [Var "FirstS"]), (Predicate "Tati" [Var "SecondS"]), 
    (Predicate "Tati" [Var "ThirdS"]), (Predicate "Tati" [Var "FourthS"])])
-- James is a member of: [First, Second, Third, Fourth]
m1 = (Disj [(Predicate "James" [Var "FirstS"]), (Predicate "James" [Var "SecondS"]), 
    (Predicate "James" [Var "ThirdS"]), (Predicate "James" [Var "FourthS"])])
-- Jack is a member of: [First, Second, Third, Fourth]
n1 = (Disj [(Predicate "Jack" [Var "FirstS"]), (Predicate "Jack" [Var "SecondS"]), 
    (Predicate "Jack" [Var "ThirdS"]), (Predicate "Jack" [Var "FourthS"])])
-- Lee is a member of: [First, Second, Third, Fourth]
o1 = (Disj [(Predicate "Lee" [Var "FirstS"]), (Predicate "Lee" [Var "SecondS"]), 
    (Predicate "Lee" [Var "ThirdS"]), (Predicate "Lee" [Var "FourthS"])])


-- ¬FirstS(Tati) ∧ ¬FirstB(Tati)
a1 = (Conj [(Negation (Predicate "Tati" [Var "FirstS"])), (Negation (Predicate "Tati" [Var "FirstB"]))])

-- FourthS(James) -> SecondS(Tati) ∨ (ThirdS(Tati)
b1 = (Implies (Predicate "James" [Var "FourthS"]) (Disj [(Predicate "Tati" [Var "SecondS"]), (Predicate "Tati" [Var "ThirdS"])]))

-- ThirdS(James) ∨ FourthS(James) -> SecondS(Tati)
c1 = (Implies (Disj [(Predicate "James" [Var "ThirdS"]), (Predicate "James" [Var "FourthS"])]) (Predicate "Tati" [Var "SecondS"]))

-- FourthB(James) -> SecondB(Tati)  ∨ (ThirdB(Tati)
d1 = (Implies (Predicate "James" [Var "Fourth"]) (Predicate "Tati" [Var "Second"]))

-- ThirdB(James) ∨ FourthB(James) -> SecondB(Tati)
e1 = (Implies (Disj [(Predicate "James" [Var "Third"]), (Predicate "James" [Var "Fourth"])]) (Predicate "Tati" [Var "Second"]))

-- ∃x(FirstS(x) -> ThirdB(x))
f1 = (Exists "x" (Implies (Predicate "x" [Var "FirstS"]) (Predicate "x" [Var "ThirdB"])))

-- FirstB(Jack)
g1 = (Predicate "Jack" [Var "FirstB"])

-- SecondS(Jack) -> FirstS(Lee)
h1 = (Implies (Predicate "Jack" [Var "SecondS"]) (Predicate "Lee" [Var "FirstS"]))

-- ThirdS(Jack) -> FirstS(Lee)) ∨ SecondS(Lee)
i1 = (Implies (Predicate "Jack" [Var "ThirdS"]) (Disj [(Predicate "Lee" [Var "FirstS"]), (Predicate "Lee" [Var "SecondS"])]))
    
-- FourthS(Jack) -> ∧ FirstS(Lee)) ∨ SecondS(Lee) ∧ ThirdS(Lee))
j1 = (Implies (Predicate "Jack" [Var "FourthS"]) (Disj [(Predicate "Lee" [Var "FirstS"]), (Predicate "Lee" [Var "SecondS"]), (Predicate "Lee" [Var "ThirdS"])]))

-- ¬FourthS(James) ∧ ¬FourthB(James)
k1 = (Conj [(Negation (Predicate "James" [Var "FourthS"])), (Negation (Predicate "James" [Var "FourthB"]))])

puz1conjunct = Conj [l1, m1, n1, o1, a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1]



-- Puzzle 2

-- ∃a∃b∃c∃d Swapped(Child(a), Sandwich(b), Fruit(c), Dessert(d)) -> 
--           Swapped(Child(b), Sandwich(a), Fruit(d), Dessert(c)) 
--           ∧ Swapped(Child(c), Sandwich(d), Fruit(a), Dessert(b)) 
--           ∧ Swapped(Child(d), Sandwich(c), Fruit(b), Dessert(a))
a2 = Exists "a" (Exists "b" (Exists "c" (Exists "d" (Implies 
    (Predicate "Swapped" [Function "a" [Var "Child"], Function "b" [Var "Sandwich"], 
    Function "c" [Var "Fruit"], Function "d" [Var "Dessert"]])
    (Conj [(Predicate "Swapped" [Function "b" [Var "Child"], Function "a" [Var "Sandwich"], 
    Function "d" [Var "Fruit"], Function "c" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "c" [Var "Child"], Function "d" [Var "Sandwich"], 
    Function "a" [Var "Fruit"], Function "b" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "d" [Var "Child"], Function "c" [Var "Sandwich"], 
    Function "b" [Var "Fruit"], Function "a" [Var "Dessert"]])])))))

-- Sandwich(Pam) == "Jam"
b2 = Equiv (Predicate  "Pam"[Var "Sandwich"]) (Predicate "Jam" [Var "Sandwich"])

-- Fruit(Alex) == "Dragonfruit"
c2 = Equiv (Predicate "Alex" [Var "Fruit"]) (Predicate "Dragonfruit" [Var "Fruit"])

-- ∃x∃y Original(Child(x), "Bologna", "Banana", Dessert(y))
d2 = Exists "x" (Exists "y" 
    (Predicate "Original" [Function "Child" [Var "x"], Function "Bologna" [Var "Sandwich"], Function "Banana" [Var "Fruit"], Function "y" [Var "Dessert"]]))

-- ∃x∃y Swapped(Child(x), Sandwich(y), "Avocado", "Chocolate Cupcake")
e2 = Exists "x" (Exists "y" (Predicate "Swapped" 
  [Function "x" [Var "Child"], Function "y" [Var "Sandwich"], Function "Avocado" [Var "Fruit"], Function "Chocolate Cupcake" [Var "Dessert"]]))

-- ∃x∃y Original(Child(Alex), Sandwich(Alex), Fruit(Alex), Dessert(Alex)) ∧ Swapped(Child(Alex), Sandwich(x), Fruit(Pam), Dessert(y))
f2 = Exists "x" (Exists "y" (Conj 
    [(Predicate "Original" [Function "Alex" [Var "Child"], Function "Alex" [Var "Sandwich"], Function "Alex" [Var "Fruit"], Function "Alex" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "Child" [Var "Alex"], Function "Sandwich" [Var "x"], Function "Fruit" [Var "Pam"], Function "y" [Var "Dessert"]])]))

    -- ∃x∃y Original(Child(Pam), Sandwich(Pam), Fruit(Pam), Dessert(Pam)) ∧ Swapped(Child(Pam), Sandwich(Pam), Fruit(Alex), Dessert(y))
g2 = Exists "x" (Exists "y" (Conj [(Predicate "Original" [Function "Pam" [Var "Child"], Function "Pam" [Var "Sandwich"], Function "Pam" [Var "Fruit"], Function "Pam" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "Child" [Var "Pam"], Function "Sandwich" [Var "x"], Function "Fruit" [Var "Alex"], Function "y" [Var "Dessert"]])]))

    -- ∃x∃y Original(Child(Pam), Sandwich(Pam), Fruit(Pam), Dessert(Pam)) ∧ Swapped(Child(Pam), Sandwich(Alex), Fruit(x), Dessert(y))
h2 = Exists "x" (Exists "y" (Conj [(Predicate "Original" [Function "Pam" [Var "Child"], Function "Pam" [Var "Sandwich"], Function "Pam" [Var "Fruit"], Function "Pam" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "Pam" [Var "Child"], Function "Alex" [Var "Sandwich"], Function "x" [Var "Fruit"], Function "y" [Var "Dessert"]])]))

    -- ∃x∃y∃z Original(Child(Ash), Sandwich(Ash), Fruit(Ash), Dessert(Ash)) ∧ Swapped(Child(Ash), Sandwich(x), Fruit(y), Dessert(z))
i2 = Exists "x" (Exists "y" (Conj [(Predicate "Original" [Function "Ash" [Var "Child"], Function "Ash" [Var "Sandwich"], Function "Ash" [Var "Fruit"], Function "Ash" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "Ash" [Var "Child"], Function "x" [Var "Sandwich"], Function "y" [Var "Fruit"], Function "z" [Var "Dessert"]])]))

-- ∃x∃y∃z Original(Child(x), Sandwich(x), Fruit(x), Dessert(x)) ∧ Swapped(Child(x), Sandwich(Pam), Fruit(y), "Candy Bar")
j2 = Exists "x" (Exists "y" (Exists "z" (Conj [(Predicate "Original" [Function "x" [Var "Child"], Function "x" [Var "Sandwich"], Function "x" [Var "Fruit"], Function "x" [Var "Dessert"]]),
    (Predicate "Swapped" [Function "x" [Var "Child"], Function "Pam" [Var "Sandwich"], Function "y" [Var "Fruit"], Function "z" [Var "Candy Bar"]])])))

puz2conjunct = Conj [a2, b2, c2, d2, e2, f2, g2, h2, i2, j2]    



-- Puzzle 3

-- Surname(Didduck) ∧ ¬First(Iris) -> Photo(Tugboat)
a3 = Implies (Conj [(Predicate "Didduck" [Var "Surname"]), (Negation (Predicate "Iris" [Var "First"]))]) (Predicate "Tugboat" [Var "Photo"])
-- ∃x (Female(x) ∧ ¬Surname(Purpuri)) -> Photo(Sunset)
b3 = Exists "x" (Implies (Conj [(Predicate "x" [Var "Female"]), (Negation (Predicate "Swaboda" [Var "Surname"]))]) (Predicate "Sunset" [Var "Photo"]))
-- Surname(Lombardi) ∧ ¬First(Iris) ∧ ¬First(Hannah) -> Photo(Horse)
c3 = Implies (Conj [(Predicate "Lombardi" [Var "Surname"]), (Negation (Predicate "Iris" [Var "Iris"])), (Negation (Predicate "Hannah" [Var "First"]))]) (Predicate "Horse" [Var "Photo"])
-- Surname(Swaboda) -> First(Gregory)
d3 = Implies (Predicate "Swaboda" [Var "Surname"]) (Predicate "Gregory" [Var "First"])
-- ¬First(Iris) -> Photo(Shrub)
e3 = Implies (Negation (Predicate "Iris" [Var "First"])) (Predicate "Shrub" [Var "Photo"])
-- ¬First(Iris) ∧ ¬First(Hannah) -> Photo(Sunset)
f3 = Implies (Conj [(Negation (Predicate "Iris" [Var "First"])), (Negation (Predicate "Hannah" [Var "First"]))]) (Predicate "Sunset" [Var "Photo"])

puz3conjunct = Conj [a3, b3, c3, d3, e3, f3]




--count number of positive literals, ues to find Horn clauses
-------------------------------------------------------------------------------------------------------------------------

isPos (Pos _ _) = 1
isPos (Neg _ _) = 0

countPosLit :: [Literal] -> Integer
countPosLit [] = 0
countPosLit (ele:lits) = (isPos ele) + (countPosLit lits)

isHorn clause = if (countPosLit clause) <= 1 then 1 else 0

countHorn formula = foldr (\x rest -> isHorn x + rest) 0 (formulaToCFE formula)
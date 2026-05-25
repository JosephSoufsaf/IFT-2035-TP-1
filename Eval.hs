{- HLINT ignore "Use record patterns" -}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Eval where

import Parseur ( Sexp(..), Symbol )
import GHC.Exts.Heap (GenClosure(queue))

-- ===========================================================================
-- Types
-- ===========================================================================
-- Représentation des types du mini-Haskell.
--   TInt         : le type entier primitif
--   TData sym    : un type algébrique nommé (ex. Bool, ListInt)
--   TArrow t1 t2 : un type fonction t1 -> t2

data Type = TInt
          | TData Symbol
          | TArrow Type Type
          deriving (Eq)

-- Affichage des types : les flèches sont associatives à droite,
-- on parenthèse uniquement le côté gauche si c'est lui-même une flèche.
instance Show Type where
  show :: Type -> String
  show TInt = "Int"
  show (TData sym) = sym
  show (TArrow t1 t2) = showParen' t1 ++ " -> " ++ show t2
    where showParen' x@(TArrow _ _) = "(" ++ show x ++ ")"
          showParen' x = show x

-- Un constructeur de données : son nom et la liste de ses types d'arguments.
-- Ex. : (Cons Int ListInt) → ("Cons", [TInt, TData "ListInt"])
type DataConstructor = (Symbol, [Type])

-- Une déclaration de type algébrique : le nom du type et ses constructeurs.
-- Ex. : (ListInt Nil (Cons Int ListInt)) → ("ListInt", [("Nil",[]), ("Cons",[TInt, TData "ListInt"])])
type NewDataType = (Symbol, [DataConstructor])

-- Un motif de case : le nom du constructeur, les variables liées, et le corps.
-- Ex. : ((Cons h t) (+ 1 n)) → ("Cons", ["h","t"], EApp ...)
type CasePattern = (Symbol, [Symbol], Exp)

-- ===========================================================================
-- Expressions
-- ===========================================================================
-- Arbre syntaxique abstrait (ASA) du mini-Haskell.
--   EInt n          : littéral entier
--   EVar x          : variable
--   EApp f a        : application f a
--   ELam x t e      : fonction anonyme (lambda (x t) e)
--   ELet ds e       : liaison let ; ds = [(nom, type, expr)]
--   EData decls e   : déclaration de types algébriques suivie d'une expression
--   ECase e pats    : filtrage par motif

data Exp = EInt Int
         | EVar Symbol
         | EApp Exp Exp
         | ELam Symbol Type Exp
         | ELet [(Symbol, Type, Exp)] Exp
         | EData [NewDataType] Exp
         | ECase Exp [CasePattern]
         deriving (Eq)

-- ===========================================================================
-- Valeurs (résultats de l'évaluation)
-- ===========================================================================
-- VInt n          : entier
-- VLam x e env   : fermeture (lambda + environnement de capture)
-- VPrim f        : fonction primitive Haskell (+, -, *)
-- VData name vs  : valeur construite (ex. Cons 1 Nil → VData "Cons" [VInt 1, VData "Nil" []])

data Value = VInt Int
           | VLam Symbol Exp Env
           | VPrim (Value -> Value)
           | VData Symbol [Value]

-- Affichage des valeurs :
--   - un constructeur sans arguments s'affiche tel quel (ex. "True")
--   - un constructeur avec arguments est parenthésé (ex. "(Cons 1 Nil)")
--   - les fonctions ne sont pas affichables
instance Show Value where
  show (VInt n) = show n
  show (VData name []) = name
  show (VData name args) = "(" ++ name ++ " " ++ unwords (map show args) ++ ")"
  show _ = "<function>"

-- Égalité structurelle : deux valeurs sont égales si elles ont le même
-- constructeur et les mêmes arguments. Les fonctions ne sont jamais égales.
instance Eq Value where
  (VInt n1) == (VInt n2) = n1 == n2
  (VData n1 a1) == (VData n2 a2) = n1 == n2 && a1 == a2
  -- Les fonctions et primitives ne sont pas comparables
  _ == _ = False

-- ===========================================================================
-- Environnements
-- ===========================================================================
-- Un environnement associe des noms de variables à leurs valeurs.
-- On le représente comme une liste de paires (nom, valeur) ;
-- la recherche se fait de gauche à droite (les liaisons plus récentes
-- masquent les plus anciennes).

type Env = [(Symbol, Value)]

-- Environnement initial avec les opérateurs arithmétiques primitifs.
-- Chaque opérateur est une fonction curryfiée : (Int -> Int -> Int).
env0 :: Env
env0 = [("+", prim (+)),
        ("-", prim (-)),
        ("*", prim (*))]
  where prim op =
          VPrim (\ (VInt x) -> VPrim (\ (VInt y) -> VInt (x `op` y)))

type Error = String

-- ===========================================================================
-- Analyse syntaxique : Sexp → Exp
-- ===========================================================================

-- Vérifie qu'un Sexp est bien un identifiant et retourne son nom.
id2Exp :: Sexp -> Either Error Symbol
id2Exp (SSym var) = Right var
id2Exp _ = Left "Syntax Error : Expecting an identifier"

-- Convertit un Sexp représentant un type en valeur de type Type.
-- Les types sont représentés comme des listes S-expression :
--   Int            → TInt
--   Bool           → TData "Bool"
--   (Int Int)      → TArrow TInt TInt        (fonction de Int vers Int)
--   (Bool Int Int) → TArrow (TData "Bool") (TArrow TInt TInt)
-- Une liste de longueur n≥2 est interprétée comme n-1 flèches (associativité droite).
sexp2type :: Sexp -> Either Error Type
sexp2type (SSym "Int") = Right TInt
sexp2type (SSym sym) = Right $ TData sym
sexp2type (SList [x]) = sexp2type x       -- (T) est équivalent à T
sexp2type (SList (x : xs)) = do
  type1 <- sexp2type x
  type2 <- sexp2type (SList xs)
  return $ TArrow type1 type2
sexp2type _ = Left "Ill formed type"

-- Mots-clés réservés : ils ne peuvent pas être utilisés comme variables.
reservedKeywords :: [Symbol]
reservedKeywords = ["lambda", "let", "case", "data", "Error"]

-- Convertit un Sexp (arbre S-expression issu du parseur) en Exp (ASA).
-- Le pipeline complet est : String → Sexp → Exp → (typeCheck) → (eval) → Value
--
-- Syntaxe reconnue :
--   n                              → EInt n
--   x                              → EVar x
--   (lambda ((x T) ...) corps)     → ELam (avec currying automatique)
--   (let ((x T expr) ...) corps)   → ELet
--   (data ((Nom Con ...) ...) corps)→ EData   [à implanter]
--   (case expr ((motif corps)...)) → ECase   [à implanter]
--   (f arg1 arg2 ...)              → EApp (avec application gauche-associative)
sexp2Exp :: Sexp -> Either Error  Exp
sexp2Exp (SNum x) = Right $ EInt x
sexp2Exp (SSym ident) | ident `elem` reservedKeywords
  = Left $ ident ++ " is a reserved keyword"
sexp2Exp (SSym ident) = Right $ EVar ident
sexp2Exp (SList [SSym "lambda", SList [], _]) = Left "Syntax Error : No parameter"

-- Désucrage des lambda multi-paramètres :
-- (lambda ((x Int) (y Int)) corps) → ELam "x" TInt (ELam "y" TInt corps)
sexp2Exp (SList [SSym "lambda", SList params, body]) = do
  body' <- sexp2Exp body
  params' <- mapM params2Exp params
  return $ mkLam params' body'

  where params2Exp :: Sexp -> Either Error (Symbol, Type)
        params2Exp (SList [SSym var, t]) = do
            t' <- sexp2type t
            return (var, t')
        params2Exp _ = Left "Syntax Error : Ill formed parameter"

        mkLam :: [(Symbol, Type)] -> Exp -> Exp
        mkLam [(var, t)] body2 = ELam var t body2
        mkLam ((var, t) : xs) body2 = ELam var t (mkLam xs body2)
        mkLam _ _ = undefined -- Pattern impossible à rejoindre

-- Analyse d'un let :
-- (let ((x Int 5) (f (Int Int) (lambda ...))) corps)
-- Les liaisons sont mutuellement récursives.
sexp2Exp (SList [SSym "let", SList definitions, body]) = do
  body' <- sexp2Exp body
  params' <- mapM def2Exp definitions
  return $ ELet params' body'

  where def2Exp :: Sexp -> Either Error (Symbol, Type, Exp)
        def2Exp (SList [SSym var, t, exp]) = do
            t' <- sexp2type t
            exp' <- sexp2Exp exp
            return (var, t', exp')
        def2Exp _ = Left "Syntax Error : Ill formed let definition"

-- TODO: Analyse d'une déclaration de types algébriques.
-- Syntaxe : (data ((NomType Con1 (Con2 T1 T2) ...) ...) corps)
-- Chaque type est une liste dont le premier élément est le nom du type,
-- suivis de ses constructeurs. Un constructeur est soit un symbole (0 argument)
-- soit une liste (nom + types des arguments).
-- Retourner EData avec la liste des NewDataType et le corps parsé.
sexp2Exp (SList [SSym "data", SList _, _]) = error "TODO: implanter sexp2Exp pour EData"

-- TODO: Analyse d'un filtrage par motif.
-- Syntaxe : (case expr ((Con1 corps1) ((Con2 x y) corps2) ...))
-- Chaque motif est soit (Con corps) pour un constructeur sans argument,
-- soit ((Con x y ...) corps) pour un constructeur avec variables liées.
-- Retourner ECase avec l'expression scrutée et la liste des CasePattern.
sexp2Exp (SList [SSym "case", _, SList _]) = error "TODO: implanter sexp2Exp pour ECase"

-- Application gauche-associative :
-- (f a b c) → EApp (EApp (EApp f a) b) c
sexp2Exp (SList (func : args)) = do
  func' <- sexp2Exp func
  arg' <- mapM sexp2Exp args
  return $ mkApp func' arg'

  where mkApp :: Exp -> [Exp] -> Exp
        mkApp f [arg] = EApp f arg
        mkApp f (a : as) =
          let inner = EApp f a
          in mkApp inner as


sexp2Exp _ = Left "Syntax Error : Ill formed Sexp"

-- ===========================================================================
-- Évaluation
-- ===========================================================================

-- Recherche d'une variable dans l'environnement d'évaluation.
-- Erreur à l'exécution si la variable est absente (ne devrait pas arriver
-- après le typeCheck).
lookupVar :: [(Symbol, Value)] -> Symbol -> Value
lookupVar [] sym = error "oups ..."
lookupVar ((s,v) : _) sym | s == sym =  v
lookupVar (_ : xs) sym = lookupVar xs sym

-- Évalue une expression dans un environnement et retourne une valeur.
-- L'environnement env est une liste de paires (nom, valeur) représentant
-- les variables accessibles au point d'évaluation.
eval :: Env -> Exp -> Value
eval _ (EInt x) = VInt x
eval env (EVar sym) = lookupVar env sym

-- TODO: Évaluer une abstraction lambda.
-- Un lambda s'évalue en une fermeture qui capture l'environnement courant.
eval env (ELam s t e) = VLam s e env

-- TODO: Évaluer une application f arg.
-- Évaluer f et arg, puis appliquer :
--   - si f est une VLam, étendre la fermeture et évaluer le corps
--   - si f est une VPrim, appeler la fonction primitive
eval env (EApp f arg) = case eval env f of
    VLam s body env -> eval ((s, eval env arg) : env) body
    VPrim v -> v (eval env arg)
    otherwise -> error "eval EApp expected function and argument"

-- TODO: Évaluer un let.
-- Toutes les liaisons sont mutuellement récursives :
-- construire env2 = (noms ↦ valeurs) ++ env où les valeurs sont elles-mêmes
-- évaluées dans env2 (nœud de point fixe).
eval env (ELet defs body) = eval env2 body where
    env2 = map binding defs ++ env
    binding (x, _, e) = (x, eval env2 e)

-- TODO: Évaluer une déclaration data.
-- Les constructeurs deviennent des valeurs dans l'environnement :
--   - constructeur sans argument → VData "Nom" []
--   - constructeur avec n arguments → une suite de VPrim qui accumulent
--     les arguments et produisent un VData quand tous sont fournis.
eval env (EData dts body) = eval env2 body
  where
    env2 = ajouterType dts ++ env

    ajouterType [] = []
    ajouterType ((_, constrsuctor) : queue) = ajouterConstructeur constrsuctor ++ ajouterType queue

    ajouterConstructeur [] = []
    ajouterConstructeur ((nomConstructor, args) : queue) = (nomConstructor, creerValeur nomConstructor args) : ajouterConstructeur queue

    creerValeur nomConstructor args = case args of
      [] -> VData nomConstructor []
      _  -> accumulerArgs  nomConstructor (compter args) []
        

    accumulerArgs  nom 0 acc = VData nom (inverser acc)
    accumulerArgs  nom n acc = VPrim (\v -> accumulerArgs  nom (n-1) (v:acc))

    inverser :: [a] -> [a]
    inverser [] = []
    inverser (x:xs) = inverser xs ++ [x] 

    compter :: [a] -> Int
    compter [] = 0
    compter (_:xs) = 1 + compter xs

-- TODO: Évaluer un case.
-- Évaluer l'expression scrutée (doit donner un VData).
-- Trouver le motif dont le constructeur correspond, lier les variables
-- aux arguments du VData, puis évaluer le corps dans cet environnement étendu.
eval env (ECase scrutin branches) =
  case eval env scrutin of
    VData nom args -> eval (combiner vars args ++ env) corps
      where (vars, corps) = trouverBranche branches nom
  where
    trouverBranche [] nom = error "Pas de branche pour ce constructeur"
    trouverBranche ((nomConstr, vars, corps) : reste) nom =
      case nomConstr == nom of
        True  -> (vars, corps)
        False -> trouverBranche reste nom

    combiner [] _ = []
    combiner _ [] = []
    combiner (v:vs) (a:as) = (v, a) : combiner vs as


-- ===========================================================================
-- Vérification de types
-- ===========================================================================

-- Un environnement de typage associe des noms de variables à leurs types.
type Tenv = [(Symbol, Type)]

-- Environnement de typage initial avec les opérateurs arithmétiques.
tenv0 :: Tenv
tenv0 = [("+", TArrow TInt (TArrow TInt TInt)),
         ("-", TArrow TInt (TArrow TInt TInt)),
         ("*", TArrow TInt (TArrow TInt TInt))]

-- Recherche d'un symbole dans l'environnement de typage.
-- Retourne une erreur si le symbole n'est pas lié.
lookupSym :: [(Symbol, Type)] -> Symbol -> Either Error Type
lookupSym [] sym = Left $ "Not in scope variable : " ++ show sym
lookupSym ((s,v) : _) sym | s == sym = Right v
lookupSym (_ : xs) sym = lookupSym xs sym

-- Inférence/vérification de type d'une expression dans un environnement.
-- Retourne le type de l'expression, ou un message d'erreur.
typeCheck :: Tenv -> Exp -> Either Error Type
typeCheck _ (EInt _) = Right TInt
typeCheck env (EVar sym) = lookupSym env sym
-- TODO: Vérifier le type d'un lambda.
-- Le paramètre x de type t est ajouté à l'environnement pour typer le corps.
-- Le type retourné est TArrow t typeCorps.
typeCheck _ (ELam _ _ _) = error "TODO: implanter typeCheck pour ELam"
-- TODO: Vérifier le type d'une application f arg.
-- f doit avoir un type TArrow t1 t2, arg doit avoir le type t1.
-- Le type retourné est t2.
typeCheck _ (EApp _ _)   = error "TODO: implanter typeCheck pour EApp"
-- TODO: Vérifier le type d'un let.
-- Toutes les liaisons sont visibles les unes des autres (récursion mutuelle) :
-- construire env2 avec les types déclarés, vérifier chaque expression,
-- puis typer le corps dans env2.
typeCheck _ (ELet _ _)   = error "TODO: implanter typeCheck pour ELet"
-- TODO: Vérifier le type d'une déclaration data.
-- Vérifications à effectuer :
--   1. Int ne peut pas être redéfini
--   2. Les noms de types sont tous distincts
--   3. Les noms de constructeurs sont tous distincts (globalement)
--   4. Les déclarations data ne peuvent pas être imbriquées
-- Chaque constructeur (Nom T1 T2) introduit une liaison dans l'environnement
-- de type : Nom :: T1 -> T2 -> NomType.
-- Le corps est ensuite typé dans cet environnement étendu.
typeCheck _ (EData _ _) = error "TODO: implanter typeCheck pour EData"
-- TODO: Vérifier le type d'un case.
-- L'expression scrutée doit être de type TData nomType.
-- Pour chaque motif :
--   - retrouver le type du constructeur dans l'environnement
--   - lier les variables aux types des arguments du constructeur
--   - typer le corps dans cet environnement étendu
-- Vérifications supplémentaires :
--   - tous les constructeurs du type doivent être couverts (exhaustivité)
--   - tous les corps doivent avoir le même type
typeCheck _ (ECase _ _) = error "TODO: implanter typeCheck pour ECase"

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- | This module implements a version of
-- <http://hackage.haskell.org/package/syntactic>
-- with the following properties:
--
-- * No first-class lambdas ('TR' doesn't include function types)
--
-- * Beta-short, eta-long normal form
--     - Eta-long means that any expression of type ':->' must be a lambda. See
--       the pattern match on 'Lam' in 'inline'.
--     - The normal Syntactic also has beta-short normal form. In both versions
--       Redexes can be represented by adding an application symbol.
--
-- * Like in this paper
--   <http://www.cse.chalmers.se/~emax/documents/svenningsson2015combining.pdf>
--   'sugar' makes a smart constructor of any symbol; see the definition of
--   'share'.
--
-- Related work:
--
-- * <https://github.com/shayan-najd/QFeldspar>
--   - TODO Where exactly?
--
-- * Wren Romano's library for abstract binding trees (ABTs):
--   <https://winterkoninkje.dreamwidth.org/103978.html>
--   These allow more general binding forms than just lambdas.

module LambdaEDSL where



--------------------------------------------------------------------------------
-- * Generic stuff
--------------------------------------------------------------------------------

data Signature a
    = Const a
    | Signature a :-> Signature a

infixr :->

type Name = Integer

data Spine sym (a :: Signature *)
  where
    Var  :: Name -> Spine sym a
    Sym  :: sym a -> Spine sym a
    (:$) :: Spine sym (a ':-> b) -> Eta sym a -> Spine sym b

infixl 1 :$

data Eta sym (a :: Signature *)
  where
    Lam  :: Name -> Eta sym b -> Eta sym (a ':-> b)
    Lift :: Spine sym ('Const a) -> Eta sym ('Const a)

type AST sym a = Spine sym ('Const a)

----------------------------------------
-- ** Embedding functions
----------------------------------------

maxLam :: Eta sym a -> Name
maxLam (Lam n _) = n
maxLam (Lift s)  = maxLamSpine s

maxLamSpine :: Spine sym a -> Name
maxLamSpine (s :$ a) = maxLamSpine s `max` maxLam a
maxLamSpine _        = -1

lam :: (Spine sym a -> Eta sym b) -> Eta sym (a ':-> b)
lam f = Lam v body
  where
    v    = maxLam body + 1
    body = f $ Var v

class Syntactic a
  where
    type Domain a   :: Signature * -> *
    type Internal a :: Signature *
    desugar :: a -> Eta (Domain a) (Internal a)
    sugar   :: Spine (Domain a) (Internal a) -> a

resugar
    :: ( Syntactic a, Syntactic b
       , Domain a ~ Domain b
       , Internal a ~ Internal b
       , Internal a ~ 'Const a'
       )
    => a -> b
resugar = sugar . eta2spine . desugar
  where
    eta2spine :: Eta sym ('Const a) -> Spine sym ('Const a)
    eta2spine (Lift s) = s

instance Syntactic (Spine sym ('Const a))
  where
    type Domain   (Spine sym ('Const a)) = sym
    type Internal (Spine sym ('Const a)) = 'Const a
    desugar = Lift
    sugar   = id

instance Syntactic (Eta sym ('Const a))
  where
    type Domain   (Eta sym ('Const a)) = sym
    type Internal (Eta sym ('Const a)) = 'Const a
    desugar = id
    sugar   = Lift

instance (Syntactic a, Syntactic b, Domain a ~ Domain b) => Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a ':-> Internal b
    desugar f = lam (desugar . f . sugar)
    sugar   f = sugar . (f :$) . desugar

sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

----------------------------------------
-- ** Annotations
----------------------------------------

type family DenResult a
  where
    DenResult ('Const a) = a
    DenResult (a ':-> b) = DenResult b

data (sym :&: info) a
  where
    (:&:) :: sym a -> info (DenResult a) -> (sym :&: info) a

----------------------------------------
-- ** Evaluation
----------------------------------------

type family Denotation a
  where
    Denotation ('Const a) = a
    Denotation (a ':-> b) = Denotation a -> Denotation b

class Eval sym
  where
    evalSym :: sym a -> Denotation a

eval :: Eval sym => Spine sym a -> Denotation a
eval (Var _)  = error "TODO"
eval (Sym s)  = evalSym s
eval (s :$ a) = eval s $ evalEta a

evalEta :: Eval sym => Eta sym a -> Denotation a
evalEta (Lam _ _) = error "TODO"
evalEta (Lift s)  = eval s



--------------------------------------------------------------------------------
-- * Example
--------------------------------------------------------------------------------

data Lang a
  where
    Int :: Num a => a -> Lang ('Const a)
    Add :: Num a => Lang ('Const a ':-> 'Const a ':-> 'Const a)
    Let :: Lang ('Const a ':-> ('Const a ':-> 'Const b) ':-> 'Const b)

data TR a
  where
    IntT :: TR Int

class Type a
  where
    typeRep :: TR a

instance Type Int where typeRep = IntT

type Dom = Lang :&: TR

instance (Num a, Type a) => Num (AST Dom a)
  where
    fromInteger = sugarSym . (:&: typeRep) . Int . fromInteger
    (+) = sugarSym (Add :&: typeRep)
    (-) = undefined
    (*) = undefined
    abs = undefined
    signum = undefined

share :: Type b => AST Dom a -> (AST Dom a -> AST Dom b) -> AST Dom b
share = sugarSym (Let :&: typeRep)

-- This function is not correct, but it shows that the second argument of `Let`
-- must be a `Lam`. (Note that @-Wall@ doesn't complain.)
inline :: Spine Dom a -> Spine Dom a
inline s@(Var _) = s
inline s@(Sym (_ :&: _)) = s
inline (Sym (Let :&: _) :$ _ :$ Lam _ body) = resugar body
inline (s :$ a) = inline s :$ inlineEta a

inlineEta :: Eta Dom a -> Eta Dom a
inlineEta (Lam v a) = Lam v $ inlineEta a
inlineEta (Lift a)  = Lift a

-- \x . x y
test1 :: Eta Dom (('Const Int ':-> 'Const Int) ':-> 'Const Int)
test1 = Lam 0 (Lift (Var 0 :$ Lift (Var 1)))


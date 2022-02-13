{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

import Control.Monad.Except
import Data.List
import Control.Arrow
import Control.Monad.Trans.State

infixl 4 :@
infixr 3 :->

type Symb = String 

-- Терм
data Expr = Var Symb 
          | Expr :@ Expr
          | Lam Symb Expr
  deriving (Eq,Show)

-- Тип
data Type = TVar Symb 
          | Type :-> Type
  deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

unique = map head . group . sort

freeVars' :: Expr -> [Symb] 
freeVars' (Var a)    = [a]
freeVars' (m1 :@ m2) = (freeVars m1) ++ (freeVars m2)
freeVars' (Lam a m)  = delete a $ freeVars m
freeVars = unique . freeVars'

freeTVars' :: Type -> [Symb]
freeTVars' (TVar a) = [a]
freeTVars' (m1 :-> m2) = (freeTVars m1) ++ (freeTVars m2)
freeTVars = unique . freeTVars'

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env k) a b = Env $ (a,b):k

freeTVarsEnv' :: Env -> [Symb]
freeTVarsEnv' (Env k) = concat . map (freeTVars . snd) $ k
freeTVarsEnv = unique . freeTVarsEnv'

appEnv :: MonadError String m => Env -> Symb -> m Type
appEnv (Env xs) v = case lookup v xs of 
                      Just x -> return $ x
                      Nothing -> throwError $ "There is no variable \""++v++"\" in the enviroment."

appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy xs) (TVar a) = maybe (TVar a) id (lookup a xs)
appSubsTy a@(SubsTy xs) (m1 :-> m2) =  appSubsTy a m1 :-> appSubsTy a m2

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv x (Env ys) = Env $ map (second $ appSubsTy x) ys

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy x@(SubsTy xs) (SubsTy ys) = SubsTy . map head . groupBy ((flip $ (==) . fst) . fst) . sortBy (flip $ (flip $ compare . fst) . fst)
                                            $ (map (second $ appSubsTy x) ys) ++ xs


instance Semigroup SubsTy where
  (<>) = composeSubsTy

instance Monoid SubsTy where
  mempty = SubsTy []

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar a) (TVar b) = return . SubsTy $ if a==b then [] else [(b,TVar a)]
unify (TVar a) b = case find (==a) (freeTVars b) of 
                      Just _ -> throwError $ "Can't unify ("++show a ++") with ("++show b ++")!"
                      Nothing -> return . SubsTy $ [(a, b)]
unify a@(m1 :-> m2) b@(TVar c) = unify b a
unify (m1 :-> m2) (t1 :-> t2) = uncurry composeSubsTy <$> ((,) <$> lsubT <*> rsubT) 
  where lsubT = unify m1 t1 
        rsubT = (,) <$> ((flip appSubsTy $ m2) <$> lsubT) <*> ((flip appSubsTy $ t2) <$> lsubT) >>= uncurry unify

getFreshName len = "freshname"++(replicate len '\'')

equations' :: MonadError String m => Env -> Expr -> Type -> StateT Int m [(Type,Type)]
equations' env (Var a) d = (flip (:) []) . (flip (,) d) <$> appEnv env a

equations' env (e1 :@ e2) d = do
    curMxLen <- get
    modify (+1)
    let name = getFreshName curMxLen

    e1' <- equations' env e1 (TVar name :-> d)
    e2' <- equations' env e2 (TVar name)
    return $ e1' ++ e2'    

equations' env (Lam x t) d = do 
  curMxLen <- get 
  modify (+2)
  let name1 = getFreshName curMxLen
      name2 = name1++"'"
  
  t' <- equations' (extendEnv env x (TVar name1)) t (TVar name2)
  return $ (TVar name1 :-> TVar name2, d) : t'

getMxLen xs = foldr (\el suf -> max (length el) suf) 0 allNames
  where allNames = concat $ map (freeTVars . snd) xs

equations :: MonadError String m => Env -> Expr -> Type -> m [(Type,Type)]
equations env@(Env xs) e d = evalStateT (equations' env e d) (getMxLen xs)

principlePair :: MonadError String m =>  Expr -> m (Env,Type)
principlePair e = do
  let envXs = map (\el -> (el, TVar $ el++"'")) (freeVars e) 
      env = Env envXs 
      d = TVar $ getFreshName $ getMxLen envXs + 1000
  
  eqtns <- equations env e d 
  let (x,y) = unzip eqtns
      combine xs = foldr (\el suf -> el :-> suf) (head xs) (tail xs)
  
  case unify (combine x) (combine y) of
    Left err -> throwError err 
    Right x -> return (appSubsEnv x env, appSubsTy x d)
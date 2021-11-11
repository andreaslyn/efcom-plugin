{-# LANGUAGE CPP #-}

module Control.Efcom.Internal.Plugin (plugin) where

import GhcPlugins
import CoreUnfold
import qualified Outputable
import qualified Simplify
import qualified SimplEnv
import CoreStats (exprSize)
import SimplMonad (initSmpl)
import FamInstEnv (emptyFamInstEnvs)

import Control.Monad
import Data.List (isInfixOf)

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = addPassAfterSimplifier todo
  --fmap (++ [CoreDoPluginPass "TEST" dump]) (addPassAfterSimplifier todo)

dump :: ModGuts -> CoreM ModGuts
dump guts = do
    dflags <- getDynFlags
    bindsOnlyPass (mapM (printBind dflags)) guts
  where printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags (NonRec b expr) = do
          putMsgS ("Binding named " ++ showSDoc dflags (ppr b) ++ " =\n" ++ showSDoc dflags (ppr expr))
          return (NonRec b expr)
        printBind dflags (Rec bs) = do
          bs' <- flip mapM bs $ \ (b, expr) -> do
                    putMsgS ("Recursive binding named " ++ showSDoc dflags (ppr b) ++ " =\n" ++ showSDoc dflags (ppr expr))
                    return (b, expr)
          return (Rec bs')

countSimplPasses :: [CoreToDo] -> Int
countSimplPasses [] = 0
countSimplPasses (t : ts) =
  let x = countSimplPasses ts
  in case t of
      CoreDoSimplify _ _ -> 1 + x
      CoreDoPasses ss -> countSimplPasses ss + x
      _ -> x

addPassAfterSimplifier :: [CoreToDo] -> CoreM [CoreToDo]
addPassAfterSimplifier [] = return []
addPassAfterSimplifier (t@(CoreDoSimplify iters sm) : ts) = do
{-
  let start = if countSimplPasses ts == 0
              then [CoreDoSimplify iters (sm {sm_names = ["simpl-Control.Efcom.Internal.Plugin"]}), CoreDoPluginPass "Control.Efcom.Internal.Plugin" (pass sm), t]
              else [t, CoreDoPluginPass "Control.Efcom.Internal.Plugin" (pass sm)]
-}
  let start = [t, CoreDoPluginPass "Control.Efcom.Internal.Plugin" (pass sm)]
  fmap (CoreDoPasses start :) (addPassAfterSimplifier ts)
addPassAfterSimplifier (t@(CoreDoPasses ss) : ts) = do
  ss' <- addPassAfterSimplifier ss
  ts' <- addPassAfterSimplifier ts
  return (CoreDoPasses ss' : ts')
addPassAfterSimplifier (t : ts) =
  fmap (t :) (addPassAfterSimplifier ts)


isMarkedUnfoldable :: CoreBndr -> Bool
isMarkedUnfoldable b = isAnyInlinePragma (idInlinePragma b)


pass :: SimplMode -> ModGuts -> CoreM ModGuts
pass sm guts = do
    dflags <- getDynFlags
    bindsOnlyPass (mapM (printBind dflags)) guts
  where printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags (NonRec b expr) = do
          if isMarkedUnfoldable b
          then
            return (NonRec b expr)
          else do
            let (expr', progress) = runState (inlineBindCom dflags expr) False
            expr'' <- if progress
                      then liftIO $ do
                        --us <-  mkSplitUniqSupply 's'
                        --let sz = exprSize expr'
                        --(e, _) <- initSmpl dflags emptyRuleEnv emptyFamInstEnvs us sz (Simplify.simplExpr (SimplEnv.mkSimplEnv sm) expr')
                        return expr'
                      else
                        return expr'
            return (NonRec b expr'')
        printBind dflags (Rec bs) = do
          bs' <- flip mapM bs $ \ (b, expr) -> do
                  if isMarkedUnfoldable b
                  then
                    return (b, expr)
                  else do
                    let (expr', progress) = runState (inlineBindCom dflags expr) False
                    expr'' <- if progress
                              then liftIO $ do
                                --us <-  mkSplitUniqSupply 's'
                                --let sz = exprSize expr'
                                --(e, _) <- initSmpl dflags emptyRuleEnv emptyFamInstEnvs us sz (Simplify.simplExpr (SimplEnv.mkSimplEnv sm) expr')
                                return expr'
                              else
                                return expr'
                    return (b, expr'')
          return (Rec bs')

_isComModuleVar :: DynFlags -> Var -> Bool
_isComModuleVar dflags var =
  case nameModule_maybe (varName var) of
    Nothing -> False
    Just mod -> showSDoc dflags (pprModule mod) == "Control.Efcom.Internal.Com"

isComVar :: DynFlags -> String -> Var -> Bool
isComVar dflags s var =
  showSDoc dflags (ppr $ varName var) == s {- && isAfModuleVar var -}

inlineBindCom :: DynFlags -> CoreExpr -> State Bool CoreExpr
inlineBindCom dflags (Var var) = do
  --putMsgS $ "var = " ++ showSDoc dflags (ppr (Var var :: CoreExpr))
  return (Var var)
inlineBindCom dflags
    (App (App (App (App (App
    (Cast (App (App (App (App (App (Var var) a1) a2) a3) a4) a5) coe)
    a6) a7) a8) a9) a10) = do
  --putMsgS $ "var-inl = " ++ showSDoc dflags (ppr (Var var :: CoreExpr))
  base <- tryInlineVar
  case base of
    Cast (Lam b1 (Lam b2 (Lam b3 (Lam b4 (Lam b5 (Lam b6 (Lam b7 (Lam b8 (Lam b9 (Lam b10 body)))))))))) _ -> do
      let su = extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst
                (extendSubst emptySubst
                b1 a1)
                b2 a2)
                b3 a3)
                b4 a4)
                b5 a5)
                b6 a6)
                b7 a7)
                b8 a8)
                b9 a9)
                b10 a10
      put True
      let expr = substExpr Outputable.empty su body
      --putMsgS $ "inline-expr = " ++ showSDoc dflags (ppr (App (App (App (App (App
        --(Cast (App (App (App (App (App (Var var) a1) a2) a3) a4) a5) coe)
        --a6) a7) a8) a9) a10))
      --putMsgS $ "inline-result = " ++ showSDoc dflags (ppr expr)
      expr' <- inlineBindCom dflags expr
      --putMsgS $ "inline-final = " ++ showSDoc dflags (ppr expr')
      return expr'
    _ -> do
      --putMsgS $ "NO INLINE"
      a1' <- inlineBindCom dflags a1
      a2' <- inlineBindCom dflags a2
      a3' <- inlineBindCom dflags a3
      a4' <- inlineBindCom dflags a4
      a5' <- inlineBindCom dflags a5
      a6' <- inlineBindCom dflags a6
      a7' <- inlineBindCom dflags a7
      a8' <- inlineBindCom dflags a8
      a9' <- inlineBindCom dflags a9
      a10' <- inlineBindCom dflags a10
      return
        (App (App (App (App (App
        (Cast (App (App (App (App (App base a1') a2') a3') a4') a5') coe)
        a6') a7') a8') a9') a10')
  where
    tryInlineVar :: State Bool CoreExpr
    tryInlineVar =
      if isComVar dflags "bindCom" var
          || isComVar dflags "fmapCom" var
      then
        let unf_m = maybeUnfoldingTemplate (idUnfolding var)
        in case unf_m of
            Nothing -> do
              --putMsgS $ "WARNING: NO UNFOLDING"
              return (Var var)
            Just unf -> return unf
      else return (Var var)
inlineBindCom dflags expr@(App (App (App (App (App (App (App (Var var) a1) a2) a3) a4) a5) a6) a7) = do
  --putMsgS $ "try-skip-expr = " ++ showSDoc dflags (ppr expr)
  if isComVar dflags "ComContBind" var || isComVar dflags "$WComContBind" var
  then return expr
  else do
    a1' <- inlineBindCom dflags a1
    a2' <- inlineBindCom dflags a2
    a3' <- inlineBindCom dflags a3
    a4' <- inlineBindCom dflags a4
    a5' <- inlineBindCom dflags a5
    a6' <- inlineBindCom dflags a6
    a7' <- inlineBindCom dflags a7
    return (App (App (App (App (App (App (App (Var var) a1') a2') a3') a4') a5') a6') a7')
inlineBindCom dflags (App expr arg) = do
  --putMsgS $ "app-expr = " ++ showSDoc dflags (ppr expr)
  expr' <- inlineBindCom dflags expr
  arg' <- inlineBindCom dflags arg
  return (App expr' arg')
inlineBindCom dflags (Lam b expr) = do
  --putMsgS $ "lam-expr = " ++ showSDoc dflags (ppr expr)
  fmap (Lam b) (inlineBindCom dflags expr)
inlineBindCom dflags (Let bi expr) = do
  --putMsgS $ "let-expr = " ++ showSDoc dflags (ppr expr)
  bi' <- case bi of
          NonRec b e -> fmap (NonRec b) (inlineBindCom dflags e)
          Rec bs -> fmap Rec $ mapM (\ (b, e) -> fmap ((,) b) (inlineBindCom dflags e)) bs
  fmap (Let bi') (inlineBindCom dflags expr)
inlineBindCom dflags (Case expr b c alts) = do
  --putMsgS $ "case-expr = " ++ showSDoc dflags (ppr expr)
  expr' <- inlineBindCom dflags expr
  alts' <- mapM (\ (x, y, alt) -> fmap (\ e -> (x, y, e)) $ inlineBindCom dflags alt) alts
  return (Case expr' b c alts')
inlineBindCom dflags (Cast expr coe) = do
  --putMsgS $ "cast-expr = " ++ showSDoc dflags (ppr expr)
  fmap (\ e -> Cast e coe) (inlineBindCom dflags expr)
inlineBindCom dflags (Tick t expr) = do
  --putMsgS $ "tick-expr = " ++ showSDoc dflags (ppr expr)
  fmap (Tick t) (inlineBindCom dflags expr)
inlineBindCom dflags expr = do
  --putMsgS $ "DEFAULT CASE " ++ showSDoc dflags (ppr expr)
  return expr

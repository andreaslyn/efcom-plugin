{-# LANGUAGE CPP #-}

module Control.Af.Internal.Plugin (plugin) where

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
          if not ("$wloop" == showSDoc dflags (ppr b))
          then
            return (NonRec b expr)
          else do
            putMsgS ("Binding named " ++ showSDoc dflags (ppr b) ++ " =\n" ++ showSDoc dflags (ppr expr))
            return (NonRec b expr)
        printBind dflags (Rec bs) = do
          bs' <- flip mapM bs $ \ (b, expr) -> do
                    if not ("$wloop" == showSDoc dflags (ppr b))
                    then
                      return (b, expr)
                    else do
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
              then [CoreDoSimplify iters (sm {sm_names = ["simpl-Control.Af.Internal.Plugin"]}), CoreDoPluginPass "Control.Af.Internal.Plugin" (pass sm), t]
              else [t, CoreDoPluginPass "Control.Af.Internal.Plugin" (pass sm)]
-}
  let start = [t, CoreDoPluginPass "Control.Af.Internal.Plugin" (pass sm)]
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
            let (expr', progress) = runState (inlineBindAf dflags expr) False
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
                    let (expr', progress) = runState (inlineBindAf dflags expr) False
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

_isAfModuleVar :: DynFlags -> Var -> Bool
_isAfModuleVar dflags var =
  case nameModule_maybe (varName var) of
    Nothing -> False
    Just mod -> showSDoc dflags (pprModule mod) == "Control.Af.Internal.Af"

isAfVar :: DynFlags -> String -> Var -> Bool
isAfVar dflags s var =
  showSDoc dflags (ppr $ varName var) == s {- && isAfModuleVar var -}

inlineBindAf :: DynFlags -> CoreExpr -> State Bool CoreExpr
inlineBindAf dflags (Var var) = do
  --putMsgS $ "var = " ++ showSDoc dflags (ppr (Var var :: CoreExpr))
  return (Var var)
inlineBindAf dflags
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
      expr' <- inlineBindAf dflags expr
      --putMsgS $ "inline-final = " ++ showSDoc dflags (ppr expr')
      return expr'
    _ -> do
      --putMsgS $ "NO INLINE"
      a1' <- inlineBindAf dflags a1
      a2' <- inlineBindAf dflags a2
      a3' <- inlineBindAf dflags a3
      a4' <- inlineBindAf dflags a4
      a5' <- inlineBindAf dflags a5
      a6' <- inlineBindAf dflags a6
      a7' <- inlineBindAf dflags a7
      a8' <- inlineBindAf dflags a8
      a9' <- inlineBindAf dflags a9
      a10' <- inlineBindAf dflags a10
      return
        (App (App (App (App (App
        (Cast (App (App (App (App (App base a1') a2') a3') a4') a5') coe)
        a6') a7') a8') a9') a10')
  where
    tryInlineVar :: State Bool CoreExpr
    tryInlineVar =
      if isAfVar dflags "bindAf" var
          || isAfVar dflags "fmapAf" var
      then
        let unf_m = maybeUnfoldingTemplate (idUnfolding var)
        in case unf_m of
            Nothing -> do
              --putMsgS $ "WARNING: NO UNFOLDING"
              return (Var var)
            Just unf -> return unf
      else return (Var var)
inlineBindAf dflags expr@(App (App (App (App (App (App (App (Var var) a1) a2) a3) a4) a5) a6) a7) = do
  --putMsgS $ "try-skip-expr = " ++ showSDoc dflags (ppr expr)
  if isAfVar dflags "AfContBind" var
  then return expr
  else do
    a1' <- inlineBindAf dflags a1
    a2' <- inlineBindAf dflags a2
    a3' <- inlineBindAf dflags a3
    a4' <- inlineBindAf dflags a4
    a5' <- inlineBindAf dflags a5
    a6' <- inlineBindAf dflags a6
    a7' <- inlineBindAf dflags a7
    return (App (App (App (App (App (App (App (Var var) a1') a2') a3') a4') a5') a6') a7')
inlineBindAf dflags (App expr arg) = do
  --putMsgS $ "app-expr = " ++ showSDoc dflags (ppr expr)
  expr' <- inlineBindAf dflags expr
  arg' <- inlineBindAf dflags arg
  return (App expr' arg')
inlineBindAf dflags (Lam b expr) = do
  --putMsgS $ "lam-expr = " ++ showSDoc dflags (ppr expr)
  fmap (Lam b) (inlineBindAf dflags expr)
inlineBindAf dflags (Let bi expr) = do
  --putMsgS $ "let-expr = " ++ showSDoc dflags (ppr expr)
  bi' <- case bi of
          NonRec b e -> fmap (NonRec b) (inlineBindAf dflags e)
          Rec bs -> fmap Rec $ mapM (\ (b, e) -> fmap ((,) b) (inlineBindAf dflags e)) bs
  fmap (Let bi') (inlineBindAf dflags expr)
inlineBindAf dflags (Case expr b c alts) = do
  --putMsgS $ "case-expr = " ++ showSDoc dflags (ppr expr)
  expr' <- inlineBindAf dflags expr
  alts' <- mapM (\ (x, y, alt) -> fmap (\ e -> (x, y, e)) $ inlineBindAf dflags alt) alts
  return (Case expr' b c alts')
inlineBindAf dflags (Cast expr coe) = do
  --putMsgS $ "cast-expr = " ++ showSDoc dflags (ppr expr)
  fmap (\ e -> Cast e coe) (inlineBindAf dflags expr)
inlineBindAf dflags (Tick t expr) = do
  --putMsgS $ "tick-expr = " ++ showSDoc dflags (ppr expr)
  fmap (Tick t) (inlineBindAf dflags expr)
inlineBindAf dflags expr = do
  --putMsgS $ "DEFAULT CASE " ++ showSDoc dflags (ppr expr)
  return expr

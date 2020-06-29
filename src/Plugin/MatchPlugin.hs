{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Plugin.MatchPlugin (plugin)
  where

import           Deep.Expr
import qualified Deep.Expr as DE
import           Deep.Delineate
import           Plugin.Utils


import           Data.Data hiding (TyCon (..), tyConName, mkFunTy)
import           Data.Typeable hiding (TyCon (..), tyConName, mkFunTy)

import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           GhcPlugins hiding (Expr)

import           InstEnv

-- import           Literal (mkMachInt)

import           FamInstEnv

import           TcSMonad

import           CoreUnfold

import           TyCon

import           Inst

import           Pair

import           Coercion

import qualified Data.Kind as Kind

import           Control.Monad
import           Control.Monad.Writer hiding (pass, Alt)
import           Control.Monad.State
import           Control.Applicative

import           Data.Foldable

import           Data.Maybe

import           Control.Arrow ((&&&), (***), first, second)

import           GHC.Generics
import           GHC.Types (Int(..))

-- import           GHCUtils

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH


import           OccurAnal

import           TcRnTypes
import           TcSimplify
import           TcMType
import           TcSMonad
import           TcEvidence
import           TcType

import           Finder
import           LoadIface

import           DsBinds

import           HsBinds
import           HsDecls

import           CostCentreState

import           Bag
import           VarSet

import           Encoding

import           DynFlags

import           ErrUtils

import           Data.IORef

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Char
import           Data.List

import           CoreOpt
import           Id

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH

import Debug.Trace


plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ coreToDos = do
  return (CoreDoPluginPass "Pattern matching plugin" pass : coreToDos)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
  primMap <- forM primMapTH
                 (\(fromTH, toTH) -> do
                  fromName <- thNameToGhcName_ fromTH
                  toName <- thNameToGhcName_ toTH

                  from <- findId guts fromName emptyVarSet
                  to <- findId guts toName emptyVarSet
                  return (from, Var to))


  dflags <- getDynFlags


  bindsOnlyPass (transformBinds guts (mg_inst_env guts) primMap) guts

hasExternalize :: ModGuts -> CoreExpr -> CoreM Bool
hasExternalize guts e = do
  (_, Any a) <- runWriterT (Data.transformM go e)
  return a
  where
    go :: CoreExpr -> WriterT Any CoreM CoreExpr
    go expr@(Var f) = do
      externalizeId <- lift $ findIdTH guts 'externalize

      if f == externalizeId
        then tell (Any True) >> return expr
        else return expr
    go expr = return expr

findBind :: Var -> [CoreBind] -> Maybe CoreBind
findBind v [] = Nothing
findBind v (b@(NonRec n e):bs)
  | v == n = Just b
  | otherwise = findBind v bs
findBind v (b@(Rec rs):bs) =
  case lookup v rs of
    Just _ -> Just b
    Nothing -> findBind v bs

changeBind :: [CoreBind] -> CoreBind -> CoreBind
changeBind newBinds b@(NonRec n e) =
  let x = find (\case
                  NonRec n' e'
                    | n' == n -> True
                  _ -> False) newBinds
  in
  case x of
    Just r -> r
    Nothing -> b

changeBind newBinds b@(Rec rs) = Rec (map go rs)
  where
    go (n, e) =
      let x = mapMaybe (\case
                      Rec rs' ->
                        case lookup n rs' of
                          Just b' -> Just (n, b')
                          _ -> Nothing
                      _ -> Nothing) newBinds
      in
      case x of
        (r:_) -> r
        [] -> (n, e)

transformBinds :: ModGuts -> InstEnv -> [(Id, CoreExpr)] -> [CoreBind] -> CoreM [CoreBind]
transformBinds guts instEnv primMap binds = do
  (binds2, changedBinds) <- runWriterT $ mapM go0 binds

  let new_mg_binds = map (changeBind changedBinds) (mg_binds guts)

  mapM (go1 new_mg_binds) binds2
  where
    go0 :: CoreBind -> WriterT [CoreBind] CoreM CoreBind
    go0 b@(NonRec {}) = pure b
    go0 (Rec r) = do
      (x, bs) <- lift $ runWriterT
                  $ forM r
                  $ \ (name, e) -> do
                      hasEx <- lift $ hasExternalize guts e
                      if hasEx
                        then do
                          let r = (name, e)
                          tell [r]
                          return r
                          -- r <- (name,) <$> lift (transformTailRec guts name e)
                          -- tell [r]
                          -- return r
                        else return (name, e)

      tell [Rec bs]
      return (Rec x)

    go1 new_mg_binds (NonRec name e) = do
      hasEx <- hasExternalize guts e
      if hasEx
        then
          fmap (NonRec name) (transformExpr (guts {mg_binds = new_mg_binds}) name Nothing primMap e)
        else return (NonRec name e)

    go1 new_mg_binds (Rec r) = fmap Rec $
      forM r $ \ (name, e) -> do
        hasEx <- hasExternalize guts e
        if hasEx
          then do
            dflags <- getDynFlags
            (name,) <$> transformExpr (guts {mg_binds = new_mg_binds}) name (Just name) primMap e
          else return (name, e)


primMapTH :: [(TH.Name, TH.Name)]
primMapTH =
  [('(+), 'Add)
  ]

-- | 'Nothing' indicates that no changes were made
transformExprMaybe :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> CoreExpr -> CoreM (Maybe CoreExpr)
transformExprMaybe guts currName recName primMap e = do
  (r, progress) <- runWriterT (Data.transformM go e)
  case progress of
    Any False -> return Nothing
    Any True  -> return $ Just r
  where

    go :: CoreExpr -> WriterT Any CoreM CoreExpr
    go expr@(Var f :@ _ty :@ _dict :@ x) = do
      dflags <- getDynFlags
      externalizeId <- lift $ findIdTH guts 'externalize

      if f == externalizeId
        then do
          tell (Any True)
          lift $ encodingTransform guts currName x
        else return expr
    go expr = return expr

transformExpr :: ModGuts -> Var -> Maybe Var -> [(Id, CoreExpr)] -> CoreExpr -> CoreM CoreExpr
transformExpr guts currName recNameM primMap e = do
  dflags <- getDynFlags
  {- Data.transform (onCoercion (removeExpVarOnlyCoercion dflags)) <$> -}

  {- updateUnitTypeProofs guts =<< updateTypeProofs guts =<< updateUnitTypeProofs guts =<< -}
  untilNothingM (transformExprMaybe guts currName recNameM primMap) e


encodingTransform :: ModGuts -> Var -> CoreExpr -> CoreM CoreExpr
encodingTransform guts currName e = do
  exprTyCon <- findTyConTH guts ''Expr
  unrepId <- findIdTH guts 'unrep

  -- fromIntegral <- findIdTH guts 'fromIntegral
  -- fromInteger <- findIdTH guts 'fromInteger

  dflags <- getDynFlags
  traceM $ "encodingTransform: " ++ showPpr dflags e

  go (== unrepId) exprTyCon e
  where
    mark :: HasCallStack => CoreExpr -> CoreM CoreExpr
    mark = mark0 guts

    go :: HasCallStack => (Id -> Bool) -> TyCon -> CoreExpr -> CoreM CoreExpr
    go isUnrep exprTyCon (Case scrutinee wild ty alts) = do
      dflags <- getDynFlags
      traceM $ "alts = " ++ showPpr dflags alts

      r <- transformMatch guts mark scrutinee wild ty alts
      -- traceM $ "case result = " ++ showPpr dflags r
      return r

    go isUnrep exprTyCon expr@(Var f :@ x)
      | "D#" <- occNameString (occName f) = do

        litId <- findIdTH guts 'DE.Lit
        return (Var litId :@ expr)

    go isUnrep exprTyCon expr@(Var f :@ Type ty :@ x)
      | isUnrep f =
          return x

    go isUnrep exprTyCon expr@(_ :@ _)
      | Nothing <- getConstructorApp_maybe expr
      , (Var f, args) <- collectArgs expr
      , not (isConstructor f)
      , not (isUnrep f)
      -- , Nothing <- builtin f
      , not (hasExprTy expr) = do

        internalizeId <- findIdTH guts 'internalize

        dflags <- getDynFlags

        if f == internalizeId
          then do
            case args of
              [_, _, x] ->
                mark x
          else do
            when (f == currName) (error "Improper form of recursion (mutual recursion or non-tail recursion")

            let unfoldingF = getUnfolding guts dflags f

            markedArgs <- mapM mark args

            let (newF0, newArgs) = betaReduceAll unfoldingF args --markedArgs
                newF             = caseInlineT dflags $ caseInline dflags (caseInline dflags newF0)

            markedNewF <- mark newF

            mkExprApps guts markedNewF newArgs

      | Just (tys, dicts, constrTyCon, constr, args0) <- getConstructorApp_maybe (Data.transform (maybeApply workDataCon_maybe) expr),
        -- Nothing <- builtin constr,
        not (hasExprTy expr),
        not (isDict (Var constr)) = do

        let args = reverse args0  -- TODO: Why is this necessary?

        dflags <- getDynFlags

        constructRepId <- findIdTH guts 'ConstructRep
        repTyCon <- findTyConTH guts ''ExprRep

        if constr == constructRepId || constrTyCon == repTyCon
          then return expr
          else do

            -- traceM $ "constrTyCon = " ++ showPpr dflags constrTyCon
            -- traceM $ "constr = " ++ showPpr dflags constr
            -- traceM $ "args = " ++ showPpr dflags args


            repTyTyCon <- findTyConTH guts ''ExprRepTy

            dflags <- getDynFlags

            repDictExpr <- buildDictionaryT guts (mkTyConApp repTyCon [exprType expr])
            repDictRepTy <- buildDictionaryT guts (mkTyConApp repTyCon [mkTyConApp repTyTyCon [exprType expr]])
            repId <- findIdTH guts 'rep
            constructFnId <- findIdTH guts 'construct
            fromId <- findIdTH guts 'from

            let constr' = mkApps (Var constr) (tys ++ dicts)
            let getUnfolding' = getUnfolding guts dflags
            let repUnfolding = getUnfolding' repId

            traceM $ "constr' = " ++ showPpr dflags constr'


            let constructUnfolding = getUnfolding' constructFnId
                (constructFn0, _) =
                    betaReduceAll
                      constructUnfolding
                      [ Type (exprType expr)
                      , repDictExpr
                      ]
                constructFn1 = caseInline dflags $ Data.transform letNonRecSubst constructFn0
                (constructFnE, _) = collectArgs constructFn1

            let constructFn =
                    case constructFnE of
                      Var f -> Just f
                      _ -> Nothing



            let (rep1, repRestArgs) = betaReduceAll
                                       repUnfolding --constructUnfolding
                                         [ Type (exprType expr)
                                         , repDictExpr
                                         ]


            let tryUnfoldAndReduceDict' = tryUnfoldAndReduceDict guts dflags
            let unfoldAndReduceDict_maybe' = unfoldAndReduceDict_maybe guts dflags

            -- let rep1' = rep1

            -- let rep1'
            --       = id
            --         -- $ Data.transform letNonRecSubst
            --         -- $ tryUnfoldAndReduceDict'
            --         -- $ Data.transform letNonRecSubst
            --         -- $ tryUnfoldAndReduceDict'
            --         -- $ tryUnfoldAndReduceDict'
            --         $ caseInline dflags
            --         $ onScrutinee tryUnfoldAndReduceDict'
            --         $ Data.transform letNonRecSubst
            --         $ rep1

            unreppedArgs <- mapM (applyUnrep guts <=< mark) args
            let expr' = mkApps constr' unreppedArgs

            let elimFn fn
                  = maybeApply (transformMaybe (fmap (tryUnfoldAndReduceDict' . Data.transform letNonRecSubst . tryUnfoldAndReduceDict' . caseInline dflags) . onScrutinee_maybe unfoldAndReduceDict_maybe'))
                    . Data.transform betaReduce
                    . Data.transform (replaceVarId fn (getUnfolding' fn))

            let appedRep = (rep1 :@ expr')

            -- Unfold and reduce several 'construct's and a 'from'
            let appedRep'
                  = id
                    -- $ onAppArg tryUnfoldAndReduceDict'
                    -- $ Data.transform letNonRecSubst
                    -- $ Data.transform (caseInline dflags)
                    -- $ onAppArg tryUnfoldAndReduceDict'

                    -- $ Data.transform betaReduce
                    -- $ Data.transform (combineCasts dflags)
                    -- $ onAppArg (onAppFunId getUnfolding')

                    -- $ Data.transform letNonRecSubst
                    -- $ Data.transform (caseInline dflags)
                    -- $ onAppArg tryUnfoldAndReduceDict'
                    -- $ Data.transform (combineCasts dflags)
                    -- $ Data.transform betaReduce
                    -- $ elimFn constructFnId
                    -- $ Data.transform betaReduce
                    -- $ elimFn constructFnId
                    -- $ Data.transform (caseInline dflags)
                    -- $ Data.transform betaReduce
                    -- $ elimFn constructFnId
                    -- $ Data.transform betaReduce
                    -- $ elimFn constructFnId
                    -- $ Data.transform (caseInline dflags)
                    -- $ Data.transform betaReduce
                    -- $ Data.transform (replaceVarId constructFnId (getUnfolding' constructFnId))
                    -- $ Data.transform (caseInline dflags)
                    -- $ Data.transform betaReduce
                    -- $ maybeApply (transformMaybe (fmap (tryUnfoldAndReduceDict' . caseInline dflags) . onScrutinee_maybe unfoldAndReduceDict_maybe'))
                    -- $ Data.transform betaReduce

                    -- $ Data.transform (replaceVarId fromId (getUnfolding' fromId))

                    -- $ Data.transform betaReduce
                    -- $ Data.transform caseFloatArg
                    -- $ Data.transform caseFloatApp
                    -- $ elimFn constructFnId

                    -- $ Data.transform betaReduce
                    -- $ elimFn constructFnId


                    
                    -- $ Data.transform betaReduce
                    -- $ Data.transform (replaceVarId constructFnId (getUnfolding' constructFnId))

                    $ Data.transform (combineCasts dflags)

                    $ Data.transform betaReduce
                    $ elimFn constructFnId

                    $ Data.transform betaReduce
                    $ elimFn constructFnId

                    $ Data.transform (caseInline dflags)
                    $ Data.transform betaReduce
                    $ Data.transform (onScrutinee (Data.transform (onCastExpr tryUnfoldAndReduceDict')))
                    $ Data.transform (combineCasts dflags)
                    $ Data.transform betaReduce
                    $ elimFn fromId
                    $ Data.transform betaReduce
                    $ elimFn constructFnId
                    $ Data.transform betaReduce
                    $ elimFn constructFnId

                    $ Data.transform betaReduce
                    $ Data.transform (caseInline dflags)
                    $ Data.transform (onScrutinee betaReduce)
                    $ Data.transform (combineCasts dflags)
                    $ Data.transform (onScrutinee (Data.transform (onCastExpr tryUnfoldAndReduceDict')))
                    $ Data.transform (combineCasts dflags)
                    $ elimFn constructFnId

                    $ Data.transform betaReduce
                    $ Data.transform caseFloatApp
                    $ onAppArg tryUnfoldAndReduceDict'
                    $ Data.transform letNonRecSubst
                    $ onAppArg tryUnfoldAndReduceDict'
                    $ maybeApply (transformMaybe (fmap (caseInline dflags) . onScrutinee_maybe unfoldAndReduceDict_maybe'))
                    -- $ Data.transform (caseInline dflags)
                    -- $ Data.transform (onScrutinee tryUnfoldAndReduceDict')
                    $ Data.transform betaReduce
                    $ Data.transform (replaceVarId constructFnId (getUnfolding' constructFnId))

                    $ Data.transform betaReduce
                    $ Data.transform letNonRecSubst
                    $ (\x -> let (fn, _) = collectArgs x in trace ("unfold: " ++ showPpr dflags fn) (tryUnfoldAndReduceDict' x))

                    $ Data.transform (caseInline dflags)
                    $ Data.transform betaReduce
                    $ Data.transform letNonRecSubst
                    $ Data.transform betaReduce

                    $ onAppArg tryUnfoldAndReduceDict'

                    $ Data.transform (caseInline dflags)
                    $ onAppArg tryUnfoldAndReduceDict'
                    $ Data.transform betaReduce
                    $ Data.transform letNonRecSubst
                    $ tryUnfoldAndReduceDict'
                    $ Data.transform (caseInline dflags)
                    $ Data.transform (onScrutinee tryUnfoldAndReduceDict')
                    $ Data.transform letNonRecSubst
                    $ appedRep

            appedRep'' <- Data.transformM (elimRepUnrep guts) appedRep'

            -- traceM $ "rep: " ++ showPpr dflags rep1'
            -- traceM $ "rep type: " ++ showPpr dflags (exprType rep1')

            traceM $ "appedRep: " ++ showPpr dflags appedRep''

            -- traceM $ "repRestArgs: " ++ showPpr dflags repRestArgs

            return appedRep''

      where
        hasExprTy = hasExprTy' exprTyCon
    go _ _ e = return e

transformMatch :: HasCallStack => ModGuts -> (CoreExpr -> CoreM CoreExpr) -> CoreExpr -> Var -> Type -> [CoreAlt] -> CoreM CoreExpr
transformMatch guts mark scrutinee wild resultTy alts@[alt@(DataAlt dataAlt1, _, _)] = do
  dynFlags <- getDynFlags

  repTyCon <- findTyConTH guts ''ExprRep
  eitherTyCon <- findTyConTH guts ''Either

  scrTy <- unwrapExpType guts (exprType scrutinee)

  let scrRepTy = mkTyConApp repTyCon [scrTy]

  scrRepTyTy <- repTyWrap guts scrTy
  (scrTyCo, scrTyNorm) <- normaliseTypeCo guts scrRepTyTy
  sumTypes <- listTypesWith guts (getName eitherTyCon) scrTyNorm
  nRepType <- normaliseType' guts scrTy
  sumMatch <- go repTyCon sumTypes alts


  caseExpId <- findIdTH guts 'CaseExp
  repTypeDict <- buildDictionaryT guts scrRepTy
  scrutinee' <- mark scrutinee

  repTyTyCon <- findTyConTH guts ''ExprRepTy

  let scrTyNormRepTy = mkTyConApp repTyTyCon [scrTyNorm]

  (scrTyNormRepTyCo, _) <- normaliseTypeCo guts scrTyNormRepTy

  return (Var caseExpId
           :@ Type scrTy
           :@ Type scrTyNorm
           :@ Type resultTy
           :@ repTypeDict
           :@ mkEqBox scrTyNormRepTyCo
           :@ mkEqBox scrTyCo
           :@ scrutinee'
           :@ sumMatch)
  where
    go :: TyCon -> [Type] -> [Alt Var] -> CoreM CoreExpr
    go repTyCon [ty] [x] = do
      transformProdMatch guts mark resultTy ty x
    go _ _ _ = error "Wrong number of case alts (needs exactly 1)"


transformProdMatch :: ModGuts -> (CoreExpr -> CoreM CoreExpr) -> Type -> Type -> Alt Var -> CoreM CoreExpr
transformProdMatch guts mark resultTy ty0_ (altCon@(DataAlt dataAlt), vars0, body0) = do
  dflags <- getDynFlags
  repTyCon <- findTyConTH guts ''ExprRep

  ty0 <- (unwrapExpType guts <=< unwrapExpType guts) ty0_

  repType <- computeRepType guts ty0

  pairTyCon <- findTyConTH guts ''(,)

  prodTypes <- listTypesWith guts (getName pairTyCon) repType

  body <- mark body0
  go body pairTyCon repTyCon prodTypes vars0
  where
    go :: CoreExpr -> TyCon -> TyCon -> [Type] -> [Var] -> CoreM CoreExpr
    go body pairTyCon repTyCon (ty1:_) [] = do
      nullaryMatchId <- findIdTH guts 'NullaryMatch

      resultTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])

      return (Var nullaryMatchId :@ Type ty1 :@ Type resultTy :@ resultTyDict :@ body)

    go body pairTyCon repTyCon allTys@(ty1:_) [x] = do
      dflags <- getDynFlags

      let ty = pairWrap pairTyCon allTys

      oneProdMatchId <- findIdTH guts 'OneProdMatch

      tyDict <- buildDictionaryT guts (mkTyConApp repTyCon [ty])

      -- abs'd <- mark =<< abstractOver guts x body
      abs'd <- abstractOver guts x =<< mark body

      return (Var oneProdMatchId :@ Type ty :@ Type resultTy :@ tyDict :@ abs'd)

    go body pairTyCon repTyCon (ty1:restTys) (x:xs) = do
      dflags <- getDynFlags

      prodMatchId <- findIdTH guts 'ProdMatchExp

      let restTy = pairWrap pairTyCon restTys

      rest <- go body pairTyCon repTyCon restTys xs

      ty1Dict <- buildDictionaryT guts (mkTyConApp repTyCon [ty1])
      restTyDict <- buildDictionaryT guts (mkTyConApp repTyCon [restTy])

      abs'd <- abstractOver guts x rest

      return (Var prodMatchId
        :@ Type ty1
        :@ Type restTy
        :@ Type resultTy
        :@ ty1Dict
        :@ restTyDict
        :@ abs'd)
    go body pairTyCon repTyCon tys xs = do
      dflags <- getDynFlags

      error $ "transformProdMatch.go: (" ++ showPpr dflags tys ++ ", " ++ showPpr dflags xs ++ ")\n" -- ++ showPpr dflags body
    pairWrap _ [] = error "pairWrap"
    pairWrap pairTyCon xs = foldr1 (\x acc -> mkTyConApp pairTyCon [x, acc]) xs


-- Mark for further transformation
mark0 :: HasCallStack => ModGuts -> CoreExpr -> CoreM CoreExpr
mark0 _ e@(Type _) = return e
-- mark0 _ e@(Coercion {}) = return e
mark0 guts e@(Var f :@ Type ty :@ dict :@ x) = do
  externalizeName <- findIdTH guts 'externalize

  if f == externalizeName
    then return e
    else markIt guts e

mark0 guts x = markIt guts x

-- | Mark without special treatment for any 'unrep (Var ...)' expressions
markIt :: HasCallStack => ModGuts -> CoreExpr -> CoreM CoreExpr
markIt guts x = do
  dflags <- getDynFlags
  expTyCon <- findTyConTH guts ''Expr

  -- traceM $ "markIt: " ++ showPpr dflags x

  eType <- hasExprType guts x
  -- traceM $ "markIt x hasExprType: " ++ showPpr dflags eType
  -- liftIO $ putStrLn $ "markIt exprType = " ++ showPpr dflags (exprType x)
  if eType
    then return x
    else
      case splitFunTy_maybe (exprType x) of
        Just (a, b)
          | isExprTy expTyCon a && isExprTy expTyCon b -> return x
        _ -> markAny guts x

-- | Mark anything that isn't a dictionary
markAny :: HasCallStack => ModGuts -> CoreExpr -> CoreM CoreExpr
markAny guts x = do
  dflags <- getDynFlags
  if isDict x
    then return x
    else do
      let xTy = exprType x

      externalizeName <- findIdTH guts 'externalize

      repTyCon <- findTyConTH guts ''ExprRep

      dict <- buildDictionaryT guts (mkTyConApp repTyCon [xTy])

      return (Var externalizeName :@ Type xTy :@ dict :@ x)


-- | Does the expression already have a type of the form Expr (...)?
hasExprType :: ModGuts -> CoreExpr -> CoreM Bool
hasExprType guts e = do
  expTyCon <- findTyConTH guts ''Expr

  return $ hasExprTy' expTyCon e

hasExprTy' :: TyCon -> CoreExpr -> Bool
hasExprTy' expTyCon e = isExprTy expTyCon (exprType e)

isExprTy :: TyCon -> Type -> Bool
isExprTy expTyCon ty =
  case splitTyConApp_maybe ty of
    Nothing -> False
    Just (t, _) -> t == expTyCon

whenNotExprTyped :: ModGuts -> CoreExpr -> CoreM CoreExpr -> CoreM CoreExpr
whenNotExprTyped guts e m = do
  eType <- hasExprType guts e
  if eType
    then return e
    else m


-- | Expr t  ==>  t
-- and ExprRepTy t  ==>  t
-- otherwise, it stays the same
unwrapExpType :: ModGuts -> Type -> CoreM Type
unwrapExpType guts ty = do
  expTyCon <- findTyConTH guts ''Expr
  repTyTyCon <- findTyConTH guts ''ExprRepTy

  let ty' = case splitTyConApp_maybe ty  of
              Nothing -> ty
              Just (tyCon, args) ->
                if tyCon == expTyCon
                  then head args
                  else ty

  case splitTyConApp_maybe ty' of
    Just (tyCon, args)
      | tyCon == repTyTyCon -> return (head args)
    _ -> return ty'


-- | Wrap in ExprRepTy if it isn't already wrapped in a ExprRepTy
repTyWrap :: ModGuts -> Type -> CoreM Type
repTyWrap guts ty = do
  repTyTyCon <- findTyConTH guts ''ExprRepTy

  case splitTyConApp_maybe ty of
    Just (tyCon, _)
      | tyCon == repTyTyCon -> return ty
    _                       -> return (mkTyConApp repTyTyCon [ty])


-- | listTypesWith (lookupVar ''(,)) (a, (b, c))  ==>  [a, b, c]
-- listTypesWith (lookupVar ''Either) (Either a (Either b c))  ==>  [a, b, c]
listTypesWith :: ModGuts -> Name -> Type -> CoreM [Type]
listTypesWith guts n = go <=< (Data.transformM normaliseGenerics) -- <=< (fmap snd . topNormaliseType' guts)
  where
    normaliseGenerics :: Type -> CoreM Type
    normaliseGenerics ty = do

      repTyCon <- findTyConTH guts ''ExprRepTy
      m1TyCon <- findTyConTH guts ''M1

      case splitTyConApp_maybe ty of
        Just (repTyConPossible, (arg:_))
          | repTyConPossible == repTyCon
            -> case splitTyConApp_maybe arg of
                   Just (m1TyConPossible, _)
                     | m1TyConPossible == m1TyCon
                        || m1TyConPossible == repTyCon -- Collapse ExprRepTy's
                          -> normaliseType' guts ty
                   _ -> return ty
        _ -> return ty


    go ty =
      case splitTyConApp_maybe ty of
        Nothing -> return [ty]
        Just (tyCon, [a, b])
          | tyConName tyCon /= n -> return [ty]
          | otherwise ->
              fmap (a:) (go b)
        Just _ -> return [ty]


-- | Use ExprRepTy to find the canonical representation type
computeRepType :: ModGuts -> Type -> CoreM Type
computeRepType guts = fmap snd . computeRepTypeCo guts

computeRepTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
computeRepTypeCo guts ty = do
  repTy <- thNameToGhcName_ ''ExprRepTy

  repTy' <- findTyCon' guts repTy

  normaliseTypeCo guts (mkTyConApp repTy' [ty])

abstractOver :: HasCallStack => ModGuts -> Var -> CoreExpr -> CoreM CoreExpr
abstractOver guts v e = do

  exprTyCon <- findTyConTH guts ''Expr

  let origTy = varType v
      newTy = mkTyConApp exprTyCon [origTy]
      v' = setVarType v newTy

  lamId <- findIdTH guts 'DE.Lam

  eTy' <- unwrapExpType guts (exprType e)

  return (Var lamId :@ Type (idType v) :@ Type eTy' :@ (GhcPlugins.Lam v' e))


-- | mkExprApps f [x, y, z]  =  App (App (App f x') y') z'
-- where x', y', z' are marked versions of x, y and z
mkExprApps :: ModGuts -> CoreExpr -> [CoreExpr] -> CoreM CoreExpr
mkExprApps guts fn0 args0 =
    foldlM go fn0 args0
  where
    go f x = do
      dflags <- getDynFlags
      appId <- findIdTH guts 'DE.App

      repTyCon <- findTyConTH guts ''Expr

      tyM <- getEmbeddedFnType guts (exprType f)

      case tyM of
        Nothing -> error "mkExprApps"
        Just (tyA, tyB) -> do
          dictA <- buildDictionaryT guts (mkTyConApp repTyCon [tyA])

          markedX <- mark0 guts x

          return (Var appId :@ Type tyA :@ Type tyB :@ dictA :@ f :@ markedX)


-- | Expr (a -> b)  ===>   Just (a, b)
getEmbeddedFnType0 :: TyCon -> ModGuts -> Type -> Maybe (Type, Type)
getEmbeddedFnType0 expTyCon guts t =
    let t' = dropForAlls t
        (_, resultTy0) = splitForAllTys t'
        resultTy = finalResultType resultTy0
    in
    case splitTyConApp_maybe resultTy of
      Just (ex, [fn])
        | ex == expTyCon && isFunTy fn -> Just (splitFunTy fn)
      _ -> Nothing

getEmbeddedFnType :: ModGuts -> Type -> CoreM (Maybe (Type, Type))
getEmbeddedFnType guts t = do
    expTyCon <- findTyConTH guts ''Expr
    return $ getEmbeddedFnType0 expTyCon guts t

isEmbeddedFnType :: ModGuts -> Type -> CoreM Bool
isEmbeddedFnType guts t =
  fmap isJust (getEmbeddedFnType guts t)

finalResultType :: Type -> Type
finalResultType ty =
  case splitFunTy_maybe ty of
    Nothing -> ty
    Just (_, ty') -> finalResultType ty'


applyUnrep :: ModGuts -> CoreExpr -> CoreM CoreExpr
applyUnrep guts e = do
  dflags <- getDynFlags

  ty <- unwrapExpType guts (exprType e)

  unrepId <- findIdTH guts 'unrep

  let result = (Var unrepId :@ Type ty :@ e)
  return result


-- | rep (unrep x)  ==>  x
elimRepUnrep :: ModGuts -> CoreExpr -> CoreM CoreExpr
elimRepUnrep guts expr0@(Cast e co) = elimRepUnrep_co guts (Just co) origType e
  where origType = exprType expr0
elimRepUnrep guts expr = elimRepUnrep_co guts Nothing (exprType expr) expr

elimRepUnrep_co :: ModGuts -> Maybe Coercion -> Type -> CoreExpr -> CoreM CoreExpr
elimRepUnrep_co guts coA_M origType expr@(Var r :@ Type{} :@ dict :@ arg) =
  go0 arg
  where
    go0 e =
      case e of
        Var u :@ Type{} :@ x -> go e u Nothing x
        Cast (Var u :@ Type{} :@ x) coB -> go e u (Just coB) x
        _ -> Data.descendM (elimRepUnrep guts) expr

    go :: CoreExpr -> Id -> Maybe Coercion -> CoreExpr -> CoreM CoreExpr
    go unrepped u coB_M x = do
      dflags <- getDynFlags

      repId <- findIdTH guts 'rep
      unrepId <- findIdTH guts 'unrep
      expTyCon <- findTyConTH guts ''Expr

      let co_M = do
                    guard (isJust coA_M || isJust coB_M)
                    let newCo = buildCoercion (exprType x) origType

                    newCo' <- case splitTyConApp_maybe (coercionRKind newCo) of
                                Just (tyCon, _)
                                  | tyCon == expTyCon -> return newCo
                                _ -> Just $ buildCoercion (mkTyConApp expTyCon [exprType x]) (mkTyConApp expTyCon [origType])

                    let newCo'' =
                          case coA_M of
                            Nothing -> newCo'
                            Just coA -> mkTransCo newCo' coA

                    traceM $ "newCo'' kind = " ++ showPpr dflags (coercionKind newCo'')

                    Just $ downgradeRole Representational (coercionRole newCo'') newCo''


      if r == repId && u == unrepId
        then do
          ty <- unwrapExpType guts (exprType unrepped)

          if not $ eqType ty (exprType unrepped)
            then traceM "not eqType" >> Data.descendM (elimRepUnrep guts) x
            else elimRepUnrep guts x
        else Data.descendM (elimRepUnrep guts) expr--return $ coerceMaybe coA_M expr

    composeCos = mkTransCo

elimRepUnrep_co guts co_M _ expr = Data.descendM (elimRepUnrep guts) $ coerceMaybe co_M expr

-- TODO: Check this
coerceMaybe :: Maybe Coercion -> CoreExpr -> CoreExpr
coerceMaybe Nothing e = e
coerceMaybe (Just co) e = Cast e co


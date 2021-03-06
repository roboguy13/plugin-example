{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}

module Plugin.Utils
  where

import           GhcPlugins hiding (freeVarsBind)

import           Pair

import           CoreSubst
import           Unique
import           PrelNames

import           TcRnTypes
import           TcSimplify
import           TcMType
import           TcRnMonad
import           TcSMonad
import           TcEvidence
import           TcType

import           TyCoRep

import           TcErrors

import           InstEnv
import           FamInstEnv

import           Class

import           MkId

import           Packages

import           Coercion

import           Finder
import           LoadIface

import           DsBinds
import           DsMonad

import           HsBinds
import           HsDecls

import qualified OccName

import           CostCentreState

import           Bag
import           VarSet

import           Encoding

import           CoreOpt
import           OccurAnal

import           ErrUtils

import           Data.IORef

import qualified Data.Map as Map
import qualified Data.Set as Set

import           Control.Monad
import           Control.Monad.Identity
import           Control.Monad.Writer

import           Control.Arrow (first, second)

import           Control.Applicative

import           Data.Monoid


import           Data.Char
import           Data.List

import           Data.Generics.Uniplate.Operations
import qualified Data.Generics.Uniplate.DataOnly as Data

import           Data.Data (Data)

-- Just for TH Names:
import qualified Language.Haskell.TH.Syntax as TH

infixl 0 :@
pattern f :@ x = App f x


-- Partially from HERMIT --

-- | Build a dictionary for the given
buildDictionary :: HasCallStack => ModGuts -> Id -> CoreM (Id, [CoreBind])
buildDictionary guts evar = do
    dflags <- getDynFlags
    hsc_env <- getHscEnv
    eps <- liftIO $ hscEPS hsc_env

    (i, bs) <- runTcM guts $ do
#if __GLASGOW_HASKELL__ > 710
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
#else
        loc <- getCtLoc $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
#if __GLASGOW_HASKELL__ > 710
            wanted =  CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar, ctev_loc = loc, ctev_nosh = WDeriv }
            -- nonC = mkNonCanonical wanted
            -- wCs = mkSimpleWC [cc_ev nonC]
            wCs = mkSimpleWC [wanted]
        -- TODO: Make sure solveWanteds is the right function to call.
        (wCs', bnds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
        -- (wCs'', bnds') <- second evBindMapBinds <$> runTcS (solveWanteds wCs')
        -- liftIO $ putStrLn (showPpr dflags bnds)
#else
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkSimpleWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
#endif
        reportAllUnsolved wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        return (evar, bnds)
    bnds <- runDsM guts $ dsEvBinds bs
    -- bnds2 <- mapM (tryToFillCoHoles guts) bnds
    return (i,bnds)


buildDictionaryT :: HasCallStack => ModGuts -> Type -> CoreM CoreExpr
buildDictionaryT guts = \ ty0 -> do

    dflags <- getDynFlags

    ty <- case splitTyConApp_maybe ty0 of
            Just (tyCon, tyArgs) -> do
                tyArgs' <- mapM (normaliseType' guts) tyArgs
                let r = mkTyConApp tyCon tyArgs'
                return r
            Nothing -> return ty0

    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary guts binder
    when (null bnds) (error ("no dictionary bindings generated for " ++ showPpr dflags ty))
    -- guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)


runTcM :: HasCallStack => ModGuts -> TcM a -> CoreM a
runTcM guts m = do
    env <- getHscEnv
    dflags <- getDynFlags
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (error $ showMsgs msgs) return mr

runDsM :: ModGuts -> DsM a -> CoreM a
runDsM guts = runTcM guts . initDsTc

-- | Make a unique identifier for a specified type, using a provided name.
newIdH :: MonadUnique m => String -> Type -> m Id
newIdH nm ty = mkLocalId <$> newName' nm <*> return ty

-- | Make a 'Name' from a string.
newName' :: MonadUnique m => String -> m Name
newName' nm = mkSystemVarName <$> getUniqueM <*> return (mkFastString nm)

-- initTcFromModGuts
--   :: HscEnv
--   -> ModGuts
--   -> HscSource
--   -> Bool
--   -> TcM r
--   -> IO (Messages, Maybe r)
-- initTcFromModGuts hsc_env guts hsc_src keep_rn_syntax do_this
--   = let realSrcLoc = realSrcLocSpan $ mkRealSrcLoc (fsLit "Top level") 1 1
--     in
--     initTc hsc_env hsc_src keep_rn_syntax (mg_module guts) realSrcLoc do_this

-- | Re-Setup the typechecking environment from a ModGuts
initTcFromModGuts
    :: HscEnv
    -> ModGuts
    -> HscSource
    -> Bool          -- True <=> retain renamed syntax trees
    -> TcM r
    -> IO (Messages, Maybe r) -- Nothing => error thrown by the thing inside
                              -- (error messages should have been printed already)
initTcFromModGuts hsc_env guts hsc_src keep_rn_syntax do_this
 = do { let { type_env = mk_type_env guts } ;
        errs_var     <- newIORef (emptyBag, emptyBag) ;
        tvs_var      <- newIORef emptyVarSet ;
        keep_var     <- newIORef emptyNameSet ;
#if __GLASGOW_HASKELL__ > 710 
        used_gre_var <- newIORef [] ;
#else
        used_rdr_var <- newIORef Set.empty ;
#endif
        th_var       <- newIORef False ;
        th_splice_var<- newIORef False ;
#if __GLASGOW_HASKELL__ > 710 
        infer_var    <- newIORef (True, emptyBag) ;
#else
        infer_var    <- newIORef True ;
#endif
        lie_var      <- newIORef emptyWC ;
        dfun_n_var   <- newIORef (mk_dfun_n guts) ;
        type_env_var <- newIORef type_env ;

        dependent_files_var <- newIORef [] ;
        static_wc_var       <- newIORef emptyWC ;

        th_topdecls_var      <- newIORef [] ;
        th_topnames_var      <- newIORef emptyNameSet ;
        th_modfinalizers_var <- newIORef [] ;
        th_state_var         <- newIORef Map.empty ;
#if __GLASGOW_HASKELL__ > 710 
        th_remote_state_var  <- newIORef Nothing ;
#endif


        th_top_level_locs_var <- newIORef (Set.fromList []) ;
        th_foreign_files_var <- newIORef [] ;
        th_coreplugins_var <- newIORef [] ;

{- TODO: Verify implementations are correct for:
           tcg_semantic_mod,
           tcg_th_top_level_locs, tcg_merged, tcg_th_foreign_files,
           tcg_th_coreplugins, tcg_top_loc, tcg_complete_matches,
           tcg_cc_st
 -}

        costCentreState_var <- newIORef newCostCentreState ;
        eps <- hscEPS hsc_env ;



        let {
             dflags = hsc_dflags hsc_env ;
             mod = mg_module guts ;
             realSrcLoc = realSrcLocSpan $ mkRealSrcLoc (fsLit "Top level") 1 1 ;

             maybe_rn_syntax :: forall a. a -> Maybe a ;
             maybe_rn_syntax empty_val
                | keep_rn_syntax = Just empty_val
                | otherwise      = Nothing ;

             gbl_env = TcGblEnv {
                tcg_semantic_mod = mod, -- TODO: Is this ok?

                tcg_th_top_level_locs = th_top_level_locs_var,
                tcg_merged = [],
                tcg_th_foreign_files = th_foreign_files_var,
                tcg_th_coreplugins = th_coreplugins_var,
                tcg_top_loc = realSrcLoc,
                tcg_complete_matches = [],
                tcg_cc_st = costCentreState_var,

                -- these first four are CPP'd in GHC itself, but we include them here
                tcg_th_topdecls      = th_topdecls_var,
                tcg_th_topnames      = th_topnames_var,
                tcg_th_modfinalizers = th_modfinalizers_var,
                tcg_th_state         = th_state_var,

                -- queried during tcrnif
                tcg_mod            = mod,
                tcg_src            = hsc_src,
                -- tcg_sig_of         = getSigOf dflags (moduleName mod),
                -- tcg_impl_rdr_env   = Nothing,
                tcg_rdr_env        = mg_rdr_env guts,
                tcg_default        = Nothing,
                tcg_fix_env        = mg_fix_env guts,
                tcg_field_env      = mk_field_env guts,
                tcg_type_env       = type_env,
                tcg_type_env_var   = type_env_var,
                tcg_inst_env       = mg_inst_env guts,
                -- tcg_inst_env       = extendInstEnvList (mg_inst_env guts)
                --                       (filter (\eps_inst ->
                --                                   not (memberInstEnv (mg_inst_env guts) eps_inst))
                --                         (instEnvElts (eps_inst_env eps))),
                tcg_fam_inst_env   = mg_fam_inst_env guts,
                tcg_ann_env        = emptyAnnEnv,
#if __GLASGOW_HASKELL__ <= 710 
                tcg_visible_orphan_mods = mkModuleSet [mod],
#endif
                tcg_dfun_n         = dfun_n_var,

                -- accumulated, not queried, during tcrnif
                tcg_dependent_files = dependent_files_var,
                tcg_tc_plugins     = [],
                tcg_static_wc      = static_wc_var,
                tcg_exports        = [],
                tcg_warns          = NoWarnings,
                tcg_anns           = [],
                tcg_tcs            = [],
                tcg_insts          = [],
                tcg_fam_insts      = [],
                tcg_rules          = [],
                tcg_th_used        = th_var,
                tcg_imports        = emptyImportAvails {imp_orphs = dep_orphs (mg_deps guts)},
                tcg_dus            = emptyDUs,
                tcg_ev_binds       = emptyBag,
                tcg_fords          = [],
                -- tcg_vects          = [],
                tcg_patsyns        = [],
                tcg_doc_hdr        = Nothing,
                tcg_hpc            = False,
                tcg_main           = Nothing,
                tcg_safeInfer      = infer_var,
                tcg_binds          = emptyLHsBinds,
                tcg_sigs           = emptyNameSet,
                tcg_imp_specs      = [],
                tcg_rn_decls       = maybe_rn_syntax emptyRnGroup,
#if __GLASGOW_HASKELL__ <= 710 
                tcg_used_rdrnames  = used_rdr_var,
#endif
                tcg_rn_imports     = [],
                tcg_rn_exports     = maybe_rn_syntax [],
                tcg_keep           = keep_var,
#if __GLASGOW_HASKELL__ > 710 
                tcg_self_boot      = NoSelfBoot, -- Assume there are no hsboot files
                tcg_used_gres       = used_gre_var,
                tcg_th_remote_state = th_remote_state_var,
                tcg_tr_module       = Nothing,
#endif
                tcg_th_splice_used = th_splice_var
             } ;
             lcl_env = TcLclEnv {
                tcl_errs       = errs_var,
                tcl_loc        = realSrcLoc,
                tcl_ctxt       = [],
                tcl_rdr        = emptyLocalRdrEnv,
                tcl_th_ctxt    = topStage,
                tcl_th_bndrs   = emptyNameEnv,
                tcl_arrow_ctxt = NoArrowCtxt,
                tcl_env        = emptyNameEnv,
                tcl_bndrs      = [],
                -- tcl_tidy       = emptyTidyEnv,
                tcl_tyvars     = tvs_var,
                tcl_lie        = lie_var,
                tcl_tclvl      = topTcLevel
             } ;
        } ;

        -- OK, here's the business end!
        maybe_res <- initTcRnIf 'a' hsc_env gbl_env lcl_env $
                     do { r <- TcRnMonad.tryM do_this
                        ; case r of
                          Right res -> return (Just res)
                          Left _    -> return Nothing } ;

        -- Check for unsolved constraints
        lie <- readIORef lie_var ;
        if isEmptyWC lie
           then return ()
           else pprPanic "initTc: unsolved constraints" (ppr lie) ;

        -- Collect any error messages
        msgs <- readIORef errs_var ;

        let { final_res | errorsFound dflags msgs = Nothing
                        | otherwise               = maybe_res } ;

        return (msgs, final_res)
    }


mk_type_env :: ModGuts -> TypeEnv
-- copied from GHC.compileCore
mk_type_env guts = typeEnvFromEntities (bindersOfBinds (mg_binds guts))
                                           (mg_tcs guts)
                                           (mg_fam_insts guts)
mk_field_env :: ModGuts -> RecFieldEnv
-- TODO
#if __GLASGOW_HASKELL__ > 710
mk_field_env _ = emptyNameEnv 
#else
mk_field_env _ = RecFields emptyNameEnv emptyNameSet
#endif

mk_dfun_n :: ModGuts -> OccSet
-- TODO
mk_dfun_n _ = emptyOccSet

-- | Possible results from name lookup.
-- Invariant: One constructor for each NameSpace.
data Named = NamedId Id
           | NamedDataCon DataCon
           | NamedTyCon TyCon
           | NamedTyVar Var

instance Show Named where
    show (NamedId _) = "NamedId"
    show (NamedDataCon _) = "NamedDataCon"
    show (NamedTyCon _) = "NamedTyCon"
    show (NamedTyVar _) = "NamedTyVar"

instance NamedThing Named where
  getOccName (NamedId x) = getOccName x
  getOccName (NamedDataCon x) = getOccName x
  getOccName (NamedTyCon x) = getOccName x
  getOccName (NamedTyVar x) = getOccName x

  getName (NamedId x) = getName x
  getName (NamedDataCon x) = getName x
  getName (NamedTyCon x) = getName x
  getName (NamedTyVar x) = getName x

tyConClassNS :: NameSpace
tyConClassNS = tcClsName

dataConNS :: NameSpace
dataConNS = dataName

tyVarNS :: NameSpace
tyVarNS = tvName

varNS :: NameSpace
varNS = varNameNS

-- | Rename this namespace, as 'varName' is already a function in Var.
varNameNS :: NameSpace
varNameNS = OccName.varName

allNameSpaces :: [NameSpace]
allNameSpaces = [varNS, dataConNS, tyConClassNS, tyVarNS]

findId :: ModGuts -> Name -> VarSet -> CoreM Id
findId guts nm c = do
    nmd <- findInNameSpaces guts [varNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> error $ "findId: impossible Named returned: " ++ show other

findVar :: ModGuts -> Name -> VarSet -> CoreM Var
findVar guts nm c = do
    nmd <- findInNameSpaces guts [varNS, tyVarNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedTyVar v -> return v
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> error $ "findVar: impossible Named returned: " ++ show other

findDataConWorkId :: ModGuts -> Name -> CoreM Id
findDataConWorkId guts nm = do
  nmd <- findInNameSpaces guts [dataConNS] nm emptyVarSet
  case nmd of
    NamedDataCon dc -> return $ dataConWorkId dc
    other -> error $ "findDataConWorkId: impossible Named returned: " ++ show other


findTyCon' :: ModGuts -> Name -> CoreM TyCon
findTyCon' guts nm = findTyCon guts nm emptyVarSet

findTyCon :: ModGuts -> Name -> VarSet -> CoreM TyCon
findTyCon guts nm c = do
    nmd <- findInNameSpace guts tyConClassNS nm c
    case nmd of
        NamedTyCon tc -> return tc
        other -> error $ "findTyCon: impossible Named returned: " ++ show other

findType :: ModGuts -> Name -> VarSet -> CoreM Type
findType guts nm c = do
    nmd <- findInNameSpaces guts [tyVarNS, tyConClassNS] nm c
    case nmd of
        NamedTyVar v -> return $ mkTyVarTy v
        NamedTyCon tc -> return $ mkTyConTy tc
        other -> error $ "findType: impossible Named returned: " ++ show other

findNamed :: ModGuts -> Name -> VarSet -> CoreM Named
findNamed guts nm c =
    findInNameSpaces guts allNameSpaces nm c

--------------------------------------------------------------------------------------------------

findInNameSpaces :: ModGuts -> [NameSpace] -> Name -> VarSet -> CoreM Named
findInNameSpaces guts nss nm c = do --setFailMsg "Variable not in scope." -- because catchesM clobbers failure messages.
  rs <- sequence [ findInNameSpace guts ns nm c | ns <- nss ]
  case rs of
    [] -> error "Variable not in scope"
    (r:_) -> return r

findInNameSpace :: ModGuts -> NameSpace -> Name -> VarSet -> CoreM Named
findInNameSpace guts ns nm c =
    case nonDetEltsUniqSet $ filterVarSet ((== ns) . occNameSpace . getOccName) $ findBoundVars ((== nm) . varName) c of
        _ : _ : _ -> error "multiple matching variables in scope."
        [v]       -> return (varToNamed v)
        []        -> findInNSModGuts guts ns nm

varToNamed :: Var -> Named
varToNamed v | isVarOcc onm = NamedId v
             | isTvOcc onm  = NamedTyVar v
             | otherwise = error "varToNamed: impossible Var namespace"
    where onm = getOccName v

-- | List all variables bound in the context that match the given predicate.
findBoundVars :: (Var -> Bool) -> VarSet -> VarSet
findBoundVars p = filterVarSet p

-- | Looks for TyCon in current GlobalRdrEnv. If not present, calls 'findInNSPackageDB'.
findInNSModGuts :: ModGuts -> NameSpace -> Name -> CoreM Named
findInNSModGuts guts ns nm = do
    let rdrEnv = mg_rdr_env guts
    case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
        [gre] -> nameToNamed $ gre_name gre
        []    -> findInNSPackageDB guts ns nm
        _     -> error "findInNSModGuts: multiple names returned"

-- | We have a name, find the corresponding Named.
nameToNamed :: MonadThings m => Name -> m Named
nameToNamed n | isVarName n     = liftM NamedId $ lookupId n
              | isDataConName n = liftM NamedDataCon $ lookupDataCon n
              | isTyConName n   = liftM NamedTyCon $ lookupTyCon n
              | isTyVarName n   = error "nameToNamed: impossible, TyVars are not exported and cannot be looked up."
              | otherwise       = error "nameToNamed: unknown name type"

-- | Make a RdrName for the given NameSpace and HermitName
toRdrName :: NameSpace -> Name -> RdrName
toRdrName ns nm = maybe (mkRdrUnqual onm) (flip mkRdrQual onm) (Just mnm)
    where onm = nameOccName nm
          mnm = moduleName $ nameModule nm

-- | Looks for Named in package database, or built-in packages.
findInNSPackageDB :: ModGuts -> NameSpace -> Name -> CoreM Named
findInNSPackageDB guts ns nm = do
    mnm <- lookupName guts ns nm
    case mnm of
        Nothing -> findNamedBuiltIn ns nm
        Just n  -> nameToNamed n

-- | Helper to call lookupRdrNameInModule
lookupName :: ModGuts -> NameSpace -> Name -> CoreM (Maybe Name)
lookupName guts ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        liftIO $ lookupRdrNameInModule hscEnv guts m rdrName
    where rdrName = toRdrName ns nm
          --
-- | Looks for Named amongst GHC's built-in DataCons/TyCons.
findNamedBuiltIn :: Monad m => NameSpace -> Name -> m Named
findNamedBuiltIn ns n
    | isValNameSpace ns =
        case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc, n == (getName dc) ] of
            [] -> error "name not in scope."
            [dc] -> return $ NamedDataCon dc
            dcs -> error $ "multiple DataCons match: " ++ intercalate ", " (map unqualifiedName dcs)
    | isTcClsNameSpace ns =
        case [ tc | tc <- wiredInTyCons, n == (getName tc) ] of
            [] -> error "type name not in scope."
            [tc] -> return $ NamedTyCon tc
            tcs -> error $ "multiple TyCons match: " ++ intercalate ", " (map unqualifiedName tcs)
    | otherwise = error "findNameBuiltIn: unusable NameSpace"

-- | Finds the 'Name' corresponding to the given 'RdrName' in the context of the 'ModuleName'. Returns @Nothing@ if no
-- such 'Name' could be found. Any other condition results in an exception:
--
-- * If the module could not be found
-- * If we could not determine the imports of the module
--
-- This is adapted from GHC's function called lookupRdrNameInModuleForPlugins,
-- but using initTcFromModGuts instead of initTcInteractive. Also, we ImportBySystem
-- instead of ImportByPlugin, so the EPS gets populated with RULES and instances from
-- the loaded module.
--
-- TODO: consider importing by plugin first, then only importing by system when a name
-- is successfully found... as written we will load RULES/instances if the module loads
-- successfully, even if the name is not found.
lookupRdrNameInModule :: HscEnv -> ModGuts -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrNameInModule hsc_env guts mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing

    let go mod = do
            -- Find the exports of the module
            (_, mb_iface) <- initTcFromModGuts hsc_env guts HsSrcFile False $
                             initIfaceTcRn $
                             loadSysInterface doc mod

            case mb_iface of
                Just iface -> do
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
#if __GLASGOW_HASKELL__ <= 710 
                        provenance = Imported [ImpSpec decl_spec ImpAll]
#else
                        provenance = Just $ ImpSpec decl_spec ImpAll
#endif
                        env = mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"

                Nothing -> error $ "Could not determine the exports of the module " ++ moduleNameString mod_name --throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]

    case found_module of
        Found _ mod -> go mod
        NotFound {} ->
          case lookupModuleWithSuggestions dflags mod_name Nothing of
            LookupHidden _ ((mod, _):_) ->  go mod
            _ -> error "Cannot find module"
          -- error $ "Cannot find module: " ++ showPpr dflags fr_mods_hidden ++ "\n===>" ++ showPpr dflags fr_unusables
        err -> --throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
          error $ "Cannot find module: " ++ moduleNameString mod_name
                  ++ showSDoc dflags (cannotFindModule dflags mod_name err)
                  -- ++ "\n" ++ show err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "contains a name used in an invocation of lookupRdrNameInModule")

-- | Get the unqualified name from a 'NamedThing'.
unqualifiedName :: NamedThing nm => nm -> String
unqualifiedName = getOccString

-- Adapted from getUnfoldingsT in HERMIT:
getUnfolding_either :: ModGuts -> DynFlags -> Id -> Either String CoreExpr
getUnfolding_either guts dflags i =
  case lookup i (flattenBinds (mg_binds guts)) of
    Nothing ->
      case unfoldingInfo (idInfo i) of
        CoreUnfolding { uf_tmpl = uft } -> Right uft
        dunf@(DFunUnfolding {})         -> Right $ dFunExpr dunf
        _ -> case idDetails i of
              ClassOpId cls -> do
                let selectors = zip [ idName s | s <- classAllSelIds cls] [0..]
                    msg = getOccString i ++ " is not a method of " ++ getOccString cls ++ "."
                    idx = maybe (error msg) id $ lookup (idName i) selectors
                    r = mkDictSelRhs cls idx
                -- trace ("mkDictSelRhs = "  ++ showPpr dflags r)
                (Right r)
              idDet           -> Left $ "Cannot find unfolding for " ++ showPpr dflags i
                                        ++ "  (idDetails=" ++ showPpr dflags idDet ++ ")"
    Just e -> Right e
  where
    flattenBinds [] = []
    flattenBinds (NonRec b e:rest) = (b, e) : flattenBinds rest
    flattenBinds (Rec bs:rest) = bs ++ flattenBinds rest

getUnfolding :: HasCallStack => ModGuts -> DynFlags -> Id -> CoreExpr
getUnfolding guts dflags i =
  case getUnfolding_either guts dflags i of
    Left e -> error e
    Right x -> x

thNameToGhcName_ :: TH.Name -> CoreM Name
thNameToGhcName_ thName = do
  nameMaybe <- thNameToGhcName thName
  case nameMaybe of
    Nothing -> error $ "Cannot find name: " ++ show thName
    Just name -> return name

normaliseType' :: ModGuts -> Type -> CoreM Type
normaliseType' guts = fmap snd . normaliseTypeCo guts

normaliseTypeCo :: ModGuts -> Type -> CoreM (Coercion, Type)
normaliseTypeCo guts ty = normaliseTypeCo_role guts Nominal ty


normaliseTypeCo_role :: ModGuts -> Role -> Type -> CoreM (Coercion, Type)
normaliseTypeCo_role guts role ty = do
  (r, env) <- runTcM guts . runTcS $ do
    famInstEnvs <- getFamInstEnvs
    return (normaliseType famInstEnvs role ty)

  return r

-- | Build a CoreExpr for a DFunUnfolding
dFunExpr :: Unfolding -> CoreExpr
dFunExpr dunf@(DFunUnfolding {}) = mkCoreLams (df_bndrs dunf) $ mkCoreConApps (df_con dunf) (df_args dunf)
dFunExpr _ = error "dFunExpr: not a DFunUnfolding"

findIdTH :: ModGuts -> TH.Name -> CoreM Id
findIdTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findIdTH: Cannot find " ++ show thName
      Just name -> findId guts name emptyVarSet

findVarTH :: ModGuts -> TH.Name -> CoreM Var
findVarTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findVarTH: Cannot find " ++ show thName
      Just name -> findVar guts name emptyVarSet

findTyConTH :: ModGuts -> TH.Name -> CoreM TyCon
findTyConTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findTyConTH: Cannot find " ++ show thName
      Just name -> findTyCon guts name emptyVarSet

findDataConWorkIdTH :: ModGuts -> TH.Name -> CoreM Id
findDataConWorkIdTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findDataConWorkId: Cannot find " ++ show thName
      Just name -> findDataConWorkId guts name

findTypeTH :: ModGuts -> TH.Name -> CoreM Type
findTypeTH guts thName = do
    nameMaybe <- thNameToGhcName thName
    case nameMaybe of
      Nothing -> error $ "findTypeTH: Cannot find " ++ show thName
      Just name -> findType guts name emptyVarSet


untilNothingM :: Monad m => (a -> m (Maybe a)) -> a -> m a
untilNothingM f = go
  where
    go x = do
      fx <- f x
      case fx of
        Just r  -> go r
        Nothing -> return x

isDictVar :: Var -> Bool
isDictVar v =
  let str = occNameString (occName v)
  in
  length str >= 2 && (take 2 str == "$f" || take 2 str == "$d" || take 2 str == "$w" || take 2 str == "$c" || take 2 str == "C:")

isDict :: CoreExpr -> Bool
isDict (Var v) = isDictVar v
isDict e       = tcIsConstraintKind (tcTypeKind (exprType e))


isConstructor :: Var -> Bool
isConstructor v
  | isId v =
    case idDetails v of
      DataConWorkId {} -> True
      DataConWrapId {} -> True
      _ -> trace ("is not constructor: " ++ occNameString (occName v)) False
  | otherwise = False

getConstructorTyCon_maybe :: Var -> Maybe TyCon
getConstructorTyCon_maybe v
  | isId v = --trace ("idDetails: " ++ showSDocUnsafe (ppr (idDetails v))) $
    case idDetails v of
      DataConWorkId dc -> Just $ dataConTyCon dc
      DataConWrapId dc -> Just $ dataConTyCon dc
      -- DataConWorkId dc -> Just $ dataConTyCon dc
      _ -> Nothing
getConstructorTyCon_maybe _ = Nothing

builtinConstructor :: Var -> Bool
builtinConstructor v =
    "I#" == occNameString (occName v)
    || "D#" == occNameString (occName v)
    || "F#" == occNameString (occName v)
    || "C#" == occNameString (occName v)

getConstructorApp_maybe ::
  Expr Var
    -> Maybe
        ( [Expr Var]  -- Type arguments
        , [Expr Var]  -- Dictionary arguments
        , TyCon       -- The TyCon of the type of the constructor
        , Var         -- Constructor name
        , [Expr Var]) -- Constructor arguments
getConstructorApp_maybe e =
  case go e of
    -- Just (_, _, _, []) -> Nothing -- TODO: Do we want this?
    (Just (_, _, _, constr, _))
      | builtinConstructor constr -> Nothing
    r -> r
  where
    go (Var v)
      | Just tyCon <- getConstructorTyCon_maybe v = Just ([], [], tyCon, v, [])
    go (App f x)
      | isTypeArg x = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (x:tys, dicts, tyCon, constr, args)

      | isCoArg x || isDict x = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (tys, x:dicts, tyCon, constr, args)

      | otherwise             = do
          (tys, dicts, tyCon, constr, args) <- go f
          return (tys, dicts, tyCon, constr, x:args)

    go _ = Nothing


-- | Beta-reduce as many lambda-binders as possible.
betaReduceAll :: CoreExpr -> [CoreExpr] -> (CoreExpr, [CoreExpr])
betaReduceAll e0@(Lam v body) (a:as) =
  let (r, as') = betaReduceAll (substCoreExpr v a body) as
  in
    -- trace ("betaReduceAll: " ++ showSDocUnsafe (ppr (a, v))) $
    (r, as')

-- Coercion handling is based on the hypothetical operational semantics
-- for GHC's implementation of System FC given here https://github.com/ghc/ghc/tree/master/docs/core-spec
betaReduceAll e@(Cast (Lam v body) gamma) (a:as) =
  case a of
    Coercion gamma' -> -- S_CPush
      let rho = coercionRole gamma'
          gamma0 = mkNthCo rho 2 (mkNthCo Representational 2 gamma)
          gamma1 = mkSymCo (mkNthCo rho 3 (mkNthCo Representational 2 gamma))
          gamma2 = mkNthCo Representational 3 gamma
      in
      betaReduceAll (Lam v (Cast body gamma2)) (Coercion (mkTransCo gamma0 (mkTransCo gamma gamma1)) : as)

    Type tau -> -- S_TPush
      -- trace ("S_TPush: " ++ showSDocUnsafe (ppr (tau, v))) $
      let gamma' = mkSymCo (mkNthCo Nominal 0 gamma)
          tau' = Cast a gamma'
          (result, remainingArgs) = betaReduceAll (Lam v body) (tau':as)
      in
      (Cast result
           (mkInstCo gamma (mkSymCo (mkGReflCo Nominal tau (MCo gamma'))))
      ,remainingArgs)

    _ -> -- S_Push
      let gamma0 = mkSymCo (mkNthCo Representational 2 gamma)
          gamma1 = mkNthCo Representational 3 gamma
      in
      betaReduceAll (Lam v (Cast body gamma1)) ((Cast a gamma0) : as)
betaReduceAll e            as     = (e,as)

betaReduce :: CoreExpr -> CoreExpr
betaReduce x =
  let (f, args) = collectArgs x
  in
  case args of
    [] -> x
    _  -> uncurry mkApps $ betaReduceAll f args

 -- | Substitute all occurrences of a variable with an expression, in an expression.
substCoreExpr :: Var -> CoreExpr -> (CoreExpr -> CoreExpr)
substCoreExpr v e expr = substExpr (text "substCoreExpr") (extendSubst emptySub v e) expr
    where emptySub = mkEmptySubst (mkInScopeSet (localFreeVarsExpr (Let (NonRec v e) expr)))


-- | Find all locally defined free variables in an expression.
localFreeVarsExpr :: CoreExpr -> VarSet
localFreeVarsExpr = filterVarSet isLocalVar . freeVarsExpr


-- | Find all free variables in an expression.
freeVarsExpr :: CoreExpr -> VarSet
freeVarsExpr (Var v) = extendVarSet (freeVarsVar v) v
freeVarsExpr (Lit {}) = emptyVarSet
freeVarsExpr (App e1 e2) = freeVarsExpr e1 `unionVarSet` freeVarsExpr e2
freeVarsExpr (Lam b e) = delVarSet (freeVarsExpr e) b
freeVarsExpr (Let b e) = freeVarsBind b `unionVarSet` delVarSetList (freeVarsExpr e) (bindersOf b)
freeVarsExpr (Case s b ty alts) = let altFVs = delVarSet (unionVarSets $ map freeVarsAlt alts) b
                                  in unionVarSets [freeVarsExpr s, freeVarsType ty, altFVs]
freeVarsExpr (Cast e co) = freeVarsExpr e `unionVarSet` freeVarsCoercion co
freeVarsExpr (Tick t e) = freeVarsTick t `unionVarSet` freeVarsExpr e
freeVarsExpr (Type ty) = freeVarsType ty
freeVarsExpr (Coercion co) = freeVarsCoercion co

freeVarsTick :: Tickish Id -> VarSet
freeVarsTick (Breakpoint _ ids) = mkVarSet ids
freeVarsTick _ = emptyVarSet

-- | Find all free identifiers in a binding group, which excludes any variables bound in the group.
freeVarsBind :: CoreBind -> VarSet
freeVarsBind (NonRec v e) = freeVarsExpr e `unionVarSet` freeVarsVar v
freeVarsBind (Rec defs)   = let (bs,es) = unzip defs
                             in delVarSetList (unionVarSets (map freeVarsVar bs ++ map freeVarsExpr es)) bs

-- | Find all free variables on a binder. Equivalent to idFreeVars, but safe to call on type bindings.
freeVarsVar :: Var -> VarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsVar v = varTypeTyCoVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#else
freeVarsVar v = varTypeTyVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#endif

-- | Find all free variables in a case alternative, which excludes any variables bound in the alternative.
freeVarsAlt :: CoreAlt -> VarSet
freeVarsAlt (_,bs,e) = delVarSetList (freeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free local variables in a case alternative, which excludes any variables bound in the alternative.
localFreeVarsAlt :: CoreAlt -> VarSet
localFreeVarsAlt (_,bs,e) = delVarSetList (localFreeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free variables in a type.
freeVarsType :: Type -> TyVarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsType = tyCoVarsOfType
#else
freeVarsType = tyVarsOfType
#endif

-- | Find all free variables in a coercion.
freeVarsCoercion :: Coercion -> VarSet
freeVarsCoercion co =
  let vars = tyCoVarsOfCo co
  in vars


-- This function is copied from GHC, which defines but doesn't expose it.
-- A 'let' can bind a type variable, and idRuleVars assumes
-- it's seeing an Id. This function tests first.
bndrRuleAndUnfoldingVars :: Var -> VarSet
bndrRuleAndUnfoldingVars v | isTyVar v = emptyVarSet
                           | otherwise = idUnfoldingVars v



-- Adapted from CoreOpt and given a name (in the GHC API):
caseInlineT :: DynFlags -> CoreExpr -> CoreExpr
caseInlineT dflags = Data.transform (caseInline dflags)

-- -- TODO: Make sure this works (I believe it does)
-- caseInline_maybe :: DynFlags -> CoreExpr -> Maybe CoreExpr
-- caseInline_maybe dflags expr0@(Case _ wild0 _ _) =
--   case caseInline dflags expr0 of
--     expr1@(Case _ wild1 _ _)
--       | wild1 == wild0 -> Nothing
--     expr1              -> Just expr1
-- caseInline_maybe _ _ = Nothing

caseInline :: DynFlags -> CoreExpr -> CoreExpr
caseInline dflags expr =
  caseInline0 dflags init_subst expr
  where
    init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))

caseInline0 :: DynFlags -> Subst -> CoreExpr -> CoreExpr
caseInline0 dflags subst expr = go expr
  where

    in_scope     = substInScope subst

    in_scope_env = (in_scope, simpleUnfoldingFun)

    go (Case e b ty as)
        -- | trace ("wild name = " ++ showPpr dflags b) True
        -- , trace ("as = " ++ showPpr dflags (map (\(_, x, _) -> x) as)) True
        | not (varUnique b `elemVarSetByKey` altFvs)
        , Just lit <- exprIsLiteral_maybe in_scope_env e'
        , Just (altcon, bs, rhs) <- findAlt (LitAlt lit) as
        = caseInline0 dflags subst' rhs

        -- See Note [Getting the map/coerce RULE to work]
        -- | isDeadBinder b
        | not (varUnique b `elemVarSetByKey` altFvs)
        , Just (con, _tys, es) <- exprIsConApp_maybe in_scope_env e'
        , Just (altcon, bs, rhs) <- findAlt (DataAlt con) as
        = let (env', mb_prs) = mapAccumL simple_out_bind subst' $
                                 zipEqual "simpleOptExpr" bs es
              subst' = extendSubst subst b e
          in --trace ("second case: " ++ showPpr dflags b) $
            case altcon of
              DEFAULT -> caseInline0 dflags env' rhs --go rhs
              _       -> foldr substInto (caseInline0 dflags env' rhs) mb_prs

         -- Note [Getting the map/coerce RULE to work]
        -- | isDeadBinder b
        | not (varUnique b `elemVarSetByKey` altFvs)
        , [(DEFAULT, _, rhs)] <- as
        , isCoVarType (varType b)
        , (Var fun, _args) <- collectArgs e
        , fun `hasKey` coercibleSCSelIdKey
           -- without this last check, we get #11230
        = caseInline0 dflags subst' rhs --go rhs

        | otherwise
        = Case e' b' (CoreSubst.substTy subst ty)
                     (map (go_alt subst') as)
      where
         altFvs = unionVarSets $ map (\(_, _, rhs) -> exprFreeVars rhs) as
         e' = go e
         (subst', b') = subst_opt_bndr subst b
    go e = substExpr (text "caseInline0.go") subst e

    go_alt env (con, bndrs, rhs)
      = (con, bndrs', caseInline0 dflags subst' rhs)
      where
        (subst', bndrs') = subst_opt_bndrs env bndrs

-- | Skip wrapping in a 'let' and just substitute
substInto :: Maybe (Id, CoreExpr) -> CoreExpr -> CoreExpr
substInto Nothing body = body
substInto (Just (b, r)) body = substCoreExpr b r body

wrapLet :: Maybe (Id,CoreExpr) -> CoreExpr -> CoreExpr
wrapLet Nothing      body = body
wrapLet (Just (b,r)) body = Let (NonRec b r) body

simpleUnfoldingFun :: IdUnfoldingFun
simpleUnfoldingFun id
  | isAlwaysActive (idInlineActivation id) = idUnfolding id
  | otherwise                              = noUnfolding

simple_out_bind :: Subst -> (InVar, OutExpr)
                -> (Subst, Maybe (OutVar, OutExpr))
simple_out_bind subst (in_bndr, out_rhs)
  | Type out_ty <- out_rhs
  = --ASSERT( isTyVar in_bndr )
    ( CoreSubst.extendTvSubst subst in_bndr out_ty , Nothing)

  | Coercion out_co <- out_rhs
  = --ASSERT( isCoVar in_bndr )
    ( CoreSubst.extendCvSubst subst in_bndr out_co , Nothing)

  | otherwise
  = simple_out_bind_pair subst in_bndr Nothing out_rhs
                         (idOccInfo in_bndr) True False

-------------------
simple_out_bind_pair :: Subst
                     -> InId -> Maybe OutId -> OutExpr
                     -> OccInfo -> Bool -> Bool
                     -> (Subst, Maybe (OutVar, OutExpr))
simple_out_bind_pair subst in_bndr mb_out_bndr out_rhs
                     occ_info active stable_unf
  | post_inline_unconditionally
  = (  extendIdSubst subst in_bndr out_rhs 
    , Nothing)

  | otherwise
  = ( env', Just (out_bndr, out_rhs) )
  where
    (env', bndr1) = case mb_out_bndr of
                      Just out_bndr -> (subst, out_bndr)
                      Nothing       -> subst_opt_bndr subst in_bndr
    out_bndr = add_info env' in_bndr bndr1

    post_inline_unconditionally :: Bool
    post_inline_unconditionally
       | not active                  = False
       | isWeakLoopBreaker occ_info  = False -- If it's a loop-breaker of any kind, don't inline
                                             -- because it might be referred to "earlier"
       | stable_unf                  = False -- Note [Stable unfoldings and postInlineUnconditionally]
       | isExportedId in_bndr        = False -- Note [Exported Ids and trivial RHSs]
       | exprIsTrivial out_rhs       = True
       | coercible_hack              = True
       | otherwise                   = False

    -- See Note [Getting the map/coerce RULE to work]
    coercible_hack | (Var fun, args) <- collectArgs out_rhs
                   , Just dc <- isDataConWorkId_maybe fun
                   , dc `hasKey` heqDataConKey || dc `hasKey` coercibleDataConKey
                   = all exprIsTrivial args
                   | otherwise
                   = False

subst_opt_bndrs :: Subst -> [InVar] -> (Subst, [OutVar])
subst_opt_bndrs subst bndrs = mapAccumL subst_opt_bndr subst bndrs

subst_opt_bndr :: Subst -> InVar -> (Subst, OutVar)
subst_opt_bndr subst bndr
  | isTyVar bndr  = ( subst_tv , tv')
  | isCoVar bndr  = ( subst_cv , cv')
  | otherwise     = subst_opt_id_bndr subst bndr
  where
    (subst_tv, tv') = CoreSubst.substTyVarBndr subst bndr
    (subst_cv, cv') = CoreSubst.substCoVarBndr subst bndr

subst_opt_id_bndr :: Subst -> InId -> (Subst, OutId)
-- Nuke all fragile IdInfo, unfolding, and RULES;
--    it gets added back later by add_info
-- Rather like SimplEnv.substIdBndr
--
-- It's important to zap fragile OccInfo (which CoreSubst.substIdBndr
-- carefully does not do) because simplOptExpr invalidates it

subst_opt_id_bndr subst old_id
  = (new_subst, new_id)
  where
    Subst in_scope id_subst tv_subst cv_subst = subst

    id1    = uniqAway in_scope old_id
    id2    = setIdType id1 (CoreSubst.substTy subst (idType old_id))
    new_id = zapFragileIdInfo id2
             -- Zaps rules, unfolding, and fragile OccInfo
             -- The unfolding and rules will get added back later, by add_info

    new_in_scope = in_scope `extendInScopeSet` new_id

    no_change = new_id == old_id

        -- Extend the substitution if the unique has changed,
        -- See the notes with substTyVarBndr for the delSubstEnv
    new_id_subst
      | no_change = delVarEnv id_subst old_id
      | otherwise = extendVarEnv id_subst old_id (Var new_id)

    new_subst = Subst new_in_scope new_id_subst tv_subst cv_subst

add_info :: Subst -> InVar -> OutVar -> OutVar
add_info subst old_bndr new_bndr
 | isTyVar old_bndr = new_bndr
 | otherwise        = maybeModifyIdInfo mb_new_info new_bndr
 where
   mb_new_info = substIdInfo subst new_bndr (idInfo old_bndr)

--
-- Adapted from GHC API:
--

decomposeFunCo_maybe ::
                  Role      -- Role of the input coercion
               -> Coercion  -- Input coercion
               -> Maybe (Coercion, Coercion)
-- Expects co :: (s1 -> t1) ~ (s2 -> t2)
-- Returns (co1 :: s1~s2, co2 :: t1~t2)
-- See Note [Function coercions] for the "2" and "3"
decomposeFunCo_maybe r co
  | all_ok = Just (mkNthCo r 2 co, mkNthCo r 3 co)
  | otherwise = Nothing
  where
    Pair s1t1 s2t2 = coercionKind co
    all_ok = isFunTy s1t1 && isFunTy s2t2

-- From  CoreOpt:
    -- Unconditionally safe to inline
safe_to_inline :: OccInfo -> Bool
safe_to_inline (IAmALoopBreaker {}) = False
safe_to_inline IAmDead              = True
safe_to_inline occ@(OneOcc {})      =  not (occ_in_lam occ)
                                    && occ_one_br occ
safe_to_inline (ManyOccs {})        = False


maybeApply :: (a -> Maybe a) -> a -> a
maybeApply f x0 =
  case f x0 of
    Just x -> x
    _      -> x0


workDataCon_maybe :: CoreExpr -> Maybe CoreExpr
workDataCon_maybe (Var v)
  | isId v =
      case idDetails v of
        DataConWrapId dc -> Just $ Var $ dataConWorkId dc
        _ -> Nothing
workDataCon_maybe _ = Nothing


-- | Transform scrutinee of a case. If not a 'case', leave it alone.
onScrutinee :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
onScrutinee f = maybeApply (onScrutinee_maybe (Just . f))
-- onScrutinee f (Case scrutinee wild ty alts) = Case (f scrutinee) wild ty alts
-- onScrutinee _ e = e

onScrutinee_maybe :: (CoreExpr -> Maybe CoreExpr) -> CoreExpr -> Maybe CoreExpr
onScrutinee_maybe f (Case scrutinee wild ty alts) = do
    s' <- f scrutinee
    Just $ Case s' wild ty alts
onScrutinee_maybe _ e = Nothing


-- | @Let (NonRec v e) body@ ==> @body[e/v]@
letNonRecSubst :: CoreExpr -> CoreExpr
letNonRecSubst (Let (NonRec v rhs) body) =
  -- trace ("letNonRecSubst: v = " ++ showSDocUnsafe (ppr v)) $
  substCoreExpr v rhs body
letNonRecSubst expr = expr

isClassVar :: CoreExpr -> Bool
isClassVar (Var v) =
  let str = occNameString (occName v)
  in
  length str >= 2 && take 2 str == "C:"
isClassVar _ = False

isDictNotClass :: DynFlags -> CoreExpr -> Bool
isDictNotClass dflags e =
  isDict e && not (isClassVar e)

isDictNotClassApp :: DynFlags -> CoreExpr -> Bool
isDictNotClassApp dflags e@(App _ _) =
  case collectArgs e of
    (fn, _) -> let r = isDictNotClass dflags fn in trace ("isDictNotClassApp: " ++ showPpr dflags (r, fn))  r
isDictNotClassApp dflags e = False

-- | $fDict x0 x1 ... xN    ==>   [unfolding of $fDict] x0 x1 ... xN
unfoldAndReduceDict_either :: ModGuts -> DynFlags -> CoreExpr -> Either String CoreExpr
unfoldAndReduceDict_either guts dflags e =
  case collectArgs e of
    -- (_, []) -> Left "unfoldAndReduceDict_either: empty args"
    (fnE@(Var dictFn), dictArgs) ->
      if isDictNotClass dflags fnE
        then
          case getUnfolding_either guts dflags dictFn of
            Left err -> Left err
            Right dictFnUnfolding ->
              case betaReduceAll dictFnUnfolding dictArgs of
                (fn, args) -> Right $ mkApps fn args
        else
          Left $ "unfoldAndReduceDict_either: not isDictNotClass: " ++ showPpr dflags e
    _ -> Left $ "unfoldAndReduceDict_either: not of form App (... (App (Var v) x) ...) z. Given: " ++ showPpr dflags e

tryUnfoldAndReduceDict :: ModGuts -> DynFlags -> CoreExpr -> CoreExpr
tryUnfoldAndReduceDict guts dflags e =
  case unfoldAndReduceDict_either guts dflags e of
    Right e' -> e'
    _ -> e

unfoldAndReduceDict_maybe :: ModGuts -> DynFlags -> CoreExpr -> Maybe CoreExpr
unfoldAndReduceDict_maybe guts dflags e =
  case unfoldAndReduceDict_either guts dflags e of
    Right e' -> Just e'
    _ -> Nothing

unfoldAndReduceDict :: HasCallStack => ModGuts -> DynFlags -> CoreExpr -> CoreExpr
unfoldAndReduceDict guts dflags e =
  case unfoldAndReduceDict_either guts dflags e of
    Right e' -> e'
    Left err -> error ("unfoldAndReduceDict: " ++ err)

replaceVarId :: Id -> CoreExpr -> CoreExpr -> CoreExpr
replaceVarId i new e =
  case replaceVarId_maybe i new e of
    Just e' -> e'
    _ -> e

transformMaybe :: Data a => (a -> Maybe a) -> a -> Maybe a
transformMaybe f e0 =
  let (r, Any madeProgress) = runWriter (Data.transformM go e0)
  in
    if madeProgress
      then Just r
      else Nothing
  where
    go e =
      case f e of
        Nothing -> return e
        Just e' -> tell (Any True) >> return e'

replaceVarId_maybe :: Id -> CoreExpr -> CoreExpr -> Maybe CoreExpr
replaceVarId_maybe i new (Var v)
  | v == i = Just new
replaceVarId_maybe _ _ _ = Nothing

onCastExpr_maybe :: (CoreExpr -> CoreExpr) -> CoreExpr -> Maybe CoreExpr
onCastExpr_maybe t (Cast e co) = Just (Cast (t e) co)
onCastExpr_maybe _ _ = Nothing

onCastExpr :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
onCastExpr t = maybeApply (onCastExpr_maybe t)

-- | Transform the function position of a collection of Apps:
-- f :@ x0 :@ x1 :@ ... :@ xN    ==>    (t f) :@ x0 :@ x1 :@ ... :@ xN
onAppFun_maybe :: (CoreExpr -> Maybe CoreExpr) -> CoreExpr -> Maybe CoreExpr
onAppFun_maybe t e@(App _ _) =
  let (f, args) = collectArgs e
  in mkApps <$> t f <*> pure args
onAppFun_maybe t e = Nothing

onAppFunId_maybe :: (Id -> Maybe CoreExpr) -> CoreExpr -> Maybe CoreExpr
onAppFunId_maybe t e = onAppFun_maybe go e
  where
    go (Var f) = t f
    go _ = Nothing

onAppFun :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
onAppFun = maybeApply . onAppFun_maybe . (Just .)

onAppFunId :: (Id -> CoreExpr) -> CoreExpr -> CoreExpr
onAppFunId = maybeApply . onAppFunId_maybe . (Just .)

-- | ((case s wild of { P ... -> f; ... }) v)   ==>   case s wild of { P ... -> f v; ... }
caseFloatApp_maybe :: CoreExpr -> Maybe CoreExpr
caseFloatApp_maybe e0@(App (Case s b wild alts) v) =
  let vFVs = freeVarsExpr v
      altsFVs = foldr unionVarSet emptyVarSet $ map (mkVarSet . altVars) alts
      newAlts = mapAlts (`App` v) alts
  in
    if isEmptyVarSet (intersectVarSet vFVs altsFVs)
      then Just $ Case s b (coreAltsType newAlts) newAlts
      else Nothing
    -- captures    <- appT (liftM (map mkVarSet) caseAltVarsT) (arr freeVarsExpr) (flip (map . intersectVarSet))
    -- bndrCapture <- appT caseBinderIdT (arr freeVarsExpr) elemVarSet
    -- appT ((if not bndrCapture then idR else alphaCaseBinderR Nothing)
    --       >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAltR)
    --      )
    --       idR
    --       (\(Case s b _ alts) v -> let newAlts = mapAlts (`App` v) alts
    --                                 in Case s b (coreAltsType newAlts) newAlts)
caseFloatApp_maybe _ = Nothing

caseFloatApp :: CoreExpr -> CoreExpr
caseFloatApp = maybeApply caseFloatApp_maybe

-- f (case s wild of { P ... -> e; ... })   ==>   case s wild of { P ... -> f e; ... }
caseFloatArg_maybe :: CoreExpr -> Maybe CoreExpr
caseFloatArg_maybe e0@(App f (Case s b wild alts)) =
  let fFVs = freeVarsExpr f
      altsFVs = foldr unionVarSet emptyVarSet $ map (mkVarSet . altVars) alts
      newAlts = mapAlts (f `App`) alts
  in
    if isEmptyVarSet (intersectVarSet fFVs altsFVs)
      then Just $ Case s b (coreAltsType newAlts) newAlts
      else Nothing
caseFloatArg_maybe e = Nothing

caseFloatArg :: CoreExpr -> CoreExpr
caseFloatArg = maybeApply caseFloatArg_maybe

coercionRKind :: Coercion -> Type
coercionRKind co =
  let Pair _ y = coercionKind co
  in y

coercionLKind :: Coercion -> Type
coercionLKind co =
  let Pair x _ = coercionKind co
  in x

combineCasts_maybe :: DynFlags -> CoreExpr -> Maybe CoreExpr
combineCasts_maybe dflags origE@(Cast (Cast e coA) coB) =
  if coercionRole coA /= coercionRole coB
    then error "combineCasts_maybe: *** coercion roles do not match ***"
    else
     let newCo = mkTransCo coA coB
     in
     Just $ Cast e newCo
combineCasts_maybe _ _ = Nothing

combineCasts :: DynFlags -> CoreExpr -> CoreExpr
combineCasts dflags e =
  case combineCasts_maybe dflags e of
    Just e' -> e'
    _ -> e

onAppArg_maybe :: (CoreExpr -> CoreExpr) -> CoreExpr -> Maybe CoreExpr
onAppArg_maybe t (App f x) = Just $ App f (t x)
onAppArg_maybe _ _ = Nothing

onAppArg :: (CoreExpr -> CoreExpr) -> CoreExpr -> CoreExpr
onAppArg t = maybeApply (onAppArg_maybe t)


-- Modified from 'Inst':

mkEqBox :: TcCoercion -> CoreExpr
mkEqBox co =
    Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Coercion co
  where
    k = tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

mkEqBoxRepr :: TcCoercion -> CoreExpr
mkEqBoxRepr co =
    Var (dataConWorkId eqDataCon) :@ Type k :@ Type ty1 :@ Type ty2 :@ Coercion co
  where
    k = mkReprPrimEqPred ty1 ty2 --tcTypeKind ty1
    Pair ty1 ty2 = coercionKind co

-- From hermit's HERMIT.Core:
-- | Map a function over the RHS of each case alternative.
mapAlts :: (CoreExpr -> CoreExpr) -> [CoreAlt] -> [CoreAlt]
mapAlts f alts = [ (ac, vs, f e) | (ac, vs, e) <- alts ]
-- | List the variables bound by a case alternative.
altVars :: CoreAlt -> [Var]
altVars (_,vs,_) = vs


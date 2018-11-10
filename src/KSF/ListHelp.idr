module KSF.ListHelp

%access public export
%default total

-- TODO add to Prelude
Uninhabited ([] = _ :: _) where
    uninhabited Refl impossible
  
Uninhabited (_ :: _ = []) where
  uninhabited Refl impossible
  
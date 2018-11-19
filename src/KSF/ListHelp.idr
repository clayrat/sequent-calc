module KSF.ListHelp

%access public export
%default total

-- TODO added to Prelude after 1.3.1
Uninhabited ([] = _ :: _) where
    uninhabited Refl impossible
  
Uninhabited (_ :: _ = []) where
  uninhabited Refl impossible
  
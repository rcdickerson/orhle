module MapNames
  ( MappableNames
  , mapNames
  , prefix
  , substitute
  , substituteAll
  ) where

class MappableNames a where
  mapNames :: (String -> String) -> a -> a

prefix :: MappableNames a => String -> a -> a
prefix pre a = mapNames ((++) pre) a

substitute :: MappableNames a => String -> String -> a -> a
substitute from to a = mapNames sub a
  where sub name = if (name == from) then to else name

substituteAll :: MappableNames a => [String] -> [String] -> a -> a
substituteAll from to x = foldr (uncurry substitute) x $ zip from to

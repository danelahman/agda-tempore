------------------------------------------------------------------
-- Comparison relations                                         --
--                                                              --
-- The six relations of the comparison rule `cmp`: equality,    --
-- disequality and the four orderings. All are typed alike, so  --
-- one rule tagged by the relation covers them.                 --
------------------------------------------------------------------

module TypeInference.OpenSyntax.Comparisons where

data Cmp : Set where
  eq ne lt le gt ge : Cmp

module MyLevel where

  postulate Level : Set 
  postulate lzero : Level
  postulate lsucc : Level → Level
  postulate _⊔_ : Level → Level → Level 
  
  infixl 5 _⊔_ 

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsucc #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}

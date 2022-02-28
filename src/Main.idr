module Main

import Prelude

import Playground

%hide Prelude.False
%hide Prelude.True
%hide Prelude.No
%hide Prelude.Yes
%hide Prelude.Equal

main : IO ()
main = do
  case rel Equal.Equal Bool.False Bool.True of
    False => putStrLn "NO"
    True => putStrLn "YES"
  putStrLn "OK"

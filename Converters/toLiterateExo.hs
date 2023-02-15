
main = interact (unlines . restoreMarkdown . lines)

restoreMarkdown :: [String] -> [String]
restoreMarkdown [] = []
restoreMarkdown (l:ls)
  | isComment l = unComment l : restoreMarkdown ls
  | isExo l = mkExo l : skipSol ls
  | otherwise = l : restoreMarkdown ls

skipSol :: [String] -> [String]
skipSol (l:ls)
  | isComment l = unComment l : restoreMarkdown ls
  | isEmpty l = l : restoreMarkdown ls
  | otherwise = skipSol ls 

unComment :: String -> String
unComment = drop (length prefix)

isComment :: String -> Bool
isComment cs = take 5 cs == prefix

prefix :: String
prefix = "--MD " 

exo :: String
exo = "--EXO "

isExo :: String -> Bool
isExo cs = take (length exo) cs == exo

mkExo :: String -> String
mkExo = drop (length exo) 

isEmpty :: String -> Bool
isEmpty = all (' '==)

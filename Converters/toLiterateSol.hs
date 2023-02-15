
main = interact (unlines . restoreMarkdown . lines)

restoreMarkdown :: [String] -> [String]
restoreMarkdown [] = []
restoreMarkdown (l:ls)
  | isComment l = unComment l : restoreMarkdown ls
  | isExo l = keepSol ls
  | otherwise = l : restoreMarkdown ls

keepSol :: [String] -> [String]
keepSol (l:ls)
  | isComment l = unComment l : restoreMarkdown ls
  | isEmpty l = l : restoreMarkdown ls
  | otherwise = l : keepSol ls 

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

isEmpty :: String -> Bool
isEmpty = all (' '==)
